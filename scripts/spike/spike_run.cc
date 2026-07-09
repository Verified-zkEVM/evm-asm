// spike_run.cc — minimal SPIKE driver for the codegen stateless guest.
// Usage: spike_run <guest.elf> <input-file> <output-file>
//   Mirrors `ziskemu -e <elf> -i <input> -o <output>`:
//   - loads guest.elf; preloads <input-file> at 0x40000000 (an 8-byte zero meta
//     word followed by the ziskemu -i file, which is [8B LE len][blob][pad]);
//   - installs the M-mode trap handler at 0x60000000 and points mtvec at it
//     (services read_input t0=0xF2 and halt a7=93 — the guest's only 2 ecalls);
//   - registers the zisk_accel crypto-CSR extension;
//   - runs to HTIF exit, then writes SPIKE_OUTPUT_LEN bytes (default 256) from
//     0xa0010000 to <output-file>.
#include <sys/syscall.h>
#include "sim.h"
#include "cfg.h"
#include "mmu.h"
#include "processor.h"
#include "extension.h"
#include "debug_module.h"
#include "elfloader.h"
#include "handler_bin.h"   // generated: handler_bin[] / handler_bin_len
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <optional>
#include <vector>
#include <string>
#include <fstream>
#include <iterator>
#include <cstdlib>

extern extension_t* make_zisk_accel_extension();

static const reg_t INPUT_ADDR    = 0x40000000ULL;
static const reg_t OUTPUT_ADDR   = 0xa0010000ULL;
static const size_t DEFAULT_OUTPUT_LEN = 256;
static const reg_t HANDLER_ADDR  = 0x60000000ULL;
static const reg_t HALT_FLAG     = 0x60008000ULL;  // handler writes nonzero here on halt
static const uint64_t STEP_CAP   = 20000000000ULL; // safety cap on total instructions
static const size_t STEP_BATCH   = 2000000;


static size_t output_len() {
  const char* raw = getenv("SPIKE_OUTPUT_LEN");
  if (!raw || !*raw) return DEFAULT_OUTPUT_LEN;
  char* end = nullptr;
  unsigned long long n = strtoull(raw, &end, 0);
  if (!end || *end != '\0' || n == 0) {
    fprintf(stderr, "spike_run: invalid SPIKE_OUTPUT_LEN=%s\n", raw);
    exit(2);
  }
  return (size_t)n;
}

static void wr(simif_t* s, reg_t a, const uint8_t* d, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    char* p = s->addr_to_mem(a + i);
    if (!p) { fprintf(stderr, "spike_run: unmapped write @0x%llx\n",
                      (unsigned long long)(a + i)); exit(2); }
    *p = (char)d[i];
  }
}
static void rd(simif_t* s, reg_t a, uint8_t* d, size_t n) {
  for (size_t i = 0; i < n; ++i) { char* p = s->addr_to_mem(a + i); d[i] = p ? (uint8_t)*p : 0; }
}

int main(int argc, char** argv) {
  if (argc != 4) { fprintf(stderr, "usage: %s <guest.elf> <input> <output>\n", argv[0]); return 2; }

  cfg_t cfg;
  cfg.isa  = "RV64IMAC_Zicclsm";
  cfg.priv = "M";
  cfg.hartids = std::vector<size_t>{0};
  cfg.mem_layout = {
    mem_cfg_t(0x40000000ULL, 0x01000000ULL),  // input arena
    mem_cfg_t(0x60000000ULL, 0x00010000ULL),  // handler + tohost/fromhost
    mem_cfg_t(0x7ffff000ULL, 0x40001000ULL),  // headers+text+data+sszscratch+output -> 0xc0000000
  };
  std::vector<std::pair<reg_t, abstract_mem_t*>> mems;
  for (auto& m : cfg.mem_layout) mems.push_back({m.get_base(), new mem_t(m.get_size())});

  std::vector<std::string> args = { argv[1] };
  // Env-gated commit log: set SPIKE_COMMITLOG=<file> to get a per-instruction
  // trace (pc, insn word, reg/mem writes) for EVM-faithfulness debugging.
  const char* log_path = getenv("SPIKE_COMMITLOG");
  sim_t sim(&cfg, false, mems, {}, false, args, debug_module_config_t(),
            log_path, false, nullptr, false, nullptr, std::nullopt);
  if (log_path) sim.configure_log(false, true);
  processor_t* p = sim.get_core(0);
  // register_extension() (called post-construction) does NOT invoke get_csrs(),
  // and the proc's init-time get_csrs sweep already ran, so add the accelerator
  // CSRs to the csrmap explicitly.
  extension_t* ext = make_zisk_accel_extension();
  p->register_extension(ext);
  for (auto& c : ext->get_csrs(*p)) p->get_state()->add_csr(c->address, c);

  // trap handler + mtvec; zero the halt flag
  wr(&sim, HANDLER_ADDR, handler_bin, handler_bin_len);
  p->get_state()->mtvec->write(HANDLER_ADDR);
  uint8_t zero8[8] = {0};
  wr(&sim, HALT_FLAG, zero8, 8);

  // The ELF is loaded by sim.run()'s boot, which we bypass for a step-loop, so
  // load it explicitly into memory and start at its entry (bypassing spike's
  // reset bootrom at 0x1000). The guest's _start sets up its own registers and
  // fetches input via the read_input ecall, so it needs nothing from boot.
  reg_t entry = 0;
  load_elf(argv[1], &sim.memif(), &entry, 0, 64);
  p->get_state()->pc = entry;

  // preload input: 8-byte zero meta + ziskemu -i file ([8B len][blob][pad])
  std::ifstream f(argv[2], std::ios::binary);
  std::vector<uint8_t> blob((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
  std::vector<uint8_t> img(8, 0);
  img.insert(img.end(), blob.begin(), blob.end());
  wr(&sim, INPUT_ADDR, img.data(), img.size());

  if (getenv("SPIKE_RUN_DEBUG")) {
    uint8_t insn[4]; rd(&sim, entry, insn, 4);
    fprintf(stderr, "[dbg] entry=0x%llx insn@entry=%02x%02x%02x%02x pc=0x%llx\n",
            (unsigned long long)entry, insn[3], insn[2], insn[1], insn[0],
            (unsigned long long)p->get_state()->pc);
    for (int i = 0; i < 60; ++i) {
      reg_t pc = p->get_state()->pc;
      p->step(1);
      fprintf(stderr, "[dbg] step %2d: pc=0x%llx -> 0x%llx mcause=0x%llx\n", i,
              (unsigned long long)pc, (unsigned long long)p->get_state()->pc,
              (unsigned long long)p->get_state()->mcause->read());
    }
  }

  // step until the handler signals halt (HALT_FLAG nonzero) or the cap is hit.
  // flag==1 clean halt; flag==2 guest fault (info at HALT_FLAG+0x10/0x18/0x20).
  uint64_t flagv = 0;
  for (uint64_t done = 0; done < STEP_CAP; done += STEP_BATCH) {
    p->step(STEP_BATCH);
    uint8_t flag[8]; rd(&sim, HALT_FLAG, flag, 8);
    memcpy(&flagv, flag, 8);
    if (flagv) break;
  }
  if (flagv == 2) {
    uint8_t b[8]; uint64_t mcause=0, mtval=0, mepc=0;
    rd(&sim, HALT_FLAG + 0x10, b, 8); memcpy(&mcause, b, 8);
    rd(&sim, HALT_FLAG + 0x18, b, 8); memcpy(&mtval, b, 8);
    rd(&sim, HALT_FLAG + 0x20, b, 8); memcpy(&mepc, b, 8);
    fprintf(stderr, "spike_run: guest FAULT mcause=0x%llx mtval=0x%llx mepc=0x%llx\n",
            (unsigned long long)mcause, (unsigned long long)mtval, (unsigned long long)mepc);
  } else if (flagv == 0) {
    fprintf(stderr, "spike_run: step cap reached without halt\n");
  }
  bool halted = (flagv == 1);

  size_t out_len = output_len();
  std::vector<uint8_t> out(out_len);
  rd(&sim, OUTPUT_ADDR, out.data(), out_len);
  std::ofstream of(argv[3], std::ios::binary);
  of.write((const char*)out.data(), out_len);
  for (auto& m : mems) delete m.second;
  return halted ? 0 : 3;
}
