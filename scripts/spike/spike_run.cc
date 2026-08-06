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
//
// Debug env (optional; unset = previous byte-identical behavior):
//   SPIKE_COMMITLOG=<file>   per-instruction commit log (existing)
//   SPIKE_DEBUG_CMD=<file>   headless debug script (see scripts/spike/README.md)
//   SPIKE_WATCH=<hex>        true 8-byte write watch: print PC+old+new on any change
//   SPIKE_WATCH_STOP=1       stop the run after the first watch hit (default: log+continue)
//   SPIKE_BREAK_PC=<hex>     stop after executing the insn at this PC (logs once)
//   SPIKE_RUN_DEBUG=1        existing: dump first 60 steps
//   SPIKE_INIT_WRITES=<addr>:<u64>[,<addr>:<u64>...]
//                            tooling-only LE dword writes after ELF/input load
//   SPIKE_DUMP_RANGES=<addr:length,...> + SPIKE_DUMP_FILE=<file>
//                            final-memory ranges for tooling-only inspection
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
#include <functional>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <iterator>
#include <cstdlib>
#include <cctype>

extern extension_t* make_zisk_accel_extension();

static const reg_t INPUT_ADDR    = 0x40000000ULL;
static const reg_t OUTPUT_ADDR   = 0xa0010000ULL;
static const size_t DEFAULT_OUTPUT_LEN = 256;
static const reg_t HANDLER_ADDR  = 0x60000000ULL;
static const reg_t HALT_FLAG     = 0x60008000ULL;  // handler writes nonzero here on halt
static const uint64_t STEP_CAP   = 20000000000ULL; // safety cap on total instructions
static const size_t STEP_BATCH   = 2000000;

struct DumpRange {
  reg_t addr;
  size_t len;
};


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

static uint64_t rd_u64(simif_t* s, reg_t a) {
  uint8_t b[8]; rd(s, a, b, 8);
  uint64_t v = 0; memcpy(&v, b, 8); return v;
}

static unsigned long long parse_u64(const char* raw, const char* what) {
  char* end = nullptr;
  unsigned long long v = strtoull(raw, &end, 0);
  if (!end || *end != '\0') {
    fprintf(stderr, "spike_run: invalid %s=%s\n", what, raw);
    exit(2);
  }
  return v;
}

struct InitWrite {
  reg_t addr;
  uint64_t value;
};

static std::vector<InitWrite> parse_init_writes() {
  const char* raw = getenv("SPIKE_INIT_WRITES");
  if (!raw || !*raw) return {};
  std::vector<InitWrite> writes;
  std::string specs(raw);
  size_t begin = 0;
  while (begin <= specs.size()) {
    size_t end = specs.find(',', begin);
    std::string spec = specs.substr(begin, end == std::string::npos
                                             ? std::string::npos : end - begin);
    size_t colon = spec.find(':');
    if (spec.empty() || colon == std::string::npos ||
        spec.find(':', colon + 1) != std::string::npos) {
      fprintf(stderr, "spike_run: invalid SPIKE_INIT_WRITES item '%s'\n",
              spec.c_str());
      exit(2);
    }
    std::string addr_s = spec.substr(0, colon);
    std::string value_s = spec.substr(colon + 1);
    writes.push_back({(reg_t)parse_u64(addr_s.c_str(), "SPIKE_INIT_WRITES address"),
                      (uint64_t)parse_u64(value_s.c_str(), "SPIKE_INIT_WRITES value")});
    if (end == std::string::npos) break;
    begin = end + 1;
  }
  return writes;
}

static std::vector<DumpRange> parse_dump_ranges() {
  const char* raw = getenv("SPIKE_DUMP_RANGES");
  const char* path = getenv("SPIKE_DUMP_FILE");
  if (!raw && !path) return {};
  if (!raw || !*raw || !path || !*path) {
    fprintf(stderr,
            "spike_run: SPIKE_DUMP_RANGES and SPIKE_DUMP_FILE must be set together\n");
    exit(2);
  }

  std::vector<DumpRange> ranges;
  std::string specs(raw);
  size_t begin = 0;
  while (begin <= specs.size()) {
    size_t end = specs.find(',', begin);
    std::string spec = specs.substr(begin, end == std::string::npos
                                             ? std::string::npos : end - begin);
    size_t colon = spec.find(':');
    if (spec.empty() || colon == std::string::npos ||
        spec.find(':', colon + 1) != std::string::npos) {
      fprintf(stderr, "spike_run: invalid SPIKE_DUMP_RANGES item '%s'\n",
              spec.c_str());
      exit(2);
    }
    std::string addr_s = spec.substr(0, colon);
    std::string len_s = spec.substr(colon + 1);
    unsigned long long addr = parse_u64(addr_s.c_str(), "SPIKE_DUMP_RANGES address");
    unsigned long long len = parse_u64(len_s.c_str(), "SPIKE_DUMP_RANGES length");
    if (len == 0 || len > static_cast<unsigned long long>(SIZE_MAX) ||
        addr > UINT64_MAX - (len - 1)) {
      fprintf(stderr, "spike_run: invalid SPIKE_DUMP_RANGES item '%s'\n",
              spec.c_str());
      exit(2);
    }
    ranges.push_back({(reg_t)addr, (size_t)len});
    if (end == std::string::npos) break;
    begin = end + 1;
  }
  if (ranges.empty()) {
    fprintf(stderr, "spike_run: SPIKE_DUMP_RANGES has no ranges\n");
    exit(2);
  }
  return ranges;
}

static void put_le_u32(std::ofstream& out, uint32_t value) {
  uint8_t b[4] = {(uint8_t)value, (uint8_t)(value >> 8),
                  (uint8_t)(value >> 16), (uint8_t)(value >> 24)};
  out.write((const char*)b, sizeof(b));
}

static void put_le_u64(std::ofstream& out, uint64_t value) {
  uint8_t b[8];
  for (unsigned i = 0; i < sizeof(b); ++i) b[i] = (uint8_t)(value >> (8 * i));
  out.write((const char*)b, sizeof(b));
}

static void dump_ranges(simif_t* memif, const std::vector<DumpRange>& ranges,
                        const char* path) {
  std::ofstream out(path, std::ios::binary | std::ios::trunc);
  if (!out) {
    fprintf(stderr, "spike_run: cannot open SPIKE_DUMP_FILE=%s\n", path);
    exit(2);
  }
  const char magic[] = "SPKDMP01";
  out.write(magic, sizeof(magic) - 1);
  put_le_u32(out, 1);  // format version
  put_le_u32(out, (uint32_t)ranges.size());
  for (const DumpRange& range : ranges) {
    put_le_u64(out, range.addr);
    put_le_u64(out, range.len);
    for (size_t i = 0; i < range.len; ++i) {
      char* p = memif->addr_to_mem(range.addr + i);
      if (!p) {
        fprintf(stderr, "spike_run: unmapped dump read @0x%llx\n",
                (unsigned long long)(range.addr + i));
        exit(2);
      }
      out.put(*p);
    }
  }
  if (!out) {
    fprintf(stderr, "spike_run: write failed for SPIKE_DUMP_FILE=%s\n", path);
    exit(2);
  }
  fprintf(stderr, "spike_run: dumped %zu final-memory range(s) to %s\n",
          ranges.size(), path);
}

// ABI / numeric register name -> x-reg index. Returns -1 on failure.
static int parse_reg_name(const std::string& s) {
  if (s.empty()) return -1;
  if (s[0] == 'x' || s[0] == 'X') {
    char* end = nullptr;
    long n = strtol(s.c_str() + 1, &end, 10);
    if (end && *end == '\0' && n >= 0 && n < 32) return (int)n;
  }
  static const char* abi[] = {
    "zero","ra","sp","gp","tp","t0","t1","t2",
    "s0","s1","a0","a1","a2","a3","a4","a5",
    "a6","a7","s2","s3","s4","s5","s6","s7",
    "s8","s9","s10","s11","t3","t4","t5","t6"
  };
  // fp == s0
  if (s == "fp") return 8;
  for (int i = 0; i < 32; ++i)
    if (s == abi[i]) return i;
  // bare number
  char* end = nullptr;
  long n = strtol(s.c_str(), &end, 10);
  if (end && *end == '\0' && n >= 0 && n < 32) return (int)n;
  return -1;
}

static void print_regs(processor_t* p) {
  auto* st = p->get_state();
  static const char* abi[] = {
    "zero","ra","sp","gp","tp","t0","t1","t2",
    "s0","s1","a0","a1","a2","a3","a4","a5",
    "a6","a7","s2","s3","s4","s5","s6","s7",
    "s8","s9","s10","s11","t3","t4","t5","t6"
  };
  for (int r = 0; r < 32; ++r) {
    fprintf(stderr, "  %4s: 0x%016llx%s", abi[r],
            (unsigned long long)st->XPR[r],
            ((r + 1) % 4 == 0) ? "\n" : "");
  }
}

static void print_watch_hit(processor_t* p, reg_t addr, uint64_t oldv, uint64_t newv) {
  auto* st = p->get_state();
  fprintf(stderr,
          "SPIKE_WATCH hit addr=0x%llx old=0x%016llx new=0x%016llx pc=0x%llx\n"
          "  ra=0x%llx sp=0x%llx a0=0x%llx a1=0x%llx a2=0x%llx a3=0x%llx\n"
          "  s0=0x%llx s1=0x%llx s2=0x%llx s3=0x%llx s4=0x%llx\n",
          (unsigned long long)addr,
          (unsigned long long)oldv, (unsigned long long)newv,
          (unsigned long long)st->pc,
          (unsigned long long)st->XPR[1], (unsigned long long)st->XPR[2],
          (unsigned long long)st->XPR[10], (unsigned long long)st->XPR[11],
          (unsigned long long)st->XPR[12], (unsigned long long)st->XPR[13],
          (unsigned long long)st->XPR[8], (unsigned long long)st->XPR[9],
          (unsigned long long)st->XPR[18], (unsigned long long)st->XPR[19],
          (unsigned long long)st->XPR[20]);
}

// Minimal headless debugger. Stock spike's interactive()/--debug-cmd is private
// to sim_t and only runs inside sim.run()/idle(), which our driver bypasses
// (custom step loop + HALT_FLAG). So we reimplement the useful subset here.
//
// Commands (one per line; # comments; blank ignored):
//   help
//   pc [core]                 print PC (core ignored; always hart 0)
//   reg [core] [reg]          print one/all XPR
//   mem <hex addr>            print 8-byte LE at physical addr
//   until pc [core] <hex>     run until PC == val
//   until mem <hex> <hex>     run until 8-byte LE at addr == val
//   until reg [core] <r> <v>  run until XPR[r] == val
//   until halt                run until HALT_FLAG nonzero
//   rs / run                  alias for until halt
//   step [n]                  step n instructions (default 1)
//   quit / q                  end debug script; resume normal dump
//
// Note: stock `until mem ADDR VAL` is value-match, NOT a write watch.
// Use SPIKE_WATCH=<addr> for true "any write" / "nothing wrote" detection.
enum class DbgAction { Continue, Done, Quit };

static DbgAction run_until(simif_t* memif, processor_t* p,
                           const std::function<bool()>& pred,
                           uint64_t* steps_left) {
  while (*steps_left > 0) {
    if (rd_u64(memif, HALT_FLAG)) return DbgAction::Done;
    if (pred()) return DbgAction::Continue;
    p->step(1);
    (*steps_left)--;
  }
  fprintf(stderr, "spike_run: debug until: step cap reached\n");
  return DbgAction::Done;
}

static DbgAction handle_debug_line(simif_t* memif, processor_t* p,
                                   const std::string& line, uint64_t* steps_left) {
  // strip comment
  std::string s = line;
  auto hash = s.find('#');
  if (hash != std::string::npos) s = s.substr(0, hash);
  // trim
  while (!s.empty() && isspace((unsigned char)s.front())) s.erase(s.begin());
  while (!s.empty() && isspace((unsigned char)s.back())) s.pop_back();
  if (s.empty()) return DbgAction::Continue;

  std::istringstream iss(s);
  std::string cmd;
  iss >> cmd;
  auto* st = p->get_state();

  if (cmd == "help" || cmd == "h") {
    fprintf(stderr,
            "spike_run debug commands:\n"
            "  pc | reg [r] | mem <addr>\n"
            "  until pc <addr> | until mem <addr> <val> | until reg <r> <val> | until halt\n"
            "  step [n] | rs | run | quit\n"
            "True write-watch: SPIKE_WATCH=<addr> (env), not 'until mem'.\n");
    return DbgAction::Continue;
  }
  if (cmd == "quit" || cmd == "q") return DbgAction::Quit;
  if (cmd == "pc") {
    fprintf(stderr, "0x%llx\n", (unsigned long long)st->pc);
    return DbgAction::Continue;
  }
  if (cmd == "reg") {
    std::string a, b;
    iss >> a;
    if (a.empty()) { print_regs(p); return DbgAction::Continue; }
    // optional core number then reg, or just reg
    std::string rname = a;
    if (iss >> b) rname = b; // skip core
    else if (a.size() == 1 && isdigit((unsigned char)a[0]) && a[0] == '0') {
      // bare "reg 0" means all regs of core 0 (stock spike)
      print_regs(p); return DbgAction::Continue;
    }
    int ri = parse_reg_name(rname);
    if (ri < 0) { fprintf(stderr, "bad reg %s\n", rname.c_str()); return DbgAction::Continue; }
    fprintf(stderr, "0x%016llx\n", (unsigned long long)st->XPR[ri]);
    return DbgAction::Continue;
  }
  if (cmd == "mem") {
    std::string addr_s;
    iss >> addr_s;
    if (addr_s.empty()) { fprintf(stderr, "mem needs addr\n"); return DbgAction::Continue; }
    reg_t addr = (reg_t)parse_u64(addr_s.c_str(), "mem addr");
    fprintf(stderr, "0x%016llx\n", (unsigned long long)rd_u64(memif, addr));
    return DbgAction::Continue;
  }
  if (cmd == "step") {
    std::string n_s; iss >> n_s;
    uint64_t n = n_s.empty() ? 1 : parse_u64(n_s.c_str(), "step count");
    for (uint64_t i = 0; i < n && *steps_left > 0; ++i) {
      if (rd_u64(memif, HALT_FLAG)) return DbgAction::Done;
      p->step(1); (*steps_left)--;
    }
    fprintf(stderr, "pc=0x%llx\n", (unsigned long long)st->pc);
    return DbgAction::Continue;
  }
  if (cmd == "rs" || cmd == "run" || cmd == "r") {
    return run_until(memif, p, []() { return false; }, steps_left);
  }
  if (cmd == "until" || cmd == "untiln") {
    std::string kind; iss >> kind;
    if (kind == "halt") {
      fprintf(stderr, "until halt …\n");
      auto act = run_until(memif, p, []() { return false; }, steps_left);
      fprintf(stderr, "halt_flag=0x%llx pc=0x%llx\n",
              (unsigned long long)rd_u64(memif, HALT_FLAG),
              (unsigned long long)st->pc);
      return act;
    }
    if (kind == "pc") {
      std::string a, b; iss >> a >> b;
      // until pc <core> <val>  OR  until pc <val>
      std::string val_s = b.empty() ? a : b;
      reg_t want = (reg_t)parse_u64(val_s.c_str(), "until pc");
      fprintf(stderr, "until pc 0x%llx …\n", (unsigned long long)want);
      auto act = run_until(memif, p, [&]() { return st->pc == want; }, steps_left);
      fprintf(stderr, "stopped pc=0x%llx\n", (unsigned long long)st->pc);
      return act;
    }
    if (kind == "mem") {
      std::string a, b, c; iss >> a >> b >> c;
      // until mem [core] <addr> <val>  OR  until mem <addr> <val>
      std::string addr_s, val_s;
      if (!c.empty()) { addr_s = b; val_s = c; }
      else { addr_s = a; val_s = b; }
      reg_t addr = (reg_t)parse_u64(addr_s.c_str(), "until mem addr");
      uint64_t want = parse_u64(val_s.c_str(), "until mem val");
      fprintf(stderr, "until mem 0x%llx == 0x%llx …\n",
              (unsigned long long)addr, (unsigned long long)want);
      auto act = run_until(memif, p, [&]() { return rd_u64(memif, addr) == want; }, steps_left);
      fprintf(stderr, "stopped pc=0x%llx mem=0x%016llx\n",
              (unsigned long long)st->pc,
              (unsigned long long)rd_u64(memif, addr));
      return act;
    }
    if (kind == "reg") {
      std::string a, b, c; iss >> a >> b >> c;
      // until reg <core> <r> <v>  OR until reg <r> <v>
      std::string r_s, v_s;
      if (!c.empty()) { r_s = b; v_s = c; }
      else { r_s = a; v_s = b; }
      int ri = parse_reg_name(r_s);
      if (ri < 0) { fprintf(stderr, "bad reg %s\n", r_s.c_str()); return DbgAction::Continue; }
      uint64_t want = parse_u64(v_s.c_str(), "until reg val");
      fprintf(stderr, "until reg %s == 0x%llx …\n", r_s.c_str(), (unsigned long long)want);
      auto act = run_until(memif, p, [&]() { return st->XPR[ri] == want; }, steps_left);
      fprintf(stderr, "stopped pc=0x%llx %s=0x%016llx\n",
              (unsigned long long)st->pc, r_s.c_str(),
              (unsigned long long)st->XPR[ri]);
      return act;
    }
    fprintf(stderr, "until: unknown kind '%s' (pc|mem|reg|halt)\n", kind.c_str());
    return DbgAction::Continue;
  }
  fprintf(stderr, "unknown debug cmd: %s (try help)\n", cmd.c_str());
  return DbgAction::Continue;
}

static void run_debug_cmd_file(simif_t* memif, processor_t* p,
                               const char* path, uint64_t* steps_left) {
  std::ifstream in(path);
  if (!in) {
    fprintf(stderr, "spike_run: cannot open SPIKE_DEBUG_CMD=%s\n", path);
    exit(2);
  }
  fprintf(stderr, "spike_run: SPIKE_DEBUG_CMD=%s\n", path);
  std::string line;
  while (std::getline(in, line)) {
    DbgAction a = handle_debug_line(memif, p, line, steps_left);
    if (a == DbgAction::Quit) {
      fprintf(stderr, "spike_run: debug quit\n");
      return;
    }
    if (a == DbgAction::Done) {
      fprintf(stderr, "spike_run: debug done (halt or cap)\n");
      return;
    }
  }
  fprintf(stderr, "spike_run: debug-cmd EOF\n");
}

int main(int argc, char** argv) {
  if (argc != 4) {
    fprintf(stderr,
            "usage: %s <guest.elf> <input> <output>\n"
            "env: SPIKE_COMMITLOG SPIKE_DEBUG_CMD SPIKE_WATCH SPIKE_WATCH_STOP "
            "SPIKE_BREAK_PC SPIKE_OUTPUT_LEN SPIKE_RUN_DEBUG "
            "SPIKE_INIT_WRITES SPIKE_DUMP_RANGES SPIKE_DUMP_FILE\n",
            argv[0]);
    return 2;
  }

  cfg_t cfg;
  cfg.isa  = "RV64IMAC_Zicclsm";
  cfg.priv = "M";
  cfg.hartids = std::vector<size_t>{0};
  cfg.mem_layout = {
    mem_cfg_t(0x40000000ULL, 0x01000000ULL),  // input arena
    mem_cfg_t(0x60000000ULL, 0x00010000ULL),  // handler + tohost/fromhost
    mem_cfg_t(0x7ffff000ULL, 0x40001000ULL),  // headers+text+data+sszscratch+output -> 0xc0000000
  };
  std::vector<DumpRange> dump_ranges_spec = parse_dump_ranges();
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

  // Tooling-only initialization hook.  The normal runner leaves the ELF's
  // initialized data untouched; agreement_sweep uses this to arm its
  // otherwise-inert runtime flag for a measurement process.
  for (const InitWrite& write : parse_init_writes()) {
    uint8_t value[8];
    memcpy(value, &write.value, sizeof(value));
    wr(&sim, write.addr, value, sizeof(value));
  }

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

  uint64_t steps_left = STEP_CAP;

  // Headless debug script (SPIKE_DEBUG_CMD) — runs before free-run.
  if (const char* dcmd = getenv("SPIKE_DEBUG_CMD")) {
    if (*dcmd) run_debug_cmd_file(&sim, p, dcmd, &steps_left);
  }

  // Optional true write-watch / PC log. Stock `until mem` cannot prove absence.
  bool have_watch = false;
  reg_t watch_addr = 0;
  uint64_t watch_prev = 0;
  uint64_t watch_hits = 0;
  if (const char* w = getenv("SPIKE_WATCH")) {
    if (*w) {
      have_watch = true;
      watch_addr = (reg_t)parse_u64(w, "SPIKE_WATCH");
      watch_prev = rd_u64(&sim, watch_addr);
      fprintf(stderr, "spike_run: SPIKE_WATCH=0x%llx initial=0x%016llx\n",
              (unsigned long long)watch_addr, (unsigned long long)watch_prev);
    }
  }
  bool watch_stop = false;
  if (const char* ws = getenv("SPIKE_WATCH_STOP"))
    watch_stop = ws[0] != '\0' && ws[0] != '0';

  bool have_break_pc = false;
  reg_t break_pc = 0;
  bool break_hit = false;
  if (const char* b = getenv("SPIKE_BREAK_PC")) {
    if (*b) {
      have_break_pc = true;
      break_pc = (reg_t)parse_u64(b, "SPIKE_BREAK_PC");
      fprintf(stderr, "spike_run: SPIKE_BREAK_PC=0x%llx\n", (unsigned long long)break_pc);
    }
  }

  // step until the handler signals halt (HALT_FLAG nonzero) or the cap is hit.
  // flag==1 clean halt; flag==2 guest fault (info at HALT_FLAG+0x10/0x18/0x20).
  uint64_t flagv = rd_u64(&sim, HALT_FLAG);
  if (!flagv) {
    const bool fine = have_watch || have_break_pc;
    const size_t batch = fine ? 1 : STEP_BATCH;
    while (steps_left > 0) {
      size_t n = batch;
      if ((uint64_t)n > steps_left) n = (size_t)steps_left;
      if (have_break_pc && !break_hit && p->get_state()->pc == break_pc) {
        break_hit = true;
        fprintf(stderr, "SPIKE_BREAK_PC hit pc=0x%llx\n", (unsigned long long)break_pc);
        print_regs(p);
        // fall through: execute the insn at break_pc, then continue
      }
      p->step(n);
      steps_left -= n;
      if (have_watch) {
        uint64_t cur = rd_u64(&sim, watch_addr);
        if (cur != watch_prev) {
          print_watch_hit(p, watch_addr, watch_prev, cur);
          watch_prev = cur;
          watch_hits++;
          if (watch_stop) {
            fprintf(stderr, "spike_run: SPIKE_WATCH_STOP — ending run after hit\n");
            break;
          }
        }
      }
      flagv = rd_u64(&sim, HALT_FLAG);
      if (flagv) break;
    }
  }
  if (have_watch) {
    fprintf(stderr, "spike_run: SPIKE_WATCH done hits=%llu final=0x%016llx\n",
            (unsigned long long)watch_hits, (unsigned long long)watch_prev);
  }
  if (flagv == 2) {
    uint8_t b[8]; uint64_t mcause=0, mtval=0, mepc=0;
    rd(&sim, HALT_FLAG + 0x10, b, 8); memcpy(&mcause, b, 8);
    rd(&sim, HALT_FLAG + 0x18, b, 8); memcpy(&mtval, b, 8);
    rd(&sim, HALT_FLAG + 0x20, b, 8); memcpy(&mepc, b, 8);
    fprintf(stderr, "spike_run: guest FAULT mcause=0x%llx mtval=0x%llx mepc=0x%llx\n",
            (unsigned long long)mcause, (unsigned long long)mtval, (unsigned long long)mepc);
  } else if (flagv == 0) {
    fprintf(stderr, "spike_run: step cap reached without halt (or watch-stop)\n");
  }
  bool halted = (flagv == 1);

  size_t out_len = output_len();
  std::vector<uint8_t> out(out_len);
  rd(&sim, OUTPUT_ADDR, out.data(), out_len);
  std::ofstream of(argv[3], std::ios::binary);
  of.write((const char*)out.data(), out_len);
  if (!dump_ranges_spec.empty()) {
    dump_ranges(&sim, dump_ranges_spec, getenv("SPIKE_DUMP_FILE"));
  }
  for (auto& m : mems) delete m.second;
  return halted ? 0 : 3;
}
