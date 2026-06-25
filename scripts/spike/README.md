# SPIKE backend for the stateless guest (WIP)

Goal: run the codegen `stateless_guest` ELF on SPIKE (`riscv-isa-sim`) as a
faster alternative to `ziskemu` (ziskemu re-transpiles the ~447 MB ROM ~32 s
every run; SPIKE interprets directly). Success = SPIKE produces the **identical
256-byte output** ziskemu produces (byte-parity is the correctness gate).
No guest/codegen changes — SPIKE adapts to the existing ELF's contract.

## Status

**Working & validated (macOS arm64):**
- SPIKE builds from source at `$SPIKE_SRC` (default `/Users/dhsorens/devel/riscv-isa-sim`).
- `build.sh` produces `libziskaccel.so` (extension for stock `spike --extlib`) AND
  `spike_run` (custom driver: `spike_run <guest.elf> <input> <output>`, a drop-in
  for `ziskemu -e/-i/-o`).
- Accelerator CSRs, all isolation-validated (`test/*_selfcheck.s`, exit 0 only if byte-correct):
  - **Keccak-f[1600] `csrs 0x800`** — published zero-state vector.
  - **arith256_mod `csrs 0x802`** `d=(a·b+c) mod m` — `(7·11+5) mod 20 = 2`.
  - **sha256 `csrs 0x805`** — SHA-256("abc") = ba7816bf…
- **`spike_run` runs the real stateless guest END-TO-END** (loads ELF, services the
  read_input/halt ecalls via an installed trap handler, runs the accelerator CSRs,
  halts cleanly) and on the CLZ `single_bit_106` block its output **matches ziskemu
  byte-for-byte for the full 32-byte root**. Key fixes that got it there: enable
  Zicclsm (misaligned loads, like ziskemu); explicit `load_elf` + start at the ELF
  entry (bypass spike's bootrom); explicit `state.add_csr()` (register_extension
  does NOT call get_csrs); trap handler reports faults (mcause/mtval/mepc).

**Remaining divergence (the parity gap):** byte 32 (the succ/verdict bit) and the
tail still differ (spike says invalid, ziskemu valid). The matching root proves
keccak/sha256/SSZ-merkleization are correct, so the divergence is in the EVM
**re-execution** path that produces the verdict — most likely a subtle
`arith256_mod` edge case (large/non-canonical operands) or a spike-vs-ziskemu CPU
semantic difference. Debug next: run a no-tx / minimal block (does succ match
then?) to localize EVM-exec vs systemic; add a wider arith256 isolation test with
full 256-bit operands; compare spike vs ziskemu step traces around the verdict.

Build: `SPIKE_SRC=/path/to/riscv-isa-sim ./build.sh`

## The guest's runtime contract (see ../../../.claude/plans for full map)
- Memory: header `0x7ffff000`, `.text 0x80000000`, `.data 0xa3000000`,
  `.sszscratch 0xbf500000`, input `0x40000000`, output `0xa0010000`.
- 2 ecalls: `read_input` (t0=0xF2: write inputBufBase=0x40000000 → [a0], len → [a1]),
  halt (a7=93). Input file layout at 0x40000000: 8-byte zero meta + 8-byte LE len + blob.
- 17 custom accelerator CSRs (all decoded). MVP needs 0x800/0x802/0x805; the rest
  (0x803/4 secp256k1, 0x806–0x810 bn254/bls12, 0x819 blake2b-round) are precompile-only.
  Each is one more `accel_csr_t` subclass in zisk_accel.cc; zisk semantics + param
  layouts are documented in the plan file.

## Remaining for an end-to-end MVP (next steps)
1. **ecall + I/O harness.** Stock spike only loads ELF segments and has no
   input/output flags. Build EITHER:
   (a) a small custom driver (links libriscv/libfesvr) that: creates sim_t with the
       extension + `-m` regions, writes the input blob to `0x40000000`, services the
       2 ecalls (read_input/halt) via an in-memory M-mode trap handler whose `mtvec`
       it sets, runs to HTIF exit, then reads 256 B at `0xa0010000` to an output file; OR
   (b) an injected reset+trap-handler shim ELF (sets mtvec, services ecalls, HTIF
       exit) + ELF section-patch the input at 0x40000000 + `+signature` over the
       output region (note: this spike build's `+signature=` HTIF arg needs the right
       passing form; `begin/end_signature` symbols are read from the ELF symtab —
       fesvr/htif.cc:199).
   Recommended: (a), a custom driver — most robust, gives direct input-preload +
   output-dump and avoids the signature-arg friction.
2. **Run the real guest** end-to-end on a non-precompile block.
3. **Byte-parity gate** `spike-parity-check.sh`: run the same blocks on ziskemu and
   SPIKE, diff the 256-byte outputs. Reuse `gen-out/loop/full/manifest.tsv` + input files.
4. **Wire `EEST_BACKEND=ziskemu|spike`** into the loop tooling (loop_run.py / sweep.py)
   + a `spike-run.sh <elf> <input> <output>` drop-in mirroring `ziskemu -e/-i/-o`.
5. Add remaining precompile CSRs as needed; validate each via parity on its fixtures.
