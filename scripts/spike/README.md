# SPIKE backend for the stateless guest (WIP)

Goal: run the codegen `stateless_guest` ELF on SPIKE (`riscv-isa-sim`) as a
faster alternative to `ziskemu` (ziskemu re-transpiles the ~447 MB ROM ~32 s
every run; SPIKE interprets directly). Success = SPIKE produces the **identical
256-byte output** ziskemu produces (byte-parity is the correctness gate).
No guest/codegen changes — SPIKE adapts to the existing ELF's contract.

## Status

**Working & validated:**
- macOS arm64: original spike backend MVP.
- Linux x86_64: builds with a local `riscv-isa-sim` checkout plus OpenSSL/libcrypto and `riscv64-unknown-elf-*` binutils; validated through the EEST runner with `EEST_BACKEND=spike`.

- SPIKE builds from source at `$SPIKE_SRC` (default: a `riscv-isa-sim` checkout sibling to this repo).
- `build.sh` produces `libziskaccel.so` (extension for stock `spike --extlib`) AND
  `spike_run` (custom driver: `spike_run <guest.elf> <input> <output>`, a drop-in
  for `ziskemu -e/-i/-o`).
- Accelerator CSRs (`test/*_selfcheck.s` contains stock-Spike isolation checks; the EEST backend path is validated by byte parity below):
  - **Keccak-f[1600] `csrs 0x800`** — published zero-state vector.
  - **arith256_mod `csrs 0x802`** `d=(a·b+c) mod m` — `(7·11+5) mod 20 = 2`.
  - **sha256 `csrs 0x805`** — SHA-256("abc") = ba7816bf…
- **secp256k1 affine point add `csrs 0x803` / double `csrs 0x804`** — implemented
  with OpenSSL BIGNUM field arithmetic over the secp256k1 prime (needed for tx
  sender recovery / ecrecover); validated by full byte-parity below.
- **BLS12-381 Fp2 add/sub/mul `csrs 0x80e` / `0x80f` / `0x810`** — implemented
  with OpenSSL BIGNUM; needed by the BLS12-381 precompiles (fixed in `cfcbdb56f`).
- **BLAKE2b round `csrs 0x819`** — implemented directly from the RFC 7693 G
  mixing function (SIGMA schedule + 8 MIX_TABLE index sets); backs the BLAKE2F
  (`0x09`, EIP-152) precompile; validated by full byte-parity on all blake2 EEST
  fixtures.
- **arith384_mod `csrs 0x80b`** `d=(a·b+c) mod m` over 6-limb (384-bit) values with
  a parameter-supplied modulus — mirrors `0x802` widened to 6 limbs; foundational
  for the BLS12-381 precompiles.
- **BLS12-381 affine point add `csrs 0x80c` / double `csrs 0x80d`** — implemented
  with OpenSSL BIGNUM field arithmetic over the BLS12-381 base-field prime (6 limbs);
  needed for the G1/G2 add/msm precompiles.
- **BN254 (alt_bn128) affine point add `csrs 0x806` / double `csrs 0x807`** —
  implemented with OpenSSL BIGNUM field arithmetic over the BN254 prime (4 limbs);
  needed for the ecAdd (0x06) / ecMul (0x07) precompiles.
- **BN254 Fp2 complex add/sub/mul `csrs 0x808` / `0x809` / `0x80a`** — implemented
  over `Fp2 = Fp[u]/(u^2+1)` (4 limbs per component); needed for the ecPairing (0x08)
  precompile.
- **`spike_run` runs the real stateless guest END-TO-END and is BYTE-IDENTICAL to
  ziskemu.** `scripts/spike/parity-check.sh N SEED` runs N random blocks on both
  backends and diffs the 256-byte output: **8/8 match** (contract creation,
  precompiled-touch, returndata, SSTORE, tx intrinsic gas, address opcodes, …),
  **0 differ**. Speed: ziskemu ~55–62 s/block (ROM transpile dominates), spike
  ~1 s/block — **~50× faster**. Linux validation on this repo branch: focused row
  skip=139 ran in 0.45s with SPIKE vs 1.06s with cached ziskemu; the 22-row EIP-7708
  cluster ran in 2.62s with SPIKE vs 13.05s with cached ziskemu; the first 1000 rows
  ran 1000/1000 full matches in 95.87s with SPIKE (4 workers).
  Key fixes that got it there: enable Zicclsm (misaligned loads, like ziskemu);
  explicit `load_elf` + start at the ELF entry (bypass spike's bootrom); explicit
  `state.add_csr()` (`register_extension` does NOT call `get_csrs`); secp256k1
  add/double CSRs; trap handler reports faults (mcause/mtval/mepc).

Build: `SPIKE_SRC=/path/to/riscv-isa-sim scripts/spike/build.sh`
Run one block: `scripts/spike/spike_run <guest.elf> <input> <output>`
EEST backend: `EEST_BACKEND=spike scripts/codegen-eest-stateless-check.sh --limit 1000 --jobs 4`
Parity gate: `scripts/spike/parity-check.sh 8 1`

## Debugging: per-instruction commit log

`spike_run` supports an env-gated commit log for EVM-faithfulness / gas-model
debugging. Set `SPIKE_COMMITLOG=<file>` and spike writes its standard per-instruction
trace (RV64 `pc`, instruction word, register and memory writes) to that file.
Unset, behavior is byte-identical to before (zero impact on parity/CI runs).

```bash
SPIKE_COMMITLOG=/tmp/cl.log scripts/spike/spike_run <guest.elf> <input> /tmp/out
```

The guest\'s EVM-bytecode interpreter has a single dispatch loop; its opcode
fetch is the `lbu t0, 0(a0)` at the `.dispatch_loop` label (a0/x10 = EVM PC,
t0/x5 = opcode byte). To extract the executed EVM bytecodes from the log, find
that fetch instruction\'s address (e.g. via `riscv64-unknown-elf-objdump -d
<guest.elf> | grep -A2 .dispatch_loop`) and filter:

```bash
rg "<fetch-addr> \(0x00054283\)" /tmp/cl.log \
  | rg -o 'x5\s+0x([0-9a-f]+)\s+mem\s+0x([0-9a-f]+)' -r '$1 $2'
# column 1 = opcode/operand byte, column 2 = EVM PC (memory address)
```

This gives the executed-EVM-byte sequence (count includes PUSH operand bytes),
useful for diffing guest vs execution-specs per-opcode traces (`ethereum.trace`).

## The guest's runtime contract (see ../../../.claude/plans for full map)
- Memory: header `0x7ffff000`, `.text 0x80000000`, `.data 0xa3000000`,
  `.sszscratch 0xbf600000`, input `0x40000000`, output `0xa0010000`.
- 2 ecalls: `read_input` (t0=0xF2: write inputBufBase=0x40000000 → [a0], len → [a1]),
  halt (a7=93). Input file layout at 0x40000000: 8-byte zero meta + 8-byte LE len + blob.
- 17 custom accelerator CSRs (all decoded). MVP needs 0x800/0x802/0x805; the rest
  (0x803/4 secp256k1, 0x806–0x80a bn254, 0x80b arith384_mod, 0x80c/0x80d bls12-curve,
  0x80e–0x810 bls12-fp2, 0x819 blake2b-round) are precompile-only.
  Each is one more `accel_csr_t` subclass in zisk_accel.cc; zisk semantics + param
  layouts are documented in the plan file.

## Remaining (post-MVP)
- **All accelerator CSRs are now implemented.** `0x800` (keccak), `0x802`
  (arith256_mod), `0x803`/`0x804` (secp256k1), `0x805` (sha256),
  `0x806`/`0x807` (bn254 curve), `0x808`–`0x80a` (bn254 Fp2), `0x80b`
  (arith384_mod), `0x80c`/`0x80d` (bls12 curve), `0x80e`–`0x810` (bls12 Fp2),
  and `0x819` (blake2b-round) are all done.
- **Phase 3 — selectable backend**: `scripts/codegen-eest-stateless-check.sh` supports
  `--backend ziskemu|spike` / `EEST_BACKEND=ziskemu|spike` for stateless EEST runs
  (default ziskemu). Remaining loop tooling such as `loop_run.py`/`sweep.py` can adopt
  the same backend variable when those paths need SPIKE.
- Generalize: read the guest entry/regions instead of hardcoding; handle multi-page
  misaligned if any block needs it.

## Historical: getting to the first end-to-end MVP (next steps, now done)
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
