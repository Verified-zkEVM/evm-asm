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

## Debugging the guest (recipe)

### Headline: `hits=0` means nothing wrote here

`SPIKE_COMMITLOG` is a **trace of writes**. It is structurally blind to the
**absence** of a write — the correct-but-unfed class (global stays zero because
no store ever targeted it). The fleet hit that class twice in one day; once it
cost **~two hours of commitlog archaeology** to learn that `bsbd_deleg_target`
held 24 zero bytes on a child path because nothing ever wrote it.

`SPIKE_WATCH` is the cheap instrument for that question. Point it at a guest
global on a **real fixture**. If the run ends with `hits=0`, you have the
answer in one shot — stop hunting for a clobber and look for a missing store.

**Worked example (known answer, real guest+fixture — not a toy):**

```bash
# guest sha256 7c630c93fb53684b1c0f25d3a7873307bfdfe47fa9180c3ed87e4d8d30491337
# run-20260801T112401Z-2945520 / 00000 selfdestructing_initcode…
# nm: bsbd_deleg_target @ 0xbaeaa268  (re-nm after every rebuild)
ELF=gen-out/eest-run/run-20260801T112401Z-2945520/stateless_guest.elf
IN=gen-out/eest-run/run-20260801T112401Z-2945520/00000_*.input

SPIKE_WATCH=0xbaeaa268 \
  scripts/spike/spike_run "$ELF" "$IN" /tmp/out 2>/tmp/watch.log
```

Actual stderr from that run:

```
spike_run: SPIKE_WATCH=0xbaeaa268 initial=0x0000000000000000
spike_run: SPIKE_WATCH done hits=0 final=0x0000000000000000
```

`hits=0` = the two-hour answer, in one command. A new instrument proved against
a **known** fleet answer is trustworthy in a way one proved only on unknowns
never is.

Unset every debug env var and `spike_run` is **byte-identical** to the
pre-tooling path (`cmp` matched the prior 256-byte output on the same fixture).

### Tool map

| Tool | Best for | Cost |
|------|----------|------|
| `SPIKE_WATCH` | **"did anything write this address?"** (`hits=0` / who wrote) | steps 1 insn at a time; full guest slower but finishes |
| `SPIKE_DEBUG_CMD` | break at PC/symbol, dump regs/mem, value-match `until mem` | headless; ~normal wall if breakpoint hits early |
| `SPIKE_BREAK_PC` | one-shot reg dump at a PC, then continue | step-1 until hit, then batch |
| `SPIKE_COMMITLOG` | "what writes happened?" archaeology | huge files (~0.5 GB/fixture) |
| `scripts/pointer-follow-census.py` | static: did a callee **read** a symbol through a passed pointer? (GH #11229) | pure asm parse; seconds on full guest `.s` |

### Static reference censuses are bounded (GH #11229)

Same-line `la <reg>, S` + load-off-reg greps are an **upper bound on deadness**,
never a proof of "nothing reads this". Three mechanisms they miss:

1. **Pointer argument to a callee that loads** — `la a0, S; jal ra, u256_add_be`
   (callee does `lbu` through `a0`). No line names `S` and loads from it.
2. **Multi-line write** — `la` on one line, `sd` on another (written-cell census
   is a floor, not a total).
3. **Store-and-reload pointer flow** — pointer spilled to memory, reloaded,
   then dereferenced.

`SPIKE_WATCH` is unaffected: it observes the **cell**, so pointer-mediated
accesses still count. Where a deletion needs a negative, prefer a watch.

For static work that must stay offline, use the pointer-follow detector:

```bash
python3 scripts/pointer-follow-census.py gen-out/stateless_guest.s --demo
python3 scripts/pointer-follow-census.py gen-out/stateless_guest.s --symbol bmvmx_gascost
```

Verdicts: `live_direct`, `live_via_callee` (classic false-dead break),
`unresolved` (arg-reg + `jal` but callee missing/no load found — named gap,
not "dead"), `upper_bound_dead`, `no_la`.

### Final-memory BAL producer dump

For the tooling-only BAL producer differential, set both
`SPIKE_DUMP_RANGES=addr:length,addr:length,...` and
`SPIKE_DUMP_FILE=<file>`. The runner writes a self-describing `SPKDMP01`
version-1 file after the guest halts. Ranges are explicit and checked for
mapped memory; a missing variable or an unmapped byte is an error. The BAL
probe derives these ranges from `nm` symbols and keeps `SPIKE_COMMITLOG` as a
separate attempted-write audit.

```bash
SPIKE_DUMP_RANGES=0xb9d84948:0xb8,0xb9d84a00:3360000 \
SPIKE_DUMP_FILE=/tmp/bal-final-memory.bin \
scripts/spike/spike_run <guest.elf> <input> /tmp/output
```

Use `scripts/spike/bal_producer_set.sh` for the complete pre-registered
fixture comparison; it checks exact row contents before the secondary hash
cross-check. See `docs/bal-producer-differential.md`.

### 0. Resolve addresses

```bash
ELF=gen-out/eest-run/<run>/stateless_guest.elf   # or whatever guest you built
IN=gen-out/eest-run/<run>/00000_*.input
riscv64-unknown-elf-nm "$ELF" | rg 'h_CREATE$|bsbd_deleg_target|create_balance_be'
# addresses move every rebuild — always re-nm before watching
```

### 1. True write-watch (`SPIKE_WATCH`)

Watches one **8-byte LE** cell. On any change, prints `pc`, old/new, and a
useful register subset. End-of-run `hits=0` is the absence signal.

```bash
SPIKE_WATCH=0xbaeaa268 \
  scripts/spike/spike_run "$ELF" "$IN" /tmp/out 2>/tmp/watch.log

# Stop on first hit (don't wait for halt):
SPIKE_WATCH=0xbaeaa268 SPIKE_WATCH_STOP=1 \
  scripts/spike/spike_run "$ELF" "$IN" /tmp/out 2>/tmp/watch.log
```

### 2. Headless breakpoints (`SPIKE_DEBUG_CMD`)

Stock spike's `-d` / `--debug-cmd` only run inside `sim.run()` → `idle()` →
`interactive()`. Our driver **bypasses** that path (custom `p->step` loop +
`HALT_FLAG` at `0x60008000`), so stock flags do nothing on `spike_run`.
`SPIKE_DEBUG_CMD` is the harness-native replacement (same command shapes).

```bash
cat > /tmp/dbg.cmd <<'EOF'
# stop at h_CREATE entry (re-nm the address!)
until pc 0x80053704
pc
reg          # all XPR
reg s4       # env base in many handlers
mem 0xbd79d600   # create_balance_be (re-nm)
until halt
quit
EOF
SPIKE_DEBUG_CMD=/tmp/dbg.cmd \
  scripts/spike/spike_run "$ELF" "$IN" /tmp/out 2>/tmp/dbg.log
# worked example:
#   until pc 0x80053704 …
#   stopped pc=0x80053704
#   s4 = factory env, etc.
```

Commands (one per line; `#` comments ok):

| cmd | meaning |
|-----|---------|
| `pc` | print PC |
| `reg` / `reg <name>` | all XPR, or one (`a0`, `s4`, `x10`, …) |
| `mem <hex>` | print 8-byte LE at physical addr |
| `until pc <hex>` | run until PC equals |
| `until mem <hex> <hex>` | run until cell **equals** value (not a write watch!) |
| `until reg <r> <hex>` | run until XPR equals |
| `until halt` / `rs` / `run` | run until `HALT_FLAG != 0` |
| `step [n]` | single-step |
| `quit` | end script; driver still dumps the 256 B output |

**Value-match vs write-watch:** stock spike and our `until mem ADDR VAL` only
stop when the cell becomes `VAL`. They cannot prove "nothing wrote". Use
`SPIKE_WATCH` for that.

```bash
# value-match: stop when halt flag becomes 1 (works)
until mem 0x60008000 0x1
```

### 3. One-shot PC log (`SPIKE_BREAK_PC`)

Logs regs once when PC equals the address, then continues to halt (no script):

```bash
SPIKE_BREAK_PC=0x80053704 \
  scripts/spike/spike_run "$ELF" "$IN" /tmp/out 2>/tmp/brk.log
# → SPIKE_BREAK_PC hit pc=0x80053704 + full reg dump
```

### 4. Commit log (existing)

```bash
SPIKE_COMMITLOG=/tmp/cl.log scripts/spike/spike_run "$ELF" "$IN" /tmp/out
```

Per-instruction trace (pc, insn word, reg/mem writes). Great for "show me the
store that produced this value" once you know a write happened. Bad for absence.

EVM opcode stream (dispatch fetch is `lbu t0, 0(a0)` at `.dispatch_loop`):

```bash
rg "<fetch-addr> \(0x00054283\)" /tmp/cl.log \
  | rg -o 'x5\s+0x([0-9a-f]+)\s+mem\s+0x([0-9a-f]+)' -r '$1 $2'
# col1 = opcode/operand byte, col2 = EVM PC address
```

### What does NOT work (honest)

| Approach | Status |
|----------|--------|
| Stock `spike -d` / `--debug-cmd=FILE` on our guest | **No** — no input preload, no zisk accel CSRs wired that way, no `HALT_FLAG` contract. Use `spike_run` env vars above. |
| Stock `spike --halted --rbb-port=N` + gdb | **Impractical here today.** Needs OpenOCD (`openocd` not installed on this host) + a three-process dance (spike / openocd / gdb-multiarch). `spike_run` also does not expose `--rbb-port`. If someone installs OpenOCD later, wire rbb into `spike_run` and revisit; until then `SPIKE_WATCH` + `SPIKE_DEBUG_CMD` cover the fleet need. |
| Hardware-style "break on any write" via stock interactive | **No** — stock only has value-match `until mem`. Our `SPIKE_WATCH` is the true write watch. |
| Watching wider than 8 bytes with one `SPIKE_WATCH` | **No** — watches one dword. For a 24-byte buffer watch three addresses or the first dword (enough for "anything touched this object"). |
| Fast full-run watch | **Slow** — watch/break force `step(1)`. Acceptable for one fixture; don't put it in CI. |

### Rebuild after editing `spike_run.cc`

```bash
SPIKE_SRC=/path/to/riscv-isa-sim scripts/spike/build.sh
# produces scripts/spike/spike_run
```

## The guest's runtime contract (see ../../../.claude/plans for full map)
- Memory: header `0x7ffff000`, `.text 0x80000000`, `.data`/`.bss` from ELF
  program headers (currently `-Tdata=0xa0b00000`, bss `0xa0b70000`; GH #11186),
  `.sszscratch 0xbf980000`, input `0x40000000`, output `0xa0010000` (runner ABI).
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
