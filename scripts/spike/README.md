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
| `SPIKE_OUTPUT_LEN` | capture more than the 256-byte default output (512 → exactly 512 B, measured) | free |
| `SPIKE_RUN_DEBUG` | first 60-step `[dbg]` trace from entry (entry line + 60 steps, measured) | free |
| `scripts/pointer-follow-census.py` | static: did a callee **read** a symbol through a passed pointer? (GH #11229) | pure asm parse; seconds on full guest `.s` |

### The EEST runner: reproduce, classify, then drill down

The tools below assume you already hold one failing row. Getting there is its
own step, and the runner prints the exact recipe on every FAIL line.

#### Reproduce exactly one row

Every failure line ends with the rerun coordinates
(`… manifest_row=196/300 case_id=… rerun_skip=195 rerun_limit=1 random_seed=20260818`),
which map to:

```bash
scripts/codegen-eest-stateless-check.sh --backend spike \
  --skip 195 --limit 1 --run-dir <EMPTY dir>
```

- `--run-dir` must START EMPTY or the script refuses (GH #11748); keep the
  log file OUTSIDE the run dir.
- ⚠️ If the leg ran `--random --seed N`, the converter shuffles ALL blocks
  with that seed BEFORE applying skip/limit (GH #10596). Plain `--skip` then
  selects a DIFFERENT population — the rerun must repeat
  `--random --seed N` verbatim.
- `--guest-elf <path>` pins the guest and implies `--no-build`. ⚠️ It does
  NOT pin the verdict-debug probe: the probe re-emits from the CURRENT tree
  even under `--no-build` (`run-provenance.tsv` records both shas — read them
  back before believing a debug-cell claim).
- One repro is seconds of guest time; the runner's manifest/probe steps
  dominate the wall clock.

#### Get `bv_fail_code` (the gate that rejected)

Verdict debug is ON by default (`--no-verdict-debug` disables it for
pass/fail-only legs). On a FAIL the run dir gets a
`zisk_stateless_verdict_v2_debug.elf` probe plus per-case
`.verdict-debug.output`. The default capture is 256 bytes; the extended cells
need more — `SPIKE_OUTPUT_LEN` is honored when driving the probe directly
(`=512` yields exactly 512 bytes, measured):

```bash
SPIKE_OUTPUT_LEN=2048 scripts/spike/spike_run \
  <run-dir>/zisk_stateless_verdict_v2_debug.elf <run-dir>/NNNNN_*.input /tmp/dbg.out
```

Cell layout: `format_verdict_debug` in `scripts/codegen-eest-stateless-check.sh`
(u64 labels `+0..+160`, recomputed root `+168`, payload root `+200`, gas arena
`+232…`, completeness shape `+408`, enforce `+416`, dispatch status `+456`,
mtx index `+816`, tx count `+888`). The `bv_fail_code` integer names the
rejecting gate; the code→label table lives in the sink-list comments of
`EvmAsm/Codegen/Programs/BlockVerdictReceiptsTail.lean`. Code in hand, grep
the label, read that gate's source — a search becomes a lookup. Two cell
namespaces exist (probe cells above vs the guest epilogue's own diagnostics
at OUTPUT `0xa0010000+112…`); don't mix them.

#### Concurrency: the silent `.lake` contention trap

`--run-dir` isolates results, but the debug probe builds via `lake exe codegen`
against the GLOBAL `.lake`. Two concurrent verdict-debug runs interfere, and
the failure is SILENT: `emit verdict debug probe` is logged, then no ELF, no
output file, no `bv_fail` field — a reader wrongly concludes the probe does
not support their case. One verdict-debug run at a time; use
`--no-verdict-debug` for pass/fail legs running alongside another.

#### Wall clock tracks mismatch count, not row count

Each succ mismatch triggers an EXTRA verdict-debug guest invocation
(~5.5k failures ⇒ ~30k invocations, not 26k), so a HEALTHIER guest runs
FASTER. Wall clock is therefore never a cross-guest performance signal.

#### Job sizing (spike)

`EEST_SPIKE_JOB_CPU_THREADS` (default 1) and `EEST_SPIKE_JOB_MEM_MIB`
(default 1024) feed the automatic job cap
(`scripts/codegen-eest-stateless-check.sh:604`). Measured on this host
(codex2, #12582): `=2` + `=512` → 16 jobs on 32 CPUs.

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

### 4b. Commitlog search mechanics

Line anatomy: `core   0: 3 0x<16-hex pc> (0x<insn>) [xN 0x<val> …] [mem 0x<addr>]`.

- Loads print the destination reg AND the `mem 0x<addr>` read; stores print
  `mem 0x<addr> 0x<value>`.
- ⚠️ Addresses are 16-hex-digit ZERO-PADDED. `rg '0xbd562000' /tmp/cl.log`
  finds nothing; grep the bare digits (`rg 'bd5620' /tmp/cl.log`).
- Only TAKEN branches/jumps appear; an untaken branch logs nothing. To read a
  branch decision, find the branch line and check whether the NEXT line's pc
  is the fallthrough or the target.
- Execution counts are `rg -c '<pc>'` on any line (entry lines are cheapest).
- Size warning, sharpened (#12582): one row produced 11,024,604 lines / 660 MB
  on one fixture and 17,023,552 lines on another (row 618 of the 2026-08-18
  full-corpus leg). Budget disk before `--all` legs with commitlog on.

### Method: blame the producer only after measuring it

The recurring false-reject shape is producer/consumer disagreement. Before
blaming an emitter, measure the producer's calls, then count BOTH sides of the
consumer's gate (worked example: #12616/#12608, 2026-08-18):

1. `nm` the routines; note call sites in the linked disassembly
   (`riscv64-unknown-elf-objdump -d`).
2. Producer: grep the commitlog for the `jal` at each call site and read the
   argument registers off the surrounding lines. (Measured: the auth SET call
   carried `a3` = designator ptr, `a4` = 23; the auth CLEAR carried `a3` = 0,
   `a4` = 0 — producer correct at both calls.)
3. Consumer: count executions of EACH side of the gate. (Measured: post-hash
   keccak ran 2×, block-baseline keccak 0×, `beqz s5` taken both times — the
   baseline lookup never once consulted the block tier.)
4. Dead region vs wrong value: grep the WHOLE log for any write into the
   reader's base range. 2,184 reads into `0xbdb8…` and ZERO writes there
   run-wide, while the writer emitted at `0xbd562000`, is a dead-base scan —
   not a wrong value, and no amount of value diffing will find it.

### Traps that cost real time (fleet-measured)

- **A hex grep reports FIXED for arithmetically reconstructed constants.**
  `lui 1 / addiw 1975 / slli 19` contains no `0xbdb80000` anywhere.
  Source-side, `scripts/check-layout-literals.sh` models the trio; in a
  disasm, read the immediates and do the arithmetic.
- **DIFF-RULE: assert length == rebuilt_len or REFUSE the diff.** When a
  rebuilt structure (BAL digest, receipts RLP) mismatches, compare the
  LENGTHS first. A byte-gap localizes the drop instantly (a 3-byte gap was
  exactly one missing `c2 02 80` RLP item); field-diffing unequal lists
  manufactures false leads.
- **Run-dir file stems are 0-based; the FAIL line's `manifest_row` is
  1-based** (label 00195 ↔ manifest_row 196 ↔ file `00195_*.input`). One
  off-by-one sent a diagnosis to the wrong fixture.
- **A debug instrument built against mismatched source reports plausible
  wrong values instead of failing.** If a debug view contradicts the guest's
  own verdict, re-check the probe's provenance (same sha at both paths, or
  re-emit) before re-diagnosing the guest.

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
