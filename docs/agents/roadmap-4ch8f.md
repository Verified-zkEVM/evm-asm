# The 4ch8f roadmap — how to take `run_stateless_guest` verification to conclusion

**Audience**: the agent (any capability tier) picking up the next bead of epic
`evm-asm-4ch8f`. This page is the map; it tells you which bead to pick, which
recipe applies, which gates you must run, and where every load-bearing
definition lives. Read it top-to-bottom once; afterwards jump via §7.

**The goal, in one sentence**: prove
`runStatelessGuestSound cr fuel fr execute` (`EvmAsm/Stateless/EntrySpec.lean`)
for the real guest image — every routine of the RISC-V `stateless_guest`
replaced by a verified triple — while the empirical harness
`scripts/codegen-eest-stateless-check.sh` (EEST conformance,
`tests-zkevm@v0.4.0` fixtures) keeps passing at every step.

Companion pages (do not duplicate their content; link into them):
- `docs/agents/port-playbook.md` — the per-routine port workflow (kit → spec →
  proof → `port-check.sh`). **This is the recipe for ~80 % of remaining beads.**
- `docs/agents/review-playbook.md` — how to review a 4ch8f PR (the gates CI
  does NOT run, the adversarial checklists, the known-hole catalog).
- `docs/agents/top-theorem-ledger.md` — obligation rows from the statement
  down; update rows as beads close.
- `docs/4ch8f-top-spec.md` (the statement + trust boundary),
  `docs/4ch8f-interp-strategy.md` (interpreter/dispatch/frames),
  `docs/4ch8f-crypto-strategy.md` (crypto kernels + field-arith library),
  `docs/sasm-design.md` (the SAsm framework itself),
  `docs/agents/proof-patterns.md` + `docs/agents/tactics-deep.md` (tactic craft).

## 1. The layer DAG (verify callee-first, bottom-up)

```
L0  DONE  machine model + accelerators (.1), SAsm core (.2-.5, .10 machinery),
          layout + phase model (.6), asm→Program conversions (.9, 384 defs),
          statement (.8), all strategy decisions (.7, .10, .11)
L1  leaf ports          .12 .13 .14 .15 .16 .20 .23 .24 (+.17 .18 hash bridges)
L2  mid composites      .19 .21 .22 .25 .26 .27 .35 .36 .37 (decode/extract/gas)
L3  state + MPT         .28 .29 .30 .31 .32 (walk -> mutation -> roots)
L4  headers + chain     .33 .34
L5  crypto track        .38 -> .39 .40 -> .57 -> .58   (order: 4ch8f-crypto-strategy §5)
L6  interpreter         .49 (loop) .50-.55 (handler families) .56 (frames)
L7  tx + verdict        .41-.48 .59 .60 .61 .62
L8  shell + top         .63 -> .64
```

Rules:
- **A bead is READY when every routine it calls is verified** (or it calls
  none). `bd show <bead>` lists the family's functions; the call tree is in the
  routine's header comment in `EvmAsm/Codegen/Programs/*.lean` ("Composes:" /
  "Calling convention:" blocks).
- **Pick the lowest READY layer.** Within a layer, prefer beads that unblock
  the most (the MPT chain .28→.32 and the hash bridges .17/.18 have the widest
  fan-out).
- L1/L2 beads have one-session children (`port: verify <fn>`). If a family
  bead you reach has no children yet, **decompose it first** (§5) — that
  decomposition is itself a valid session outcome.

## 2. Which recipe applies (by routine shape)

| shape | recipe | exemplar (proved, on main) |
|---|---|---|
| straight-line loads/stores | port-playbook, block lemma over `execInstrRF` | `SSZ/Decode/ChainIdSAsm.lean` |
| fixed-trip loop (byte reverse, copy N) | SAsm `while` + `vcgen` | `Codegen/Programs/KeccakReverseSAsm.lean`, `BalValueReverseSAsm.lean` |
| data-dependent loop (len/count from input) | `Stmt.whileS` + static cap; cap as spec hypothesis | `SAsm/LoopFuelDemo.lean` (`capScanFn_spec`) |
| calls a verified routine | `Fn`/`FnHandle`, `Stmt.call`/`callReg` | `SAsm/CallRegDemo.lean` |
| state-transforming callee at one call site (handlers) | `FnHandleS` + `Stmt.callRegS` | `SAsm/InterpLoopDemo.lean`, `Codegen/Proofs/HandlerHandles*.lean` |
| accelerator invocation (`csrs 0x8xx`) | machine-level CSRS triple + `FnHandleS` wrapper; NEVER extend the SAsm block engine | `SAsm/AccelStep.lean` (`csrs_arith256Mod_spec_within`) |
| exponent/scalar ladder | `Crypto/PowLadder.lean` fold + `whileS`; post in `Nat.pow`/scalar-mult | `SAsm/PowLadderDemo.lean` (`powFn_spec`) |
| aliased arena phases (call-frame windows) | `anyBytes`/`phaseDView` focus/unfocus | `SAsm/PhaseSplit.lean`, `Codegen/CallFrameWindows.lean` |
| ro table indexed load | `tableAt` + `exec_table_load` | `Codegen/Proofs/OpcodeTables.lean` |
| bottom-test loop (fixed-limb crypto, sequential accumulate) | `Stmt.doWhile` (#9818) + fold invariant | `SAsm/*` (doWhile demo); consumers: `Bls12Fq12`, `Bn254Fq12`, `TxIntrinsicStateGas` |
| outer counting loop w/ bottom test (snapshot) | `Stmt.doWhileS` (`.69`) + entry-snapshot inv | mirrors `whileS`; see `.70.3` consumer inventory |
| mid-break scan ("until predicate", found/not-found) | `Stmt.whileBreak` (#9804) + flag in `post` | `Codegen/Programs/SwdMinimalCopySAsm.lean` |
| early-return-from-loop (walk short-circuit) | **no byte-match combinator** — decide in `.70.2` (whileBreak-to-epilogue vs drop-in) | `mpt_insert`, `mpt_set` (only 2 in corpus) |

**Shape census** (all 848 `*Function` asm defs, exhaustive CFG parse — see
`docs/agents/4ch8f-shape-survey.md` `.70`): **612 straight-line** (424 flat
`block`, 188 `ite`/`when` cascades) + **236 looping** (159 single, 77 nested,
**0 indirect**). The **628 loop back-edges** split **493 top-test `while` / 100
bottom-test `doWhile` / 34 `whileBreak` / 1 unresolved / 0 rotated-while** —
i.e. every emitted loop already byte-matches an existing combinator; **no new
loop combinator is needed**. `while`-vs-`whileS` and `doWhile`-vs-`doWhileS` is a
*proof-side* choice (identical bytes): use the `S` variant only for an **inner**
loop whose invariant must see an **outer** loop's counter register. Byte-match is
a hand-authoring *convention*, not a codegen pass — protect it with the `.70.1`
loop-shape lint rather than reshaping emission.

Spec-side reference: `EvmAsm/Stateless/SpecRef/*` is the Lean port of the
Python spec (`tests-zkevm@v0.4.0` — read the Python via
`git -C ~/execution-specs show 'tests-zkevm@v0.4.0:src/ethereum/forks/amsterdam/<file>'`;
those files exist ONLY on that tag). When a routine has a SpecRef counterpart,
the port's functional post must be stated against it (or against a leaf-level
byte equation the SpecRef bridge later consumes).

## 3. Gates: what CI runs vs what YOU must run

CI (`.github/workflows/build.yml`) runs: `lake build` (+no-warnings),
forbidden-tactics, file-size, unimported, roundtrip-coverage,
heartbeats-approved, layering, opcode-structure, naming, codegen build,
stateless-link-check, progress, DRIFT.md, axioms (registered witnesses),
conformance-floor, fuzz-arith, statement-tamper, region-map/link-layout.

**You must run, by change type** (paste outputs in the PR body):

| change type | required beyond CI |
|---|---|
| Lean-proof-only (new specs/theorems) | `#print axioms <full.name>` per headline theorem (classical-3 only: `[propext, Classical.choice, Quot.sound]`); `scripts/port-check.sh <module>` where applicable |
| emitted-string / `_prog` conversion | `scripts/check-asm-to-program.sh` CLEAN; whole-guest LINKED `.text` byte-identity vs merge-base (`lake exe codegen --program stateless_guest --halt linux93 -o …`, `objcopy -O binary -j .text`, `cmp`; state size+sha256); ≥2 `codegen-zisk-*-check.sh` probes embedding changed functions; dispatcher render 0-added-`auipc` |
| guest-BYTE-changing (fix/restructure) | all of the above EXCEPT byte-identity, replaced by: the SAME-PR layout regen (`gen-symbol-addresses.py --build` + `asm_to_program.py guest-addrs` + repin `RegionMap.textSizeBytes`), a scoped dispatcher/guest `.s` diff (only the intended change), AND **EEST parity**: `scripts/codegen-eest-stateless-check.sh` pass/fail sets identical vs base (or strictly better, with the flipped cases named) |
| layout metadata regen | `check-region-map.sh` GREEN, `check-asm-to-program.sh` CLEAN, byte-identity UNCHANGED (metadata must never move guest bytes) |

**EEST harness**: `scripts/codegen-eest-stateless-check.sh` is the ground-truth
conformance sweep. It is slow; run the full sweep only for byte-changing PRs
(A/B vs base) — probes cover everything else. `--jobs 8` is the calibrated cap
(see the check-script perf notes in PLAN.md history).

## 4. Non-negotiable conventions (each has bitten before)

1. **No `sorry`, `native_decide`, `bv_decide`** anywhere; never raise
   `maxHeartbeats`/`maxRecDepth` (find the real cause — usually a `let`-bundle
   needing `@[irreducible]`, or an over-unfolded window; see
   `docs/agents/tactics-deep.md`).
2. **Compose, don't enumerate**: anything sized 256/1025/4096 is proved by a
   generic lemma over `n`/`List.replicate`, never case enumeration.
3. **Base-parameterized everything**: no numeric guest addresses in specs;
   reference `GuestAddrs.*` constants BY NAME only inside `_prog` defs (they
   are regenerated wholesale on layout drift).
4. **No ∃-state escapes in posts**: a postcondition pins exit
   registers/windows as FUNCTIONS of inputs/snapshot. If you find yourself
   writing `∃ ws', …` for something the routine determines, stop — that is a
   spec-weakening (review-playbook §3 has the catalog of past instances).
5. **The STOP rule**: a routine that surprises you (overlap semantics,
   misaligned access, unreachable-looking guard, spec mismatch) ⇒ STOP that
   bead, write the finding into it, file a P1 for any guest↔spec divergence
   (standing policy), move on. A documented blocker always beats a weakened
   spec or a "conservative" workaround. **Never bail-to-reject to make
   something pass** — fix the exact model (no-conservative-skips policy).
6. **Aligned accesses only**: the verified semantics traps on misaligned
   LD/SD/LW; ziskemu tolerating it does not make it legal. Byte access =
   LBU+shift/OR.
7. **Regen is authoritative**: merge conflicts on
   `GuestAddrs.lean`/`symbol-addresses.tsv`/`RegionMap` sizes are NEVER
   resolved textually — take either side, then re-run the regen on the merged
   tree. Merge layout-racing PRs promptly.
8. Git: merge (never rebase); stack PRs with `--base`; never push to a branch
   whose PR is near merge; conventional-commit titles; commit trailer
   `Co-Authored-By:` line per repo convention; zero-sorry PRs only.

## 5. Decomposing a family bead (when you reach one without children)

Pattern (already applied to .12/.13 — copy it):
1. `bd show <family>` — the description lists the routine names.
2. For each routine: `bd create --parent <family> -p 1 -t task
   "port: verify \`<fn>\` (SAsm, one-session)"` with a description holding:
   the file (grep the label in `EvmAsm/Codegen/Programs/`), its MANIFEST/
   fixture row, its callees ("Composes:" comment), the SpecRef counterpart if
   any, and the recipe row from §2 that applies.
3. Order the children callee-first in the family bead's notes.
4. A routine that is COMPOSITE/unconverted or calls unverified helpers gets a
   `blocked-by` note naming the prerequisite bead instead of being guessed at.

The composition beads (.48, .61, .62, .63, .64) are NOT decomposable this way
— each carries a bead note written by the strategy sessions describing its
specific plan; read the note before starting, and extend the note (not the
description) with what you learn.

## 6. Where the bodies are buried (session knowledge you would otherwise lack)

- **The statement has been through one repair cycle**: `GuestFraming`
  (scratch/residue + `scratch_sat`) exists because the bare form was
  unprovable, and the 40-byte pinned observation window exists because a
  decode-based `∃ out` post is vacuously dischargeable. Details + both defects:
  `docs/4ch8f-top-spec.md` §3a. Do not "simplify" either away.
- **`1 < m` gates every pow-ladder consumer** (`Crypto/PowLadder.lean`): at
  `m = 1` the staged `acc = 1` is unreduced — exactly the `.11.5` MODEXP bug
  class. Ladder consumers must gate or special-case `m ≤ 1`.
- **Handlers move the stack pointer by convention**: binary ops `x12 → sp+32`,
  unary in place, POP `+32` with no bytes; dead bytes below the new top are
  PINNED to old contents in the posts (`Codegen/Proofs/HandlerHandles*.lean`).
- **The frame arena is havoc-first**: dispatch owns `phaseDView` (contents
  forgotten); anything reading a frame must go through
  `cpsTripleWithin_anyBytes_pre` (all-contents quantification) or a focused
  window. Never assume Phase-H contents in Phase-D.
- **`bytesRegion` pads trailing dwords with zeros** — a non-multiple-of-8 byte
  list pins its final-dword tail to 0. Choose window sizes ≡ 0 (mod 8) or
  account for the pad explicitly.
- **The `.data` tables are drift-guarded, not assumed**:
  `scripts/check-opcode-tables.sh`, `scripts/check-region-map.sh` — if your
  work adds a Lean mirror of any emitted data, add the same style of
  ELF-comparison guard in the same PR.
- **EEST receipt-gas / bv_fail lore**: the verdict-side false-reject debugging
  history (bv_fail codes, receipt-gas reconstruction, EIP-8037 state gas) is
  indexed in the memory files referenced from PLAN.md history; for verdict
  beads (.44/.45/.61/.62) grep PLAN.md and the bead notes before re-deriving.

## 7. Quick index

| I need… | go to |
|---|---|
| next bead | §1 rules + `bd list --parent evm-asm-4ch8f` |
| the port workflow | `docs/agents/port-playbook.md` |
| review a PR | `docs/agents/review-playbook.md` |
| the top statement + trust boundary | `docs/4ch8f-top-spec.md`, `EvmAsm/Stateless/EntrySpec.lean` |
| dispatch/frames/interpreter plan | `docs/4ch8f-interp-strategy.md` |
| crypto tiers + field-arith library | `docs/4ch8f-crypto-strategy.md` |
| SAsm reference | `docs/sasm-design.md`, `docs/agents/wp-framework.md` |
| memory layout / regions | `EvmAsm/Codegen/RegionMap.lean`, `docs/4ch8f-region-map.md` |
| spec ground truth | `EvmAsm/Stateless/SpecRef/`, `tests-zkevm@v0.4.0` tag |
| conformance harness | `scripts/codegen-eest-stateless-check.sh` (§3) |
