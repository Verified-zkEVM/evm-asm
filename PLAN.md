# PLAN: Verified RISC-V EVM Implementation

> **Agent instruction**: Keep this file up to date as you work. When you finish
> implementing an opcode or task, move it to the "Done" list under
> "Current Status", update any counts or details that changed, and note any
> new sub-tasks you discovered. Check this file at the start of each session
> to pick up where the last agent left off.

Goal: implement and verify the EVM state transition function (STF) as RISC-V
macro assembly programs, for use as a zkEVM. Each EVM opcode becomes a verified
RISC-V subroutine operating on 256-bit stack words in memory. The STF is the
single most important piece in the execution layer — it processes blocks of
transactions against the world state.

**Target: RV64IM (64-bit)**, per the zkvm-standards spec
(`EvmAsm/Evm64/zkvm-standards/`). RV32IM was removed (not relevant).

Reference spec: `execution-specs/src/ethereum/forks/shanghai/vm/` (Python).
zkVM standards: `EvmAsm/Evm64/zkvm-standards/` (submodule).

> **Parallel codegen track.** Emitting verified `Program`s as executable
> RV64 ELFs that run on the Zisk emulator is tracked separately in
> [`CODEGEN.md`](CODEGEN.md). **M0–M10 are done**: text emitter, total
> `Instr` coverage, `evm_add` round-trip on `ziskemu` from both `.data`
> and `ziskemu -i`, tiny EVM interpreter with runtime fetch/decode/
> dispatch, and **91 wired opcodes** through `tinyInterpRegistry` —
> PUSH0–32, DUP1–16, SWAP1–16, 17 clean-shape singletons, MLOAD/MSTORE/
> MSTORE8 (M7), DIV/MOD (M8), runtime-bytecode dispatcher (M8.5),
> SDIV/SMOD via trampoline (M9), and ADDMOD via inline-callable (M10).
> EXP via inline-callable `_fixed_fixed_headroom` body (M27; per-limb
> counter in callee-saved x22 so it survives `mul_callable`, plus the
> architecture-B headroom layout that runs the squaring loop in the stack
> slack — fixes the caller-stack-corruption bug `evm-asm-fjivz`). Codegen-
> proofs **Phase 1 (registry invariants)** and the first 13/91
> instances of **Phase 4 (handler-level `cpsTripleWithin` specs via
> `cleanRetHandlerSpec`)** have landed under
> `EvmAsm/Codegen/Proofs/`. Codegen remains purely additive — it does
> not modify the verified core.

---

## Architecture Overview

### RISC-V Backend

| | RV64IM (Evm64) |
|---|---|
| **Target** | `riscv64im_zicclsm-unknown-none-elf` |
| **Word size** | 64-bit (`BitVec 64`) |
| **Limbs per EvmWord** | 4 × 64-bit (LE) |
| **Memory ops** | LD/SD (8-byte aligned) |
| **Files** | `EvmAsm/Evm64/` |
| **Infrastructure** | `EvmAsm/Rv64/` |

### zkVM Standards (submodule: `EvmAsm/Evm64/zkvm-standards/`)

The standards define the target environment for Ethereum zkVMs:
- **RISC-V target**: RV64IM + Zicclsm (misaligned load/store support)
- **IO interface**: `read_input` / `write_output` for private input and public output
- **Cryptographic accelerators**: C interface for keccak256, ecrecover, SHA-256,
  RIPEMD-160, modexp, BN254, BLS12-381, BLAKE2f, KZG, secp256r1 (via
  `zkvm_accelerators.h`)
- These accelerators map directly to Ethereum precompiles and KECCAK256

### Machine State (Rv64)

```
MachineState:
  regs : Reg → BitVec 64       -- Registers: x0(zero), x1(ra), x2(sp),
                                --   x5-x7(t0-t2), x10-x12(a0-a2)
  mem  : Addr → BitVec 64      -- 64-bit addressable memory
  code : Addr → Option Instr   -- Instruction memory (immutable)
  pc   : BitVec 64             -- Program counter
  committed : List (Word × Word)  -- legacy SP1 COMMIT word-pair outputs
  publicValues : List (BitVec 8)  -- public output bytes for write_output/WRITE
  privateInput : List (BitVec 8)  -- legacy SP1 HINT_READ input stream
```

EVM stack: x12 is EVM stack pointer, stack grows upward, 32 bytes per element.

### Proof Framework

- **Separation logic**: `r ↦ᵣ v` (register), `a ↦ₘ v` (memory), `**` (sep conj)
- **CPS Hoare triples**: `cpsTriple base end P Q` — from `base` to `end`, if P
  holds then Q holds, with automatic frame rule for untouched resources
- **Per-limb composition**: Each 256-bit op decomposes into 4 per-limb specs,
  then composed via `runBlock` tactic
- **Key tactics**: `xperm`, `xsimp`, `xcancel`, `seqFrame`, `runBlock`,
  `validMem`, `liftSpec`, `pcFree`

---

## Current Status

### Evm64 (PRIMARY) — 52 opcodes

| Category | Opcodes | Instructions (per op) | Status |
|----------|---------|----------------------|--------|
| Arithmetic | ADD, SUB, MUL, SIGNEXTEND | 30 / 30 / 63 / 48 | ✅ Fully proved |
| Bitwise | AND, OR, XOR, NOT | 17 / 17 / 17 / 12 | ✅ Fully proved |
| Shift | SHR, SHL, SAR | 90 / 90 / 95 | ✅ Fully proved |
| Comparison | ISZERO, LT, GT, EQ, SLT, SGT | 12 / 26 / 26 / 21 / 25 / 25 | ✅ Fully proved |
| Byte/SignExt | BYTE, SIGNEXTEND | 45 / 48 | ✅ Fully proved |
| Stack | POP, PUSH0, PUSH1-32, DUP1-16, SWAP1-16 | 1 / 5 / (5+2n) / 9 / 16 | ✅ Fully proved |

**Deleted spec files** (incomplete CodeReq migration, easier to recreate):
- ~~`ShiftSpec.lean`~~ — ✅ Recreated as `LimbSpec.lean` (SHR) + `ShlSpec.lean` (SHL) + `Compose.lean` + `ShlCompose.lean` + `Semantic.lean` + `ShlSemantic.lean`
- ~~`ShlSpec.lean`~~ — ✅ Recreated (per-limb + body + composition + stack-level spec)
- ~~`SarSpec.lean`~~ — ✅ Recreated (per-limb + body + sign-fill + composition + stack-level spec)
- ~~`ByteSpec.lean`~~ — ✅ Recreated as `Byte/Spec.lean` (stack-level `evm_byte_stack_spec`) + `Byte/LimbSpec.lean` (per-body + cascade dispatch)
- ~~`StackOps.lean`~~ — ✅ Recreated as modular `Pop.lean`, `Push0.lean`, `Dup.lean`, `Swap.lean`

All deleted spec files have been recreated. See **Pending: Recreate Deleted Spec Files** below for details.

**Removed targets** (not relevant to primary goal):
- Evm32 (secondary RV32IM target) — removed entirely
- Rv32 infrastructure — removed entirely
- Examples (Swap, HelloWorld, Echo, etc.) — removed (all depended on Rv32)

### Infrastructure — RV64 only, no sorry

- RV64: Basic, Instructions, Program, Execution, CPSSpec,
  ControlFlow, SepLogic, GenericSpecs, InstructionSpecs, SyscallSpecs,
  HalfwordOps, WordOps
- Tactics: XPerm, XSimp, XCancel, SeqFrame, RunBlock, LiftSpec, ValidMem,
  PcFree, SpecDb
- **CodeReq infrastructure** (Issue #35): `CodeReq` type + `cpsTriple` 5-arg
  form + composition rules + tactic support in Rv64.
  CodeReq monotonicity helpers in SepLogic.lean
  (`union_singleton_apply`, `beq_base_offset`, `union_mono_tail`).
- **`CodeReq.ofProg`** (recent): Replaces chains of `singleton.union` with
  program-based CodeReq construction. Key infrastructure in SepLogic.lean:
  - `ofProg base prog` — builds CodeReq from a `List Instr`
  - `ofProg_append` — splits `ofProg base (p1 ++ p2)` into two `ofProg` unions
  - `ofProg_none_range` — proves out-of-range addresses return `none`
  - `unionAll` — structural subsumption for lists of CodeReqs
  - Range-based `ofProg` disjointness (O(1) vs O(n) singleton expansion)
  - MultiplySpec col0–col3 migrated to `ofProg` pattern
- **runTacticSilent**: Suppresses bv_omega diagnostic leaks from speculative
  tactic calls (Lean 4.29 regression fix in SeqFrame.lean/RunBlock.lean).
- **`bv_decide` purge — COMPLETE** (fully kernel-checkable trust base):
  Following the `native_decide` elimination (206 → 0), `bv_decide` was driven
  from **290 → 0** call sites. The full library builds green (3027 jobs) and
  the witnessed trust base (`check-axioms.sh --report`) is **0 non-classical
  axioms** beyond `propext`/`Classical.choice`/`Quot.sound`. Conversion
  techniques: `BitVec.eq_of_getLsbD_eq` + `simp`/`omega` (getLsbD block-splits
  for `fromLimbs`/`getLimb`/8-byte-concat identities), `congr 1`/`decide` +
  `bv_omega` for address/`signExtend` arithmetic, a shared
  `ushr63_bool : x >>> 63 ∈ {0,1}` helper for sign disjunctions, the bit-0
  parity helper for `&&& ~~~1` JALR masks, `decide` for concrete 256-bit goals
  (kernel `Nat` is GMP-fast), and — for the multi-limb two's-complement
  lemmas in `SDiv`/`SMod` `Compose/Words.lean` (`…_eq_neg_word_of_sign_one`,
  `= -quotient`, `= -modulus`, plus the dependent `…_sign_split`/`…_eq_zero_iff`
  /`…_limb_sign` lemmas) — `EvmWordArith.add_carry_chain_correct (~~~v) 1`
  (the ripple-carry negation `sdivAbsWord = ~~~v + 1 = -v`) composed with
  `fromLimbs_getLimb`/`BitVec.neg_eq_not_add`. The `divmod_addr`/`rv64_addr`
  grind-set definition files use a local `addrclose` macro. The 6 now-unused
  `import Std.Tactic.BVDecide` lines were removed. **CI keeps it out** via two
  complementary gates (`.github/workflows/build.yml`):
  `scripts/check-forbidden-tactics.sh` (fast source scan — fails on any
  `bv_decide`/`native_decide` tactic invocation in `EvmAsm/**.lean`) and
  `scripts/check-axioms.sh` (kernel-truth `#print axioms` backstop — now
  forbids `bv_decide` trust axioms too, not just `native_decide`). See
  `CLAUDE.md` / `CONTRIBUTING.md`.
- **Progress-registry semantics — agent-steering rollout** (`EvmAsm/Progress.lean`,
  `docs/agent-progress-steering-review.md`):
  - **Phase 0 (merged, PR #7994):** `check-axioms.sh`, `check-statement-tamper.sh`,
    `check-conformance-floor.sh`, `check-forbidden-tactics.sh` wired into
    `build.yml`.
  - **Phase 1 (this work):** added a `conditional` `ProofTier` (complete
    top-level Hoare triple gated by a nonvacuous input-domain precondition —
    distinct from `partly`, which has no complete triple). **DIV, MOD, SDIV**
    reclassified `.partly → .conditional` (each gated by `b.getLimbN 3 = 0` /
    `hStack`). New kernel-checked counts `conditionalCount_eq = 3` /
    `conditionalBytes_eq = 3`; `partialCount 9→6`, `partialBytes 39→36`; totals
    unchanged (85 entries / 149 bytes). SMOD/MULMOD/EXP/ADDMOD stay `.partly`
    (no full triple; ADDMOD's triple is single-point `b=0` only). Added typed
    `cycleBound : Option Nat` to `OpcodeEntry` (the `N=…` cycle bounds migrated
    out of free-text `notes` into this field, rendered in the `Cycles (N)`
    column — R-C4) plus optional `milestones`/`coverRef` scaffold fields
    (R-A4/R-A3). Registry rows now use an `entry` smart constructor so the
    optional fields stay defaulted. Per-tier rubric documented in `AGENTS.md` +
    `progress-template.md`. **Follow-up (deferred):** kernel-checked *binding*
    of `cycleBound` to the witness theorem's literal `cpsTripleWithin N` (the
    `Progress.lean`→Spec circular-import problem; option ii/iii in the bootstrap)
    — landed field+renderer (option i) for now. Cover lemmas for the three
    `conditional` entries (`coverRef`) also not yet written.
  - **Phase 2 (this work) — direction tracking:** net-new kernel-checked
    obligation tracker `EvmAsm/Progress/Obligations.lean` (`ObligationStatus`
    `done|blocked|notStarted`, a `Blocker` sum type `.opcode|.infra`, the 9
    guest-program obligations, `by decide` counts `doneCount_eq = 2` /
    `blockedCount_eq = 6` / `notStartedCount_eq = 1` / `totalObligations_eq = 9`,
    and `blocker_opcodes_in_registry` — a `by decide` cross-check that every
    `.opcode` blocker names a real `Progress.registry` entry, so a renamed
    opcode fails the build). `MainProgress.lean` renders an "obligation ×
    blocker" matrix into `PROGRESS.md` (the obligations table moved out of
    `progress-template.md` into the generated section). New `DRIFT.md` TCB /
    "what is NOT proven" ledger, generated by `lake exe progress-report drift`
    (`scripts/drift-report.sh`) and drift-gated by `scripts/check-drift.sh`
    (wired into `build.yml`) — lists the conditional uncovered domains, the
    `partly`/`execSpec`/`notStarted` opcodes, and the trust boundaries (codegen
    unverified by design, RV64/EVM/gas modeling). Velocity time-series:
    `scripts/progress-snapshot.sh` (one JSONL row per commit, parsed from the
    drift-gated `PROGRESS.md` — no build needed) + `scripts/progress-velocity.sh`
    (deltas + monotonic-regression alarm for the DIV-style silent downgrade),
    persisted to a `progress-history` orphan branch by
    `.github/workflows/progress-history.yml` (mirrors `benchmark-history`), which
    also surfaces an advisory velocity read in the job summary on each main push.
    Obligations carry a kernel invariant `done_obligations_well_formed`
    (`done → witness ∧ no blockers`) so a false-green status flip can't be a
    one-token edit. **Follow-up (deferred to Phase 4 / R-B1 scorecard):** wire
    `progress-velocity.sh --check` as a *PR-time* gate (the post-merge workflow
    can't block a merge); it is advisory-only today.
  - **Phase 3 (this work) — DIV-class defense (differential / fuzz testing):**
    closes the *codegen* blind spot (the kernel proves the in-Lean semantics,
    not the RISC-V lowering / ziskemu — the home of the v4 DIV bug).
    - **D1 (R-E1) — boundary-biased arithmetic differential fuzzer.**
      `EvmAsm/Tests/ArithDiffCheck.lean` + `lake exe arith-diff-check` fuzz
      `EvmWord.{div,mod,sdiv,smod,mulmod,addmod}` against an INDEPENDENT
      Nat/Int reference over operands biased toward the Knuth-D rare paths
      (sign edges ±2^255, limb boundaries, 4-limb divisors with a large top
      word — the `b.getLimbN 3 ≠ 0` regime the v4 proof excluded, add-back).
      Permanent regression corpus `tests/fuzz-corpus/arith/corpus.jsonl`
      (29 curated DIV-class edges) carries the execution-specs *amsterdam*
      oracle verdict, re-checked by the PR fast-path without Python. Nightly
      tier `scripts/fuzz-arith-diff.sh --python` (`.github/workflows/
      fuzz-arith.yml`) drives 20k+ operands through both evm-asm and the
      UNMODIFIED execution-specs oracle (`scripts/fuzz_arith_oracle.py` under
      `uv run`), appending any divergence to the corpus. PR fast-path wired
      into `build.yml`. The oracle is a TEST ORACLE ONLY (never in the TCB).
    - **D2 (R-E3) — EEST budget-vs-wrong distinction.**
      `scripts/codegen-eest-stateless-check.sh` now buckets a `--steps`
      exhaustion as `BUDGET` (separate from `ERROR`, never folded into fail
      or the `--min-*` gates), detected via the overridable
      `EEST_STEP_LIMIT_RE`; non-match falls through to `ERROR` (regression-
      free). Per-opcode/per-step localization deferred (needs ziskemu trace
      instrumentation).
    - **D4 (R-E4) — round-trip coverage fence.**
      `scripts/check-roundtrip-coverage.sh` (wired into `build.yml`) asserts
      every `Rv64/Basic.lean` `Instr` constructor (55) has a `#guard` in
      `Codegen/RoundTripTests.lean`; fails when a new shape lands unguarded.
    - **D3 (R-E2) — dual-path differential: DEFERRED.** In-Lean execution
      model vs codegen→ziskemu round-trip; the ziskemu-equality assertion
      can't be validated without a working ziskemu (unavailable this
      session). Concrete build plan captured in
      `docs/dual-path-differential-design.md` for a session with ziskemu.
  - **Phase 4 (this work) — review throughput & merge safety (P3):** rations the
    single maintainer's attention with objective triage and enforces the trust
    boundary at the merge gate. Stacked on the Phase 3 branch (Phases 2–4 still
    unmerged at hand-off).
    - **D1 (R-C5) — enforced trust boundary.** Net-new `.github/CODEOWNERS`
      maps the verified core (`Progress.lean`, `Progress/`, `Rv64/`,
      `**/Spec.lean`, `EL/Conformance/`, verifier-config scripts, `lakefile.toml`/
      `lean-toolchain`, `.github/workflows/`) to `@pirapira`; codegen is
      deliberately left unowned (lighter bar — unverified by design, fenced by
      conformance/fuzz/dual-path). CODEOWNERS is advisory until paired with a
      branch ruleset (a repo *setting*); the proposed ruleset + the approval-
      count question are in the PR body (open question #1).
    - **D2 (step 14) — merge-queue design doc FIRST.**
      `docs/merge-queue-design.md` documents the GitHub native merge queue with
      *batching* + TAP test-and-bisect eviction (on batch failure, bisect to
      eject the offending PR — `O(log N)` runs — rather than re-running the
      ~516-script ziskemu suite per PR). `build.yml` already triggers on
      `merge_group`; the doc gates *activation* (a repo setting), it does not
      flip the queue on. Heavy-vs-light check placement table included.
    - **D3 (R-B1) — deterministic risk scorecard.** Extended
      `scripts/progress-delta.sh` (still pure git+awk, no LLM, the existing
      `summary.yml` payload path — not new plumbing) with a 5-column scorecard
      `{new top-level triples, Δtier counts, net Δsorries+axioms, Δconformance,
      touches-trusted-core, statement-edit, changed-lines}` + a HIGH/MEDIUM/LOW
      risk label. HIGH = touches `Progress.lean`/`Rv64/Basic.lean`/`*Spec.lean`,
      XL diff (>1000 lines excl. `codegen-*.sh`), or codegen changed with no
      round-trip/conformance script change; MEDIUM = other trusted-core /
      statement / sorry-axiom-increase signals. Trusted-core path set mirrors
      `check-statement-tamper.sh`. Risk is **triage ordering only — not
      auto-merge authority for the verified core**. Also fixed a latent
      `conformance_count` regex bug (required a space before the backtick-wrapped
      `allConformanceVectors_length`, so conformance delta always read `?`).
    - **D4 (R-B2) — path + size auto-labeling.** `.github/labeler.yml` +
      `.github/workflows/labeler.yml` (`actions/labeler@v5`) tag
      `area:verified-core` / `area:codegen` / `area:docs`; a size labeler buckets
      `size/XS..XL` from per-file API line counts **excluding `scripts/codegen-*.sh`**
      so a bulk script regen isn't mislabeled XL (XL boundary 1000 = scorecard
      threshold).
    - **D5 (R-B3) — statement-strength rubric.** `docs/pr-summary-progress-prompt.md`
      gains a spec-quality sign-off (`Statement-strength: OK|REVIEW — …`) layered
      **only** on the un-kernel-checkable question (vacuous/over-restricted
      precondition? postcondition covers stack+memory+gas+halting?) — explicitly
      **never on proof correctness** (the kernel is the perfect oracle there).
    - **D6 (G2.6) — long-running-branch visibility.** `BEADS.md` claim ledger
      (coordination overlay on the `bd` tracker — collision detection for
      double-claimed beads) + `.github/workflows/stale-pr-nudge.yml`
      (`actions/stale@v9`, 21-day nudge, **never auto-closes**, `long-running`
      label exempts deliberately long-lived stacks).
    - **D7 (Phase-2 deferral / R-A5) — PR-time velocity gate.**
      `.github/workflows/progress-velocity-check.yml` snapshots PR **base** (via
      new `progress-snapshot.sh --ref <commit>`, pure `git show`, no checkout)
      vs PR **head** and runs `progress-velocity.sh --check` on the 2-record log
      — catching a monotonic proven/conformance/obligation downgrade *before* it
      lands. Base→head (not head-vs-latest-main) avoids false positives on
      stale branches. Cheap (no `lake build`). **Blocking by default** — a
      monotonic downgrade fails the PR; set the `VELOCITY_GATE` repo var to
      `warn` to relax to advisory for a known generalization, then restore to
      `block` (open question #4).
    - **Open questions surfaced in the PR:** (1) ruleset approval counts for a
      single-maintainer repo; (2) merge-queue batch size + eviction; (3) risk
      XL threshold + exact trusted-core path set; (4) velocity gate warn-vs-block.
    - **Opportunistic carry-overs still deferred:** Phase-1 `cycleBound`-binding
      (R-C4) + `coverRef` cover lemmas (R-A3); Phase-3 D3 dual-path (needs
      ziskemu) + per-opcode EEST localization.
  - **Phase 5 (this work) — conventions-as-gates + cost trend (P1/P3): the
    FINAL phase. ROLLOUT COMPLETE (Phases 0–5 done).** Grows the `check-*.sh`
    suite so prose conventions become executable architecture fitness functions
    (Ford/Parsons), retires the one dead gate, and stands up advisory cost/churn
    trend infra — without tripping the build-budget / noisy-gate non-goals. No
    Lean source touched (pure scripts/config/workflows/docs), so `lake build` is
    unaffected. Branched off fresh `upstream/main` (Phases 0–4 all merged).
    - **D1 (R-D1) — opcode-structure gate.** `scripts/check-opcode-structure.sh`
      hard-fails (block) on a broken `AddrNorm.lean`↔`AddrNormAttr.lean` pairing
      (Lean forbids `register_simp_attr` in its declaring file — a real
      structural bug, holds tree-wide today). The four `OPCODE_TEMPLATE.md`
      essentials can't be blanket-required (only `DivMod` has all four; FullPath
      is the end-state composition), so the rest is an **advisory checklist**
      diff-scoped to *newly-added complex* opcode dirs (those adding `Compose/`
      or `LimbSpec/`): nudges for FullPath, `@[irreducible]` Post, `Offsets.lean`.
    - **D2 (R-D1) — naming scan (advisory).** `scripts/check-naming.sh` flags
      camelCase hypotheses (`hLt`) *newly added in the PR diff*, the PR #1497
      regression class. Diff-scoped + advisory because the tree already has
      thousands of legacy camelCase hypotheses — a full-tree gate would be pure
      noise. Never blocks.
    - **D3 (R-D1) — heartbeat allowlist (block).** `check-heartbeats-approved.sh`
      + `scripts/approved-heartbeat-overrides.txt` make heartbeats off-limits:
      a **dumb case-insensitive `grep heartbeats`** over ALL repo `.lean`
      (excluding `.lake/` dependency sources) + the lakefiles flags EVERY
      mention (overrides AND prose), each adjacent value of which must be
      sanctioned in the allowlist at its exact value (`-` for a non-numeric
      docstring mention). No Lean lexer — nothing to bypass (three review rounds
      each found a fresh hole in an earlier comment/string-aware scanner; the
      policy is simply "nobody touches heartbeats," so the gate matches it).
      Seeded green with the two grandfathered numeric overrides
      (`Swap/Spec.lean` 800000, `ALUProofs.lean` 4000000; each carries a
      relitigation bead, open question #3) + three sanctioned prose mentions.
    - **D4 (R-D1, REFRAMED) — layering gate (block).** `scripts/check-layering.sh`.
      The bootstrap's "EL must not import Rv64" is **false against the tree**
      (RLP spans both directions: `EL/RLP/*`→`Rv64` *and* `Rv64/RLP/Phase*`→`EL`),
      so it was reframed to the true, currently-clean invariants: **L1** the
      verified core never imports the unverified `Codegen` layer (fences the
      report §6 "codegen unverified by design" boundary) — scoped
      *core-by-default*, i.e. every `EvmAsm/` dir except `Codegen`/`Tests`/
      `Examples`, so a future new dir can't become an unscanned laundering hop —
      **L2** nothing imports the `Progress` registry, **L3** core never imports
      the `Tests`/`Examples` escape hatches (which may import Codegen), closing
      the last `core→Tests→Codegen` hop. Advisory
      rider: `Rv64`↛`Evm64` with the one grandfathered tactic-bridge edge
      (`Rv64/Tactics/LiftSpec.lean`) allowlisted.
    - **D5 (R-D1) — fitness-function reframing + dead-gate retirement.** AGENTS.md
      now documents the `check-*.sh` suite as architecture fitness functions
      (blocking vs advisory tiers tabulated). Retired the orphaned
      `scripts/check-unbounded-cps.sh` (unwired since `6e7ce6dec`; it matched
      only prose `cpsTriple` mentions and would red-line if wired — it policed
      nothing).
    - **D6 (R-C6) — churn report (advisory).** `scripts/churn-report.sh` (pure
      `git log`, no deps): top-churn `.lean`/`scripts` per window + short-lived
      churn. Runs on the weekly `quality-trends.yml` cadence (needs full history,
      off the per-PR path). Never gates.
    - **D7 (R-C6) — duplication watch (advisory).** `scripts/check-duplication.sh`
      + `scripts/jscpd.json` + `scripts/duplication-baseline.txt` (budget seeded
      2.93% over the default `scripts/` scope). Rule of Three: `codegen-*.sh` and
      concrete `Program(s).lean` excluded. Per-PR scope is `scripts/` only (a full
      ~2000-file `.lean` sweep exceeds 300s); the full sweep runs weekly in
      `quality-trends.yml`. Advisory now; `--gate` promotes after calibration
      (open question #2).
    - **D8 (R-F1) — ziskemu cycle instrumentation (schema + appender; live parse
      DEFERRED).** `scripts/cycles-append.sh` + the `cycles-history.jsonl` schema
      (git-derived commit/date, pinned EEST tag, nullable `steps`/`cycles`). The
      only path to validating the founding "better zkVM performance" claim. No
      working ziskemu this session → the log live-parse is guarded/deferred; the
      schema + appender land now so codegen scripts can start emitting (open
      question #4).
    - **D9 (R-F2) — proof-size + build-time trend.** `benchmark.yml`'s `lakeprof`
      job already records per-module build *time*; added the deterministic proof-
      *size* dimension (`.github/workflows/scripts/oleansize_collect.sh` merges
      top-N `.olean` byte sizes into the appended record). Size is noise-free
      where CI time is noisy, so a ballooning n=4 division proof surfaces as a
      monotone trend. Deliberate no-hard-threshold stance preserved — **never a
      heartbeat bump to force a proof green**.
    - **D10 (R-F3) — external export scaffold.** `.github/workflows/export-metrics.yml`
      (monthly) bundles `benchmark-history` + `cycles-history.jsonl` and uploads
      an artifact; pushes toward `eth-act/zkevm-benchmark-workload` only when
      `vars.METRICS_EXPORT_REPO` + `secrets.METRICS_EXPORT_TOKEN` are configured
      (no-op otherwise). Performance ≠ conformance — "proves X% of blocks" is
      never a verification signal.
    - **Block vs advisory (open question #1, decided):** BLOCK = opcode-structure
      pairing + heartbeat allowlist + layering. ADVISORY = naming + opcode
      checklist + churn + duplication + all cost/trend infra (D8–D10).
    - **Verifier-config hardening:** the new allowlists/configs
      (`approved-heartbeat-overrides.txt`, `duplication-baseline.txt`,
      `jscpd.json`) + `churn-report.sh`/`cycles-append.sh` + `.github/labeler.yml`
      were added to all four trusted-core path sets (CODEOWNERS,
      `is_trusted_core`, `is_verifier_config`, `labeler.yml`) so they can't be
      self-weakened without maintainer review.
    - **Open question (R-C2 enforcement strength, surfaced by review):** a
      gate-neutering edit — adding `continue-on-error`, deleting a blocking step,
      or editing a `check-*.sh` to `exit 0` — currently fails NO CI check:
      `check-statement-tamper.sh` runs **advisory** in `build.yml` (no `--strict`),
      so verifier-config edits are only *printed*, and enforcement rests on
      CODEOWNERS + the (repo-setting) Code-Owner ruleset + human review — the
      report's intended approve-by-exception model. Defense-in-depth option for
      the maintainer: run the tamper scan `--strict` over the
      `scripts/check-*.sh` + `.github/workflows/**` subset (the
      `[allow-verifier-change]` commit token is the escape hatch) so a
      self-neutering edit at least *fails a check*. Deliberately NOT changed here
      (it reverses a Phase-0 design choice and would gate every verifier-config
      PR); flagged for a maintainer decision.
    - **Rollout-wide still-deferred beads:** R-C4 `cycleBound`-binding, R-A3
      `coverRef` cover lemmas, R-E2 dual-path (needs ziskemu), D8 ziskemu cycle
      live-parse **+ its persistence/caller wiring** (`cycles-history.jsonl` is
      gitignored and not yet persisted to an orphan branch, so the cycles half
      of the export bundle is empty until ziskemu lands — mirror
      `benchmark-history` then), and the two grandfathered heartbeat-override
      relitigations.
- **Proof-ergonomics infra distilled from the purge** (see `GRIND.md` §7):
  - **`signExtend` simprocs + `signext` tactic** (`Rv64/SignExtendSimproc.lean`):
    `reduceSignExtend12/13/21` are `dsimproc_decl`s (definitional, kernel-checkable,
    *not* in default simp) that evaluate `signExtend1? <literal>` → its `Word`
    constant, including negative offsets (`-32#12`) the core `BitVec.reduceSignExtend`
    declines. The `signext` tactic then closes `addr + signExtend c = addr + K`
    / pure-address / standalone-eval goals via `bv_omega`. Replaces the bespoke
    `congr 1 <;> decide` / `rw [show … by decide]` idiom; `Exp/AddrNorm`'s
    `addrclose` now delegates to it (84 sites).
  - **`evmword_limb` grind/simp set** (`Evm64/Basic.lean` + `EvmWordLimbAttr.lean`):
    the `getLimb`/`fromLimbs`/`getLimbN` round-trips + bitwise-distribution lemmas
    are dual-tagged `@[evmword_limb, grind =]`, so `grind` discovers limb
    normalizations and `simp [evmword_limb]` normalizes limb expressions.
  - **`Rv64/BitAux.lean`** — shared `Word` bit-level helpers (`ushr63_bool`,
    `ult_zero_false`, `word_xor_zero`, `bv6_63_toNat`, …) that were previously
    copied as `private` decls into `SDiv`/`SMod` `Compose/Words.lean` (now
    imported from one place), plus 2-byte-alignment lemmas
    (`word_andn_one_of_even`, `word_add_even_and_one`/`_andn_one`, the latter
    two `@[grind →]`) that dedup the inline JALR-mask (`&&& ~~~1` / `&&& 1 = 0`)
    parity proofs; `Exp/AddrNorm.addrAligned` and the two `SDiv/Compose/Base`
    mask lemmas now delegate to them.
  - **DONE (PR #9536, issue #266):** the near-identical multi-limb
    two's-complement `…= -v` proofs in `SDiv`/`SMod` `Compose/Words.lean` are now
    factored behind one shared `rippleNegWord limb0 limb1 limb2 limb3 sign` kernel
    + two generic lemmas (`rippleNegWord_of_sign_{one,zero}`). The five concrete
    defs (`sdivAbsDividendWord`, `sdivAbsDivisorWord`, `sdivResultSignFixedWord`,
    `sdivSignFixedWord`, `smodResultSignFixedWord`) became thin `rippleNegWord`
    applications and the per-operand proofs collapsed to 2-line wrappers (net
    −162 lines; def names/statements unchanged so name-level consumers were
    untouched; axiom footprint unchanged). The DIV/MOD main-loop dedup half of
    #266 remains a separate, larger `DivMod/LoopBody*` refactor.
- **Execution Layer specs** (`EvmAsm/EL/`): Pure Lean specs for Ethereum
  data structures, independent of RISC-V. Currently:
  - `EL/RLP/` — RLP encoding/decoding with round-trip proofs (`decide`)
- **Byte-level infrastructure** (`ByteOps.lean`): `extractByte`/`replaceByte`
  algebra, `generic_lbu_spec` and `generic_sb_spec` CPS specs bridging
  byte-addressable operations to word-level separation logic assertions.
- **`divmod_addr` simp/grind set** (`Evm64/DivMod/AddrNorm.lean`, `AddrNormAttr.lean`,
  issue #263): Registers atomic `signExtend12`/`<<<`/`BitVec.toNat` evaluations
  on every concrete offset used in DivMod (33 signExtend12 offsets, 5 word
  shifts, 11 BitVec 6 toNat values) as `@[divmod_addr, grind =]` facts. The
  `divmod_addr` tactic macro closes address-arithmetic equalities grind-first,
  simp+bv_omega-fallback. First migration: 4 lemmas in `LoopComposeN3.lean`.
  Conventions, layout patterns, empirical justification, rules of thumb, and
  rollout roadmap are documented in `GRIND.md` (single source of truth for
  simp/grind-set conventions; `CLAUDE.md` and `AGENTS.md` link to it).
- **`rv64_addr` simp/grind set** (`Rv64/AddrNorm.lean`, `AddrNormAttr.lean`,
  GRIND.md Phase 3): Rv64-wide counterpart to `divmod_addr`. Registers ~47
  atomic facts (29 `signExtend13` evaluations + 19 `signExtend21` evaluations
  + `word_zero_add` / `word_add_zero` identities) as `@[rv64_addr, grind =]`.
  The `rv64_addr` tactic macro tries `grind` first and falls back to
  `simp only [rv64_addr, BitVec.add_assoc]; rfl` — subsumes the legacy
  `bv_addr`. Inline `rw [show signExtend1? N = <const> from by decide]`
  migration complete across DivMod / SignExtend / Shift / Byte (82 sites
  across 12 files under PRs #385 / #388 / #390 / #392 / #395).
- **`reg_ops` simp/grind set** (`Rv64/RegOps.lean`, `RegOpsAttr.lean`,
  GRIND.md Phase 5): Registers ~40 projection lemmas (`pc_set<F>`,
  `code_set<F>`, `getReg_setPC`, `getMem_set<F>`, `committed_*`,
  `publicValues_*`, `privateInput_*` + `_append{Commit,PublicValues}`)
  from `Basic.lean` with `@[reg_ops, grind =]` via `attribute` commands.
  The `reg_ops` tactic closes projection chains in one line. Inductive
  `*_writeWords` / `*_writeBytesAsWords` variants deliberately excluded
  to avoid grind-loop risk on open-ended lists.
- **Opcode-subroutine template** (`Evm64/OPCODE_TEMPLATE.md`, issue #313):
  Day-one conventions for the next opcode subtree — parallel
  `LimbSpec/` / `LoopDefs/` / `Compose/` layout, unified Bool/Fin dispatch
  from day one (no `<Opcode>Skip.lean` + `<Opcode>Addback.lean`
  intermediates), sibling-opcode (SMOD/ADDMOD) factoring, `@[irreducible]`
  bundling for ≥3 `let` bindings or >20-atom frames, named
  `Compose/Offsets.lean` with drift checks, per-opcode `AddrNorm` +
  `AddrNormAttr` files, `structure <Opcode>Valid` validity bundle,
  pre-opcode audit checklist, reviewer checklist. Linked from `AGENTS.md`.
- **`LoopDefs/{Iter,Post,Bundle}.lean` split** (`Evm64/DivMod/LoopDefs/`,
  issue #312): Monolithic 1,359-line `LoopDefs.lean` split into three
  focused sub-files — `Iter.lean` (pure `Word`/`Prop` computations),
  `Post.lean` (Assertion-valued postconditions), `Bundle.lean`
  (Assertion-valued preconditions). `LoopDefs.lean` reduced to a 16-line
  hub that re-exports the three sub-files, so every downstream
  `import EvmAsm.Evm64.DivMod.LoopDefs` works unchanged. Follow-on work
  on `LimbSpec.lean` (still 2,992 lines) pending.
- **n=1 single-limb DIV/MOD fast path** (`Evm64/DivMod/FastN1Program.lean`,
  issue #9303): `evm_div_v6` / `evm_mod_v6` prepend a runtime dispatch that
  routes single-limb divisors (`b1=b2=b3=0, b0≠0`) to a lightweight path —
  normalize one limb, then 4 exact per-limb 128/64 divides through the fast
  path's own `divK_div128_v5` copy, threading the remainder with a single
  MUL/SUB (no 4-limb mul-sub correction loop). n≥2 and b=0 fall through to the
  reused, untouched `evm_div_v5`/`evm_mod_v5`. **Status: executable + `#guard`
  functional tests landed** (`FastN1ProgramTest.lean`, both normalization
  paths + dispatch routing validated end-to-end; ~700→~420 step est).
  **DIV-perf Phase 3 measurement (DONE, branch `perf/div-algorithm-redesign`):**
  the extended `bench/DivBench.lean` now runs the verified `step` semantics over
  a **frequency-weighted sample of 800 real mainnet DIV + 400 MOD operands**
  (`scripts/sample-div-operands.py` → `bench/div-operands-sample.txt`) and
  reports the TRUE mean step count (no representative-bias), with a representative
  weighted point estimate kept only as a cross-check. **Measured result:
  `evm_div_v6` = 399.1 mean steps vs deployed 551.5 → −27.6% DIV; `evm_mod_v6` =
  406.5 vs 609.5 → −33.3% MOD** (MOD gains more — n=1 is 68% of MOD). Correct on
  all 1200 sampled ops + the 112 corner sweep. (`evm_div_v5` is a −1.08%
  regression vs v4 — fallback core only.) So **`evm_div_v6`/`evm_mod_v6` are the
  ranked winners and the recommended next verification target.** Full table + the
  cheap-dispatch (~−50% off v6, to be measured) and n=2 (most-defensible
  un-captured win, 18.2%) roadmap in `docs/divmod-evm-redesign.md`.
  **Stack-level proof TODO** — composition reuse must first pin the consistent
  (spec, executable, code-bundle) triple: the proven `evm_div_stack_spec` is
  over `divCode` (v1 `divK_div128` block), while executables use v4/v5 div128
  and `divCode_v5` is currently unused by any spec (v1→v4→v5 migration
  artifact). Then: dispatch `cpsBranchWithin`, fast-path body
  `cpsTripleWithin` (micro-decomposed under the WHNF atom ceiling), reuse the
  n1 exactness math (`fullDivN1R*`), and merge arms on `divStackDispatchPost`.
- **File-size guardrail** (`scripts/check-file-size.sh`, issue #314): CI step
  enforcing per-file line caps (1200 for `Compose/**`, 1500 elsewhere; `Program.lean`
  exempt). Files may opt out with a `-- file-size-exception: <reason>` comment in
  the first 20 lines. 6 oversize files grandfathered with exception comments
  pointing to their tracking issues (#312, #283, #266). Documented in `AGENTS.md`
  ("File-size guardrail") and `CONTRIBUTING.md`.
- **LP64 Calling Convention** (`Evm64/CallingConvention.lean`): LP64-aligned
  calling convention for the x0–x12 register subset, per zkvm-standards.
  - x1 (ra) = return address, x2 (sp) = call stack (grows down, callee-saved)
  - x10-x11 (a0-a1) = args/return values, x12 (a2) = EVM stack pointer
  - Program snippets: `cc_ret`, `cc_prologue` (16-byte frame), `cc_epilogue`
  - Proved specs: `callNear_spec`, `callFar_spec`, `ret_spec`, `ret_spec'`,
    `cc_prologue_spec`, `cc_epilogue_spec`,
    `callNear_function_spec` (call+return round-trip),
    `nonleaf_function_spec` (prologue+body+epilogue composition)
  - All new subroutines (handlers, RLP, interpreter) should use this convention.
    The older DivMod ad-hoc convention (x2 as return address) is legacy.
- **SAIL golden-model equivalence** (`EvmAsm/Rv64/SailEquiv/`): proves our
  simplified `Rv64` model faithfully implements RISC-V by relating each
  instruction to the official Sail RISC-V spec (`LeanRV64D`). Anchored on
  `StateRel` (`StateRel.lean`) — register + memory agreement. Per-class
  `*_sail_equiv` theorems (ALU/Imm/Shift/MExt/Branch/Mem) relate Sail `execute_*`
  to `execInstrBr`. Axiom footprint: the 3 classical axioms + the Sail model's
  `sys_enable_experimental_extensions` (from `LeanRV64D`, present in every
  SailEquiv proof — this track is outside the `check-axioms.sh` STF witness set).
  - **PC / control-flow equivalence (DONE this slice).** `StateRel` deliberately
    omitted PC ("proved separately at step level"); that step theorem was never
    written, so the branch/jump proofs were *vacuous on PC* (only reg/mem). Now:
    `StateRelPC` (`StateRel.lean`) = `StateRel` + committed-`PC` agreement (the
    step-stable, fetch-boundary relation, kept separate because `execute_*` writes
    only `nextPC`; `tick_pc` commits `PC := nextPC`). `runSail_tick_pc`
    (`MonadLemmas.lean`) reduces the commit. The 8 branch/jump `*_sail_equiv`
    theorems (`BranchProofs.lean`) were strengthened to expose
    `nextPC = (execInstrBr sRv i).pc` (the real **target** check, via the existing
    `runSail_jump_to` for taken arms and the post-fetch invariant
    `nextPC = pc+4` for fall-through). `StepProofs.lean` adds the generic
    `step_of_execute` glue + 8 `*_step_sail_equiv` capstones proving
    `execute_* ; tick_pc` lands `StateRelPC (execInstrBr sRv i)` — so
    BEQ/BNE/BLT/BGE/BLTU/BGEU/JAL/JALR now have their **target PC verified against
    the golden model**. Axiom-clean (track footprint), 0 sorry, no `bv_decide`.
  - **Non-control PC threading (DONE).** All 32 non-control `*_sail_equiv`
    theorems (ALU/Imm/Shift/MExt — RTYPE/ITYPE/UTYPE/SHIFTIOP/ADDIW/MUL/DIV/REM)
    now take `h_nextpc : nextPC = pc+4` and additionally conclude
    `nextPC = pc+4` (these instructions leave `nextPC` untouched; discharged
    uniformly by the `@[simp] sailStateWithReg_get?_nextPC` helper + `h_nextpc`).
    So every non-memory instruction's equivalence theorem now pins the PC
    behaviour — the prerequisite the uniform step theorem consumes.
  - **MisalignedAccess trap distinction (DONE).** So memory soundness can be
    stated cleanly ("unless a misaligned access happens"), `Execution.lean` gains a
    trap-aware companion to `step` — *without* touching `step`/`stepN` (which
    underpin `cpsTriple` and ~all proofs). `TrapKind` (`misalignedAccess | other`,
    extensible) + `StepResult` (`ok | trap`); `isMisalignedAccess` flags an
    in-range-but-misaligned memory access (splitting the conflated
    `isValidMemAddr && isAligned*` guard); `stepResult s := if isMisalignedAccess s
    then .trap .misalignedAccess else stepResultOfOption (step s)`. Bridge
    `step_eq_stepResult_toOption : step s = (stepResult s).toOption` (+
    `stepResult_ok_iff`, `isMisalignedAccess_imp_step_none`) connects it to the
    `step`/`stepN` corpus. Axiom-clean (`propext`/`Quot.sound`), 0 sorry, full
    `EvmAsm.Rv64` builds untouched.
  - **Remaining.** (1) A uniform `step_sail_equiv` dispatching via `InstrMap.lean`
    over a decoded instruction (composes the per-class results via
    `step_of_execute`; blocked on the memory class below, since it must cover
    LD/SD). (2) **Memory: the
    `MemProofs.lean` stubs.** Every load/store is a `*_sail_equiv_stub` that
    *assumes* an `h_exec` hypothesis (Sail `execute_LOAD/STORE` already succeeds +
    lands in `StateRel`); discharge it by reducing Sail `vmem_read`/`vmem_write` in
    bare mode (Machine priv, `satp=0`, aligned). Per maintainer: prove the
    **forward** direction (evm-asm ⇒ riscv-sail) — always valid since evm-asm
    issues no misaligned accesses; full both-directions holds only under the
    alignment precondition `Rv64.step` already enforces
    (`isValidDwordAccess`/`isValidMemAccess`).

---

## Pending: Recreate Deleted Spec Files

Five Evm64 spec files were deleted because their CodeReq migration was
incomplete (manual `cpsTriple_seq_perm_same_cr` calls lacked the `hd :
cr1.Disjoint cr2` argument added during the migration, and CR tree shapes
didn't match goals). The program definitions and tests remain in the
corresponding non-Spec files.

### Files to recreate (by priority)

#### ~~1. StackOps.lean — POP, PUSH0, DUP1-16, SWAP1-16~~ ✅ DONE

- **Files**: `Evm64/Pop.lean`, `Evm64/Push0.lean`, `Evm64/Dup.lean`, `Evm64/Swap.lean`
  (modular split; shared infra in `Stack.lean`)
- **Programs**: `evm_pop` (1 instr), `evm_push0` (5), `evm_dup(n)` (9), `evm_swap(n)` (16)
- **Specs**: All fully proved (0 sorry). Three-level hierarchy per opcode:
  low-level (explicit limbs) → EvmWord → stack (evmStackIs).
- **Pattern**: POP/PUSH0 use `CodeReq.ofProg` + `runBlock`. DUP/SWAP use
  explicit `CodeReq` union chains (symbolic `n` prevents `ofProg` whnf) with
  `runBlock` manual mode handling monotonicity via `buildMonoProof`'s
  union-split support. Per-limb helpers (`dup_pair_spec`, `swap_limb_spec`)
  use `runBlock` auto mode.
- **Shared infra** added to `Stack.lean`: `signExtend12_ofNat_small`,
  `evmStackIs_split_at`, `EvmWord.getLimb_zero`, `signExtend12_neg32`.

#### ~~2. ShiftSpec.lean — SHR per-limb, phase, body specs~~ ✅ DONE

- **Files**: `Evm64/Shift/LimbSpec.lean` (SHR per-limb + phase + body specs),
  `Evm64/Shift/Compose.lean` (`shrCode` + subsumption + composition),
  `Evm64/Shift/Semantic.lean` (stack-level `evm_shr_stack_spec`).
- **Status**: Fully proved (0 sorry). Per-limb helpers (`shr_merge_limb_spec`,
  `shr_last_limb_spec`, `shr_ld_or_acc_spec`, `shr_last_limb_inplace_spec`),
  phase specs (`shr_cascade_step_spec`, `shr_phase_c_spec`,
  `shr_phase_a_code_spec`), body specs (`shr_body_{0,1,2,3}_spec`), and
  zero path (`shr_zero_path_spec`) all recreated under the new
  `CodeReq` + `runBlock` conventions. Mirrors items #3 (ShlSpec) and
  #4 (SarSpec) below.

#### ~~3. ShlSpec.lean — SHL per-limb + body specs~~ ✅ DONE

- **Files**: `Evm64/Shift/ShlSpec.lean` (per-limb + body),
  `Evm64/Shift/ShlCompose.lean` (composition + bridge lemmas),
  `Evm64/Shift/ShlSemantic.lean` (stack-level `evm_shl_stack_spec`)
- **Bridge lemmas** in `Evm64/Basic.lean`: `getLimb_shiftLeft`,
  `getLimb_shiftLeft_eq_div`, `getLimb_shiftLeft_low` — connect per-limb body
  outputs to `getLimb (value <<< n)`, using `extractLsb'_split_64`
- **Composition**: mirrors SHR `Compose.lean` with `shlCode`, subsumption lemmas,
  zero-path specs (`evm_shl_zero_high_spec`, `evm_shl_zero_large_spec`),
  and body-path composition (`evm_shl_body_evmWord_spec`)
- **Stack-level spec**: `evm_shl_stack_spec` — zero axioms, zero sorry

#### ~~4. SarSpec.lean — SAR per-limb + body + sign-fill + composition + stack-level specs~~ ✅ DONE

- **Files**: `Evm64/Shift/SarSpec.lean` (per-limb + body + sign-fill),
  `Evm64/Shift/SarCompose.lean` (composition + bridge lemmas),
  `Evm64/Shift/SarSemantic.lean` (stack-level `evm_sar_stack_spec`)
- **Bridge lemmas** in `Evm64/Basic.lean`: `getLimb_sshiftRight_eq_ushiftRight`,
  `getLimb_sshiftRight_last`, `getLimb_sshiftRight_sign'`,
  `getLimb_sshiftRight_geq_256`, `getLimb_fromLimbs_const` — connect per-limb
  body outputs to `getLimb (sshiftRight value n)`
- **Composition**: mirrors SHR `Compose.lean` with `sarCode`, subsumption lemmas,
  sign-fill specs (`evm_sar_sign_fill_high_spec`, `evm_sar_sign_fill_large_spec`),
  SAR Phase C dispatch (`sar_phase_c_spec_pure`), and body-path composition
  (`evm_sar_body_evmWord_spec`)
- **Stack-level spec**: `evm_sar_stack_spec` — zero axioms, zero sorry
- **Key difference from SHR/SHL**: Sign-fill path (all limbs = `sshiftRight(v[3], 63)`)
  replaces zero-path; SRA instruction for MSB limb; sign extension for vacated limbs

#### ~~5. ByteSpec.lean — BYTE per-body + store + phase B specs~~ ✅ DONE

- **Files**: `Evm64/Byte/Spec.lean` (stack-level `evm_byte_stack_spec`, 3-way case split),
  `Evm64/Byte/LimbSpec.lean` (per-body + cascade dispatch specs),
  `Evm64/Byte/Program.lean` (45-instruction program + tests)
- **Specs**: `evm_byte_zero_high_spec`, `evm_byte_zero_geq32_spec`,
  `evm_byte_body_evmWord_spec`, `evm_byte_stack_spec` — all proved, 0 sorry
- **Pattern**: Uses `CodeReq.ofProg_mono_sub` for subsumption, cascade dispatch
  with frame and consequence rules, evmWordIs abstraction for stack-level spec

### General recreation guidelines

- Use `runBlock` auto mode wherever possible (handles CR extension, address
  normalization, and composition automatically).
- For manual compositions with different CRs, use `cpsTriple_seq_perm`
  with `(by crDisjoint)` for the `hd` argument, or extend to a common CR
  first and use `_same_cr` variants (`cpsTriple_seq_perm_same_cr`).
- All `_code` abbrevs should be `CodeReq` — prefer `CodeReq.ofProg base prog`
  over chains of `singleton.union`. See MultiplySpec.lean for the current pattern.
- Theorem statements use 5-arg `cpsTriple base exit cr P Q` with no
  `instrAt` atoms in P or Q.
- Reference the existing working specs (And.lean, Add.lean, MultiplySpec.lean,
  DivModSpec.lean) for the correct patterns.

---

## Roadmap: Phases 1-6 (Opcode Implementation)

All phases below target **Evm64** primarily. Files are under `EvmAsm/Evm64/`.

### ~~Phase 1: Complete Comparisons~~ — DONE

#### ~~1.1 SLT (Signed Less Than)~~ ✅
- **Files**: `Evm64/Comparison.lean` (helpers: `beq_eq_spec`, `beq_ne_spec`, `slt_msb_load_spec`) + `Evm64/Slt.lean`
- **Approach**: Compare MSB limbs (limb 3) with signed SLT instruction.
  If equal, fall through to unsigned borrow chain on lower 3 limbs.
  Uses `by_cases` on MSB equality for deterministic paths + `runBlock`.
- 25 instructions = 100 bytes. Also added `slt_spec_gen` to `SyscallSpecs.lean`.

#### ~~1.2 SGT (Signed Greater Than)~~ ✅
- **Files**: `Evm64/Comparison.lean` + `Evm64/Sgt.lean`
- **Approach**: SGT(a,b) = SLT(b,a). Swap operand load order (b-limbs into x7, a-limbs into x6).
- 25 instructions = 100 bytes. Mirrors SLT proof structure exactly.

### ~~Phase 2: Remaining Shifts & Bitwise~~ — DONE

> **Note**: Phases 2.1–2.3 were originally proved, then deleted in commit
> `1197924` due to incomplete CodeReq migration, then fully recreated.
> All specs are now proved with 0 sorry.

#### ~~2.1 SHL (Shift Left)~~ ✅
- **Files**: `Evm64/Shift/ShlSpec.lean` (per-limb + body), `Evm64/Shift/ShlCompose.lean`
  (composition + bridge lemmas), `Evm64/Shift/ShlSemantic.lean` (stack-level `evm_shl_stack_spec`)
- 90 instructions = 360 bytes. All specs proved, 0 sorry.

#### ~~2.2 SAR (Shift Right Arithmetic)~~ ✅
- **Files**: `Evm64/Shift/SarSpec.lean` (per-limb + body + sign-fill),
  `Evm64/Shift/SarCompose.lean` (composition + bridge lemmas),
  `Evm64/Shift/SarSemantic.lean` (stack-level `evm_sar_stack_spec`)
- 95 instructions = 380 bytes. All specs proved, 0 sorry.

#### ~~2.3 BYTE (Extract byte from word)~~ ✅
- **Files**: `Evm64/Byte/Spec.lean` (stack-level `evm_byte_stack_spec`),
  `Evm64/Byte/LimbSpec.lean` (per-body + cascade dispatch), `Evm64/Byte/Program.lean`
- 45 instructions = 180 bytes. All specs proved, 0 sorry.

### Phase 3: Stack Extensions

#### ~~3.1 DUP1-16 and SWAP1-16 (Generic)~~ ✅
- **Files**: `Evm64/Pop.lean`, `Evm64/Push0.lean`, `Evm64/Dup.lean`, `Evm64/Swap.lean`
- **Approach**: `evm_dup (n : Nat)` and `evm_swap (n : Nat)` as generic
  Lean functions producing `Program`. 9 instructions for DUP, 16 for SWAP.
  Full spec hierarchy: low-level (explicit limbs) → evmWordIs → evmStackIs.
  Added `signExtend12_ofNat_small` and `evmStackIs_split_at` to `Stack.lean`.
- Covers 34 opcodes (POP, PUSH0, DUP1-16, SWAP1-16) with one proof each. Fully proved.

#### ~~3.2 PUSH1-32~~ ✅
- **Files**: `Evm64/Push/Program.lean` (`evm_push n`, `5 + 2n` instrs),
  `Evm64/Push/Spec.lean` (PUSH0/PUSH1 + zero-slot prefix + `pushImmediateWord`),
  `Evm64/Push/ImmediateCompose.lean` (the full `n`-byte composition)
- **Approach**: Read `n` immediate bytes from the EVM code region
  (`code[codePtr+1 .. codePtr+n]`), big-endian, into the freshly-allocated
  32-byte stack slot. The full spec models BOTH the code source and the stack
  slot as byte-addressable `bytesRegion`s (`Rv64/MemRegion.lean`), sidestepping
  the symbolic-limb case split (immediate byte `i` lands in limb `(n-1-i)/8`,
  not concrete for symbolic `n`). Inductive `n`-byte copy chain composed via
  `cpsTripleWithin_seq` + `ofProg_append`, then folded back to
  `evmStackIs nsp (pushImmediateWord n byteAt :: rest)`.
- **Status**: `evm_push_stack_spec_within` (`1 ≤ n ≤ 32`) — complete
  unconditional stack spec, 0 sorry, trust base = 3 classical axioms. Registry
  `PUSH2..32` lifted `.partly → .proven` (31 byte-codes). PUSH0/PUSH1 already proven.

### Phase 4: Remaining Arithmetic

#### ~~4.1 MUL (256-bit Multiply)~~ ✅
- **Files**: `Evm64/Multiply.lean` (program + 16 tests)
- **Approach**: Schoolbook 4×4 limb column-wise multiplication using RV64 MUL/MULHU.
  Column j processes b[j] × a[0..3-j]. After column j, result[j] is finalized.
  Carry detection via SLTU after ADD. Intermediate r[3] accumulator spilled to memory
  (reusing freed a-limb slots). Added `sltu_spec_gen_rd_eq_rs2` to SyscallSpecs.lean.
  Fixed operator precedence bug in rv64_mulhu/rv64_mulh/rv64_mulhsu (`>>>` binds tighter than `*`).
- 63 instructions = 252 bytes. All specs proved, 0 sorry.
  Manual-mode `runBlock` with column decomposition (col0: 21, col1: 23, col2: 13, col3: 5, epilogue: 1).
  Added `mul_spec_gen_rd_eq_rs1`, `mulhu_spec_gen_rd_eq_rs1`, `sltu_spec_gen_rd_eq_rs2` to SyscallSpecs.

#### 4.2 DIV and MOD — in progress (program + specs + composition in progress)
- **Files**: `Evm64/DivMod.lean` (program + tests), `Evm64/DivModSpec.lean` (CPS specs),
  `Evm64/DivModCompose.lean` (hierarchical composition)
- **Approach**: Knuth Algorithm D in base 2^64. 316 instructions total (21 phases
  + 49-instr div128 subroutine + NOP separator). DIV and MOD share 95% of code,
  differ only in epilogue (load quotient vs remainder).
- **Status**: 69 CPS specs proved in LimbSpec.lean (0 sorry). All building
  blocks for every phase. div128 subroutine fully specified in composable blocks
  including phase1, step1 (init+clamp_q1+prodcheck1), compute_un21, step2
  (init+clamp_q0+prodcheck2), end. Branch merge specs for BEQ/BLTU patterns.
  Composed per-limb specs: mulsub_limb (11 instrs), addback_limb (8 instrs),
  trial_load (12 instrs), store_qj (4 instrs).
  Hierarchical composition using progAt to avoid WHNF scaling limit:
  - `divCode`/`modCode` split `progAt base evm_div/evm_mod` into 14 per-phase progAt blocks
  - `divCode_mid` (12 blocks excl phaseA+zeroPath), `divCode_noAB` (12 blocks excl phaseA+phaseB)
  - `progAt_divK_phaseB_at32`: pre-normalized phaseB expansion (21 instrAt atoms at base+K offsets)

  **Completed compositions (0 sorry):**
  - `evm_div_bzero_spec` (b=0 path): phaseA → BEQ taken → zeroPath ✅
  - `evm_div_phaseA_ntaken_spec` (b≠0): phaseA body → BEQ ntaken → base+32 ✅
  - `evm_div_phaseB_n4_spec` (b[3]≠0): init1→init2→ADDI→BNE(taken)→tail, 16 instrs ✅
  - `evm_div_phaseAB_n4_spec` (b≠0, b[3]≠0): phaseA+phaseB composed, 24 instrs, base→base+116 ✅
  - `evm_mod_bzero_spec` (b=0 path): same as div but with modCode ✅
  - `evm_mod_phaseA_ntaken_spec` (b≠0): same as div but with modCode ✅

  - Phase B cascade variants ✅: n=3, n=2, n=1 all composed (0 sorry)
    - `evm_div_phaseB_n3_spec` (b[3]=0, b[2]≠0): 18 instrs, x5=b[2], n=3
    - `evm_div_phaseB_n2_spec` (b[3]=b[2]=0, b[1]≠0): 20 instrs, x5=b[1], n=2
    - `evm_div_phaseB_n1_spec` (b[3]=b[2]=b[1]=0): 21 instrs (full phaseB), x5=b[0], n=1
    - 5 singleton subsumption lemmas for cascade step instructions (indices 11-15 of phaseB)
  - CLZ (Count Leading Zeros) ✅: 24 instructions, 6-stage binary search
    - `divK_clz_spec` at base+116→base+212, `clzResult` function for postcondition
    - Combined stage specs avoid exponential branching via conditional postconditions

  - Phase C2 ✅: shift check cpsBranch (4 instrs, base+212)
    - `divK_phaseC2_ntaken_spec` (shift≠0 → normB), `divK_phaseC2_taken_spec` (shift=0 → copyAU)
  - NormB ✅: normalize divisor (21 instrs, base+228), `divK_normB_full_spec`
  - NormA ✅: normalize dividend (21 instrs + JAL, base+312→base+432), `divK_normA_full_spec`
  - CopyAU ✅: copy a[]→u[] (9 instrs, base+396), `divK_copyAU_full_spec`

  - LoopSetup ✅: cpsBranch (4 instrs, base+432)
    - `divK_loopSetup_ntaken_spec` (m≥0 → loop body), `divK_loopSetup_taken_spec` (m<0 → denorm)
  - DIV Epilogue ✅: load q[0..3] + store to output (10 instrs, base+1004), `divK_div_epilogue_spec`

  **Full path compositions:**
  - LoopBody (main Knuth D loop): 114 instructions at base+448
    - 20 sorry-free theorems in `LoopBody.lean` + N-specific variants in `LoopBodyN{1,2,3,4}.lean`
    - `intro_lets` tactic added for selective let-binding expansion (xperm scaling fix)
    - Per-case concrete specs were in `LoopBodyN{X}Concrete.lean` (removed, see semantic path below)
  - Per-n full specs: removed (existentially quantified computation results → not useful)
  - Stack-level b≠0 specs: TODO (needs semantic correctness bridge first)

  **Remaining work (semantic correctness):**
  - Multi-limb arithmetic foundations: `MultiLimb.lean` — half-word decomposition, rv64_divu/mulhu
    Nat-level correctness, val128/val256 representation, partial product decomposition (done)
  - Div128 mathematical foundations: `Div128Lemmas.lean` — half-word OR-combine, 128-bit Euclidean
    uniqueness, trial quotient bounds (q_true ≤ q̂ ≤ q_true + 2 when normalized) (done)
  - Multiply-subtract chain: `MulSubChain.lean` — carry/borrow propagation, 4-limb telescoping
    chain (`mulsub_chain_nat`), correction step (`mulsub_correction_eq`) (done)
  - Normalization: `Normalization.lean` — `norm_div_eq` (shifting preserves quotient),
    `norm_euclidean_bridge` (recover original q,r from normalized), `div_mod_no_overflow` (done)
  - Division bridge: `DivBridge.lean` — `bv_eq_of_nat_eq` (Nat eq → BitVec eq, auto no-overflow),
    `div_of_nat_euclidean` / `mod_of_nat_euclidean` (Nat Euclidean → EvmWord.div/mod), `div_from_mulsub` (done)
  - N=4 case lemmas: `DivN4Lemmas.lean` — quotient bound (≤1 when MSB set), q=0/q=1 subcases,
    MSB → hi32 normalization condition, val256 positivity (done)
  - CLZ correctness: `CLZLemmas.lean` — `clz_zero_imp_msb` (shift=0 → val ≥ 2^63),
    `msb_imp_clz_zero` (converse), `clzResult_fst_eq_zero_iff` (biconditional),
    algebraic proof via `clzStep` abstraction with stage bound chain (done)
  - Limb bridge: `DivLimbBridge.lean` — OR-reduce nonzero → val256 > 0 / fromLimbs ≠ 0,
    per-limb val256 lower bounds (n=1: ≥1, n=2: ≥2^64, n=3: ≥2^128, n=4: ≥2^192) (done)
  - Per-limb mulsub: `DivMulSubLimb.lean` — `mulhu_toNat_le` (MULHU ≤ 2^64-2),
    `mulsub_limb_nat_eq` (per-limb carry equation from register ops),
    `mulsub_carry_word_eq` (Word carry = Nat carry when < 2^64),
    `mulsub_4limb_euclidean_div` (4-limb chain → EvmWord.div/mod for single-digit quotient) (done)
  - Per-limb addback: `DivAddbackLimb.lean` — `addback_limb_nat_eq` (per-limb carry equation),
    `addback_4limb_val256` (4-limb addition chain), `addback_correction_euclidean`
    (mulsub underflow + addback → corrected Euclidean with q-1) (done)
  - Remainder bound: `DivRemainderBound.lean` — `remainder_lt_of_ge_floor` (key: Euclidean eq +
    overestimate → exact quotient + remainder < divisor), `mulsub_no_underflow_correct` (happy path),
    `mulsub_addback_correct` (addback path), `val256_euclidean_to_div_mod` (val256 → EvmWord bridge),
    `norm_euclidean_correct` (normalization round-trip) (done)
  - Quotient accumulation: `DivAccumulate.lean` — multi-iteration telescoping (`iter_accumulate_{2,3,4}`),
    val256 trailing-zero simplifications, per-n end-to-end `div_correct_n{1,2,3,4}_no_shift`,
    `div_quotient_of_normalized` / `mod_remainder_of_normalized` (shift bridge),
    `div_of_val256_eq_div` / `mod_of_val256_eq_mod` (val256 → EvmWord),
    `div_correct_normalized` / `mod_correct_normalized` (combined normalization bridge) (done)
  - Mulsub carry strict bound: `DivMulSubCarry.lean` — `mulsub_limb_carry_strict_lt` (per-limb carry
    always < 2^64, proven via case analysis on MULHU maximum), `mulsub_limb_word_carry_eq` (Word carry
    = Nat carry, unconditional), `mulsub_limb_nat_word_eq` (per-limb equation with Word carry_out),
    `mulsub_register_4limb_val256` (4-limb register ops → val256 Euclidean equation) (done)
  - Addback carry bridge: `DivAddbackCarry.lean` — `or_toNat_eq_add_of_le_one` (OR = ADD for {0,1}
    Words), `addback_carries_exclusive` (two overflow flags can't both fire), `addback_limb_nat_word_eq`
    (per-limb addback with OR carry), `addback_register_4limb_val256` (4-limb addback → val256) (done)
  - Stack spec bridge: `DivLimbBridge.lean` — `ne_zero_iff_getLimbN_or` (EvmWord nonzero ↔ limbs OR
    nonzero), `getLimbN_fromLimbs_match` / `getLimbN_fromLimbs_{0,1,2,3}` (fromLimbs round-trip for
    reconstructing evmWordIs from individual memory cells) (done)
  - **Semantic correctness path:**
    - Step 1: Make `loopBodyPostN{1,2,3,4}` parametric — move output values to definition
      parameters so per-case concrete specs can fill them in concretely.
      Status: ✅ Done (PRs #197 + #202)
    - Step 2: Per-n loop iteration cpsTriple specs using `divK_store_loop_j0_spec` (j=0)
      and `divK_store_loop_jgt0_spec` (j>0). Four raw specs per (n, j) pair
      (max_skip, max_addback, call_skip, call_addback), then unified skip/addback
      into `divK_loop_body_nX_{max,call}_unified_jY_spec`.
      Status:
        - ✅ n=4: j=0 all 4 paths done (`LoopIterN4.lean`)
        - ✅ n=3: j=0 all 4 paths + j=1 all 4 paths + unified specs (`LoopIterN3.lean`, `LoopComposeN3.lean`)
        - ✅ n=2: j=0,j=1,j=2 all 4 paths + unified specs (`LoopIterN2.lean`, `LoopComposeN2.lean`)
        - ✅ n=1: j=0,j=1,j=2,j=3 all 4 paths + unified specs (`LoopIterN1.lean`, `LoopComposeN1.lean`)
    - Step 2b: **Bool-parameterized loop composition** (Issue #262, PRs #267–#272).
      Unifies max/call branch paths via `(bltu : Bool)` parameter so that
      2^k path combinations collapse to 1 theorem.
      Status:
        - ✅ Unified defs: `iterN3`, `iterN2`, `loopIterPostN3`, `loopN3UnifiedPost`, `loopN2UnifiedPost` (`LoopDefs.lean`)
        - ✅ n=3 unified 2-iteration composition: `divK_loop_n3_unified_spec (bltu_1 bltu_0 : Bool)` (`LoopUnifiedN3.lean`)
        - ✅ n=3 unified preloop+loop: `evm_div_n3_preloop_loop_unified_spec` (`Compose/FullPathN3LoopUnified.lean`)
        - ✅ n=2 unified 3-iteration composition: `divK_loop_n2_unified_spec (bltu_2 bltu_1 bltu_0 : Bool)` (`LoopUnifiedN2.lean`)
          Layered: iter10 (4 cases) → max/call+iter10 (2 lemmas) → unified dispatch
        - ✅ n=1 unified 4-iteration composition: `divK_loop_n1_unified_spec (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)` (`LoopUnifiedN1.lean`)
          5-layer composition: iter10 → max/call_iter10 → iter210 → max/call_iter210 → unified
        - `iterN2Max`/`iterN2Call` marked `@[irreducible]` to prevent stuck if-reduction in projections
        - Unified condition predicates: `isTrialN3_j1/j0`, `isTrialN1_j3/j2/j1/j0`
      Issue #262 is **complete** — Bool unification achieved for all n-values (n=1,2,3; n=4 trivial).
    - Step 3: Per-n full-path composition theorems (base→base+1064) with bundled postconditions.
      Composes pre-loop (normalization) + loop body + post-loop (denorm/epilogue).
      Status:
        - ✅ n=4 shift≠0: `evm_div_n4_full_{max,call}_{skip,addback}_spec` (`FullPathN4.lean`)
        - ✅ n=4 shift=0: `evm_div_n4_full_shift0_call_{skip,addback}_spec` (`FullPathN4Shift0.lean`)
        - ✅ n=3 shift≠0: 4 full-path theorems (`FullPathN3Loop.lean`) — can be replaced by unified version
        - ✅ n=3 shift=0: 2 full-path theorems (`FullPathN3Shift0.lean`)
        - ✅ n=2 shift≠0: unified full-path `evm_div_n2_full_unified_spec` (`FullPathN2Full.lean`, `FullPathN2Cases.lean`)
          8 per-case lemmas + unified dispatch via `delta + rfl` postcondition bridge
        - ✅ n=2 shift=0: unified full-path `evm_div_n2_full_shift0_unified_spec` (`FullPathN2Shift0.lean`)
          j=2 always call (u4=0 < b1), unified over (bltu_1 bltu_0 : Bool) for 4 combinations
        - ✅ n=1 shift≠0: unified full-path `evm_div_n1_full_unified_spec` (`FullPathN1Full.lean`)
          16-case denorm_comp with parametric denorm' helper, all 16 Bool combinations
        - ✅ n=1 shift=0: unified full-path `evm_div_n1_full_shift0_unified_spec` (`FullPathN1Shift0.lean`)
          j=3 always call (u_top=0 < b0), unified over (bltu_2 bltu_1 bltu_0 : Bool) for 8 combinations
      All n-values complete. Next:
        - MOD variants: factor shared DIV/MOD loop to avoid duplication (Issue #266)
    - Step 4: Semantic correctness bridge — connect algorithm computations to `EvmWord.div`.
      Infrastructure exists: `div_correct_n4_no_shift`, `remainder_lt_of_ge_floor`,
      `mulsub_no_underflow_correct`, `mulsub_addback_correct`, `mulsubN4_val256_eq`.
      Partial progress:
        - ✅ Max trial overestimate: `val256_div_lt_pow64` — when b3≠0, val256(a)/val256(b) ≤ 2^64-1
        - ✅ Skip path correctness: `n4_max_skip_correct` — c3=0 + max trial → EvmWord.div correct
        - **Missing math theorem (Knuth's Theorem B)**: for the addback and call paths, need:
          1. **Mulsub borrow bound**: prove that `mulsubN4` borrow c3 has `c3.toNat ≤ 1`
             when the trial quotient overestimates by ≤ 1 (i.e., q_hat ≤ ⌊u/v⌋ + 1).
             This ensures the 2^256 terms cancel in the mulsub+addback combined equation.
          2. **Call path trial quotient overestimate**: prove that `div128Quot u_top u3 v3`
             produces a quotient q̂ satisfying `⌊u/v⌋ ≤ q̂ ≤ ⌊u/v⌋ + 1` when the divisor's
             leading limb has its MSB set (normalized). This is the formal version of
             Knuth TAOCP Vol 2 §4.3.1 Theorem B.
          3. **Addback combined equation**: given c3=1 (borrow) and carry=1 (addback carry),
             derive `val256(a) = (q_hat-1) * val256(b) + val256(aun)` from `mulsubN4_val256_eq`
             + `addbackN4_val256_eq`.
      Status: In progress (`DivN4Overestimate.lean`). This is independent of Steps 2-3 and can
      proceed in parallel. Once done for n=4, the bridge generalizes to n=1,2,3 via the same
      `div_correct_normalized` framework.
    - Step 5: Stack-level spec using `evmWordIs`. Case-split on b=0/≠0, then on n,
      apply full-path spec + semantic bridge to prove `evmWordIs (sp+32) (EvmWord.div a b)`.
      Status: Not started (blocked on Steps 3+4 for all n values)

  **Path to EVM-level DIV/MOD specs (summary):**
  1. ✅ Complete n=2 loop composition with Bool unification (PRs #270–#272)
  2. ✅ Complete n=2 full-path composition (PRs #274–#277)
  3. ✅ Complete n=1 loop iteration specs + Bool-unified composition (PRs #282–#286)
  4. ✅ Complete n=1 + n=2 shift=0 and shift≠0 full-path compositions (PRs #280, #288, #289)
  5. Complete Knuth's Theorem B (Step 4) — can proceed in parallel
  5. Per-n semantic bridge: connect full-path postconditions to `EvmWord.div`/`EvmWord.mod`
  6. Stack-level spec: case-split b=0/≠0, then on n, compose full-path + semantic bridge
  7. Factor shared DIV/MOD loop (Issue #266) to derive MOD specs from DIV proofs

  **V5 track — `divK_div128_v5` migration (in progress, bead `evm-asm-wbc4i.6`):**
  The executable `evm_div`/`evm_mod` were switched to `divK_div128_v4` on
  2026-05-19 (PR #4992). The **v5** track replaces the inner div128 subroutine
  with `divK_div128_v5` — the *capped* Knuth Algorithm D variant that repairs
  v4's two buggy ULTs by clamping the trial quotients `q1c`/`q0c` at `2^32 − 1`
  — and rebuilds the spec layer against it for full-domain (n=4) correctness.
  Files under `Evm64/DivMod/`:
  - **Shared code surfaces** (`Compose/V5Code.lean`): `sharedDivModCode_v5`
    and `sharedDivModCodeNoNop_v5` mirror the v4 surfaces (`Compose/Base.lean`,
    `Compose/V4NoNop.lean`), swapping in `divK_div128_v5` at block 12. These are
    the `CodeReq`s for `div128_v5_spec_shared` / `div128_v5_spec_shared_noNop`.
    Kept in a dedicated file because `Base.lean` is at its size cap.
  - **Block specs** (`LimbSpec/Div128*V5.lean`): `Div128CapV5` (cap clamp),
    `Div128Phase1bV5` (prodcheck1;;prodcheck1b body), `Div128Phase2bV5`
    (phase2b body + the two D3 spill blocks), `Div128Step1V5` / `Div128Step1FullV5`
    (step1 prefix+guard+full block spec), `Div128Step2V5` / `Div128Step2FullV5`
    (step2 prefix init+cap_q0+guard+full block spec). Built up over the
    V5.6.5–V5.6.12 commit series.
  - **n=4 dispatcher predicates + runtime chain** (`Spec/CallAddbackV5.lean`,
    `Spec/CallAddbackRuntimeV5.lean`, `LoopBody/TrialCallV5.lean`,
    `LoopDefs/IterV5.lean`): mirror the v4 `CallAddback` dispatcher predicates
    and the `hq_over`-assuming n4 runtime chain to v5.
  - **Proof-scaling discipline**: V5 follows the fold-before-`xperm` guidance in
    `AGENTS.md` — `@[irreducible]` `…PostCore` / `…PostFromBody` helpers behind
    the postcondition spine, refold via `change` in branch bridges, named lemmas
    for fresh heartbeat budgets. See `GRIND.md` for the simp/grind conventions.

Before starting **any** of the remaining arithmetic opcodes below (SDIV,
SMOD, ADDMOD, MULMOD, EXP), read
[`EvmAsm/Evm64/OPCODE_TEMPLATE.md`](EvmAsm/Evm64/OPCODE_TEMPLATE.md) —
it codifies the day-one conventions distilled from the DivMod retrofit
experience (parallel `LimbSpec/` / `LoopDefs/` / `Compose/` layout,
unified Bool/Fin dispatch from day one, sibling-opcode factoring,
`@[irreducible]` bundling thresholds, named `Compose/Offsets.lean`,
per-opcode `AddrNorm` grindset, `structure <Opcode>Valid` validity
bundle). Tracked by issue #313.

#### 4.3 SDIV and SMOD (Signed)
- **Approach**: Check signs, compute unsigned div/mod, apply sign correction.
- **Per OPCODE_TEMPLATE.md**: SMOD is a sign-sibling of SDIV; layout the
  files with a shared body + per-sibling epilogue split from the first PR
  (do not copy DIV's retrofit-style parallel MOD clone).

#### 4.4 ADDMOD and MULMOD
- **Approach**: ADDMOD needs 257-bit intermediate (carry). MULMOD needs
  512-bit intermediate. Both reuse DIV/MOD.

#### 4.5 EXP (Exponentiation)
- **Approach**: Square-and-multiply using MUL. Loop over exponent bits.

#### ~~4.6 SIGNEXTEND~~ ✅
- **Files**: `Evm64/SignExtend/` — `Program.lean` (program + 16 tests), `LimbSpec.lean` (per-body + phase A/B/C specs),
  `Compose.lean` (subsumption + no-change + body path composition), `Spec.lean` (stack-level `evm_signextend_stack_spec`)
- **Approach**: If b >= 31, result = x. Else compute limb_idx = b/8, shift_amount = 56 - (b%8)*8.
  Cascade dispatch to body_N: SLL+SRA sign-extends target limb in-place, SRAI fills higher limbs.
  Shares Phase B computation with BYTE opcode. `EvmWord.signextend` definition + per-limb bridge lemmas in `EvmWordArith.lean`.
- 48 instructions = 192 bytes. All specs proved, 0 sorry. Axiom-clean.

### Phase 5: Memory & Code Region

#### 5.1 EVM Code Region Model
- **File**: `Evm64/CodeRegion.lean` (new)
- **Approach**: Define EVM bytecode as a byte array in RISC-V memory.
  Use LBU for byte access. Define `evmCodeIs(base, bytes)` assertion.
  Needed for PUSH1-32, and for the interpreter loop (Phase 7).

#### 5.2 EVM Memory Model
- **File**: `Evm64/Memory.lean` (new)
- **Approach**: EVM memory as a byte-addressable region in RISC-V memory.
  Use LB/SB/LBU for byte access. Define `evmMemIs` assertion.
  Zero-initialized, auto-expanding (model fixed max size initially).

#### 5.3 MLOAD, MSTORE, MSTORE8, MSIZE
- **File**: `Evm64/Memory.lean`
- **Approach**: MLOAD pops offset, loads 32 bytes, pushes word.
  MSTORE pops offset+value, stores 32 bytes. MSTORE8 stores 1 byte.
  MSIZE pushes current memory size (track in register or memory).

### Phase 6: Environment & Block Context

#### 6.1 Environment Context Layout
- **File**: `Evm64/Environment.lean` (new)
- **Approach**: Memory layout for EVM execution context:
  - msg.caller, msg.value, msg.data (calldata)
  - block.number, block.timestamp, block.basefee, etc.
  - tx.origin, tx.gasprice, chainid
  Store at known base address. Define `envIs` separation logic assertion.

#### 6.2 Simple Environment Opcodes
- ADDRESS, CALLER, CALLVALUE, ORIGIN, GASPRICE, COINBASE, TIMESTAMP,
  NUMBER, CHAINID, BASEFEE, SELFBALANCE, CODESIZE, RETURNDATASIZE
- Each is LD × 4 from environment region + push to stack.

#### 6.3 CALLDATALOAD, CALLDATASIZE, CALLDATACOPY
- Load from calldata region in environment.

---

## Execution Layer Prerequisites

The STF (Phase 11) reads RLP-encoded blocks via `read_input`. These
prerequisites provide the pure spec and RISC-V infrastructure for that.

### EL.1 RLP Specification ✅
- **Files**: `EvmAsm/EL/RLP/Basic.lean`, `Decode.lean`, `Properties.lean`
- `RLPItem` type (bytes | list), `encode`, `decode` with canonical enforcement
- 17 kernel-verified properties via `decide` (round-trip, spec conformance)
- 0 sorry, 0 axioms
- ✅ **General byte-string round-trip (parametric, not `decide`)** (`Properties.lean`).
  `decode_encode_bytes (data) (hlen : data.length < 256^8) :
  decode (encode (.bytes data)) = some (.bytes data, [])` — every leaf `RLPItem`
  re-decodes to itself, for all lengths the decoder's 8-byte length field
  supports. Short form (`≤ 55`) is unconditional. Supporting new foundations:
  `Nat.fromBytesBE_toBytesBE` (big-endian round-trip), `Nat.fromBytesBE_snoc`,
  `Nat.toBytesBE_succ`, `Nat.toBytesBE_length_le` (`len < 256^k → length ≤ k`),
  `Nat.toBytesBE_eq_cons_of_pos` (nonzero leading byte / no-leading-zero),
  `readLength_toBytesBE_append`, `encodeBytes_long_of_length`. All Lean-core
  (no Mathlib): `Nat.toBytesBE.induct`, `omega`, `List.take_left`/`drop_left`.
  Axiom-clean (propext/Classical.choice/Quot.sound), 0 sorry. This is the leaf
  half of the round-trip keystone.
- ✅ **Full round-trip keystone (`decode (encode item) = some (item, [])`)**
  (`Properties.lean`). `decode_encode (item) (h : (encode item).length < 256^8)`
  re-decodes *every* `RLPItem` (lists + nesting) to itself; `decodeFully_encode`
  discharges `FullDecode.decodeFully_encode_of_decode_encode`'s `h_roundtrip`
  hypothesis, making full decode of any (length-bounded) encoded item
  unconditional. Key idea: both `decodeAux`/`decodeItems` recurse on the fuel
  `nDepth`, so `decode_encode_mutual` is proved by a single **step induction on
  `nDepth`** (an `decodeAux`-on-`encode` statement ∧ a `decodeItems`-on-
  `encodeItems` statement) — the IH at `nDepth-1` covers all sub-items, so no
  induction on `RLPItem` is needed. Reuses the leaf round-trip via the new
  fuel-parametric `decodeAux_succ_encodeBytes_append`, plus `encode_list_short`/
  `_long`, `decodeItems_succ_of_ne_nil`, `takeBytes_append_length`,
  `le_encodeBytes_length`. A single top-level `< 256^8` bound implies every
  nested bound. Axiom-clean, 0 sorry. **The RLP encode→decode round-trip is now
  complete end-to-end.**
- ✅ **Decodability part 1 — injectivity + canonical bijection + quasi-encoding
  rejection** (`Properties.lean`). Informed by Coglio's ACL2 RLP work
  (arXiv:2009.13769), whose headline results are the encode/decode *mutual
  inverses*, injectivity, and rejection of non-canonical "quasi-encodings".
  Added: `encode_injective` (`encode i₁ = encode i₂ → i₁ = i₂`, a corollary of
  the round-trip); `Nat.toBytesBE_fromBytesBE_of_canonical` (the canonical
  inverse of the big-endian bijection — `toBytesBE (fromBytesBE bs) = bs` for a
  no-leading-zero `bs`, the foundation the right-inverse needs) +
  `Nat.fromBytesBE_pos_of_head_ne_zero`; and a documented **quasi-encoding
  rejection** section (the five ACL2 forms, each pointed at its rejecting lemma
  with `decide` cross-checks). **Now imports Mathlib** (`List.reverseRecOn`,
  `positivity`) rather than re-deriving list/arithmetic facts. Axiom-clean
  (classical), 0 sorry.
- ✅ **Decodability part 2 — the full right inverse** (`Properties.lean`).
  `decode_eq_some_imp_encode : decode bs = some (item, rest) → bs = encode item ++ rest`
  — whatever `decode` accepts re-encodes to exactly the bytes consumed, so the
  decoder accepts *only* canonical encodings (the ACL2
  `rlp-encode-tree-of-rlp-parse-tree` analogue, the property whose failure hid a
  real decoder bug in Coglio's work). Proved by `decode_right_inverse_mutual`
  (step induction on the fuel `nDepth`, same shape as `decode_encode_mutual`):
  byte classes are standalone `decodeAux_{singleByte,shortBytes,longBytes}_right_inv`
  lemmas; list classes recurse through the IH. Reconstruction helpers
  `takeBytes_eq_some_imp`, `readLength_eq_some_imp` (the latter exposing the
  canonical length field via `toBytesBE_fromBytesBE_of_canonical`). Capstone
  `decodeFully_eq_encode : decodeFully bs = some item ↔ bs = encode item`
  (within the 8-byte bound) — full decode is *exactly* the inverse of `encode`.
  Axiom-clean (classical), 0 sorry. **RLP decodability is now complete: both
  inverses + injectivity + quasi-encoding rejection, to parity with the ACL2
  formalization.**
- ✅ **Self-delimiting encoding / prefix-unambiguity** (`Properties.lean`).
  `decode_encode_append` (left inverse with arbitrary trailer), `encode_append_cancel`
  (`encode i₁ ++ r₁ = encode i₂ ++ r₂ → i₁ = i₂ ∧ r₁ = r₂`), and
  `encode_prefix_unambiguous` (`encode i₁ <+: encode i₂ → i₁ = i₂`, the ACL2
  `rlp-encode-tree-unamb-prefix` analogue — no valid encoding is a proper prefix
  of another). All fall out of the two inverses. Axiom-clean, 0 sorry.
- ✅ **RLP scalar layer** (`EvmAsm/EL/RLP/Scalar.lean`, ACL2 `rlp-encode-scalar`).
  `encodeScalar n := encodeBytes (Nat.toBytesBE n)` (nonneg int → minimal
  big-endian bytes → byte string; nonces/balances/gas/lengths) and `decodeScalar`.
  `decodeScalar_encodeScalar` (round-trip), `encodeScalar_injective`, and
  `decodeScalar_eq_some_imp` (right inverse) — all reuse `decode_encode_bytes` +
  the `Nat.fromBytesBE/toBytesBE` bijection. Axiom-clean, 0 sorry. **Pure-spec RLP
  is now at full ACL2 parity (tree + scalar, both inverse directions).**

### EL.2 Byte-Level Infrastructure ✅
- **File**: `EvmAsm/Rv64/ByteOps.lean`
- `extractByte`/`replaceByte` algebra (round-trip, independence, overwrite)
- `generic_lbu_spec`: CPS spec for LBU in terms of `extractByte` on containing dword
- `generic_sb_spec`: CPS spec for SB in terms of `replaceByte` on containing dword

### EL.3 RLP RISC-V Decoder (in progress)
- **Files**: `EvmAsm/Rv64/RLP/`
- Phase 1: Prefix classifier (cascade BLTUs, 5 exits) — ✅ all three variants landed
  - `rlp_phase1_step_spec` (per-step with pure ult fact),
    `rlp_phase1_step_spec_plain` (strips pure facts),
    `rlp_phase1_step_spec_acc` (frames with accumulator, merges into single `⌜Acc ∧ …⌝`).
  - `rlp_phase1_classifier_spec` — plain 5-exit `cpsNBranch` at boundaries
    0x80, 0xB8, 0xC0, 0xF8 (no dispatch facts).
  - `rlp_phase1_classifier_spec_pure` — per-step dispatch facts at each
    exit (`⌜ult v5 k_i⌝` for taken, `⌜¬ ult v5 k4⌝` for fall-through).
  - `rlp_phase1_classifier_spec_acc` — full accumulated-chain variant:
    each exit carries the complete conjunction of prior `¬ult` facts plus
    (for taken exits) the current `ult` fact. Enables downstream range
    proofs like `0x80 ≤ p < 0xB8` at exit `e2`.
- Phase 2: Length extraction — ⏳ short form + long-form accumulation step
  - `rlp_phase2_short_length_spec` (`EvmAsm/Rv64/RLP/Phase2Short.lean`):
    one-instruction `ADDI x11, x5, -k` extractor for short byte strings
    (k = 0x80) and short lists (k = 0xC0). Concrete tests verify
    0x85 → 5, 0xB7 → 55, 0xC3 → 3, 0x80 → 0 via `decide`.
  - `rlp_phase2_long_acc_spec` (`EvmAsm/Rv64/RLP/Phase2LongAcc.lean`):
    two-instruction `SLLI x11, x11, 8 ; ADD x11, x11, x12` big-endian
    accumulation core of the long-form length-of-length loop. Post:
    `x11 ← (len <<< 8) + byte`.
  - `rlp_phase2_long_load_acc_spec` (`EvmAsm/Rv64/RLP/Phase2LongLoad.lean`):
    three-instruction `LBU x12, x13, 0` prefix over the accumulation
    step. Reads one byte from `mem[x13]` and folds it into `x11`.
  - `rlp_phase2_long_iter_spec` (`EvmAsm/Rv64/RLP/Phase2LongIter.lean`):
    five-instruction full loop body (no back-branch) adding pointer
    advance (`ADDI x13, x13, 1`) and counter decrement
    (`ADDI x14, x14, -1`) on top of load-accumulate.
  - `rlp_phase2_long_loop_body_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean`): six-instruction loop
    body as a `cpsBranch` — iteration body + `BNE x14, x0, back`.
    Taken at `(base+20) + signExtend13 back` with `⌜cnt' ≠ 0⌝`; fall-
    through at `base + 24` with `⌜cnt' = 0⌝`.
  - `rlp_phase2_long_loop_one_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopOne.lean`): single-iteration
    closure (lenLen = 1). When `x14 = 1` at entry, the taken branch is
    unreachable (`cnt' = 0`), so the `cpsBranch` collapses to a plain
    `cpsTriple` exiting at `base + 24`.
  - `rlp_phase2_long_loop_two_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopTwo.lean`): two-iteration closure
    (lenLen = 2). Composes the body spec (iter 1, BNE taken) with the
    one-byte closure (iter 2, fall-through) via
    `cpsTriple_seq_perm_same_cr`. Assumes both bytes live in the
    same doubleword.
  - `rlp_phase2_long_loop_three_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopThree.lean`): three-iteration
    closure (lenLen = 3). Composes body spec (iter 1) with two-byte
    closure (iters 2–3). All three bytes assumed in same doubleword.
  - `rlp_phase2_long_loop_four_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopFour.lean`): four-iteration
    closure (lenLen = 4). Composes body spec (iter 1) with three-byte
    closure (iters 2–4). All four bytes assumed in same doubleword.
  - `rlp_phase2_long_loop_five_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopFive.lean`): five-iteration
    closure (lenLen = 5). Composes body spec (iter 1) with four-byte
    closure (iters 2–5). All five bytes assumed in same doubleword.
  - `rlp_phase2_long_loop_six_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopSix.lean`): six-iteration
    closure (lenLen = 6, prefixes `0xBD` / `0xFD`). Composes body
    spec (iter 1) with five-byte closure (iters 2–6). All six bytes
    assumed in same doubleword (`byteOffset ptr ≤ 2`).
  - `rlp_phase2_long_loop_seven_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopSeven.lean`): seven-iteration
    closure (lenLen = 7, prefixes `0xBE` / `0xFE`). Composes body
    spec (iter 1) with six-byte closure (iters 2–7). All seven bytes
    assumed in same doubleword (`byteOffset ptr ≤ 1`).
  - `rlp_phase2_long_loop_eight_byte_spec`
    (`EvmAsm/Rv64/RLP/Phase2LongLoopEight.lean`): eight-iteration
    closure (lenLen = 8, prefixes `0xBF` / `0xFF` — the maximum
    permitted by RLP). Composes body spec (iter 1) with seven-byte
    closure (iters 2–8). All eight bytes assumed in same doubleword
    (`byteOffset ptr = 0`, i.e., `ptr` is doubleword-aligned).
    Single-doubleword unrolling track now complete.
  - General `n`-iteration closure (induction over `cnt`) still pending
    (initial attempt hit Lean-level issues around
    `BitVec.ofNat 64 n` arithmetic and associativity normalization;
    unrolling is catching up in the meantime).
- Phase 3: Single-item flat decode (byte strings only) — ⏳ scaffolding
  - `rlp_phase3_single_byte_spec` (`EvmAsm/Rv64/RLP/Phase3SingleByte.lean`):
    one-instruction `ADDI x11, x0, 1` that materializes `length = 1` for
    Phase 1's `e1` exit (prefix byte `< 0x80`, single-byte string —
    the prefix IS the data). The data pointer in `x13` rides through
    as a frame atom; no pointer advance is needed.
  - `rlp_phase3_long_string_spec` (`EvmAsm/Rv64/RLP/Phase3LongString.lean`):
    three-instruction entry block for Phase 1's `e3` exit
    (`p ∈ [0xB8, 0xC0)`). Sets `x14 = p − 0xB7` (length-of-length;
    range [1, 8]), clears the length accumulator `x11 := 0`, and
    advances the data pointer `x13 += 1` to the first length byte —
    leaving the machine in the canonical pre-loop state expected by
    the `rlp_phase2_long_loop_*_byte_spec` family.
  - `rlp_phase1_e3_0xB8_one_byte_length_spec`
    (`EvmAsm/Rv64/RLP/Phase1E3LongStringOne.lean`): concrete full path
    for the smallest long-string prefix (`0xB8`). Composes Phase 1 e3
    classification, Phase 3 long-string entry, and the one-byte Phase 2
    length loop. Postcondition gives the zero-copy output pair:
    `x11 = payload_length_byte`, `x13 = payload_start`.
  - ✅ **Long-form single-doubleword full paths complete (lenLen 1–8).**
    Mirroring the `0xB8` one-byte path, every long-form prefix now has an
    end-to-end Phase 1 → Phase 3 → Phase 2 composition:
    - Long byte-strings (e3, prefixes `0xB8`–`0xBF`):
      `rlp_phase1_e3_0x{B8..BF}_{one..eight}_byte_length_spec_within`
      (`Phase1E3LongString{One..Eight}.lean`).
    - Long lists (e5, prefixes `0xF8`–`0xFF`):
      `rlp_phase1_e5_0x{F8..FF}_{one..eight}_byte_length_spec_within`
      (`Phase1E5LongList{One..Eight}.lean`).
    Each composes the proven `rlp_phase1_e{3,5}_full_path_spec'_within`
    entry with the matching `rlp_phase2_long_loop_{N}_byte_spec_within`
    closure via `cpsTripleWithin_seq`; the postcondition restates the
    big-endian length by reference to that closure's `…_post`. All
    16 theorems are axiom-clean (only `propext`/`Classical.choice`/
    `Quot.sound`), 0 sorry. Wired into the `EvmAsm.Rv64.RLP` umbrella.
  - ✅ **Long-form length bridged to the pure spec (`Nat.fromBytesBE`).**
    The full-path outputs above leave `x11` as a raw big-endian
    accumulation; `Phase2LongLengthBridge.lean` proves it equals the value
    the pure RLP spec decodes. Core: `rlp_be_len_{1..8}_eq_fromBytesBE`
    (and `rlp_be_byte_eq_fromBytesBE`) show
    `(((0 <<< 8) + e0) <<< 8 …) + e_{N-1} = BitVec.ofNat 64 (Nat.fromBytesBE
    [e0,…,e_{N-1}])` for `N ≤ 8` (no 64-bit overflow since the value is
    `< 256^8 = 2^64`), backed by the pure bound `Nat.fromBytesBE_lt`
    (`EL/RLP/Properties.lean`). `Phase1E{3,5}…FromBytesBE.lean` thread this
    through to 16 end-to-end `…_fromBytesBE_spec_within` restatements whose
    postcondition states `x11 = BitVec.ofNat 64 (Nat.fromBytesBE [extractByte
    …, …])` — i.e. the decoder computes the *spec-correct* length, not just a
    bitvector. All axiom-clean, 0 sorry.
  - ✅ **Per-exit `classifyPrefix`-level bridges complete (all five exits).**
    Every classification exit now has a wrapper restating its full path
    against the pure RLP classifier `classifyPrefix` (input side) and the
    matching pure length (output side): e1 `rlp_phase1_e1_single_byte_of_class_spec_within`
    (`classifyPrefix = .singleByte` → `x11 = 1`), e2
    `rlp_phase1_e2_full_path_payload_len_of_class_spec_within`
    (`x11 = ofNat (rlpPrefixShortBytesPayloadLen pfx)`), e4
    `rlp_phase1_e4_full_path_payload_len_of_class_spec_within`
    (`rlpPrefixShortListPayloadLen`), and e3/e5's `…_lenOfLen_of_class…`
    (the long-form `lenLen` counter). The e1/e2 wrappers (this slice) mirror
    e4 and reuse `rlpPrefixShortBytesPayloadLen_toWord_of_class`
    (`EL/RLP/ProgramSpec.lean`). Axiom-clean, 0 sorry.
  - ✅ **General n-iteration long-form loop closure** (`Phase2LongLoopGeneral.lean`).
    The decoder runs a single back-branching loop whose iteration count is the
    runtime counter; the eight unrolled closures only covered fixed counts 1–8.
    `rlp_phase2_long_loop_n_byte_spec_within (n) (1 ≤ n ≤ 8)` now proves the
    loop for an **arbitrary** count in one theorem (by induction on the count),
    with the decoded length bridged to the pure spec
    `BitVec.ofNat 64 (Nat.fromBytesBE (rlpLoopByteList …))`. This is the
    keystone for a unified single-item decoder (apply at the symbolic
    length-of-length). The prior blocker — parametric counter arithmetic
    (`BitVec.ofNat 64 (n+1) + signExtend12 (-1) = BitVec.ofNat 64 n`) — is
    resolved by `word_ofNat_succ_dec`/`_ne_zero`/`_add_one` (toNat + omega).
    Supporting: `rlpLoopAcc` (the loop's big-endian fold), `rlpLoopAcc_toNat`
    (mod-form invariant), and `rlpLoopAcc_zero_eq_fromBytesBE` (the fold ↔
    `fromBytesBE` bridge). Axiom-clean, 0 sorry.
  - ✅ **General long-form full paths** (`Phase1E3LongBytesFull.lean` /
    `Phase1E5LongListFull.lean`). For an **arbitrary** in-class prefix,
    `rlp_phase1_e3_longBytes_full_spec_within` /
    `rlp_phase1_e5_longList_full_spec_within` compose the Phase-1 classify +
    Phase-3 entry with the n-iteration closure at the symbolic
    `n = rlpPrefixLong{Bytes,List}LenOfLen pfx ∈ [1,8]`, yielding the decoded
    `x11 = ofNat (Nat.fromBytesBE (rlpLoopByteList …))` and payload pointer
    `x13`. Collapses the 16 concrete-prefix `…_fromBytesBE_spec_within` paths
    into 2 parametric theorems (e5 reuses the existing
    `…_lenOfLen_of_class…` prefix wrapper; e3 rewrites `x14 = pfx − 0xB7` to
    `ofNat n` via `rlpPrefixLongBytesLenOfLen_toWord_of_class`). Axiom-clean,
    0 sorry.
  - ✅ **Unified single-item decode (capstone)** (`UnifiedDecodeItem.lean`).
    `rlp_decode_single_item_spec_within`: for an arbitrary prefix byte, one
    theorem whose conclusion is a `match classifyPrefix pfx` dispatching to the
    five per-class full-path handlers — the RV64 analogue of the pure
    `decodeAux_cons_eq_classifyPrefix_match`. Each branch reaches the
    class-appropriate exit with the spec-correct decoded length
    (`1` / `rlpPrefixShort{Bytes,List}PayloadLen` / `Nat.fromBytesBE …`).
    Long-form-only proof obligations (window `hwin`, loop `hback`) ride in a
    `match`-typed hypothesis `rlpDecodeLongHyps` so flat callers needn't supply
    them. Proof: `cases classifyPrefix pfx` + `exact <handler>`. Axiom-clean,
    0 sorry. **The single-item RLP decode arc is complete end-to-end**
    (classify → per-class length extraction → unified dispatch).
  - ✅ **List-payload single-byte-run decode (pure spec)** (`EL/RLP/ListDecode.lean`).
    The merged `ListDecodeBridge` *characterizes* list decode in terms of
    `decodeItems`/`decodeListPayload` but never *computes* `decodeItems` for any
    concrete payload class. `decodeItems_singleByte_run` closes that gap: a run of
    bytes each `< 0x80` (with depth budget `2 * bs.length ≤ nDepth`) decodes to
    one one-byte `RLPItem.bytes` per byte, consuming the whole run (induction on
    `bs`, reusing `decodeAux_cons_singleByte_of_classifyPrefix` +
    `classifyPrefix_singleByte_iff`). `decodeAux_shortList_of_singleByte_items`
    lifts it through the merged short-list characterization
    (`ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff`) to a full
    `RLPItem.list` of single-byte items, with a concrete cross-check
    (`0xC3 [0x01,0x7F,0x05]`). Axiom-clean (propext/Quot.sound), 0 sorry. This is
    the pure-spec foundation for the first RV64 list-payload loop (single-byte
    items are the one fixed-stride, zero-copy case); the RV64 loop + `decodeItems`
    bridge is the follow-up.
  - Remaining (future): a full semantic bridge to the pure `decodeAux` (needs
    canonical-encoding `>55`/leading-zero validation the RV64 path does not
    perform, plus recursive list decode `decodeItems` for list payloads);
    cross-doubleword length spans (`n ≤ 8` single-doubleword only); Phase-4
    `read_input` pipeline integration.
- Phase 4: `read_input` integration (obtain RLP input pointer + length)
- ✅ **Multi-dword byte-region memory abstraction** (`EvmAsm/Rv64/MemRegion.lean`,
  Phase-5 foundation). `bytesRegion (base) (bs : List (BitVec 8))` — a contiguous
  byte region stored little-endian across consecutive 8-byte dwords (each named
  `↦ₘ` via `packBytes`), mirroring `Evm64.CodeRegion.evmCodeIs` but at the `Rv64`
  layer so the RLP decoder can use it. Closes the gap that the existing decoder
  reads only **within one dword** (`Phase2LongLoopGeneral.hwin` forces a single
  `dwordAddr`). Lemmas: `bytesRegion_nil`, `bytesRegion_eq_cons` (peel one dword,
  address `+8` — the workhorse), `bytesRegion_pcFree` (frames). The pure
  byte-packing primitives (`packBytes`, `extractByte_packBytes`, `packDword`)
  were **relocated** from `Evm64/CodeRegion.lean` down to `Rv64/ByteOps.lean`
  (their natural home; one source of truth for both layers). Axiom-clean, 0 sorry.
- ✅ **`bytesRegion_lbu_within` — read byte `i` across dwords** (`MemRegion.lean`).
  An `LBU` at `regionBase + i` (`i < bs.length`, base dword-aligned, no overflow)
  reads `bs[i]` — the multi-dword read the single-`dwordAddr` `hwin` model could
  not express (cross-check: reads byte 9 of a 10-byte / 2-dword region). New
  supporting lemmas: `alignToDword_add_ofNat_of_aligned`
  (`alignToDword (base + i) = base + 8*(i/8)`) and `byteOffset_add_ofNat_of_aligned`
  (`= i % 8`) — the BitVec masking arithmetic the existing loop *assumes*; plus
  `bytesRegion_dword_at` (extract the `dw`-th dword cell, partial last chunk OK).
  Composition mirrors `Evm64/Push`: `generic_lbu_spec_within` +
  `extractByte_packBytes`, framed via `cpsTripleWithin_frameR` + `xperm_hyp`.
  Axiom-clean, 0 sorry.
- ✅ **Single-byte-item list-decode loop** (`SingleByteListLoop.lean`). The first
  RV64 RLP *list*-decode loop: a 4-instruction back-branch body
  (`LBU x12,x13,0; ADDI x13,x13,1; ADDI x14,x14,-1; BNE x14,x0,back`) traversing a
  single-byte-item payload, reading each byte from `bytesRegion` via
  `bytesRegion_lbu_within` (assume-precondition scope — every byte `< 0x80` assumed,
  no in-line validation/fail-exit yet). Layers: `sbll_iter_spec_within` (3-instr
  triple), `sbll_body_spec_within` (2-exit `cpsBranchWithin`), `sbll_loop_succ/n_spec_within`
  (n-iteration closure by **remaining-count induction with a generalized start
  index** — keeping `regionBase`/`bs` fixed and re-indexing the per-iteration
  validity hypotheses, since `bytesRegion_lbu_within` is keyed by the *absolute*
  byte index, unlike Phase-2's `dwordAddr`-shift), and `sbll_loop_bridge` tying the
  operational spec to the pure `decodeItems_singleByte_run` (zero-copy: shared
  `< 0x80` precondition + matching consumed length `bs.length`). Cross-dword
  cross-check: 10-byte / 2-dword payload → 10 items in `4*10` steps. Reuses
  Phase-2's `word_ofNat_*`/`cnt_dec_1` counter lemmas. Axiom-clean, 0 sorry.
- ✅ **In-line `< 0x80` validation — drop the `hsingle` assumption**
  (`SingleByteListLoopValidated.lean`). The validated loop *proves* every payload
  byte `< 0x80` in-machine instead of assuming it: it ORs each byte into an
  accumulator (`x11`) during the scan (a `cpsTripleWithin` closure mirroring the
  Phase-2 accumulator — `sbll_val_iter/body/loop_succ/n`), then a single post-loop
  `ANDI x15, x11, 0x80; BNE x15, x0, fail` (accumulate-then-check, avoiding a
  branching loop closure). `sbll_val_loop_checked_spec_within` is the 2-exit
  `cpsBranchWithin` (success = `acc &&& 0x80 = 0`, fail = some byte `≥ 0x80`);
  `sbll_val_loop_bridge` derives `decodeItems_singleByte_run` from the
  *machine-checked* success condition — **no `hsingle` precondition**. Key new
  BitVec lemma `orAccList_and_0x80_eq_zero_imp_all_lt` (accumulator bit-7 clear ⇒
  all bytes `< 0x80`) via `BitVec.msb_eq_false_iff_two_mul_lt`. `OR` cannot
  overflow ⇒ no `n ≤ 8` bound. Cross-dword cross-check at 10 bytes. Axiom-clean,
  0 sorry.
- ✅ **Unified decoder 5-exit reconvergence — flat classes**
  (`UnifiedDecodeItemReconverge.lean`). The unified single-item decoder
  (`rlp_decode_single_item_spec_within`) reaches 5 different exit PCs with 5
  different posts; a per-item list loop needs one common exit + a uniform post.
  This reconverges the **3 flat classes** (`singleByte`/`shortBytes`/`shortList` —
  no memory, no `x12`/`x14`): each class handler runs to its exit, then an
  unconditional `JAL x0` (`jal_x0_spec_gen_within`, 1 step, `emp` pre/post)
  jumps to a common `joinPC`. `rlp_decode_single_item_reconverged_flat` is one
  `cpsTripleWithin 11 base joinPC cr` whose uniform post exposes the cascade
  residue / payload length / payload pointer via `classifyPrefix`-dispatched
  helpers (`itemCascadeResidue`/`itemPayloadLen`/`itemPayloadPtr`), so a loop can
  advance uniformly by `x13 += x11`. Generic `reconverge_arm` (handler ∘ JAL ∘
  `extend_code` to the shared `cr` ∘ `mono_nSteps`) + a 3-way `classifyPrefix`
  case split; `singleByte`'s `x13`-free pre is unified by framing `x13`. The
  shared decoder code is a parameter `cr` with per-class sub-CR hypotheses
  (`handlerCR ∪ JAL ⊆ cr`), discharged by the eventual loop caller. Axiom-clean,
  0 sorry.
- ✅ **Unified decoder 5-exit reconvergence — ALL classes**
  (`UnifiedDecodeItemReconvergeAll.lean`). Completes the reconvergence by adding
  the 2 long classes (`longBytes`/`longList` — `(dwordAddr ↦ₘ wordVal)` + `x12`/`x14`
  + variable steps). `rlp_decode_single_item_reconverged_all` is a single
  `cpsTripleWithin 60 base joinPC cr` (60 = `max(3,6,10,9+6·8,11+6·8)+1`, longList
  binds it) over ALL of `classifyPrefix pfx`, with a uniform post exposing
  `x10`/`x11`/`x12`/`x13`/`x14`/memory via 5-class match helpers
  (`itemResidue`/`itemLen`/`itemPtr`/`itemX12`/`itemX14`). Bound-parameterized
  `reconverge_arm_n` (the flat arm with `11`→`N`); 5-way `classifyPrefix` case
  split invoking each handler directly (flat arms frame `x12`/`x14`/memory; long
  arms carry them); variable long-step bound discharged by
  `rlpPrefixLong{Bytes,List}LenOfLen_le_8_of_class`. Axiom-clean, 0 sorry.
- ✅ **Flat per-item list-loop BODY** (`FlatListLoopBody.lean`). One iteration of
  the flat-item list-decode loop as a 2-exit `cpsBranchWithin`: `LBU x5,x13,0`
  (read the prefix from `bytesRegion` via `bytesRegion_lbu_within`) → the flat
  reconverged decoder (passed as an OPAQUE `cpsTripleWithin` hypothesis,
  `decoder_base = lbase+4`) → `ADD x13,x13,x11` (advance to the next item) →
  `ADDI x14,x14,-1` (item counter) → `BNE x14,x0,back` (taken → `lbase`).
  `fll_body_spec_within` (step bound 15) with bundled post `fll_body_post`;
  new stride helpers `itemTotalLen`/`itemNextPtr` + `itemNextPtr_eq`
  (`itemPayloadPtr + itemPayloadLen = v13 + itemTotalLen`, the factored form the
  closure re-indexes on). The decoder is opaque so its disjointness from the
  loop's LBU/ADD/ADDI/BNE singletons is taken as hypotheses (the closure
  discharges them from the concrete decoder layout). `bytesRegion`+`x14` framed
  through the decoder. Flat-only (long items need the decoder's length-read
  upgraded to `bytesRegion`). Axiom-clean, 0 sorry.
- ✅ **Flat-item stride-equivalence** (`FlatListLoop.lean`). The mathematical
  core the closure needs: `isFlatItem` (`.bytes data` with `data.length ≤ 55`;
  `.list` with payload `≤ 55`), `classifyPrefix_encode_head_flat` (a flat item's
  encoding starts with a flat prefix), and **`encode_head_eq_itemTotalLen`**:
  `itemTotalLen ((encode item)[0]) = ofNat (encode item).length` — the
  operational per-item stride equals the pure encoding length (per-class
  byte-shape algebra via `encodeBytes`/`encode_list_short`/`classifyPrefix_*_iff`,
  no `bv_decide`). Bridges the machine loop's pointer advance to the pure
  `encode`/`decodeItems` round-trip. Axiom-clean, 0 sorry.
- ✅ **Concrete flat decoder program** (`FlatDecoderConcrete.lean`). Discharges the
  list-loop closure's abstract `decoderH` with REAL code: `flat_decoder_prog`
  (one linear 16-instruction program — the 4-step phase-1 cascade + the three
  flat-class phase-3 handlers + their reconvergence `JAL`s) and
  **`flat_decoder_spec`** (`∀` flat prefix, `cpsTripleWithin 11 base (base+64)
  (CodeReq.ofProg base flat_decoder_prog) …` — exactly the `decoderH` shape).
  Proved by instantiating `rlp_decode_single_item_reconverged_flat` at the forced
  offsets (`off1=off2=28, off4=24, joff1=28, joff2=16, joff4=4`) and discharging
  every side-condition: `htarget*`/`hjoin*` via `rv64_addr`; the six `hd_*`
  disjointness via `crDisjoint`; the three `hsub_*` subsets via `union_sub` +
  `ofProg_mono_sub`/`singleton_mono` (`flat_piece`/`flat_jal_piece` helpers). No
  `bv_decide`. Axiom-clean, 0 sorry.
- ✅ **Flat list-loop n-closure + bridge** (`FlatListLoop.lean`). The operational
  loop over a list of flat items: `fll_loop_spec_within` (structural induction
  over `items : List RLPItem`, threading the byte offset via
  `bs.drop O = encode.encodeItems items`, applying `fll_body_spec_within` per
  item and re-indexing the pointer with `encode_head_eq_itemTotalLen`; the
  decoder is a ∀-hypothesis `decoderH`, discharged per iteration; uniform
  `15 * items.length` steps with `regOwn`-abstracted scratch in `fll_loop_post`),
  `fll_loop_n_spec_within` (offset-0 entry), and `fll_loop_bridge` (conjoins the
  loop with the pure `decodeItems (2*len+1) … = some (items, [])` via
  `decode_encode_mutual.2` — strict fuel `2*len < nDepth`). Axiom-clean, 0 sorry.
- ✅ **Fully concrete end-to-end flat list decoder** (`FlatListLoopConcrete.lean`).
  Wires `flat_decoder_spec` into `fll_loop_bridge`: **`flat_list_loop_concrete_bridge`**
  has NO abstract hypotheses — a real RV64 program (`[LBU] ++ flat_decoder_prog ++
  [ADD, ADDI, BNE]` at `base`, scaffold bracketing the 16-instr decoder so
  `joinPC=base+68`, loop exit `base+80`, back-edge `-76`) decodes a non-empty flat
  `items` list from `bytesRegion` in `15*items.length` steps AND coincides with the
  pure `decodeItems` round-trip. The loop's `decoderH` is `flat_decoder_spec (base+4)`
  (exit rewritten `(base+4)+64 → base+68`); scaffold disjointness via
  `singleton_ofProg`/`ofProg_singleton` + `ofProg_none_range_len` + `bv_omega` (the
  `crDisjoint` tactic times out on the opaque 16-instr `ofProg`); `hback` via
  `signExtend13 (-76) = -76` (`decide`) + `bv_omega`. Concrete 2-item `example`.
  Axiom-clean, 0 sorry. This completes the **flat** RLP list-decoder arc.
- 🚧 **Long-item-capable list loop** (arc, step 2 of 6). Goal: a list loop that
  handles `longBytes`/`longList` (real Ethereum RLP exceeds 55 bytes). Design:
  reuse the 5-class single-item decoder (`rlp_decode_single_item_reconverged_all`,
  already proven), with the list-loop item counter on **x15** (the decoder
  clobbers x14 as its length-read counter), the uniform advance `x13 += x11`
  (decoder leaves x13=payloadPtr, x11=payloadLen), and all reads over `bytesRegion`.
  - ✅ **Step 1 — `bytesRegion` length-read loop** (`Phase2LongLoopRegion.lean`).
    Region analog of the single-dword `Phase2Long*` stack: `rlpLoopAccRegion` (+
    `_zero_eq_fromBytesBE`), `rlp_phase2_long_region_iter_spec_within` (one iteration,
    proved by extracting the containing dword from `bytesRegion` and reusing the
    single-dword iter — the cross-dword read the `alignToDword`-constrained loop
    couldn't express), `rlp_phase2_long_region_body_spec_within` (`cpsBranchWithin 6`),
    `rlp_phase2_long_loop_region_succ_spec_within` (induction over `k+1∈[1,8]`
    iterations), and `rlp_phase2_long_loop_region_n_spec_within` (from `0`, decoded
    length `= ofNat (Nat.fromBytesBE ((bs.drop off).take n))`). Same body program as
    the single-dword version; only the memory model differs. Frame `x0` on the
    **left** (`frameL`) so `xperm` never commutes a `regIs` rightward past the opaque
    `bytesRegion` atom. Axiom-clean, 0 sorry, no `bv_decide`.
  - ✅ **Step 2 — long-item stride foundation** (`LongItemStride.lean`). Pure
    long analog of `FlatListLoop.lean` §1: `isLongItem`/`itemPayloadCount`/`itemLenOfLen`,
    `classifyPrefix_encode_head_long`, `encode_long_lenOfLen_eq_{bytes,list}`,
    `encode_long_length_eq`, `encode_long_lenBytes_read`, and **`encode_long_stride`**
    (`payloadPtr + payloadCount = v13 + (encode item).length`). NB: the long stride is
    runtime-read-dependent, so it is NOT a prefix-only `itemTotalLen` (that flat helper's
    long branch correctly stays `_ => 0`); the unified loop re-indexes via this identity.
  - ✅ **Step 3a — region long decoder arms** (`Phase1LongFullRegion.lean`).
    `rlp_phase1_e3_longBytes_full_region_spec_within` / `…_e5_longList_…`: the e3/e5 long
    arms re-derived over `bytesRegion` (analogs of `Phase1E{3,5}Long*Full.lean`). Phase
    1/Phase 3 are register-only (reused verbatim); only the phase-2 loop is swapped to the
    step-1 region length-read, `bytesRegion` framed through, and `x13` re-expressed from
    `v13 + 1` to `regionBase + ofNat (off+1)` (item at byte offset `off`). Axiom-clean, 0 sorry.
  - ✅ **Step 3b — region all-class decoder** (`UnifiedDecodeItemReconvergeAllRegion.lean`).
    **`rlp_decode_single_item_reconverged_all_region`**: the 5-class single-item decoder over
    `bytesRegion regionBase bs` (analog of `rlp_decode_single_item_reconverged_all`). Region
    post-helpers `itemLenRegion`/`itemX12Region` (read `bs` at `off+1`) + `itemPtrRegion`;
    `itemResidue`/`itemX14` reused; `rlpDecodeLongHypsRegion` (region window, no `alignToDword`);
    `reconverge_arm_n` reused unchanged. Flat arms (e1/e2/e4) reuse the existing register-only
    handlers framing `bytesRegion` (`x13` via `hv13`/`region_succ_ptr`); long arms (e3/e5) use the
    step-3a region arms (post matches the helpers exactly). The `decoderH` the long loop body
    consumes. Axiom-clean, 0 sorry.
  - ✅ **Step 4 — unified loop body** (`UnifiedListLoopBody.lean`). **`unified_body_spec_within`**:
    one iteration decoding ANY item (all 5 classes) — `LBU x5,x13,0` + region decoder (opaque
    `cpsTripleWithin 60`) + `ADD x13,x13,x11` + `ADDI x15,x15,-1` + `BNE x15,x0,back`, as a
    `cpsBranchWithin 64` (taken → `lbase`, fall → `joinPC+12`). Item counter on **x15** (the decoder
    clobbers x14/x12); x10/x12/x14 are decoder scratch. `unified_body_post` (+`_unfold`/`_pure`),
    `itemNextPtrRegion := itemPtrRegion + itemLenRegion` (the `ADD` result). Faithful mirror of
    `fll_body_spec_within`; the decoder stays opaque (the concrete region decoder discharges it in
    the end-to-end step). Axiom-clean, 0 sorry.
  - ✅ **Step 5a — unified stride-equivalence** (`UnifiedItemStride.lean`).
    **`encode_head_eq_itemNextPtrRegion`**: for ANY item (all 5 classes), the body's per-item advance
    `itemNextPtrRegion ((encode head)[0]) regionBase off bs` (= `itemPtrRegion + itemLenRegion`, the
    `ADD x13` result) re-indexes to `regionBase + ofNat (off + (encode head).length)` — the all-class
    analog of the flat `encode_head_eq_itemTotalLen`. Flat items bridge through `itemTotalLen`
    (reusing `encode_head_eq_itemTotalLen`); long items tie the runtime-read length bytes back to the
    encoding via private `long_lenBytes_in_region` (`(bs.drop (off+1)).take lenOfLen =
    toBytesBE payloadCount`) + step-2 lemmas (`encode_long_lenOfLen_eq_*`, `encode_long_lenBytes_read`,
    `encode_long_length_eq`). Also `flat_or_long` dichotomy. Axiom-clean, 0 sorry.
  - ✅ **Step 5b — unified loop closure + bridge** (`UnifiedListLoop.lean`). All-class analog of the
    flat `fll_loop_*`. **`unified_loop_spec_within`**: structural induction over arbitrary `items`,
    threading the byte offset via `bs.drop O = encode.encodeItems items`, applying the step-4 body per
    item (the 60-step region decoder supplied as the ∀-hypothesis `UnifiedDecoderH`), re-indexing `x13`
    via `encode_head_eq_itemNextPtrRegion` (5a) — uniform `64 * items.length` steps, counter on x15,
    scratch x10/x12/x14 abstracted to `regOwn` in `unified_loop_post`. **`unified_loop_n_spec_within`**
    (offset-0 entry) and **`unified_loop_bridge`** (conjoins the pure `decodeItems` round-trip via
    `decode_encode_mutual.2`). Per-head `itemPayloadCount < 256^8` discharged from `hover` (flat ≤55 /
    long via `encode_long_length_eq`). Axiom-clean, 0 sorry.
  - ✅ **Step 6a — dischargeable decoder hypothesis** (`UnifiedListLoop.lean`). Added a per-index
    `regionLongWindow` guard to `UnifiedDecoderH` (the window-only half of `rlpDecodeLongHypsRegion`: a
    long prefix's `lenOfLen` length bytes lie within the region) and discharge it in
    `unified_loop_spec_within` at every item-start offset (private `regionLongWindow_of_split`: flat →
    `True`; long → the length bytes sit inside `encode head`, in-bounds via `encode_long_length_eq`,
    readable via `hwin`). Plus local per-structure classification `classify_bytes_long`/
    `classify_list_long`. Fixes the latent gap where the old guardless `UnifiedDecoderH` was
    unsatisfiable by any concrete program (a mid-item byte can classify as a long prefix running off
    the region end). Axiom-clean, 0 sorry.
  - ✅ **Step 6b — concrete all-class decoder** (`UnifiedDecoderConcrete.lean`, analog of #9007).
    `unified_decoder_prog : List Instr` — a single 36-instruction program (phase-1 cascade @base..+32,
    e5 long-list handler+loop+JAL @+32/+44/+68, e1–e4 handlers @+72/+80/+92/+104 with the e3 long-string
    loop @+116, reconvergence JALs; `joinPC = base+144`; loop back-edge `-20`; cascade offsets
    `68/68/84/64`, JAL offsets `68/56/4/44/76`). `unified_decoder_spec` proves `cpsTripleWithin 60 base
    (base+144) (ofProg base unified_decoder_prog) …` for `bs[off]` — exactly the `UnifiedDecoderH` shape
    — discharging `rlp_decode_single_item_reconverged_all_region`'s ~30 hypotheses: targets/joins via
    `rv64_addr`, 12 disjointness via `simp [rlp_phase1_step_code]; crDisjoint`, 5 subset embeddings via
    `union_sub` + `unified_piece`/`unified_jal_piece` (`ofProg_mono_sub`/`ofProg_lookup_addr`), and
    `rlpDecodeLongHypsRegion` from the passed `regionLongWindow` window + a concrete `-20` back-edge
    (`signExtend13 (-20) = -20` by `decide`, then `bv_omega`). Key perf lesson: write piece subBases in
    the region decoder's `e_target + k` form (syntactic unification, not BitVec defeq) and skip
    `simp only [rlp_phase1_step_code]` in the subset proofs (defeq handles the abbrev); needs
    `set_option maxHeartbeats 800000`/`maxRecDepth 8000`. Axiom-clean, 0 sorry, 0 warnings.
  - ✅ **Step 6c — fully concrete end-to-end** (`UnifiedListLoopConcrete.lean`, analog of #9008).
    **`unified_list_loop_concrete_bridge`** has NO abstract hypotheses: the real RV64 program `[LBU
    x5,x13,0] ++ unified_decoder_prog ++ [ADD x13 x13 x11, ADDI x15 x15 -1, BNE x15 x0 -156]` at `lbase`
    (scaffold bracketing the 36-instr decoder so `joinPC = lbase+148`, exit `lbase+160`, back-edge
    `-156`) **decodes a non-empty list of ARBITRARY RLP items (all 5 classes, long strings/lists
    included) from `bytesRegion` in `64*items.length` steps AND coincides with the pure `decodeItems`
    round-trip**. Discharges `unified_loop_bridge`'s abstract `UnifiedDecoderH` via `unified_decoder_spec
    (lbase+4)` (`rwa [(lbase+4)+144 = lbase+148]`); back-edge `signExtend13 (-156) = -156` by `decide`;
    scaffold/decoder disjointness via `dcr_none` (`ofProg_none_range_len`, n=36) + `Disjoint.singleton_
    ofProg`/`ofProg_singleton`. Concrete 2-item `example`. Built first try, axiom-clean, 0 sorry. **This
    completes the long-item RLP list-decoder arc — single-level lists of all 5 classes now decode
    end-to-end in real RISC-V with a kernel-checkable round-trip proof.**
- **Phase 4 done.** RLP single-level list decoding (flat #9004–#9008 + long-item #9020–#9031) is
  complete. Remaining for feature-complete RLP:
- Phase 5: Recursive list decode (iterative with explicit stack)
  - ✅ **Step 1 — descend-one-level kernel** (`NestedDescendOne.lean`). **`list_item_payload_window`**:
    for a `.list items` item at offset `off`, the single-item decoder's window (`x13 = itemPtrRegion`
    payload pointer, `x11 = itemLenRegion` payload length) points at EXACTLY the `encode.encodeItems
    items` payload — `∃ payloadOff, itemPtrRegion = regionBase + ofNat payloadOff ∧ itemLenRegion =
    ofNat (encodeItems items).length ∧ bs.drop payloadOff = encode.encodeItems items ++ tail` (the
    third conjunct is precisely the list loop's `hdrop` precondition, so a caller can descend). The
    all-class analog, for the payload window, of the 5a stride lemma; short-list via
    `classifyPrefix_shortList_iff` + `encode_list_short`, long-list via `classifyPrefix_encode_head_long`
    + `encode_list_long` + `take_left'`/`drop_left'` + `fromBytesBE_toBytesBE`. Plus `decode_list_descend`
    (top-level round-trip) and concrete nested `example`s. Axiom-clean, 0 sorry.
  - ✅ **Step 2 — length-driven loop body** (`UnifiedLenLoopBody.lean`). Exploration confirmed the
    count-driven descent is a dead end (the decoder yields a payload byte-length in `x11`, not an item
    count; the count is symbolic, unloadable) — so the foundation is a LENGTH-driven loop.
    **`unified_lenloop_body_spec_within`**: one iteration as `cpsBranchWithin 63` over `LBU x5,x13,0` +
    opaque region decoder (`cpsTripleWithin 60`) + `ADD x13,x13,x11` + **`BNE x13,x15,back`** — guard
    compares the advanced pointer to the invariant end pointer `x15 = endPtr` (no counter, one fewer
    instr than the count-driven body); taken (`itemNextPtrRegion ≠ endPtr`)→`lbase`, fall (`= endPtr`)→
    `joinPC+8`. With no counter, `x15` holds `endPtr` (the decoder never touches it, framed through the
    60-step decode). `unified_lenloop_body_post` (+`_unfold`/`_pure`). Faithful mirror of the
    count-driven `unified_body_spec_within` with the guard swapped; built first try, axiom-clean, 0 sorry.
  - ✅ **Step 3 — length-driven closure + bridge** (`UnifiedLenLoop.lean`). **`unified_lenloop_spec_
    within`**: induct over `items`, `x13` from `O`, `x15 = endPtr := regionBase + ofNat (O +
    (encodeItems items).length)` fixed (invariant, threaded unchanged); applies the step-2 body per item,
    terminating when `x13` reaches `endPtr` exactly after the last item — `63 * items.length` steps, no
    item count. NEW lemma **`region_offset_ne`** (`regionBase + ofNat a ≠ regionBase + ofNat b` for
    distinct in-bounds offsets, by `bv_omega`) discharges `itemNextPtrRegion ≠ endPtr` for intermediate
    items (so the loop continues). **`unified_lenloop_n_spec_within`** (offset-0 entry, `x15 = regionBase
    + ofNat (encodeItems items).length`) and **`unified_lenloop_bridge`** (conjoins `decodeItems
    (2*len+1) … = some (items, [])` via `decode_encode_mutual.2`). Also exposed
    `regionLongWindow_of_split` (was private in `UnifiedListLoop.lean`) — both closures discharge the same
    per-item window obligation. Faithful mirror of the count-driven #9028 with termination swapped;
    axiom-clean, 0 sorry.
  - ✅ **Step 4a — concrete length-driven loop** (`UnifiedLenLoopConcrete.lean`, length-driven analog of
    #9032). **`unified_lenloop_concrete_bridge`** has NO abstract hypotheses: the real RV64 program `[LBU
    x5,x13,0] ++ unified_decoder_prog ++ [ADD x13 x13 x11, BNE x13 x15 -152]` at `lbase` (joinPC=lbase+148,
    exit lbase+156) decodes a list of arbitrary RLP items from `bytesRegion`, running until `x13` reaches
    the end pointer `x15 = regionBase + ofNat len`, in `63 * items.length` steps, AND coincides with the
    pure `decodeItems`. Discharges `UnifiedDecoderH` via `unified_decoder_spec`; `back=-152`
    (`signExtend13 (-152) = -152` by `decide`); scaffold/decoder disjointness via `dcr_none`
    (`ofProg_none_range_len`, n=36). **Directly the top-level list decoder** (the end pointer is the known
    input length). Built first try, axiom-clean, 0 sorry.
  - ✅ **Step 4b — genuine top-level descent** (`UnifiedListDescendConcrete.lean`).
    **`unified_list_descend_concrete_bridge`** has NO abstract hypotheses: the real RV64 program `[LBU
    x5,x13,0] ++ unified_decoder_prog ++ [ADD x15 x13 x11]` (header, base..base+152) `++ [LBU x5,x13,0] ++
    unified_decoder_prog ++ [ADD x13 x13 x11, BNE x13 x15 -152]` (loop, base+152..base+308) decodes a
    *complete RLP list value* `encode (.list items)` from `bytesRegion` — descending the `.list` header
    (→ `x13 = payloadPtr`, `x11 = payloadLen`), computing `x15 := endPtr = payloadPtr + payloadLen` via
    `ADD`, then running the concrete length-driven loop over the payload — in `62 + 63 * items.length`
    steps, AND coincides with the pure `decode (encode (.list items)) = some (.list items, [])`. Bridged
    by `list_item_payload_window` (#9033) with `tail = []` (top-level ⇒ payload is the exact suffix
    `bs.drop payloadOff = encode.encodeItems items`); header window via `regionLongWindow_of_split`; loop
    via `unified_lenloop_spec_within` at offset `payloadOff`. The two decoder copies' cross-disjointness
    is discharged manually (`ofProg_none_range_len` + `Disjoint.*` + a new `ofProg_disjoint_ofProg`
    helper) — `crDisjoint` over two `ofProg`s times out. The heavy `unified_lenloop_spec_within`
    application is extracted into a private `descend_loop_triple` so it elaborates in a clean local
    context (inside the main theorem's large context it provokes an unbounded `whnf`). Axiom-clean, 0
    sorry, 0 warnings.
  - ✅ **Step 5 — tail-general closure + interior descent** (`UnifiedListDescendConcrete.lean` et al.).
    Generalized `unified_lenloop_spec_within` to `bs.drop O = encode.encodeItems items ++ btail` (the
    stride/window glue — `encode_head_eq_itemNextPtrRegion`, `regionLongWindow_of_split`, and the private
    `long_lenBytes_in_region` — now take an arbitrary byte suffix `rest : List Byte`, since they only use
    that `encode head` is a prefix; the byte tail is inert). Then generalized
    **`unified_list_descend_concrete_bridge`** itself to take a trailing `tail : List Byte`: the program
    decodes a `.list` value embedded at the front of `encode (.list items) ++ tail`, stopping at the
    sub-list boundary and leaving `tail` unread, in `62 + 63 * items.length` steps, coinciding with the
    pure `decode (encode (.list items) ++ tail) = some (.list items, tail)` (via the existing
    `decode_encode_append`). The buffer-vs-value first byte is bridged by `List.getElem_append_left`
    (`(encode (.list items) ++ tail)[0] = (encode (.list items))[0]`). `tail = []` recovers the top-level
    case. Concrete examples for both `tail = []` and `tail = [0xFF]` (`[0xc2,0x01,0x02,0xFF]` ⇒
    `(.list …, [0xFF])`). Axiom-clean, 0 sorry, 0 warnings, no heartbeat override. **This is the recursive
    step toward arbitrary depth** (interior sub-lists with trailing siblings).
  - ✅ **Step 6a — offset-general descent** (`UnifiedListDescendConcrete.lean`).
    **`unified_list_descend_concrete_bridge_at`**: decode a `.list` value sitting at byte offset `O` of a
    buffer `bs` (`bs.drop O = encode (.list items) ++ tail`), with `x13` entering at `regionBase + ofNat
    O`, reading at an OFFSET into the single dword-aligned `regionBase` (rather than re-anchoring at the
    unaligned payload pointer — `bytesRegion` is dword-granular, so re-anchoring/splitting at an arbitrary
    byte is impossible). The underlying decoder/loop/window helpers were already offset-general; only the
    descent wrapper needed it. `unified_list_descend_concrete_bridge` is now the `O = 0` corollary. This
    is the building block that makes **nested descent composable** (descend a sub-list at its parent's
    payload offset). Axiom-clean, 0 sorry, 0 warnings. Concrete `O = 2` example.
  - ✅ **Step 6b — depth-2 nested descent** (`UnifiedListDescendNested.lean`).
    **`unified_list_header_descend`** (in `UnifiedListDescendConcrete.lean`): the reusable header-descend
    primitive — `LBU + unified_decoder_prog` at offset `O` leaves `x13 = itemPtrRegion` (payload pointer),
    `x11 = itemLenRegion` (payload length). **`unified_list_descend_nested_bridge`**: for an outer list
    whose head is itself a list (`.list (.list innerItems :: rest)`) at the front of `bs = encode (.list
    (.list innerItems :: rest)) ++ outerTail`, the program descends the outer header (offset 0) to its
    payload pointer (offset `payloadOff`), then descends the inner `.list innerItems` there via
    `unified_list_descend_concrete_bridge_at` — in `123 + 63 * innerItems.length` steps — coinciding with
    the pure nested `decode`. Reading at an OFFSET into the single aligned region (never re-anchoring) is
    what makes the two levels compose; the inner program's `(base+148)+k` addresses are normalized to
    `base+N` so the `seq` unifies syntactically (avoids a variable-base `whnf` blowup). `crDisjoint`
    across the two decoder copies via the now-public `ofProg_disjoint_ofProg`. Axiom-clean, 0 sorry,
    0 warnings, no heartbeat override. Concrete `[[1,2],3]` example.
  - ✅ **Step 7a — `regOwn`-re-entry descent** (`UnifiedListDescendConcrete.lean`).
    **`unified_list_descend_concrete_bridge_at_regOwn`**: the offset-general descent restated so its PRE is
    itself a `unified_lenloop_post` (at `O`) and its POST the next `unified_lenloop_post` (at `O + (encode
    (.list items)).length`). Since a descent's post abstracts the scratch registers to `regOwn` and leaves
    `x13`/`x15` at the next sibling, this lets one descent feed DIRECTLY into the next with a syntactic
    `unified_lenloop_post` match — the chainable building block for sequential sibling descent. Derived
    from `…_bridge_at` by consuming the 5 owned scratch registers (`x5,x10,x11,x12,x14`) via
    `cpsTripleWithin_of_forall_regIs_to_regOwn` (the Evm64 SDiv/SMod idiom) — each peel pinned with explicit
    `(r := …) (P := …)` so `xperm_hyp` resolves the interspersed-register reshape; `rw
    [unified_lenloop_post_unfold]` unfolds only the pre (post keeps a distinct `endPtr`). Axiom-clean,
    0 sorry, 0 warnings, no heartbeat override.
  - ✅ **Step 7b — two-sibling sequential descent** (`UnifiedListDescendSiblings.lean`).
    **`unified_list_descend_two_siblings_bridge`**: for `bs.drop O = encode (.list aItems) ++ encode (.list
    bItems) ++ tail`, the program descends `.list aItems` (at `O`, via `…_bridge_at`) then `.list bItems`
    (at the stride offset `O + (encode (.list aItems)).length`, via `…_at_regOwn`) in
    `(62 + 63*aItems.length) + (62 + 63*bItems.length)` steps, coinciding with `decode` of each. The two
    descents chain with NO glue — both intermediate states are `unified_lenloop_post`, so `cpsTripleWithin_seq`
    matches syntactically (only B's exit `base+308+308` is `rw`-normalized to `base+616`). Also adds the
    **reusable `descendCR` / `descendCR_none` / `descend_cr_disjoint`**: a descent CR maps to `none` outside
    its 77 instruction slots (`b + 4*k`, k<77), so two non-overlapping descents are disjoint — an ~8-line
    range argument (à la `ofProg_disjoint_ofProg`) instead of a 7×7 `Disjoint.*` cascade; reused by the
    N-sibling walk. Axiom-clean, 0 sorry, 0 warnings, no heartbeat override. Concrete `[0xc1,0x01,0xc1,0x02]`
    example.
  - ✅ **Step 8 — leaf-field scalar value read** (`UnifiedFieldScalarRead.lean`).
    **`unified_field_scalar_read`**: from the single-item decoder's output convention — `x13 = regionBase +
    ofNat off` (payload pointer), `x11 = ofNat n` (payload length, `1 ≤ n ≤ 8`) — reads the `n` payload
    bytes big-endian into `x11 = Nat.fromBytesBE ((bs.drop off).take n)` (the field's scalar value) and
    advances `x13` to `off + n` (the next field), in `2 + 6*n` steps. The first **value-extraction** step
    (prior steps gave only framing/pointers). Reuses the Phase-2 region BE loop
    (`rlp_phase2_long_loop_region_n_spec_within`); the only new code is a 2-instruction impedance glue
    (`ADDI x14 x11 0` to move the length into the loop's count register, `ADDI x11 x0 0` to zero the
    accumulator). Axiom-clean, 0 sorry, 0 warnings, no heartbeat override. Concrete `[0x01,0x02,0x03] →
    0x010203` example.
  - ✅ **Step 9 — full scalar field decode** (`UnifiedScalarFieldDecode.lean`).
    **`bytes_item_payload_window`** (the `.bytes` analog of `list_item_payload_window`): for a short `.bytes
    data` item at offset `O`, the decoder's window (`itemPtrRegion`/`itemLenRegion`) points exactly at
    `data` (singleByte + shortBytes cases). **`unified_scalar_field_decode`**: composes
    `unified_list_header_descend` (the general LBU+decoder item-header step) ⨾ `unified_field_scalar_read`,
    so from `x13 = regionBase + ofNat O` (a `.bytes data` field, `1 ≤ data.length ≤ 8`) the program decodes
    the header then reads the payload BE, leaving `x11 = Nat.fromBytesBE data` (the field value) and `x13`
    at the next field (offset `O + (encode (.bytes data)).length`), in `63 + 6*data.length` steps —
    coinciding with the pure `decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail)`. Clobbered
    scratch (`x5/x10/x12/x14`) is abstracted to `regOwn` in the post (chainable). Two integration details
    (both already seen in the descents): the value-read's `(base+148)+k` addresses are `rw`-normalized to
    `base+N`, and the `frameR`'d post is a `(6-group) ** (3-group)` so the `regOwn` conversion is a per-group
    `sepConj_mono`. Axiom-clean, 0 sorry, 0 warnings, no heartbeat override. Concrete `0x2a → 42` example.
  - ✅ **Step 10 — decode-and-store a scalar field** (`UnifiedScalarFieldStore.lean`).
    **`unified_scalar_field_decode_and_store`**: composes `unified_scalar_field_decode` ⨾ a single `SD rOut,
    x11, offset`, so the decoded field value `Nat.fromBytesBE data` is **persisted** to the output cell
    `outBase + offset` (u64 LE — matching the STF struct's scalar slots) while `x13` advances to the next
    field, in `64 + 6*data.length` steps. The **persistence** step a multi-field walk needs (the next field's
    decode clobbers `x11`). The output pointer/cell are framed alongside the decode (no `rOut` distinctness
    hyps — a clashing reg just makes the pre vacuous), and the store CR (`SD@base+180`) is disjoint from the
    decoder/read CR (`base .. base+176`). Rides the pure `decodeScalar` fact along. Axiom-clean, 0 sorry, 0
    warnings, no heartbeat override. Concrete `0x2a → 42` store-to-`0x3000` example. Built first try (1.6s).
  - ✅ **Step 11 — first multi-field walk** (`UnifiedTwoScalarFieldWalk.lean`).
    **`unified_scalar_field_decode_and_store_at_regOwn`**: the decode-and-store unit restated with its four
    clobbered scratch registers (`x5/x10/x12/x14`) abstracted to `regOwn` in the pre (`x11`/`x15` stay
    concrete — the prior unit supplies them), via four nested `cpsTripleWithin_of_forall_regIs_to_regOwn`,
    so it's callable after a prior field has run. **`unified_two_scalar_field_walk`**: `cpsTripleWithin_seq`
    of a concrete unit (field A → slot `offA`) ⨾ the `regOwn` variant (field B → slot `offB`) through one
    output pointer `rOut` — the first end-to-end multi-field walk. A's advanced `x13` feeds B's payload
    pointer with no glue; A's written cell is framed through B and B's cell through A, so both slots end up
    written; rides the two pure `decodeScalar` peels (`hdropB` via `← drop_drop`/`drop_append_length`). The
    36-leaf unit-A ⊥ unit-B disjointness is one explicit nested `union_left`/`union_right` term (a local
    `sDisj` helper shares the 4 singleton A-leaves; `ofProg_disjoint_range_len` for the ofProg pairs; per-leaf
    explicit lengths to avoid `first`-backtracking whnf-loops). Axiom-clean, 0 sorry, 0 warnings, no heartbeat
    override. Concrete two-byte example: `42 → 0x3000`, `7 → 0x3008`.
  - ✅ **Step 12 — reusable field-unit CR + three-field walk** (`ScalarFieldWalkChain.lean`).
    **`scalarFieldUnitCR base rOut offset`**: the decode-and-store unit's 46-slot CodeReq named for reuse
    (defeq to the units' inline CR). **`scalarFieldUnitCR_none`** / **`scalarFieldUnitCR_disjoint`**: a
    range-based disjointness lemma (à la `descend_cr_disjoint` / `descendCR_none`) — two units whose 184-byte
    code ranges don't overlap (`base2 ≥ base1 + 184`) have disjoint CodeReqs, proved ONCE. This replaces the
    36-leaf-per-pair blowup: chaining is now `union_left`/`union_right` + one lemma application per pair.
    **`unified_three_scalar_field_walk`**: composes `unified_two_scalar_field_walk` (A, B) ⨾ one more `regOwn`
    unit (C), each prior cell framed through the later units, unit-AB ⊥ unit-C via two
    `scalarFieldUnitCR_disjoint` applications; carries all three `decodeScalar` peels (offset/drop bookkeeping
    via `append_assoc` + `← drop_drop`/`drop_append_length`). The concrete inductive step toward N. Built
    first try. Axiom-clean, 0 sorry, 0 warnings, no heartbeat override. Three-byte example: `42/7/9 →
    0x3000/0x3008/0x3010`.
  - ✅ **Step 13 — recursive N-field walk infrastructure** (`ScalarFieldWalkInfra.lean`).
    Three pieces that unblock the recursive walk: **`unified_scalar_field_decode_and_store_at_regOwn_memOwn`**
    — the atomic unit with BOTH `regOwn` scratch AND a `memOwn` output cell (one extra
    `cpsTripleWithin_of_forall_memIs_to_memOwn` peel over the step-11 regOwn variant), so the walk's pre is a
    fold of `memOwn` slots; **`nFieldWalkCR base rOut fields`** — the recursive CodeReq of the unrolled
    N-unit program (unit `i` = `scalarFieldUnitCR` at `base + 184*i`); **`scalarFieldUnitCR_disjoint_walkCR`**
    — a single unit ⊥ the whole rest-of-walk CodeReq, by induction on the field list (each step a
    `scalarFieldUnitCR_disjoint`), which discharges the recursive walk's `cpsTripleWithin_seq` obligation in
    one application. Built first try. Axiom-clean, 0 sorry, 0 warnings, no heartbeat override.
  - ✅ **Step 14 — recursive N-field scalar walk** (`UnifiedNScalarFieldWalk.lean`).
    **`unified_n_scalar_field_walk`**: decode-and-store an arbitrary LIST `fields : List (BitVec 12 × List
    Byte)` of consecutive scalar fields, each to its own output slot, through one output pointer — the
    keystone generalizing the hand-unrolled 3-field walk to any N. Output cells: pre = `nFieldOutOwn` (a
    `**`-fold of `memOwn` slots), post = `nFieldOutVal` (a fold of `↦ₘ` value slots); `x13` advances past the
    whole `flatMap`-concatenation. Proved by induction on the list: nil = `cpsTripleWithin_refl` (one `x11`
    `regIs→regOwn` weakening via a `sepConj_mono` chain); cons = the `regOwn`+`memOwn` unit ⨾ IH, framing the
    tail cells (`nFieldOutOwn rest`, `pcFree` by `nFieldOutOwn_pcFree`) through the head and the head's
    written cell through the tail, disjointness via `scalarFieldUnitCR_disjoint_walkCR`. The opaque folds
    stayed single atoms so `xperm_hyp` reconciled the intermediate/goal states; the only manual step was
    re-associating the `x13` offset (`O + (lenH + lenT)` → `(O + lenH) + lenT`) before xperm. Built in two
    tries. Axiom-clean, 0 sorry, 0 warnings, no heartbeat override. Example: the 3-field schema as an
    instance.
  - ✅ **Step 15 — byte-store algebra** (`MemRegionWrite.lean`). The write-side algebra for a packed dword:
    **`packBytes_set`** (`replaceByte (packBytes chunk) k b = packBytes (chunk.set k b)`), plus
    `extractByte_replaceByte_diff`, `extractByte_packBytes_total`, `eq_of_forall_extractByte` (dword byte-wise
    extensionality), `getByteAt_set`. The algebraic core of writing into a `bytesRegion` — write analog of the
    read-side `extractByte_packBytes`. Axiom-clean, 0 sorry, 0 warnings.
  - ✅ **Step 16 — SB into bytesRegion** (`MemRegionStore.lean`). **`bytesRegion_sb_within`**: `SB` of the low
    byte of `rs2` at `regionBase + i` turns `bytesRegion regionBase bs` into `bytesRegion regionBase (bs.set i
    (v_data.truncate 8))` — the writable destination a byte-copy loop needs (write analog of
    `bytesRegion_lbu_within`). Structural core **`bytesRegion_dword_at_set`**: one induction framing the
    `i`-th dword for BOTH `bs` and `bs.set i b` with the SAME `front`/`rest` (sidesteps the existential
    mismatch of `bytesRegion_dword_at`), so the `SB` lands exactly on `bs.set i b` via `packBytes_set`. Uses
    `List.take_set`/`drop_set`. The byte-copy MEMORY MODEL is now complete (read + write). Axiom-clean, 0
    sorry, 0 warnings.
  - ⚠️ **Design correction (the byte-copy loop is UNROLLED, with independent indices).** Two refinements to
    the original "counted LBU+SB loop" plan: (1) field sizes are fixed (20/32 bytes), so the copy is an
    **unrolled chain** of N blocks (no hardware back-branch / `cpsBranchWithin` — a tight loop is a future
    code-size optimization); (2) a field copy needs **independent** src/dst byte indices — the input-buffer
    payload position `si0` is unrelated to the output-struct field offset `di0` and can be smaller than it
    (e.g. legacy-tx `value` at struct offset 76), so the destination is the WHOLE dword-aligned output-struct
    `bytesRegion` (only its base aligned; `di0` arbitrary/unaligned). The first (coupled `src = off + dst`)
    copy_iter/chain were superseded by general (independent-index) versions.
  - ✅ **Step 17 — copy-loop iteration** (`ByteCopyIter.lean`, coupled) — one LBU-read + SB-write + 3 pointer
    ADDIs; **step 20** (`ByteCopyIterGen.lean`) generalizes it to independent `si`/`di`.
  - ✅ **Step 18 — copy-chain infrastructure** (`ByteCopyChainInfra.lean`): `copyIterCR`, range-based
    `copyIterCR_disjoint`/`copyIterCR_disjoint_chainCR`, `byteCopyChainCR`, `copyRange`.
  - ✅ **Step 19/21 — copy-chain spec** (`ByteCopyChain.lean` coupled / `ByteCopyChainGen.lean` general):
    `rlp_copy_chain_gen_spec` copies N bytes `src[si0..]` → `dst[di0..]` by induction on N (dst region
    evolving via `bytesRegion_sb_within`), result `copyRangeGen dstBytes srcBytes si0 di0 N`.
  - ✅ **Step 22 — leaf byte-array field copy** (`UnifiedFieldBytesCopy.lean`). **`unified_field_bytes_copy`**:
    from `x13 = regionBase + ofNat off` (decoded payload ptr), `ADDI x14, rOut, fieldImm` sets the dst pointer
    (`signExtend12 fieldImm = ofNat di0`, caller discharges by `decide`), then the general copy chain writes
    `output[di0..di0+N) := src[off..off+N)`. The byte-array analog of `unified_field_scalar_read`. Plus
    `singleton_disjoint_byteCopyChainCR`. (CI lesson: macOS `sed \b` silently fails for import insertion —
    use Edit; `check-unimported.sh` / `check-heartbeats-approved.sh` need bash 4+, can't run on local 3.2.)
  - ✅ **Step 23 — full byte-array field decode-and-copy** (`UnifiedBytesFieldDecode.lean`).
    **`unified_bytes_field_decode_and_copy`** = `unified_list_header_descend` (header → x13 = payload ptr,
    x11 = length) ⨾ `unified_field_bytes_copy`, output region framed through the descend, header-leftover
    regs framed through the copy; `bytes_item_payload_window` connects `itemPtrRegion`/`itemLenRegion` to
    `(payloadOff, data.length)`, `copyRangeGen_congr` rewrites the `bs`-window copy to `data` at `di0`.
    Coincides with `decode (bs.drop O) = some (.bytes data, tail)`. Plus `byteCopyChainCR_none`.
  - ✅ **Step 24 — scalar register-spill into region** (`ScalarSpillIter.lean` / `ScalarSpillChain.lean` /
    `UnifiedFieldScalarStoreRegion.lean`). One spill block `SB x14,x11,0 ⨾ SRLI x11,8 ⨾ ADDI x14,1` writes a
    LE byte; `spillChainCR`/`rlp_spill_chain_spec` unroll N blocks (`spillRange`); `unified_field_scalar_store_region`
    sets up `x14 := outBase+di0` then spills the value into the shared output `bytesRegion` (scalar analog of
    `unified_field_bytes_copy`). Plus `singleton_disjoint_spillChainCR`.
  - ✅ **Step 25 — full scalar field decode-and-store into region** (`UnifiedScalarFieldRegion.lean`).
    **`unified_scalar_field_decode_and_store_region`** = `unified_scalar_field_decode` (→ x11 = value) ⨾
    `unified_field_scalar_store_region` (peel `regOwn x14`); spills the u64 LE into the output region at `di0`.
    Coincides with `decodeScalar`. Plus `spillChainCR_none`. (Scalar and byte-array fields now share ONE
    whole-struct output `bytesRegion` — only `outBase` aligned.)
  - ✅ **Step 26 — `regOwn`-pre byte-array variant** (`UnifiedBytesFieldRegOwn.lean`).
    **`unified_bytes_field_decode_and_copy_at_regOwn`**: the byte-array unit with `x5/x10/x11/x12` peeled to
    `regOwn` (via `cpsTripleWithin_of_forall_regIs_to_regOwn`), so it is callable after a prior field clobbered
    the scratch — the chaining prerequisite, mirroring `unified_scalar_field_decode_and_store_at_regOwn`.
  - ✅ **Step 27 — heterogeneous two-field walk** (`UnifiedHeteroFieldWalk.lean`). **`unified_hetero_field_walk`**:
    scalar field A (`unified_scalar_field_decode_and_store_region`, concrete pre) ⨾ byte-array field B
    (`unified_bytes_field_decode_and_copy_at_regOwn`, `regOwn` pre), through ONE shared output `bytesRegion`
    threaded directly (A's `spillRange` is B's input region → final `copyRangeGen (spillRange …) …`), A's `x13`
    feeding B's pointer with no glue. The first mixed scalar+byte-array RLP decode — keystone tying the two
    field-type decoders together. Disjointness via a clean global range split (`a < base+280` ⇒ unit B `none`,
    else unit A `none`, reusing `spillChainCR_none`/`byteCopyChainCR_none`), avoiding leaf×leaf blowup. Plus
    `spillRange_length`.
  - ✅ **Step 28 — three-field heterogeneous walk** (`UnifiedThreeFieldWalk.lean`): scalar ⨾ scalar ⨾
    byte-array, integration test for the regOwn scalar variant + range disjointness.
  - ✅ **Step 29 — reusable code-range disjointness** (`FieldUnitDisjoint.lean`): `codeReq_disjoint_of_ranges`
    + per-unit `scalarRegionUnitCR`/`bytesUnitCR` + `…_none_above/_below`.
  - ✅ **Step 30 — canonical units** (`UnifiedScalarFieldRegionCanonical.lean`): `x5,x10,x11,x12,x15` all
    `regOwn` (peel `x15`; the bytes→scalar boundary fix).
  - ✅ **Step 31 — fully-canonical units** (`UnifiedFieldUnitFullyCanonical.lean`): `x14` also `regOwn` — a
    fully uniform scratch interface (pre/post differ only in `x13` + output region).
  - ✅ **Step 32 — N-field heterogeneous fold** (`SchemaFold.lean`). **`schema_walk`**: decode an arbitrary
    `List FieldSpec` (scalar | byte-array, any order) into one shared output region. Definitions
    (`fieldSize/Steps/Enc/CR/Update`, `schemaSize/Steps/Enc/Out/CR`, `schemaINV`, `SchemaValid`,
    `schemaDecodes`), length preservation, `schemaCR_none_above/_below`/`…_disjoint…`, a kind-generic
    `field_step`, and the list-induction fold. The generic engine: concrete decoders are now instantiations.
  - ✅ **Step 33 — canonical units** (`UnifiedScalarFieldRegionCanonical.lean`): scalar + byte-array
    units with `x5,x10,x11,x12,x15` all `regOwn` (peel `x15`; fixes the byte-array→scalar boundary).
  - ✅ **Step 34 — fully-canonical units** (`UnifiedFieldUnitFullyCanonical.lean`): `x14` also `regOwn`
    — a fully uniform scratch interface (pre/post differ only in `x13` + output region).
  - ✅ **Step 35 — N-field heterogeneous fold** (`SchemaFold.lean`, `schema_walk`): decode an arbitrary
    `List FieldSpec` into one shared output region; the generic engine (see step 32 entry for contents).
  - ✅ **Step 36 — concat instantiation helper** (`SchemaFoldConcat.lean`): `schemaValid_of_concat` derives
    `SchemaValid` from one `bs.drop O = schemaEncBytes specs ++ tail` fact + per-field core validity; plus a
    concrete 3-field cross-check.
  - ✅ **Step 37 — RLP-list schema decoder** (`SchemaListWalk.lean`, `list_schema_walk`): descend one list
    level (`unified_list_header_descend`) ⨾ `schema_walk` — the shape every tx/header takes. The descend's
    post matches `schemaINV`'s order, so the bridge is a positional scratch weaken + `x13` rewrite (`hptr`).
  - ✅ **Step 38 — short-list convenience** (`SchemaListWalkShort.lean`, `short_list_schema_walk`): for a
    short list (`0xc0..0xf7`) the payload is at `O+1` and `regionLongWindow` is vacuous — discharged from
    `classifyPrefix (bs[O]) = .shortList`.
  - ✅ **Step 39 — long-list variant** (`SchemaListWalkLong.lean`, `long_list_schema_walk`): the real
    tx/header form (`0xf8..0xff`); payload at `(O+1)+lenOfLen`, window discharged from `hwin` + a
    "length bytes fit" bound.
  - ✅ **Step 40 — concrete end-to-end cross-check** (`SchemaListDecodeExample.lean`): decodes the short RLP
    list `[0xc4,0x2a,0x82,0x01,0x02]` through the full pipeline with zero bespoke proof.
  - **🎯 RLP decoder core COMPLETE & validated.** The generic engine decodes any short/long-list RLP value
    of mixed scalar|byte-array fields (any order) into a unified output `bytesRegion`, coinciding
    field-by-field with the pure spec (`schemaDecodes`).
  - **🎯 Target = legacy transaction (9 fields).** The generic engine is done; the field-type primitives
    are being lifted so a real `LegacyTransaction` (heavy `u256`, empty `to`/zero scalars, variable `data`)
    becomes decodable. Roadmap (one PR each): `n=0` empty scalar → `u256` wide scalar → assemble legacy-tx
    schema (`data ≤ 55` v1) → long byte arrays `> 55`.
  - ✅ **Step 41 — `n=0` empty scalar field** (`UnifiedScalarFieldZero.lean`,
    `unified_scalar_field_decode_and_store_zero`): a scalar `0` is the empty string `[0x80]`; the header
    descent already lands `x13` at the next field (empty payload), so the unit is just descend ⨾
    `SD rOut, x0, offset` (store 0, no read loop). Coincides with `decodeScalar (bs.drop O) = some (0, tail)`.
    Removes the `1 ≤ data.length` floor for zero-valued fields.
  - ✅ **Step 42 — `u256` wide scalar field** (`UnifiedWideScalarField.lean`,
    `unified_wide_scalar_field_decode_and_copy`): lifts the scalar ceiling from 8 to 32 bytes with NO
    multi-limb arithmetic. A `u256` payload is `≤ 32` bytes, so it rides the byte-array copy unit (proven
    `≤ 55`): copy the raw big-endian payload into the output region (contiguous, advancing `x14`). The
    scalar VALUE coincidence is free — `decodeScalar` reads the decoded item's bytes as a big-endian
    natural with no minimality check — so `decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail)`
    follows directly from the copy unit's `decode` coincidence. Output holds the field's minimal BE bytes;
    fixed 32-byte zero-padding (if a struct wants it) is a presentation step at assembly.
  - ✅ **Step 43 — scalar-value view of a schema decode** (`SchemaScalarValues.lean`): adds the missing
    forward bridge `decodeScalar_of_decode_bytes` (a byte-string decode determines its payload's BE value —
    `decodeScalar` applies no minimality check) and lifts it over a whole schema:
    `schemaDecodes ⇒ schemaScalarValues`, recovering EVERY field's numeric value whether it was decoded as a
    scalar or a byte array. Spec keystone letting the all-byte-array `schema_walk` act as a `u256`-field
    decoder (a legacy tx's `nonce/value/v/r/s` ride the byte-array path per step 42).
  - ✅ **Step 44 — long byte arrays `> 55`** (`UnifiedLongBytesField.lean`,
    `unified_long_bytes_field_decode_and_copy` + `bytes_item_payload_window_long`): RLP long-string form
    (`0xB8..0xBF`). The single-item decoder already handles the long header (`itemPtrRegion`/`itemLenRegion`
    `longBytes` branches) and the byte-copy leaf is length-generic, so the only new ingredient is the long
    payload-window lemma (payload pointer `= regionBase + ofNat(off+1+lenOfLen)`, recovered length
    `= data.length`, region `= data ++ tail`); composition then mirrors the short unit. Covers calldata and
    the 256-byte `logsBloom`. (No concrete `example`: `Nat.toBytesBE` doesn't reduce under `decide`.)
  - **🔀 Output-layout fork (needs maintainer input).** All four field-type primitives now exist (`n=0`,
    `u256`, address/hash bytes, long bytes) plus the scalar-value view. The remaining ASSEMBLY forks on how
    decoded fields are laid out: (a) **contiguous variable-width** (each field's minimal BE payload
    concatenated — what `schema_walk` already produces; cheap), or (b) **fixed-width 32-byte slots**
    (canonical EVM words; needs a new zero-pad-with-runtime-offset primitive). The choice should match the
    target tx-struct ABI (`EvmAsm/EL/Transaction.lean`, `EvmAsm/Stateless/Transaction/Decode.lean`). Also
    still needs: engine field-kinds so `n=0`/empty + wide-scalar fields integrate into `schema_walk`
    (currently `SchemaValid` requires `1 ≤ data.length` and `≤ 8` for scalar kind).
  - ✅ **Step 45 — fully-canonical long byte-array unit** (`UnifiedLongBytesFieldCanonical.lean`):
    the `_at_regOwn` → `_canonical` → `_fully_canonical` peeling chain for the `> 55`-byte unit, paralleling
    the short chain (the long unit has the identical scratch pre/post/CR/step shape, so each layer mirrors
    mechanically). Endpoint `unified_long_bytes_field_decode_and_copy_fully_canonical` has the uniform
    all-`regOwn` interface `schema_walk` consumes — the prerequisite for integrating `> 55`-byte fields into
    the schema engine.
  - ✅ **Step 46 — long bytes integrated into the schema engine** (`SchemaFold`/`SchemaFoldConcat`):
    `field_step` now dispatches short (`≤ 55`) vs long (`> 55`) byte-array units on `data.length` (both share
    `fieldSize`/`fieldCR`/`fieldUpdate`, so the conclusion is uniform), and the `SchemaValid`/`fieldCoreValid`
    bytes condition drops the `≤ 55` cap (keeps `1 ≤ len` and `(encode …).length < 256^8`). `schema_walk` /
    `long_list_schema_walk` now decode arbitrarily-long byte fields (calldata, the 256-byte `logsBloom`) with
    NO `FieldSpec` or CR change — all downstream decoders/examples rebuild unchanged.
  - ✅ **Step 47 — end-user decode-to-field-VALUES API** (`SchemaDecodeValues.lean`):
    `decode_encoded_{short,long}_list_schema_values` — the encoded-list decoders wrapped with
    `schemaDecodes_imp_scalarValues`, so the conclusion is `schemaScalarValues` (every field's big-endian
    value at its input offset, uniformly). The one-shot API behind the concrete tx/header decoders: RLP
    bytes in → operational decode + all field values out, verified.
  - **🚧 Empty (`n=0`) field support (in progress).** Closing the last gap so the engine decodes every
    valid RLP field (zero scalars, empty `to`). Minimal-disruption design: keep `FieldSpec.isScalar : Bool`,
    detect empty by `data = []`, dispatch data-dependently — only `SchemaFold`/`SchemaFoldConcat`/
    `FieldUnitDisjoint` change; downstream rebuilds unchanged.
  - ✅ **Step 49 — empty-scalar region unit** (`UnifiedEmptyScalarField.lean`,
    `unified_empty_scalar_field_decode_and_store_region`): region analog of the cell-based n=0 unit — descend
    `0x80` (`x13 → next`, `x11 = 0`) ⨾ scalar store-region leaf spilling `0` (`spillRange out 0 di 8`).
    `fieldSize = 248` (32 B shorter than the non-empty scalar unit; no read loop). Coincides with
    `decodeScalar (bs.drop O) = some (0, tail)`.
  - ✅ **Step 50 — empty-scalar canonical chain + `emptyScalarUnitCR`** (`UnifiedEmptyScalarFieldCanonical.lean`
    + `FieldUnitDisjoint.lean`): the `_at_regOwn` → `_canonical` → `_fully_canonical` peeling chain (mirrors
    the non-empty scalar chain — identical pre/post shape) to the uniform `regOwn` interface with CR
    `emptyScalarUnitCR`, plus the CR def + `empty_scalar_unit_cr_none_{above,below}` (range `[base, base+248)`).
    The empty-scalar unit is now fold-ready.
  - ✅ **Step 51 — empty-bytes region unit** (`UnifiedEmptyBytesField.lean`,
    `unified_empty_bytes_field_decode_and_copy`): descend `0x80` ⨾ byte-copy leaf with `N = 0` (copies
    nothing; `copyRangeGen out [] 0 di 0 = out`). Same statement shape as the non-empty bytes unit at
    `data = []`; `fieldSize = 152`. Coincides with `decode (bs.drop O) = some (.bytes [], tail)`.
  - ✅ **Step 52 — empty-bytes canonical chain** (`UnifiedEmptyBytesFieldCanonical.lean`): the
    `_at_regOwn` → `_canonical` → `_fully_canonical` peeling chain (mirrors the non-empty bytes chain;
    reuses `bytesUnitCR … 0`, no new CR) to the uniform `regOwn` interface. Both empty units are now
    fold-ready.
  - ✅ **Step 53 — empty fields integrated into the schema engine** (`SchemaFold`/`SchemaFoldConcat`
    + `SchemaEmptyFieldExample.lean`): `fieldSize`/`fieldCR`/`fieldSteps` are now data-dependent for the
    scalar kind (empty → 248/`emptyScalarUnitCR`; non-empty → 280/`scalarRegionUnitCR`); `field_step`
    dispatches 4 ways (empty-scalar / scalar / empty-bytes / short|long bytes); `SchemaValid` &
    `fieldCoreValid` drop the `1 ≤ data.length` floor (non-empty branches re-derive `1 ≤ len` from
    `data ≠ []`); `fieldCR_none_{above,below}` gain the empty-scalar case. No `FieldSpec` structural change;
    all ~10 downstream walk/decoder/example files rebuilt unchanged. Concrete cross-check: a record whose
    first field is a zero scalar (`[0xc2,0x80,0x2a]`) decodes to values `0` and `42`.
  - **🎉 RLP decoder COMPLETE.** `schema_walk` / the end-user `decode_encoded_{short,long}_list_schema_values`
    APIs now decode EVERY valid RLP field type a transaction/header contains — `u64`/`u256` scalars,
    zero/empty scalars, 20-byte addresses, 32-byte hashes, arbitrarily-long byte arrays (calldata, the
    256-byte bloom), and empty `to` — into a shared output region, recovering every field's value, coinciding
    with the pure RLP spec. A concrete legacy-tx/header decoder is now a direct caller instantiation
    (output layout = caller-chosen field offsets). Remaining beyond the decoder: Phase 6 host-I/O pipeline
    (`read_input → decode → write_output`).
- **🎉 Phase 6 COMPLETE — RLP pipeline end-to-end.** The full top-level pipeline
  (`read_input → decode → write_output`) is proven: RLP bytes arrive via the host `read_input`
  syscall, are decoded into the output `bytesRegion`, and the result is committed to the host
  public-values stream via `write_output`, coinciding with the pure RLP spec
  (`schemaScalarValues`). Input-buffer contract = host-ABI precondition `bytesRegion inputBufBase
  privateInput`.
  - ✅ **Step 54 — read-input pointer hand-off** (`Phase6ReadDecode.lean`, `rlp_phase6_read_input_ptr`):
    composes the `read_input` Phase-4 wrapper (`rlp_phase4_read_input_len_spec_within_exact`) with
    `LD x13, x12, ptr_ptr_off`, loading the returned `inputBufBase` into `x13` (the decoder's input
    pointer). Out-cells end `(buf_base, input.length)`, `x13 = buf_base`; `inputBufBaseIs`/`privateInputIs`
    preserved.
  - ✅ **Step 55 — read ⨾ decode** (`Phase6ReadDecode.lean`, `rlp_phase6_read_and_decode`): composes the
    hand-off with `decode_encoded_short_list_schema_values`. From the host-ABI input contract
    (`inputBufBaseIs buf_base`, `privateInputIs input`, `bytesRegion buf_base input` at the aligned/readable
    buffer) with `input = encode (.list (schemaItems specs)) ++ tail`, the `read_input` syscall + `LD` +
    decoder run end to end: the record is decoded into `bytesRegion outBase (schemaOut out specs)` with
    `schemaScalarValues` recovered.
  - ✅ **Step 56 — `readBytes`↔`bytesRegion` bridge** (`Phase6WriteOutput.lean`,
    `getByte_of_bytesRegion` + `readBytes_of_bytesRegion`): the keystone of the write-half — when
    `bytesRegion base bs` holds, `readBytes base bs.length = bs` (reconciles byte-granular `readBytes` with
    the dword-packed region via `bytesRegion_dword_at` + `extractByte_packBytes` + an offset induction).
    Connects the decoder's `bytesRegion` output to what `write_output` (which uses `readBytes`) emits.
  - ✅ **Step 57 — `publicValues`-append framing** (`Phase6WriteOutput.lean`,
    `holdsFor_sepConj_publicValuesIs_appendPublicValues` + `compatibleWith_appendPublicValues`): the
    write-half analogue of `holdsFor_sepConj_memIs_setMem` — threads the host `write_output` append
    (`publicValuesIs vals → publicValuesIs (vals ++ extra)`) through a separation-logic frame.
  - ✅ **Step 58 — CPS-level `write_output` ECALL spec** (`Phase6WriteOutput.lean`,
    `ecall_write_output_spec_gen_within`): the t0=0x10 syscall as a `cpsTripleWithin 1`, folding in
    `readBytes_of_bytesRegion` so a held `bytesRegion ptr bs` (x11 = bs.length) emits exactly `bs`:
    `publicValuesIs old → publicValuesIs (old ++ bs)`. Mirror of `ecall_read_input_spec_gen_within`.
  - ✅ **Step 59 — `write_output` wrapper** (`Phase6WriteOutput.lean`, `rlp_phase6_write_output_prog`
    + `rlp_phase6_write_output_spec_within_exact`): the 4-instruction wrapper
    (`ADDI x10,rOut,0; LI x11,len; LI x5,0x10; ECALL`), mirror of
    `rlp_phase4_read_input_len_spec_within_exact`.
  - ✅ **Step 60 — `decode ⨾ write_output`** (`Phase6DecodeWrite.lean`, `rlp_phase6_decode_and_write`
    + reusable `rlp_phase6_write_output_spec_regOwn`): composes the short-list schema decoder with the
    write wrapper, committing the decoded output region (`publicValuesIs old → publicValuesIs (old ++
    schemaOut out specs)`). The decoder's `schemaINV` post exposes scratch as `regOwn`, so the write
    wrapper is first lifted to a `regOwn` pre; the leftover state is framed through. The CR
    disjointness is range-based (`codeReq_disjoint_of_ranges` + `schemaCR_none_above`) — `crDisjoint`
    /`seqFrame` time out / `whnf`-blow up on the opaque 36-instruction decoder `ofProg`. The reshape
    is `cpsTripleWithin_weaken … xperm_hyp` with a nested `refine` so the target is concrete before
    `xperm` runs (else `Q`/`Q'` are metavars). Concrete `[0xc4,0x2a,0x82,0x01,0x02] → 0x3000` example.
  - ✅ **Step 61 — full `read ⨾ decode ⨾ write` pipeline** (`Phase6Pipeline.lean`,
    `rlp_phase6_read_decode_write`): composes the read⨾decode unit (step 55) with the write wrapper —
    the complete top-level pipeline. From the host-ABI input contract the program runs `read_input` +
    `LD` + decoder + `write_output` in `(5 + (61 + schemaSteps)) + 4` steps, committing the decoded
    record to `publicValues` and recovering every field value. Concrete end-to-end example: the host
    supplies `[0xc4,0x2a,0x82,0x01,0x02]` at `0x2000`, decoded to `0x3000` and committed.
    Axiom-clean, 0 sorry, no `bv_decide`/`native_decide`, no heartbeat overrides.
### EL.4 Untrusted-input RLP decoders (#9373, in progress)
The Phase-1..6 decoder above assumes the input is a well-formed encoding (precondition
`bs = encode(...) ++ tail`). Issue #9373 wants decoders over **untrusted** input whose spec covers
both outcomes: valid RLP of the expected shape → success, else → **fail** (nonzero `a0`); plus
**specialized** per-shape decoders (header/tx/MPT) that **abort early** the moment a fixed-arity list
shows more elements than expected (no decode-then-count). Layering:
- **Phase A — pure rejection bridges (done).** `EvmAsm/EL/RLP/{ByteStringDecodeBridge,ListDecodeBridge,
  ReadLength,FullDecode}.lean` give per-class `…_eq_some_iff` AND `…_eq_none_of_*` characterizations
  (OOB length, leading-zero/`≤55` non-canonical long form, single-byte-not-wrapped, list leftover) — the
  verdicts a validating decoder discharges. The pure `decode`/`decodeFully`/`decodeScalar` already reject
  every invalidity class.
- **Phase B — RV64 validating decoders (in progress).** 2-exit `cpsBranchWithin` with `⌜decode = some…⌝`
  / `⌜decode = none⌝` posts and NO validity hypotheses; untrusted-length contract `x15 = L`
  (the codegen K20 model), a thin wrapper sets `a0`.
  - ✅ **B.1 — validating shortBytes (non-singleton)** (`UnifiedDecodeItemShortBytesValidated.lean`,
    `rlp_decode_shortBytes_validated`): handler ⨾ `BLTU x11, x15` bound check. Taken (`len < L`) ⇒
    `decode = some (.bytes …)`; fall ⇒ `decode = none` (truncated). `payloadLen ≠ 1` (singleton-canonical
    check vacuous).
  - ✅ **B.2 — validating singleByte** (`UnifiedDecodeItemSingleByteValidated.lean`,
    `rlp_decode_singleByte_validated`): a canonical single byte always decodes, so a single-exit
    `cpsTripleWithin` carrying `⌜decode = some (.bytes [pfx], rest)⌝`; full untrusted-decoder register/mem
    interface framed through the e1 handler. No failure case. Axiom-clean, concrete `0x42` example.
  - ✅ **B.3 — validating singleton (`0x81`)** (`UnifiedDecodeItemSingletonValidated.lean`,
    `rlp_decode_singleton_validated`): completes the shortBytes class (drops B.1's `hns`). Composes a
    bound check (`BGEU x11, x15` — truncation) with a canonical check (`LBU x12,x13,0 ; ANDI x10,x12,0x80 ;
    BEQ x10,x0` — the single payload byte must be `≥ 0x80`, else non-canonical) via
    `cpsBranchWithin_seq_cpsBranchWithin`, both failure routes converging on one `failPC` with
    `⌜decode = none⌝`, success at `e2_target + 24` with `⌜decode = some (.bytes (rest.take 1), rest.drop 1)⌝`.
    Sub-lemmas `singleton_B1` (handler⨾bound) / `singleton_B2` (canonical check, empty-payload vacuity via
    `holdsFor_pure`); new bit-reasoning `byte_lt_0x80_imp_and_zero` (converse of the existing
    `byte_zext_and_0x80_eq_zero_imp_lt`). No validity hypotheses. Axiom-clean, 0 sorry, no `bv_decide`,
    concrete `0x81 0xFF` example.
  - ✅ **B.4 — offset-general validating arms** (`UnifiedDecodeItemShortBytesValidatedAt.lean`, #9456):
    `rlp_decode_shortBytes_validated_at` / `rlp_decode_singleByte_validated_at` — the B.1/B.2 arms over an
    item at an arbitrary byte offset `O` (`x5=pfx`, `x13=regionBase+O`, `x15=`avail), full `bytesRegion`
    framed. Handlers are register-only so they transfer near-verbatim. Building block for the field walk.
  - ✅ **B.5 — taken-side sequencing combinator** (`ValidatingFieldWalk.lean`, #9457):
    `cpsBranchWithin_seq_cpsTripleWithin_taken` — sequences a triple onto the SUCCESS (taken) exit of a
    2-exit branch (keeping FAIL as the abort exit), CodeReq union. The dual of the existing fall-side
    combinator; needed because the validating arms put SUCCESS on the taken exit.
  - ✅ **B.6 — validating shortBytes decode-and-advance** (`ValidatingFieldWalk.lean`,
    `rlp_decode_shortBytes_advance_at`, #9461): B.4 ⨾[taken] `ADD x13,x13,x11` — one field step of the
    walk. SUCCESS advances the cursor `x13` to the next item start (`(regionBase+O)+1+payloadLen`) while
    carrying `⌜decode = some (.bytes …)⌝`; FAIL is the decoder's abort exit. ADD framed with the 8-atom
    complement incl. the pure verdict; reshaped with `xperm_hyp` (confirmed xperm handles a trailing
    pure atom — earlier "pure blocks xperm" diagnosis was wrong; the real fix was matching the decoder's
    exact 10-atom success post). Axiom-clean.
  - ✅ **B.6.1 — clean-form advance variant** (`rlp_decode_shortBytes_advance_at_clean`, #9461): SUCCESS
    `x13` restated as `regionBase + ofNat(O+1+payloadLen)` via the unconditional `advance_cursor_clean`
    identity (`BitVec.ofNat` is mod-`2^64`, no bound needed) — the precondition shape the next field's
    decoder consumes, so steps chain without `x13` glue.
  - ⏳ **Next (F1 chain) — DESIGN CONFIRMED, arithmetic de-risked.** Field-walk register discipline
    (chosen to reuse the merged length-discipline arms with NO extra `s_end` register): `x15` holds the
    remaining byte count `bs.length - O` and is recomputed **in place** between fields by
    `SUB x15,x15,x11 ; ADDI x15,x15,-1` (= `remaining - payloadLen - 1`), then `LBU x5,x13,0` loads the
    next prefix. Per-field step = validating decode-and-advance ⨾ x15-decrement ⨾ LBU-next. Last field
    takes no LBU; instead an **exact-arity end check** (`x13 = list_end`, i.e. `O' = bs.length`).
    Three foundational lemmas **proven** (scratch in job tmp, ready to drop in):
    (1) `advance_cursor_clean` (x13, landed); (2) `ofNat_sub_ofNat : b ≤ a → a < 2^64 →
    ofNat a - ofNat b = ofNat(a-b)` (toNat+omega); (3) x15 decrement `ofNat(L-O) - ofNat pl - 1 =
    ofNat(L-(O+1+pl))` (via (2) twice). Remaining: the SUB/ADDI/LBU RV64 specs framed into the
    post-advance state + composition + end check. Then longBytes (parked, T4); singleByte/singleton
    advance analogs. Then T1 (`rlp_field_to_u64`) → T2 (`withdrawal_decode`) → T3 (header) → T4 (tx_1559).
  - ✅ **B.7 — single-pass validated scalar read** (`ValidatingScalarRead.lean`,
    `rlp_decode_shortBytes_scalar_at`, #9483): the T1 core. Composes `rlp_decode_shortBytes_validated_at`
    (#9456) with the existing `unified_field_scalar_read` on the SUCCESS exit — the validating arm leaves
    exactly the read's register convention (`x13`=payload ptr, `x11`=len), so a `≤8`-byte scalar field is
    validated AND its value read in **one descent** (single-pass; no reparse). SUCCESS: `x11 =
    Nat.fromBytesBE payload`, `x13` advanced, verdict `⌜decodeScalar (bs.drop O) = some (value, …)⌝` via
    `decodeScalar_of_decode_bytes`; FAIL: decoder's abort exit. Needs `1 ≤ payloadLen ≤ 8` (the decoder's
    `a0=2` runtime check discharges it). Key reuse insight: for EXTRACTED fields the value-read advances
    `x13` itself, so the ADD-skip advance (B.6) is for DISCARDED fields (header gaps); extracted fields
    (all of withdrawal) use this read-advance. Axiom-clean; no `maxRecDepth`.
  - ✅ **B.8 — single-pass validated scalar decode-and-store** (`ValidatingScalarStore.lean`,
    `rlp_decode_shortBytes_scalar_store_at`, #9486): B.7 ⨾[taken] `SD rOut,x11,offset` — the per-field op
    a fixed-schema scalar decoder repeats. SUCCESS: output cell `outBase+offset` = `Nat.fromBytesBE
    payload`, verdict `decodeScalar (bs.drop O) = some (value, …)`; FAIL: abort, slot untouched. `rOut` =
    callee-saved output base (distinct from `x5/x10..x15`). Mirrors valid-input
    `unified_scalar_field_decode_and_store` onto the validating taken exit. Axiom-clean.
  - ⏳ **Next (T1 `rlp_field_to_u64`)**: walk-to-field-`i` (iterate the validating advance over fields
    `0..i-1`, validating each, via the x15-decrement + LBU-next glue from #9477) → `rlp_decode_shortBytes_
    scalar_at` at field `i` → runtime `payloadLen ≤ 8` check (`a0=2`) → `SD` store value to `*a3` → F2 LP64
    wrapper. Then T2 `withdrawal_decode` (4 consecutive scalar/address fields, exact-arity).
  - ✅ **B.9 — validating shortList descend** (`UnifiedDecodeItemShortListValidated.lean`,
    `rlp_decode_shortList_validated_at`, #9489): the LIST GATEWAY. shortList (`0xc0..0xf7`) analog of the
    shortBytes arm — e4 handler ⨾ `BLTU x11,x15` bound. SUCCESS (`payloadLen < L`): `x13`=payload start,
    `x11`=payload length, `⌜takeBytes rest payloadLen = some (rest.take pl, rest.drop pl)⌝` (so with the
    shortList Phase-A bridge `decode` reduces to decoding the window as a list); FAIL: `⌜decode = none⌝`.
    Canonical-clean (length in prefix), so bound check alone validates. Axiom-clean.
  - ⏳ **Next (T2 assembly)**: descend (#9489) → 4× scalar/address field-stores (#9486) within the list
    payload (chained via x15-decrement+LBU-next #9477) → exact-arity end check (`cursor = list_end`) →
    F2 LP64 wrapper → coincidence to `decodeWithdrawal` (#9487). Also needs an address (20-byte fixed)
    field-store variant alongside the scalar one. longList descend (canonical len-of-len check) deferred
    to header/tx targets.
  - 🔑 **SINGLE-PASS directive** (maintainer @pirapira, PR #9461): the emitted program must walk the
    input **once** — validate AND copy out values in the same sweep, NOT validate-then-reparse. So each
    field-step is `validate-item → store-its-value → advance-cursor`. The validating arm already yields
    the payload location (`decode (bs.drop O) = some (.bytes (rest.take payloadLen), …)` ⇒ payload =
    `payloadLen` bytes at `cursor+1`), so the store copies straight from that window (reuse
    `ByteCopyIter`/scalar-store machinery) with no second decode; accumulated `⌜decode … = some …⌝`
    verdicts tie the stored bytes to the pure spec from one traversal. **DROP** the "establish
    `SchemaValid` then run `schema_walk` to extract" framing — `schema_walk`/`schemaScalarValues` remain
    only the **pure coincidence target** the single-pass output is proven equal to, not a runtime 2nd
    pass. So the per-field STORE step is inserted between validate and advance in the chain above.

- **Host I/O ABI**: See `docs/zkvm-host-io-interface.md`; SP1
  `HINT_LEN`/`HINT_READ`/`COMMIT` are legacy handler shapes, not the target
  C ABI.
- **Output format**: Pointer + length (zero-copy into input buffer)
- **Depends on**: EL.1 (spec to verify against), EL.2 (byte-level specs)

### EL.5 Codegen-guest RLP drop-in replacements (in progress, bead `evm-asm-cmz21`)

The codegen stateless guest links several RLP decode helpers emitted as raw
assembly **strings with no proofs** (`EvmAsm/Codegen/Programs/RlpWalk.lean`:
`rlp_walk_init`, `rlp_walk_next`, `rlp_content_to_u64`, `rlp_content_to_u256_be`;
plus `RlpRead.lean` / `Tx.lean` index-based helpers). This track replaces them,
one routine at a time, with verified `Program`s carrying **caller-facing**
Hoare triples: LP64 register I/O, where the output is located, and — crucially —
what the output memory region may hold **on failure** (`memOwn`, i.e. arbitrary
content; callers must not read it). Each verified body matches the guest's
calling convention so it is a literal drop-in.

- ✅ **`rlp_content_to_u64`** (`EvmAsm/Rv64/RLP/ContentToU64.lean`): verified
  22-instruction canonical-strict drop-in body `rlp_content_to_u64_prog`, all
  four paths proved (too-long / non-canonical / empty / success) and combined
  into the unified dispatch `rlp_content_to_u64_spec_within`. **Bridged into
  Codegen**: `rlpContentToU64Function` (`EvmAsm/Codegen/Programs/RlpWalk.lean`)
  now emits `rlp_content_to_u64_prog` via `emitProgram`, with a kernel-checked
  `rfl` drift guard (`rlpContentToU64Function_eq_verified_prog`) tying the
  Codegen string to the verified body. Status `a1`: `0` ok / `2` too long
  (`len > 8`) / `3` non-canonical (`0 < len ≤ 8 ∧ content[0] = 0`) — the
  canonical-strict status `3` is new vs. the old lenient hand-written string.
  Axiom-clean (3 classical), 0 sorry. First bridge from verified `Rv64.RLP`
  code into Codegen; `rlp_content_to_u256_be` is the natural next target.

- ✅ **`rlp_content_to_u256_be`** (`EvmAsm/Rv64/RLP/ContentToU256Be.lean`):
  faithful 26-instruction canonical-strict drop-in body
  `rlp_content_to_u256_be_prog`, all four paths proved (too-long /
  non-canonical / empty / success) and combined into the unified dispatch
  `rlp_content_to_u256_be_spec_within` (bound `7*len+16`). **Bridged into
  Codegen**: `rlpContentToU256BeFunction` (`EvmAsm/Codegen/Programs/RlpWalk.lean`)
  now emits `rlp_content_to_u256_be_prog` via `emitProgram`, with a
  kernel-checked `rfl` drift guard
  (`rlpContentToU256BeFunction_eq_verified_prog`) tying the Codegen string to
  the verified body. Status `a0`: `0` ok / `2` too long (`len > 32`) / `3`
  non-canonical (`0 < len ≤ 32 ∧ content[0] = 0`) — the canonical-strict
  status `3` is new vs. the old lenient hand-written string, which silently
  right-aligned leading-zero scalars. Axiom-clean (3 classical), 0 sorry. This
  completes both cursor-walk content helper bridges (`u64`, `u256` here);
  larger caller verification (transaction/header decoders) remains follow-up
  work.

- ✅ **`rlp_walk_next`** (`EvmAsm/Rv64/RLP/WalkNext.lean`): verified 103-instruction
  drop-in (`rlp_walk_next_prog`), all 18 reachable paths proved as leaf `cpsTripleWithin`
  triples, combined into the unified dispatch `rlp_walk_next_spec_within` (bound `87`).
  Status `a1`: `0` ok / `2` end-of-list / `3` bound / `4` non-minimal / `5` leading-zero /
  `6` non-canonical single byte. The `a1 = 0` outcome is the pure predicate `rlpWalkNextOk`
  over `rlpItemDecode` (canonical decode + **per-form overflow-safe fit** conjuncts matching
  the program's `endPtr − cursor` subtraction checks). **Every** non-`0` status carries
  `⌜¬ ∃ next len, rlpItemDecode …⌝` (no canonical item is consumable): `4/5/6` via the
  canonicality conjuncts, `3` via the fit conjuncts (each the exact negation of a bound
  check). The bound checks are overflow-robust (`avail = endPtr − cursor` subtraction, not
  `cursor + span` addition which can wrap for long forms with `dec` up to `2^64−1` — see
  the `rlp-walk-next-fit-per-disjunct` note). Axiom-clean (3 classical), 0 sorry, EEST
  200/200 spike. (Beads `evm-asm-enb37` unified theorem; `evm-asm-rpeko` overflow-robust
  bound + `a1=3` ¬∃.)

- ✅ **Codegen drift accounting complete for all four cursor-walk helpers**:
  `rlpWalkInitFunction` and `rlpWalkNextFunction` (`EvmAsm/Codegen/Programs/RlpWalk.lean`)
  now carry the same kernel-checked `rfl` drift guards as the two content
  helpers above (`rlpWalkInitFunction_eq_verified_prog`,
  `rlpWalkNextFunction_eq_verified_prog`), tying the emitted strings to
  `rlp_walk_init_prog` / `rlp_walk_next_prog`. `rlpWalkHelpersClosure_eq_helpers`
  ties the four-helper closure to the four guarded definitions, so a future
  edit cannot quietly swap one out unnoticed. This is Codegen drift
  accounting only — no new Hoare proofs; caller verification
  (transaction/header decoders) and index-based helper replacement remain
  follow-up work.

- ✅ **Codegen consumers route through `rlpWalkHelpersClosure`**: every Codegen
  `Programs/*.lean` site that previously concatenated the four cursor-walk
  helpers (`rlpWalkInitFunction ++ rlpWalkNextFunction ++ rlpContentToU64Function
  ++ rlpContentToU256BeFunction`) by hand now uses the guarded
  `rlpWalkHelpersClosure` instead (`BlockVerdictV2.lean`, `HeaderDecode.lean`
  second site, `SeedTxAccessList.lean`, `Tx.lean`, `TxDecode.lean`,
  `TxDecode1559.lean`, `TxDecode2930.lean`, `TxDecode4844.lean`,
  `TxDecode7702.lean`). Intentional partial-helper sites are unchanged (e.g.
  `HeaderDecode.lean`'s first site only needs init/next/u64, not u256). This is
  a behavior-preserving Codegen composition refactor, not a new Hoare proof:
  future helper drift among these four is now caught in one place by
  `rlpWalkHelpersClosure_eq_helpers`.

- ⏳ **`rlp_field0_to_u64` call-composition slice** (`EvmAsm/Rv64/RLP/Field0ToU64.lean`):
  first caller-level verification step composing the cursor-walk leaves
  (`rlp_walk_init`, `rlp_walk_next`, `rlp_content_to_u64`) into a small wrapper
  that decodes RLP list field 0 as a canonical `u64`, exercising the WP
  call-composition machinery (`WP.cpsCallWithin`) for the first time in this
  repo. Lands the wrapper `Program` + fixed-offset code layout (wrapper at
  `base`, `rlp_walk_init` at `base+0x100`, `rlp_walk_next` at `base+0x300`,
  `rlp_content_to_u64` at `base+0x600`) with pairwise disjointness lemmas, and
  a proved success-path theorem
  (`rlp_field0_to_u64_content_call_success_spec_within`) composing the
  `jal ra, rlp_content_to_u64` call after a hypothetical post-`rlp_walk_next`-
  success state, concluding status `0` and the decoded `Nat.fromBytesBE`
  value. Axiom-clean, 0 sorry. **Remaining work** (bead `evm-asm-zvgxe`, P0):
  lift the `rlp_walk_init`/`rlp_walk_next` calls the same way and combine with
  the two failure branches into one unified `rlp_field0_to_u64_spec_within`
  top theorem with a 4-way disjunctive postcondition. Does **not** yet replace
  Codegen's unverified `rlp_field_to_u64` (`EvmAsm/Codegen/Programs/Tx.lean`).

---

## Roadmap: Phases 7-11 (STF — State Transition Function)

The STF is the end goal. It takes a block (header + transactions) and the
pre-state, executes all transactions, and produces the post-state. The STF
is what gets proved inside the zkVM.

### STF Architecture

The STF decomposes into layers (from the execution-specs):

```
state_transition(block, pre_state) → post_state
  └── apply_body(block_header, transactions, ommers)
        └── for each tx: process_transaction(env, tx)
              └── process_message_call(message)
                    └── execute(env) — the interpreter loop
                          └── for each step: dispatch opcode → handler
```

In our RV64 implementation, this maps to:

```
main():  read_input → Block + pre_state
         call state_transition
         write_output → post_state_root
```

### Phase 7: Interpreter Loop (EVM execution core)

This is the heart of the STF — the inner loop that executes EVM bytecode.

#### 7.1 EVM Machine State
- **File**: `Evm64/EvmState.lean` (new)
- **Approach**: Define the EVM-level execution state in RISC-V memory:
  ```
  struct EvmState {
    pc      : u64       // EVM program counter (byte offset into code)
    gas     : u64       // Remaining gas
    sp      : u64       // Stack pointer (already x12)
    memory  : *u8       // EVM memory base pointer
    memsize : u64       // Current memory size
    code    : *u8       // EVM bytecode pointer
    codelen : u64       // Code length
    env     : *u8       // Environment context pointer
    status  : u64       // Running / Stopped / Reverted / Error
  }
  ```
  Define `evmStateIs` assertion combining all sub-assertions.

#### 7.2 Opcode Dispatch
- **File**: `Evm64/Dispatch.lean` (new)
- **Approach**: Read `code[evm_pc]` byte, dispatch to handler.
  **Option A**: Jump table — load handler address from table[opcode], JAL.
  **Option B**: Binary search tree of BEQ comparisons.
  Jump table is faster (O(1)) but needs 256-entry table in memory.
  Binary search is smaller but O(log n).
  **Recommendation**: Jump table. 256 × 8 = 2048 bytes, small for zkVM.
- **Spec**: `dispatch_spec` relates opcode byte to correct handler entry point.

#### 7.3 Opcode Handlers (subroutine wrappers)
- **File**: `Evm64/Handlers.lean` (new)
- **Calling convention**: Use LP64 convention from `CallingConvention.lean`.
  Each handler is a non-leaf function using `cc_prologue` / `cc_epilogue`.
  Compose with `callNear_function_spec` / `nonleaf_function_spec`.
- **Approach**: Each handler is a thin wrapper:
  1. Deduct gas cost
  2. Call the opcode subroutine (e.g., `evm_add`) via `JAL x1, offset`
  3. Advance EVM PC by appropriate amount (1 for most, 1+n for PUSHn)
  4. Return to dispatch loop via `cc_ret`
- **Spec**: Each handler spec composes gas deduction + opcode spec + PC advance.

#### 7.4 Interpreter Main Loop
- **File**: `Evm64/Interpreter.lean` (new)
- **Approach**: RISC-V loop:
  ```
  loop:
    LBU opcode, code_base[evm_pc]    // read current opcode
    // dispatch to handler via jump table
    LD  handler, table[opcode * 8]
    JALR ra, handler
    // handler returns here
    // check status: if still running, loop
    BEQ status, RUNNING, loop
    // else: halt (STOP/RETURN/REVERT/ERROR)
  ```
- **Spec**: Inductive spec relating N EVM steps to N iterations:
  `interpreter_step_spec`: one iteration preserves EVM state invariant.
  `interpreter_N_spec`: N iterations = N EVM instruction executions.
- **Key invariant**: At each loop entry, the RISC-V state correctly
  represents the EVM state (stack, memory, PC, gas, status).
- **Proof strategy**: Define simulation relation between EVM abstract state
  and RISC-V concrete state. Prove each opcode handler preserves the
  simulation. Then the loop preserves it inductively.

### Phase 8: Storage & System Calls

#### 8.1 Storage Model (via host syscalls)
- SLOAD/SSTORE use ECALL to communicate with the zkVM host.
- The host provides storage read/write as part of the witness.
- **Spec**: Abstract storage as `Map U256 U256`. SLOAD returns `storage[key]`,
  SSTORE updates `storage[key] := value`.

#### 8.2 Precompiles (via zkvm_accelerators)
- The canonical C ABI is the vendored header
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`
  (eth-act zkvm-standards). See
  [`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md)
  for the ADR; per-function bridge progress (input/output Lean payload types,
  syscall ID, Hoare-triple bridge spec) is tracked in beads parent
  `evm-asm-nr2sk`.
- Map EVM precompile addresses (0x01-0x11, 0x100) to `zkvm_accelerators.h` calls.
- ECRECOVER (0x01) → `zkvm_secp256k1_ecrecover`
- SHA256 (0x02) → `zkvm_sha256`
- RIPEMD160 (0x03) → `zkvm_ripemd160` — **DONE** (pure-software RV64 kernel,
  `Ripemd160.lean` — ZisK has no RIPEMD-160 accelerator; table-driven
  two-line compression, ~5.3k steps/64-byte block; 600+120/word gas,
  32-byte left-padded returndata; validated against the standard vectors
  via `scripts/codegen-zisk-ripemd160-check.sh`; bead fhsxz.2.4.2.62.11)
- IDENTITY (0x04) → no accelerator (pure memory copy)
- MODEXP (0x05) → `zkvm_modexp`
- BN254_ADD (0x06) → `zkvm_bn254_g1_add` — **DONE** (real kernel,
  `Bn254Field.lean`/`Bn254Curve.lean`, ZisK Bn254CurveAdd/Dbl `csrs
  0x806/0x807` + Arith256Mod `csrs 0x802` accelerators; EIP-196 validation +
  EIP-150 child-allotment failure gas; bead fhsxz.2.4.2.62.10)
- BN254_MUL (0x07) → `zkvm_bn254_g1_mul` — **DONE** (same backend; raw
  256-bit double-and-add, ~0.93M ziskemu steps worst case)
- BN254_PAIRING (0x08) → `zkvm_bn254_pairing` — **DONE** (py_ecc-mirroring
  FQ12 Miller loop + final exponentiation: `Bn254Fp2.lean` via
  Bn254ComplexAdd/Sub/Mul `csrs 0x808/0x809/0x80a`, `Bn254Fq12.lean` poly
  machine with one fused Arith256Mod per coefficient op,
  `Bn254Fq12Point.lean`/`Bn254PairingCore.lean`/`Bn254Pairing.lean` with the
  real EIP-197 G2 subgroup check; ~40M steps + ~22M/pair; bead
  fhsxz.2.4.2.62.10.1)
- BLAKE2f (0x09) → `zkvm_blake2f`
- KZG_POINT_EVAL (0x0a) → `zkvm_kzg_point_eval`
- BLS12_G1_ADD (0x0b) → `zkvm_bls12_g1_add` — **DONE** (real kernel,
  `Bls12G1.lean`, ZisK Bls12_381CurveAdd/Dbl + Arith384Mod; PR #8739)
- BLS12_G1_MSM (0x0c) → `zkvm_bls12_g1_msm` — **DONE** (LE-internal
  double-and-add + REAL order-n subgroup check; 128-pair MSM ~14.8M
  steps after PR #8741)
- BLS12_G2_ADD (0x0d) → `zkvm_bls12_g2_add` — **DONE** (software Fp2
  chord/tangent over the complex accelerators + Fermat inverse,
  `Bls12G2.lean`; PR #8740)
- BLS12_G2_MSM (0x0e) → `zkvm_bls12_g2_msm` — **DONE** (same backend)
- BLS12_PAIRING (0x0f) → `zkvm_bls12_pairing` — **DONE** (py_ecc-
  mirroring FQ12 = Fp[w]/(w^12-2w^6+2) Miller loop on fused Arith384Mod,
  `Bls12Fq12.lean`/`Bls12Pairing.lean`; real subgroup checks both sides;
  EEST 88/88; PR #8745)
- BLS12_MAP_FP_TO_G1 (0x10) → `zkvm_bls12_map_fp_to_g1` — **DONE**
  (SSWU + 11-isogeny + accelerated cofactor clear, `Bls12Map.lean`;
  EEST 77/77 with 0x11; PR #8745)
- BLS12_MAP_FP2_TO_G2 (0x11) → `zkvm_bls12_map_fp2_to_g2` — **DONE** (same file, 3-isogeny)
- secp256r1_verify (0x100) → `zkvm_secp256r1_verify`
- Non-precompile accelerators reused by EVM opcode handlers: `zkvm_keccak256`
  (KECCAK256 opcode, §8.3), `zkvm_secp256k1_verify` (transaction signature
  verification).

#### 8.3 KECCAK256 (via accelerator)
- Pop offset+size, hash EVM memory region.
- Delegates to `zkvm_keccak256` accelerator.
- Spec: result = keccak256(memory[offset..offset+size]).

#### 8.4 LOG0-LOG4
- Pop offset+size (+topics), emit log event via ECALL.

#### 8.5 CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2
- Create child EVM frames. Model as recursive interpreter calls or
  host-delegated syscalls.
- RETURN and REVERT halt the current frame with output data.

### Phase 9: Gas Metering

#### 9.1 Static Gas
- Each opcode deducts a fixed gas cost before execution.
- Out-of-gas → halt with error, revert state.

#### 9.2 Dynamic Gas
- Memory expansion: quadratic cost based on memory high-water mark.
- Storage: cold/warm access costs (EIP-2929).
- CALL gas: 63/64 rule, stipend for value transfers.

### Phase 10: Transaction Processing

#### 10.1 Message Call
- **File**: `Evm64/MessageCall.lean` (new)
- **Approach**: Set up EVM execution frame:
  1. Initialize EVM state (code, calldata, gas, value, caller)
  2. Run interpreter loop to completion
  3. Handle output (RETURN data, REVERT, error)
  4. Apply state changes (storage writes, balance transfers)
- **Reference**: `execution-specs/.../vm/interpreter.py:process_message_call`

#### 10.2 Transaction Validation & Execution
- **File**: `Evm64/Transaction.lean` (new)
- **Approach**:
  1. Validate transaction (nonce, gas limit, balance)
  2. Deduct upfront cost
  3. Execute message call
  4. Refund remaining gas
  5. Pay priority fee to coinbase
- **Reference**: `execution-specs/.../fork.py:process_transaction`

### Phase 11: Block-Level STF

#### 11.1 Block State Transition
- **File**: `Evm64/StateTransition.lean` (new)
- **Approach**: The top-level STF function:
  1. Read block (header + transactions) from `read_input`
  2. Validate block header
  3. Process each transaction sequentially, updating world state
  4. Apply block rewards
  5. Compute post-state root
  6. Write post-state root via `write_output`
- **Reference**: `execution-specs/.../fork.py:state_transition`
- **Spec**: `state_transition_spec` proves that the RISC-V program computes
  the same post-state as the Python reference spec.

#### 11.2 World State Model
- Account state: nonce, balance, storage root, code hash
- State trie: delegated to host via ECALL (trie operations are zkVM-accelerated
  or proven separately)
- MPT proof verification: either inline or via host

#### 11.3 IO Integration
- `read_input`: Reads block data + pre-state witness (per zkvm IO standard)
- `write_output`: Writes post-state root (32 bytes) as public output
- The zkVM proves: "given this block and pre-state, the post-state root is X"

#### 11.4 Conformance Testing
- Run against Ethereum test vectors (ethereum/tests).
- Compare RISC-V execution results to reference Python execution.
- Use `decide` or extraction for executable tests.

---

## SAsm structured-assembly DSL (proof-scaling track)

Design: `docs/sasm-design.md`. Branch: `feat/structured-asm-dsl`.

A DSL over the WP framework for check-heavy routines (RLP/SSZ decode,
`run_stateless_guest`): structured control flow (`ite`/`when`/bounded
`while`/`call` via the C-like ABI), inline pre/post/invariant/mid-condition
annotations over an exposed register file, a flattener that synthesizes all
branch offsets and the per-function `CodeReq.ofProg` (no manual disjointness),
and a `vcgen` tactic that reduces a function spec to labeled *pure* VCs via a
structurally-recursive generator + one generic soundness theorem (recursion-
safe by construction). Milestones M1–M5 in the design doc; M1 = AST +
flattener, M2 = block symbolic engine + soundness, M3 = structural soundness
+ `vcgen`, M4 = calls, M5 = regions. **M1–M4 + M5a done** (M1–M3
2026-07-01, M4 + M5a 2026-07-02): AST/flattener, block engine + soundness,
generic Stmt.sound, Fn + vcgen, verified calls (FnHandle in the AST,
caller-shaped Stmt.soundR/Fn.SpecR via cpsCallWithin, Fn.toHandle leaf
packaging), and read-only byte regions (Region in Fn/FnHandle, LBU/LB in
the block engine with per-block .mem VCs, region-carrying asrtM triples,
RLP-prefix-classification demo over a symbolic input buffer), wider
read-only loads (LW/LWU/LD with aligned in-range VCs), and the **first
real port**: `readChainIdFn` (Stateless/SSZ/Decode/ChainIdSAsm.lean), a
fully verified `read_chain_id` reading byte-wise — the original's
misaligned LWU/LD trap under the Lean model (bug bead evm-asm-iwzun).
Remaining: M5b-2 (.rw regions + stores; ra-spill prologue for multi-level
call trees; LH/LHU), then more Stateless/SSZ ports.

## Stateless Guest (parallel STF track)

Full plan: `~/.claude/plans/please-cut-a-branch-warm-wand.md`.
Branch: `feat/run-stateless-guest-scaffold`.

Stakeholders asked for `run_stateless_guest`
(`execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py:33`)
to be implemented in RV64IM macro-assembly **early**, so testing can
start before the proof effort catches up. Lands in a multi-PR sequence
under `EvmAsm/Stateless/`. Each module ships with a `Program.lean` and
a `Spec.lean` placeholder so CPS-triple proofs slot in later without
restructuring. Precompiles raise a distinct `Unimplemented` exit code
(0xFE marker at `OUTPUT_ADDR`); KECCAK256, ECRECOVER, SHA256, etc. go
through ECALL bridges (extending `EvmAsm/EL/Keccak*EcallBridge.lean`).

### PR sequence

| PR | Scope | First fixture that passes |
|---|---|---|
| PR1 | Scaffold + `Unimplemented` exit + `Entry` stub | `empty_witness` (Unimplemented marker round-trip) |
| PR2 | SSZ decode/encode + roundtrip script | `empty_witness` (false-validation roundtrip) |
| PR3 | Headers RLP decode + validate + Witness DBs | `single_header`, `chain_3_headers` |
| PR4 | MPT walk + read-side WitnessState | `mpt_one_account` |
| PR5 | SSZ `hash_tree_root` + SHA256 bridge | `compute_new_payload_request_root` |
| PR6 | Block + Transaction + ECRECOVER bridge | `tx_transfer` |
| PR7 | EVM interpreter dispatch + opcode wiring | `bytecode_push_add` |
| PR8+ | Remaining opcodes, MPT mutation, state-root | tracked under Phase 5–11 above |

### Status

- ✅ PR1 scaffold committed: `EvmAsm/Stateless/` with
  `MemoryLayout.lean`, `Unimplemented.lean`, `Entry.lean`,
  `EntrySpec.lean`, and the `Stateless.lean` umbrella.
- ✅ #5164 resolved: `isValidMemAddr` is a 3-region predicate
  (legacy + INPUT + RAM); existing proofs unaffected.
- ✅ PR2 SSZ output encoder + roundtrip: `Stateless/SSZ/Encode/`
  emits the 41-byte SSZ encoding of `StatelessValidationResult(root=0,
  valid=false, chain_id=1)` at `OUTPUT_ADDR`; bytes verified identical
  to Python's `serialize_stateless_output` reference encoder via
  `scripts/codegen-stateless-roundtrip-check.sh` on ziskemu.
- ✅ PR3 SSZ chain_id decoder: `Stateless/SSZ/Decode/` reads
  `chain_id` from `INPUT_ADDR + 24` (SSZ container header byte 8).
  Encoder parameterised on `x10`; the decoded `chain_id` flows
  through to `OUTPUT_ADDR`. Roundtrip test feeds Python-generated
  SSZ blobs with `chain_id ∈ {1, 0x1234567890ABCDEF}`; both pass on
  ziskemu.
- ✅ PR4 witness-length validation bit: `decode_validation_bit`
  reads `offset_1` and `offset_3` from the outer container header
  and sets `x11 = 1` iff the witness body is empty (length 12).
  Encoder ORs `x11` into the packed `bool || chain_id` word.
  Third fixture (`--with-empty-header`) flips the bool to 0;
  output round-trips through Python's SSZ decoder.
- ✅ PR5 headers-emptiness bit: `decode_validation_bit` now chases
  the inner offset chain (outer offset_1 → witness_addr → inner
  offset_headers → headers_addr; outer offset_3 → headers_end) and
  sets `x11 = 1` iff `witness.headers` is empty regardless of
  state/codes. Fourth fixture (`--with-empty-state-node`) keeps
  bool=1 under PR5 vs. 0 under PR4 -- confirms the deeper walk.
- ✅ PR6 header_count surfacing: `decode_header_count` reads the
  first u32 of the headers list (with a BEQ guard for the empty
  case) and divides by 4, leaving the count in `x16`. Encoder
  writes it as a u64 at `OUTPUT_ADDR + 48` (diagnostic field past
  the 41-byte SSZ result). Fifth fixture (`--with-two-empty-headers`)
  verifies count=2.
- ✅ PR-K1 ziskemu keccak intrinsic pinned: `CSRS 0x800, a0`
  (32-bit encoding `0x80052073`) triggers `_opcode_keccak` in
  ziskemu, which permutes the 200-byte state buffer pointed to by
  `a0` via `zisk_keccakf1600`. New `zisk_keccak_probe` BuildUnit
  emits the raw `.4byte` and copies the post-permutation state to
  OUTPUT_ADDR; matches the Keccak team's reference vector for the
  zero-state permutation. Source:
  `ziskos/entrypoint/src/syscalls/keccakf.rs` + `syscall.rs`
  (`SYSCALL_KECCAKF_ID = 0x800`) + `ziskos_syscall!` macro
  expanding to `csrs <csr>, <reg>`.
- ✅ PR-K2…PR-K286 (rolling, in active development): per-helper
  RV64IM macro-asm pieces of `run_stateless_guest` shipped under
  `EvmAsm/Codegen/Programs/` and `EvmAsm/Stateless/`. The catalogue
  currently covers RLP primitives, transaction decoders (legacy +
  EIP-1559/2930/4844/7702), account and MPT walkers, block-body
  helpers, header field extractors, withdrawal RLP/hash, address
  derivation (CREATE / CREATE2), and (recent slice, 2026-05-)
  the chain-level helpers `chain_extract_basefee_range`,
  `chain_validate_basefee_{non-decreasing,non-increasing}`,
  `chain_validate_gas_limit_{constant,non-decreasing,non-increasing}`,
  `chain_extract_gas_limit_first_last`, `chain_compute_total_gas_limit`,
  `chain_extract_excess_blob_gas_first_last`,
  `chain_compute_{max,min}_excess_blob_gas`,
  `chain_compute_{max,min}_blob_count`,
  `chain_extract_first_last_parent_beacon_block_root`,
  `chain_extract_first_last_requests_hash`,
  `header_extract_requests_hash`. Each helper ships with a
  ziskemu fixture cross-checked against
  [`execution-specs`](execution-specs/) Python; see
  `scripts/codegen-stateless-*-check.sh` for the per-helper round-
  trip scripts.
- ✅ **State-trie / MPT read family (2026-05-)**: a new tranche of
  `*_at_header_state_root` helpers walks the witness state trie from a
  header's `state_root` to read account and storage data, mirroring EVM
  account-accessing opcodes. Storage-proof scaffolding first
  (`zisk_validate_state_root_against_witness_node`,
  `zisk_validate_witness_state_contains_root`,
  `zisk_validate_storage_root_in_witness_storage`), then the account walk
  (`zisk_account_at_header_state_root`, `zisk_account_exists_at_header_state_root`)
  and the opcode-level getters built on it:
  `zisk_balance` (BALANCE), `zisk_nonce`, `zisk_code` / `zisk_code_size`
  (EXTCODESIZE) / `zisk_extcodehash` (EIP-1052) / `zisk_extcodecopy`
  (EXTCODECOPY), `zisk_slot` / `zisk_sload` (SLOAD storage-slot lookup),
  `zisk_account_is_empty` (EIP-161 emptiness), and
  `zisk_has_code_or_nonce` (EIP-684 CREATE-collision check) — all
  `_at_header_state_root`. Plus `zisk_blockhash_from_witness_headers`
  (BLOCKHASH) and `zisk_witness_headers_chain_validate` (chain continuity).
  Same fixture/round-trip discipline against `execution-specs` Python.
- ✅ **EEST conformance harness (2026-05-31)**: the `stateless_guest` ELF
  now runs against the real Ethereum Execution Spec Tests instead of only
  synthetic inputs. Target = `ethereum/execution-spec-tests` @ `zkevm@v0.4.0`
  (the dedicated stateless "zkevm" fixture line for the **Amsterdam /
  Glamsterdam** fork; adds the 2-byte schema-id prefix + filled `public_keys`
  the guest reads), vendored as the `execution-spec-tests` submodule
  (`shallow=true`). Pipeline: `scripts/eest-fetch-fixtures.sh` downloads the
  `fixtures_zkevm.tar.gz` release artifact;
  `scripts/eest-stateless-to-input.py` turns each block's
  `statelessInputBytes` into a ziskemu `-i` input (+ manifest);
  `scripts/codegen-eest-stateless-check.sh` builds the ELF, runs each input
  on ziskemu, and compares the output against the block's recorded
  `statelessOutputBytes`. Baseline (zkevm@v0.4.0): 23,219 stateless blocks
  (22,325 valid / 894 invalid); the still-partial guest matches the
  `successful_validation` bit on the 894 invalid-expecting blocks (it rejects
  every non-empty-header witness) and 0 full-output matches (it emits the
  pre-v0.4.0 empty-`active_fork` encoding). PR7+ guest completeness moves
  this baseline up; see PROGRESS.md Axis F.
- ✅ **BAL execution-vs-witness consistency + per-tx tuple soundness (beads `bmvmx.1.6.*`,
  `i3djw`; 2026-06)**: the stateless verdict re-derives the EIP-7928 `block_access_list`
  FROM execution and rejects a witness BAL that disagrees, instead of trusting it (the guest
  otherwise only pins `keccak(prover_BAL) == header.block_access_list_hash`, a consistency
  check, so every execution-derived equality is a non-redundant soundness guard).
  - **Storage finals**: per-account forward/reverse `bal_storage_matches_exec_log` /
    `bal_storage_covers_exec_log` / `bal_storage_reads_in_exec_log` over the append-per-write
    storage exec-log, wrapped all-accounts by `bal_all_accounts_storage_consistent` (callee key
    via `bal_addr_to_exec_log_key`, recipient checked in `block_verdict`).
  - **Non-storage** (balance/nonce/code, `i3djw`): per-account `bal_account_nonstorage_finals`
    → `bal_account_nonstorage_consistent` (balance+nonce forward+reverse) +
    `bal_account_code_consistent` (deployed-code bytes); wrapped all-accounts forward
    `bal_all_accounts_nonstorage_consistent` + reverse `…_covers`, and code forward
    `bal_all_accounts_code_consistent` + reverse `…_code_covers`. These scope to CALLEES via a
    `{sender, recipient, coinbase}` skip-list — the gas/value accounts are checked on the gas
    path (`sender_debit_from_gas`, `tx_gas_bal_post_verify_runtime`, sender-nonce).
  - **Per-tx tuple sequence** (`bmvmx.1.6.6`, the consensus-binding layer the spec hashes into
    `header.block_access_list_hash`; closes the finals-only false-accept gap): the exec-log
    carries a parallel `exec_log_txindex` array; `bal_slot_tuple_sequence` (BAL side) +
    `exec_log_slot_tuples` (exec side: group-by-txindex, last-write-per-tx, net-zero filtered) +
    `slot_tuple_sequences_match`, composed per-account (`account_tuple_sequences_consistent`)
    and all-accounts (`bal_all_accounts_tuple_sequences_consistent`).
  - Each ships a ziskemu probe cross-checked against `execution-specs` amsterdam
    `block_access_lists.py` / `fork.py`. **Wiring** of the non-storage/code/tuple checks into
    `block_verdict` lands as execution emits the per-account effect records + the per-tx
    `block_access_index` (multi-tx loop, `fhsxz.2.4.2.57.11.6.3`) + CREATE/SELFDESTRUCT code
    effects; the storage tuple check can wire immediately on the existing exec-log + txindex.
  - **Wired (2026-06-09)**: CREATE/CREATE2 activated in the self-contained gate (#8649,
    `.61.8.3.3`) so created accounts execute through the real init-code dispatch descent and
    emit code + non-storage effect records (CALL-value producer `i3djw.1` #8559-active, CREATE
    producer `i3djw.2` #8643). Non-storage all-accounts forward `bal_all_accounts_nonstorage_consistent`
    (#8646) + reverse `…_covers` (#8652) wired + merged + operator-EEST-sweep-confirmed (`i3djw.3`
    closed). Forward all-accounts CODE `bal_all_accounts_code_consistent` wired with an **EIP-7702
    skip** — a BAL `code_change` that is exactly a 23-byte `0xef0100||address` delegation indicator
    (installed from the authorization list, no CREATE deposit → no exec code-effect) is skipped
    instead of false-rejected (`i3djw.4`, #8653 merged + sweep-confirmed). Reverse code `…_code_covers`
    already merged (#8626).
  - **BLOCKHASH activated (2026-06-10, `3vc2p`)**: the M29 recent-blockhash table is reconstructed
    from the witness headers (`stage_blockhash_m29` #8655) and staged into the contract-recipient
    payload between the storage preload and the env trailer — written by `stage_runtime_payload_code`
    (#8662) with `env_base` shifted by `count*32`, computed in `dispatch_tx_runtime_code` (#8663) — so
    the input-driven dispatcher setup loads `env+552/+560` + `evm_block_hashes` and BLOCKHASH (0x40) is
    removed from the self-contained reject set (#8664). Only BALANCE (0x31) + SELFDESTRUCT (0xff) remain
    rejected. (3-PR chain #8662→#8663→#8664, REQUIRES EEST SWEEP.)
  - **Contract-dispatch soundness audit (2026-06-10)**: the recently-activated contract/CREATE dispatch
    path had a class of latent bugs — fixed `.data` buffers sized for the small tested contracts,
    overflowed by realistic (EIP-170/3860-sized) inputs, all passing the sweep only because tested rows
    are small. Found + fixed **4 overflows**: env_base offset mismatch for non-empty calldata/storage
    (`3vc2p.5`/srpc_env_base #8658, merged); `bv_runtime_payload` 4096→65536 + size guard (`bmvmx.1.7.2`
    #8659, merged); `bal_recipient_storage_keys`/`bvcd_keys` 16-cap → 128 (`bmvmx.1.7.3` #8660);
    CREATE init-code > EIP-3860 49152 → `.exit_outofgas` guarding `create_child_initcode` 65536
    (`.61.8.3.6` #8665). Plus a semantic gap (`5em02`, OPEN): SELFBALANCE (activated yisv8.1) reads the
    PRE-state balance, diverging for value-moving contracts — the value-transfer descent is inert; the
    fix is the in-exec balance spine (`bmvmx.1.6.x`). See `contract-dispatch-fixed-buffer-overflows`
    auto-memory for the audit method.
  - **Requests-hash derivation (EIP-7685, `8uld3`)**: `parse_deposit_requests` (#8657, merged) +
    `assemble_execution_requests` (#8666) — derive the post-execution `requests_hash` from
    execution-produced bodies, not the trusted SSZ input. Standalone + probe-verified; the execution-gated
    piece (real receipts + EIP-7002/7251 system-call return data) is the follow-up.

- 🔶 **Contract-recipient gas-measurement accuracy (beads `nxio8`, `tpdo1`; 2026-06)**: the runtime
  dispatcher meters CONTRACT execution with STATIC base opcode gas only (`Dispatch.lean:338-345`),
  dropping the dynamic components — so a contract recipient measured by `dispatch_tx_runtime_code`
  gets wrong gas, which feeds `block_regular` → the EIP-7778/8037 block-gas gate can mis-judge
  contract blocks (false-accept/reject). This is the root blocker for contract-row EEST parity.
  - **Fixed**: `bytecode_is_self_contained` now rejects SELFDESTRUCT (`0xff`) (`tpdo1`, #8628) — its
    gas needs the un-staged beneficiary, so it can never be measured self-contained (a real
    false-accept closure; only adds conservative rejects).
  - **Primitive foundation built** (`nxio8.1`–`.3`, probe-verified vs Amsterdam `vm/gas.py`,
    unwired → verdict byte-identical): `sstore_regular_gas` (#8630), `memory_expansion_gas` (#8631),
    `keccak256`/`copy`/`log`/`exp` per-unit leaves (#8633). EIP-2929 cold/warm is already charged via
    `evm_storage_access_gas`.
  - **Dynamic-gas wiring LANDED** (2026-06-09, c1): warmth table live in `h_SLOAD`/`h_SSTORE`,
    SSTORE value-transition gas + refund accumulation, M31 memory-expansion / copy / keccak /
    log / exp dynamic gas in all memory-touching handlers, account warmth in
    BALANCE/EXTCODE*/CALL*/SELFDESTRUCT. eip7778 EEST filter = 32/32 full-match.
  - **Amsterdam schedule + EIP-8037 state gas** (2026-06-12, branch
    `feat/dispatcher-eip8037-state-gas`, bead `nxio8`): SSTORE moved off the legacy Cancun
    schedule (20000 SET / 19900 zero-restore refund) to Amsterdam (2900 clean-changing +
    97,920 EIP-8037 state gas for zero-origin creation via `evm_state_gas_left`/`evm_state_gas_used`
    + the reservoir split at TX_MAX_GAS_LIMIT, restore refund 2800 + state credit); SSTORE
    stipend `check_gas(2301)`; per-dispatch-call resets for `evm_refund_acc` /
    `evm_storage_access_count` / state cells / halt_kind (all leaked across multi-tx
    dispatch calls); `dispatcher_tx_gas_settle` folds the spec's tx-level settlement
    (error → state restore + refund discard, exceptional halt → regular gas burnt) into
    the `dispatch_tx_runtime_code` / block-verdict gas captures; the standalone
    `runtime_dispatcher`/callable-probe ELFs link again (frame-helper closure bundled —
    they had been unlinkable since the CREATE-descent handlers landed).
  - **Remaining**: EIP-2930 access-list storage-key seeding (`evm_storage_access_seed_key`
    exists, unwired) + the access-list intrinsic in the runtime tx-gas; child-frame
    `incorporate_child_on_error` state-gas/refund/warmth rollback (global cells, no
    per-frame snapshot); creation-tx intrinsic state gas + code-deposit state gas.

- 🔶 **EIP-8025 witness code-preimage rejects (beads `ok3nl`/#8638, `mkwwf`; 2026-06)**: the spec rejects a
  block when execution reads a `code_hash` absent from the witness (`WitnessState.get_code` raises). (a)
  **current-frame code** (`ok3nl`, #8638 MERGED) — a contract recipient with non-empty `code_hash` but no
  `witness.codes` preimage now rejects at `.Lbv_contract_dispatch` via `witness_lookup_by_hash` (was a
  false-accept). (b) **implicitly-executed system-contract code** (`mkwwf`, OPEN) — EIP-2935 history code
  absent from the witness should reject, but a blanket witness.codes-presence requirement FALSE-REJECTS the
  valid `system_contract_reaches_gas_limit` rows (36141b1cb: tolerated/gas-limit system calls legitimately
  omit the predeploy code). Correct fix must distinguish code-required (normal execution) from code-omittable
  (system-call errors/gas-limit) — system-call-outcome modeling, not a presence check. Both only ADD rejects;
  the unsound mkwwf attempt was caught by a clean-main regression sweep. (c) **precheck-failed CALL targets**
  (`kpvxz`, PR #8656) — `bal_call_target_delegated_code_valid` hard-rejected a `witness_lookup_by_hash` miss
  on the CALL-target's own code, false-rejecting `static_create_contract_suicide_during_init` d3 (CALL with
  value inside a STATICCALL frame raises at precheck, so the target's code is never read and its preimage is
  legitimately absent). Target-own-code miss now means "no delegated-code obligation"; the marker-visible
  delegated-code reject and the extcodesize status-5 chain are unchanged (validation_codes 01427–01437 sweep
  kept all expected verdicts).

- 🔶 **Receipts → stateless verdict (bead `fhsxz.2.4.2.63.1.6.2`; 2026-06-12 overnight PR stack)**:
  the verdict never compared a guest-computed `receipts_root`/`logs_bloom` against the header (an
  audited reachable no-tx false-accept, hermes-c3). Landed as a stacked chain on the dynamic-gas PR:
  - **#8721** (base, bead `nxio8`): Amsterdam SSTORE schedule + EIP-8037 state gas + per-tx
    dispatch-state resets + `dispatcher_tx_gas_settle` settlement fold (eip8037 200/200 + 271/271,
    eip7778 32/32, random-20 — all full-match; details in the gas section above).
  - **#8722**: NO-TX receipts consensus check (empty-trie root + zero bloom vs header, fail codes
    50/51 — closes the audited false-accept) + per-tx receipt STATUS capture (settle success bit →
    `bv_tx_status_arr` → materializer).
  - **#8725**: `log_records_encode_rlp` leaf — captured LOG descriptors + `evm_log_data` → the spec
    `rlp([log..])` (probe-verified byte-exact vs a python RLP reference).
  - **PR 6 (this branch)**: per-tx log-window capture (`block_log_window_snapshot` — each dispatch
    call resets/overwrites the capture buffers, so windows are copied into a block-level arena
    between dispatches) + per-record logs RLP + bloom (`block_receipt_logs_materialize`, filling the
    `{bloom, logs_rlp, len}` descriptors `receipt_records_encode_no_logs` consumes). INERT: debug
    status only.
  - **BLOCKER for tx-bearing enforcement** (new receipts-blocker bead under `.63.1.6.2`): the
    dispatcher emits the EIP-7708 synthetic transfer log ONLY on the SELFDESTRUCT path — top-level
    tx value transfers and CALL value transfers never land in `evm_event_logs`, so guest receipts
    for ANY value-bearing tx are missing the transfer log and enforcement would false-reject. Fix =
    emit the synthetic descriptor at the top-level value move (needs a log-preseed surviving the
    per-call reset, like the callee storage seeds) + in the CALL value-transfer producer; THEN wire
    `receipt_records_encode_no_logs` → `block_validate_receipts_root_indexed` + per-record-bloom OR
    on the exact-measured path (build trie descriptors from records @40/@48, NOT by re-parsing the
    carrier list — typed receipts are `type_byte||rlp` and break `rlp_list_nth_item`).

- 🔶 **ECRECOVER recovery output (bead `fhsxz.2.4.2.62.2.5`; 2026-06-12, #8723 + #8724)**: the
  precompile returned success with empty returndata for every call. `secp256k1_recover_pubkey_staged`
  (extracted from `tx_pubkey_recover_raw`, accelerator-backed ~2e6 steps) now backs the handler tail
  (recover → keccak → 32-byte left-padded address; invalid signature keeps empty-returndata success).
  Reached via the `ecrecover_backend_ptr` cell so non-secp closures keep linking (the guest arms it in
  `dispatch_tx_runtime_code`). #8724 adds the end-to-end dispatcher probe (CALL 0x01 recovers
  `valid_signature_1` → `a94f...bf0b`; invalid v / zero r fail closed) — it caught an a0/x10 alias bug
  in the status branches (fixed on #8723). EEST ecrecover family 80/80 before AND after (the family's
  verdicts don't yet distinguish empty vs real returndata; a returndata-consuming EEST pin is noted on
  the bead). RIPEMD160 backend and MODEXP success output remain blocked on ziskemu routes
  (`docs/eest-precompile-frontier.md` row updated).

- 🔧 **FileSizeGuard cap discipline (#8645)**: `EvmAsm/Codegen/Programs/FileSizeGuard.lean`'s `#eval`
  enforces a 1500-line hard cap on every file under `Programs/`, but reads siblings via `IO.FS.readFile`
  (untracked by lake), so the guard's olean caches — incremental builds miss a too-large file while the
  clean docker `lake build codegen` fails. `BlockVerdict.lean` (1786) was split into
  `BlockVerdictStateRoot.lean` (block_state_root + stateless_verdict_v2), byte-identical assembly. Keep
  `block_verdict` itself out of splits to avoid churn with the call-frame descent.

### Cross-references

- Memory layout: `EvmAsm/Stateless/MemoryLayout.lean`.
- Reason codes (precompile, EIP-7702, EIP-4844, etc.):
  `EvmAsm/Stateless/Unimplemented.lean`.
- SDIV blocker (`evm-asm-9iqmw`) does **not** block this track —
  fixtures avoiding SDIV are picked first.

---

## Priority Order

**Immediate (recreate deleted specs) — ✅ ALL DONE:**
1. ~~Recreate `StackOps.lean`~~ — ✅ Done (Pop.lean, Push0.lean, Dup.lean, Swap.lean)
2. ~~Recreate `ShiftSpec.lean`~~ — ✅ Done (SHR per-limb + phase + body specs, 961 lines, 0 sorry)
3. ~~Recreate `ShlSpec.lean`, `SarSpec.lean`~~ — ✅ Done (SHL/SAR full hierarchy: per-limb + compose + semantic)
4. ~~Recreate `ByteSpec.lean`~~ — ✅ Done (Byte/Spec.lean + Byte/LimbSpec.lean, stack-level spec)

**Short-term (enables simple contracts):**
5. Phase 4.2: DIV, MOD — partial. Per-branch stack specs landed for
   the partial domain `b.getLimbN 3 = 0` (bzero / n=1/2/3) under the
   unified `evm_div_stack_spec` / `evm_mod_stack_spec` dispatchers
   (`Spec/Unified.lean`). Executable `evm_div` / `evm_mod` were switched
   to `divK_div128_v4` (full Knuth Algorithm D, 2-correction in both
   Phase 1b and Phase 2b) by [PR #4992](https://github.com/Verified-zkEVM/evm-asm/pull/4992)
   on 2026-05-19, so the runtime path is correct over the full
   4-limb domain. The remaining spec-layer work — extending
   `divCode` / `modCode` to v4 and proving full-domain
   `evm_div_stack_spec_unconditional` / `evm_mod_stack_spec_unconditional`
   (the n=4 path) — is tracked under bead `evm-asm-9iqmw` and reopened
   [GitHub issue #61](https://github.com/Verified-zkEVM/evm-asm/issues/61).
   In flight as of 2026-05-29: the **v5 div128 migration** (bead
   `evm-asm-wbc4i.6`) — `divK_div128_v5` caps the trial quotients to repair
   v4's two buggy ULTs, and the spec layer is being rebuilt against it
   (shared code surfaces `Compose/V5Code.lean`; step1/step2/phase1b/phase2b
   block specs in `LimbSpec/Div128*V5.lean`; n=4 dispatcher predicates and
   the `hq_over`-assuming runtime chain in `Spec/CallAddback{,Runtime}V5.lean`).
   See Phase 4.2 "V5 track" above for the file map. The earlier v4 series
   (`feat/div-n1-*`, `feat/div-n2-n3-selected-*`, `feat/div-double-addback-*`)
   landed the partial-domain conditional-carry and overestimate bridges.
   SDIV (`evm_sdiv_stack_spec_within`) and
   the SDIV/SMOD epilog wrappers are conditional on the same v4
   migration and unblock automatically when `evm-asm-9iqmw.5` lands.
6. Phase 5: MLOAD, MSTORE, EVM memory model
7. Phase 5.1: EVM code region (needed for PUSHn and interpreter)

**Execution layer (RLP decoder — STF prerequisite):**
- ~~EL.1: RLP specification~~ — ✅ Done
- ~~EL.2: Byte-level infrastructure~~ — ✅ Done
- EL.3: RLP RISC-V decoder phases 1-6

**Medium-term (interpreter loop — STF core):**
8. Phase 7.1-7.2: EVM machine state + opcode dispatch
9. Phase 7.3: Opcode handler wrappers (gas + dispatch)
10. Phase 7.4: Interpreter main loop with simulation relation proof
11. Phase 6: Environment opcodes (CALLER, CALLVALUE, etc.)

**Towards STF (full EVM execution):**
12. Phase 8.1-8.3: SLOAD/SSTORE, KECCAK256 (via syscalls/accelerators)
13. Phase 8.4-8.5: LOG, CALL/CREATE, RETURN/REVERT
14. Phase 9: Gas metering (static then dynamic)
15. Phase 10: Transaction processing (message call + validation)
16. Phase 11: Block-level STF + IO integration + conformance testing

---

## Design Decisions

1. **RV64IM target**: Per zkvm-standards, `riscv64im_zicclsm` is
   the standardized target for Ethereum zkVMs. 64-bit words mean 4 limbs
   per 256-bit word.

2. **Stack-in-memory**: EVM stack elements are 256-bit words stored in
   RISC-V memory (4 consecutive 64-bit words in RV64). SP register (x12)
   points to top of stack. Stack grows upward, 32 bytes per element.

3. **Syscall bridge (ECALL)**: Complex operations (KECCAK, SLOAD/SSTORE, CALL,
   precompiles) use ECALL to delegate to the zkVM host. This aligns with the
   `zkvm_accelerators.h` C interface standard. The host provides:
   - Cryptographic accelerators (keccak, EC ops, pairings)
   - Storage read/write
   - State trie operations

4. **Per-limb modularity**: Each 256-bit operation decomposes into 4 per-limb
   operations (RV64) with individual specs, then composed via `runBlock`.

5. **Simulation relation for STF**: The interpreter loop proof uses a
   simulation relation between abstract EVM state and concrete RISC-V state.
   Each opcode handler preserves the simulation; the loop proof is inductive.

6. **Reference spec**: All opcodes must match the semantics in
   `execution-specs/src/ethereum/forks/shanghai/vm/`.

7. **Proof automation**: `xperm`/`xsimp` for assertion permutation,
   `runBlock` for multi-limb composition, `validMem`/`liftSpec`/`pcFree`
   for boilerplate elimination. Recent refactorings (let-code, runBlock)
   have eliminated thousands of lines of manual proof.

8. **IO standard**: The STF program uses `read_input`/`write_output` per
   the zkvm IO standard. Input = block + pre-state witness. Output =
   post-state root hash.
