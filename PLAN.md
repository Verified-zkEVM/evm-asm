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
> EXP via inline-callable `_fixed_fixed` body (M27; per-limb counter
> moved x6→x22 so it survives `mul_callable`). Codegen-
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
| Stack | POP, PUSH0, DUP1-16, SWAP1-16 | 1 / 5 / 9 / 16 | ✅ Fully proved |

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
  - **Deferred:** factoring the 4 near-identical multi-limb two's-complement
    `…AbsWord …= -v` proofs (`SDiv`/`SMod` `Compose/Words.lean`) into one shared
    lemma is blocked by their 4 separate underlying definitions — a clean DRY
    needs unifying those defs into a shared `rippleNegWord` function (a larger
    refactor; the 4 proofs are correct/kernel-checkable as-is).
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

#### 3.2 PUSH1-32
- **File**: `Evm64/StackOps.lean`
- **Approach**: Requires EVM bytecode parsing. Push immediate from EVM code
  region. Read 1-32 bytes from code[pc+1..pc+n], zero-extend to 256 bits,
  push onto stack.
- **Depends on**: EVM code region model (Phase 5.1)

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
  - Remaining: long-string composition with Phase 2 for lenLen 2-8 and the planned
    general `n`-iteration closure,
    short/long-list error exits (`e4`/`e5`).
- Phase 4: `read_input` integration (obtain RLP input pointer + length)
- Phase 5: Recursive list decode (iterative with explicit stack)
- Phase 6: Top-level pipeline (`read_input` -> decode -> `write_output`)
- **Host I/O ABI**: See `docs/zkvm-host-io-interface.md`; SP1
  `HINT_LEN`/`HINT_READ`/`COMMIT` are legacy handler shapes, not the target
  C ABI.
- **Output format**: Pointer + length (zero-copy into input buffer)
- **Depends on**: EL.1 (spec to verify against), EL.2 (byte-level specs)

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
- RIPEMD160 (0x03) → `zkvm_ripemd160`
- IDENTITY (0x04) → no accelerator (pure memory copy)
- MODEXP (0x05) → `zkvm_modexp`
- BN254_ADD (0x06) → `zkvm_bn254_g1_add`
- BN254_MUL (0x07) → `zkvm_bn254_g1_mul`
- BN254_PAIRING (0x08) → `zkvm_bn254_pairing`
- BLAKE2f (0x09) → `zkvm_blake2f`
- KZG_POINT_EVAL (0x0a) → `zkvm_kzg_point_eval`
- BLS12_G1_ADD (0x0b) → `zkvm_bls12_g1_add`
- BLS12_G1_MSM (0x0c) → `zkvm_bls12_g1_msm`
- BLS12_G2_ADD (0x0d) → `zkvm_bls12_g2_add`
- BLS12_G2_MSM (0x0e) → `zkvm_bls12_g2_msm`
- BLS12_PAIRING (0x0f) → `zkvm_bls12_pairing`
- BLS12_MAP_FP_TO_G1 (0x10) → `zkvm_bls12_map_fp_to_g1`
- BLS12_MAP_FP2_TO_G2 (0x11) → `zkvm_bls12_map_fp2_to_g2`
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
