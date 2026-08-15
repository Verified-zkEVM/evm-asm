# evm-asm: A Progress-and-Quality Steering System for an Autonomous Agent Fleet

> Research report generated 2026-06-01 via a repo-grounded audit (5 internal
> dimensions) + web research (5 angles) + adversarial feasibility-check against
> the actual repository. Intended as the blueprint for a follow-up
> implementation session (CI jobs, trackers, docs). Recommendations are tagged
> `[P1/P2/P3]` (priority) and `[effort: S/M/L]`. Priority order reflects the
> project lead's stated weighting: (1) code quality & maintainability, (2) drift
> prevention + progress measurement, (3) legibility / review-throughput / triage.

## 1. Executive summary

**Core thesis.** evm-asm already has the hardest, most valuable piece of an agent-steering system that the rest of the industry lacks: a **non-gameable correctness oracle** (the Lean kernel under a strict `0-axiom / 0-sorry`, no-`native_decide`/`bv_decide` regime) wired into a **kernel-checked progress registry** (`EvmAsm/Progress.lean`) with a **drift gate** (`scripts/check-progress.sh`). External research (FormalRewardBench, RLVR) confirms this is the gold-standard reward signal: cheap, scalable, perfectly accurate, and not subject to reward hacking. Industry fleet-orchestration tooling (GitHub Agent HQ, Devin, Codex) explicitly *does not* have an automated per-agent quality score — it falls back to human diff review — because it has no such oracle. evm-asm can build the scorecard the industry can't.

The job, then, is **not** to invent new trust machinery. It is to (1) close the gap between what the kernel proves (a *named theorem exists*) and what we *claim* (a *strong-enough spec covers the full domain* and *advances a guest-program obligation*), and (2) extend the existing fitness-function suite so the prose conventions, conformance signals, and cost bounds become executable gates rather than advisory comments a drifting agent can ignore.

The single most important framing: **the kernel makes proofs unhackable, but it cannot catch a weakened/vacuous statement, a stalled obligation, or a DIV-class corner-case in the unverified codegen path.** Every recommendation targets exactly those three blind spots, in your stated priority order.

**Highest-leverage moves, in priority order:**

1. **[P2→P1 enabler] Make the registry track *direction*, not just per-opcode tier counts.** Add a kernel-checked obligation tracker (`EvmAsm/Progress/Obligations.lean`) linking each of the 9 guest-program obligations to its blocking opcodes/infrastructure, plus a new `conditional` ProofTier that separates "half-built" (`partly`) from "fully proven on a restricted domain" (the DIV/MOD `b.getLimbN 3 = 0` case). This is the difference between "71 proven bytes" and "am I on track to finish the RLP decoder before the interpreter loop?"

2. **[P1] Mechanize the `0-axiom/0-sorry` claim and the statement-strength check.** Add `scripts/check-axioms.sh` running `#print axioms` over every witness theorem (fail on anything beyond `{propext, Classical.choice, Quot.sound}`, or any `sorryAx`/`Lean.trustCompiler`). Add a CI tamper-scan that flags any diff touching a *theorem statement/type* or a verifier config (EEST harness, ziskemu, lakefile) — not just proof bodies. This closes the "agent makes a stubborn proof go green by silently weakening the spec" hole, the formal-methods analogue of overwriting unit tests, and mechanizes the currently convention-only `native_decide`/`bv_decide` ban in the same check.

3. **[P2] Gate the DIV-class bug at its source with boundary-biased differential fuzzing.** Add `scripts/fuzz-arith-diff.sh` comparing `evm_div/sdiv/mod/smod/mulmod/addmod` against the `execution-specs` Python oracle over operands **deliberately biased toward the Knuth Algorithm D add-back path** — the exact failure mode that survived common-case testing in both evm-asm (v4 bug) and `holiman/uint256`. Seed a permanent regression corpus. Wire `codegen-eest-stateless-check.sh --min-full` as a hard, monotonic CI gate.

4. **[P3] Build the per-PR scorecard for approve-by-exception.** Extend the existing deterministic `scripts/progress-delta.sh` (already invoked in `summary.yml` lines 37–40 and rendered into the PR comment) to emit a structured risk label and a 5-column objective scorecard (new kernel-checked top-level triples, Δ tier counts, net axioms/sorries, conformance delta, touches-trusted-core flag). Add a `CODEOWNERS` + ruleset gating the verified core more strictly than codegen. This rations the single human reviewer's attention — the verification-bottleneck problem that hits every AI-heavy team.

5. **[P1/P3] Promote prose conventions to fitness functions.** The `check-*.sh` suite already *is* a set of architecture fitness functions (Ford/Parsons). Grow it: kernel-check cycle bounds (move `N=` into `OpcodeEntry`), enforce layering, opcode-structure templates, and a churn/duplication watch for AI copy-paste sprawl.

---

## 2. Current state assessment — a strong foundation

evm-asm is **substantially ahead** of typical AI-author codebases. Frame everything below as the foundation to extend, not replace.

### Trust core (the crown jewel)
- **Kernel-checked progress registry**: `EvmAsm/Progress.lean` — 85 `OpcodeEntry` items, a `ProofTier` enum (proven/partly/execSpec/notStarted), and `by decide` count theorems (`provenCount_eq=41`, `partialCount_eq=9`, `execSpecCount_eq=32`, byte-weighted `provenBytes_eq=71`, …). The build *fails* if counts mismatch.
- **Witness abbrev mechanism**: each `.proven`/`.partly` entry forces a named theorem to exist and elaborate (no `sorry`/`axiom`). This catches deletion/rename — a real integrity property.
- **Drift gate**: `scripts/check-progress.sh` → `scripts/progress-report.sh --check` regenerates `PROGRESS.md` from the registry and fails the build on divergence. This is a textbook "evergreen document" (Living Documentation) with a point-of-change drift check — the pattern to replicate everywhere.
- **Strict proof regime**: `0-axiom/0-sorry`; `CLAUDE.md` bans `native_decide`/`bv_decide` (avoiding the `Lean.trustCompiler` soundness gap). This *is* the RLVR "perfectly accurate, unhackable verifier" property — though the ban is enforced only by prose/review today, not by a check (closed by R-C1).
- **The 9 guest-program obligations are documented but *not* kernel-checked.** They live as a markdown table in `PROGRESS.md`; there is **no `Obligations.lean` module** linking them to blocking opcodes. This is the single biggest gap in the trust core, not an existing asset (the target of R-A1).

### Guardrail suite (already fitness functions)
**What I verified:** `build.yml` invokes exactly **four** CI-blocking scripts — `check-no-warnings.sh`, `check-unimported.sh` (zero-orphan module graph), `check-file-size.sh` (1200/1500 line caps), and `check-progress.sh`. A fifth script, `scripts/check-unbounded-cps.sh`, exists on disk but is **not wired into `build.yml`** and is effectively **orphaned**: the unbounded CPS specs it policed were removed in commit `6e7ce6dec` (2026-04-30), so it has nothing left to match. Earlier framing of "five CI-blocking scripts (including step-bounded `cpsTripleWithin`)" was wrong — treat `check-unbounded-cps.sh` as dead code to either delete or repurpose, not as an active guardrail. Conventions are documented in `AGENTS.md`, `GRIND.md`, `OPCODE_TEMPLATE.md`, `TACTICS.md`, `CONTRIBUTING.md`.

### Conformance & codegen signals
- **66 conformance vectors**, kernel-checked (`EvmAsm/EL/Conformance/All.lean:allConformanceVectors_length = 66`).
- **~490 `codegen-*.sh` ziskemu round-trip scripts** + 59 `OpcodeTestCase` regression suite + M8.5 runtime-bytecode runner. **Not in CI.**
- **`RoundTripTests.lean`**: **61 build-time `#guard` emitter checks against 59 `Instr` constructors in `Rv64/Basic.lean` — i.e. ~103% coverage, effectively complete** (verified). This is *not* a 40%-coverage gap; it is already a strong build-time gate.
- **EEST stateless harness** (`scripts/codegen-eest-stateless-check.sh`): per-region `[root/succ/tail/full]` decomposition of the 105-byte `SszStatelessValidationResult`, with `--min-succ/--min-full/--min-root` threshold flags that **exist but are not wired into CI**.

### Cost / health infra
- **`benchmark.yml`**: weekly wall-time + peak-RSS + per-module `lakeprof` top-20, persisted as JSONL on the `benchmark-history` orphan branch (~10 weeks of history). No threshold gate (deliberate, per `docs/benchmark-workflow-design.md`).
- **Cycle bounds** (`cpsTripleWithin N`) are literal constants in `Spec.lean` files, hand-transcribed into `PROGRESS.md §C.1`. **Not kernel-checked.**

### Orchestration / review
- **`summary.yml`** (auto, advisory): deterministic `scripts/progress-delta.sh` (bash+awk, no LLM) is already called (lines 37–40), its output written to `/tmp/progress-delta.md` and concatenated into the Gemini-summary PR comment. **Non-blocking.** R-B1 extends *this exact* path — no new wiring needed, only a richer payload.
- **`review.yml`** (manual `/review`, advisory). **Non-blocking.**
- A single human (Yoichi Hirai) merges all PRs. **No `CODEOWNERS`, no required-review ruleset, no merge queue wired** — though `build.yml` *already listens on `merge_group`*, so the plumbing for a queue is half-present.
- `EEST_INSERT_HANDOFF.md` is the *only* doc forbidding agent `gh pr merge`/`--approve`/`issue close` — advisory, bead-specific.

**Bottom line:** correctness is well-defended; *direction, statement-quality, codegen conformance, cost regression, and review-throughput* are not.

---

## 3. Gap analysis (by priority)

### Priority 1 — Code quality & maintainability

**G1.1 — The registry proves existence, not statement strength (the "proved-the-wrong-theorem" gap).**
Witness abbrevs guarantee a theorem *named X* exists and elaborates. They do **not** guarantee X says what the registry claims. The Lean community's own "Did you prove it?" guidance is blunt: naming a statement is not proving it, and redefining a standard operation lets you "prove" something that merely looks right. An agent could add `abbrev _foo_witness := @SomeTrivialLemma`, flip the tier to `.proven`, and CI passes green. The kernel cannot catch a vacuous or under-specified Hoare triple (false precondition, postcondition omitting gas/memory).

**G1.2 — `partly` conflates "half-built" with "conditional/restricted-domain" (the vacuity gap).**
This is the DIV bug's *structural* signature. `evm_div_stack_spec` is parametric over `DivStackSpecCase` and **every case requires `b.getLimbN 3 = 0`** — the full `n=4` divisor case is uncovered except via a *different code surface* (`divCode_v5`). SDIV is "conditional on `hStack`." Per the hardware-FV vacuity literature, an antecedent that excludes a large input region is the hallmark of a near-vacuous spec — but the registry shows it identically to genuinely half-finished work. There is no `cover`/reachability lemma proving the precondition is satisfiable on real inputs.

**G1.3 — Prose conventions are unenforced; cycle bounds are unchecked.**
`AGENTS.md`/`OPCODE_TEMPLATE.md` rules (camelCase/snake_case, `@[irreducible]` bundling, address-grindset on first commit, `maxHeartbeats` ban-except-Shift) are prose. PR #1497 retrofitted hypotheses to camelCase *in the wrong direction* with no linter to stop it. `cpsTripleWithin 30` → `cpsTripleWithin 100` compiles silently. Heartbeat overrides (`Swap/Spec.lean` 800000, `ALUProofs.lean` 4000000) live outside any allowlist.

**G1.4 — AI copy-paste sprawl is unmetered.** GitClear's 2025 data (211M lines) shows AI-assisted dev drove ~8× more duplicated blocks and rising two-week churn. evm-asm's ~490 near-identical `codegen-*.sh` and 30+ per-opcode files are exactly that pattern. No duplication budget, no churn/hotspot report.

### Priority 2 — Drift prevention & progress measurement

**G2.1 — The registry tracks per-opcode tiers but not *direction* toward the 9 obligations.** You cannot ask "which opcodes block obligation #5?" or "am I on track?" Proven-byte counts do not imply obligation closure, and obligation completion criteria are undefined in any kernel-checked form. An agent can grind opcode tiers without advancing any guest-program goal — and no signal fires.

**G2.2 — No held-out / proxy-vs-true monitor.** SpecBench shows the gap between agent-visible pass rate and held-out pass rate can reach 100 points on long tasks. evm-asm has no held-out obligation set, so a multi-opcode push can look near-complete while real coverage stalls. The METR finding (felt +20% faster, actually −19%) is the precise risk: green dashboards manufacture false confidence.

**G2.3 — No statement/verifier-config tamper scan.** The highest-signal drift (RewardHackingAgents) is a diff that edits a *theorem statement* or *verifier config* rather than a proof body. evm-asm scans neither. A weakened spec or a loosened EEST/ziskemu config sails through.

**G2.4 — Regression visibility is advisory, not a PR gate.** `PROGRESS.md` is
point-in-time, but R-A5 now appends per-tag count snapshots to the
`progress-history` orphan branch and surfaces `progress-velocity.sh` in the
post-merge job summary. This catches DIV/MOD-style monotonic downgrades after
merge; it intentionally does not block a PR.

**G2.5 — No conformance or cycle regression gate.** ~490 ziskemu scripts and the EEST harness are **not in CI**. EEST `--min-full` is opt-in. If a PR regresses 24→20 full-matches, nothing blocks it. Cycle bounds drift silently.

**G2.6 — No stacked-PR / long-running-branch visibility.** Work on `feat/X` for weeks is invisible to metrics until it merges. No bead-claim dashboard; two agents can claim the same bead with no collision detection.

### Priority 3 — Legibility, review-throughput, triage

**G3.1 — No per-PR risk score or scorecard.** Reviewers see a flat list + advisory Gemini comments. No signal for "drifting" (many changes, no metric movement), "high-risk" (touches trust core, API break), or "low-effort." The verification bottleneck (review time +91% under AI volume) hits hardest here.

**G3.2 — No enforced trust-boundary gate.** No `CODEOWNERS`, no required-review ruleset, no merge queue active. The single human is a scaling bottleneck and single point of failure; merge skew (a PR that proved in isolation but breaks trunk post-merge) is unguarded.

**G3.3 — No "what is NOT proven" ledger.** seL4 and CompCert both publish explicit TCB/assumptions lists. evm-asm's trusted boundaries (RV64 model fidelity, the EVM reference semantics, gas/memory modeling, the codegen Phases 2/3/5 deferred, every `execSpec`-tier opcode) are scattered across `CODEGEN.md`, docstrings, and `PROGRESS.md §F` — not a single legible artifact.

### DIV bug as the worked example of the missing-signal class

The v4 `divK_div128_v4` had two buggy ULTs (Phase-1b 32-bit truncation; Phase-2 `q0c*dLo` wrapping mod 2^64); root cause was a wrong Knuth-B+2 vs Knuth-A+1 bound. It was refuted only by *manual* python search + kernel-checked counterexamples (`fbe14508b`), after which a manual rewrite to v5 was required. **Trace which signals would have fired under the current system:**

- Kernel proof? Green — the v4 *proof* was internally valid; the *statement* was restricted to the `b.getLimbN 3 = 0` domain where the bug doesn't manifest. (G1.1, G1.2)
- Conformance vectors? Only if a vector exercised the full `n=4` path with add-back operands. Coverage of that path is **unknown/unaudited**. (G2.5)
- Cycle bound? Irrelevant — value, not correctness. (G2.5)
- Differential fuzz vs execution-specs with boundary-biased operands? **Would have caught it** — this is exactly how `holiman/uint256` (same algorithm) is defended via OSS-Fuzz against `big.Int`, and exactly OpDiffer's "argument-oriented mutation." (G2.5, P2 fuzzing)

The lesson: **common-case tests + a domain-restricted proof produce a fully-green dashboard over a real bug.** Every P2 recommendation exists to make that combination impossible to ship silently.

---

## 4. Recommendations

Each tagged `[P#]` `[effort: S/M/L]`. Prefer extending named assets.

### (a) Hard-to-game *direction* signal toward the 9 obligations

- **R-A1 `[P2][M]` Kernel-checked obligation tracker.** New `EvmAsm/Progress/Obligations.lean` (does not exist today — the obligations live only as a `PROGRESS.md` table): an `ObligationStatus` enum (`done`/`blocked`/`notStarted`), 9 entries each with a `blockedBy : List EvmOpcode/InfraItem` list and, where `done`, a *witness theorem* proving the closure condition. `by decide` count theorems as in `Progress.lean`. Render an "Obligation × blocking-opcode" matrix into `PROGRESS.md`. This converts opcode-tier counts into *trajectory*: "obligation #5 is blocked by DIV/MOD full `n=4`." Justified by Mathlib's multi-orthogonal-count model (no single gameable "% done") and seL4's caller-obligation framing.

- **R-A2 `[P1][S]` Split `partly` → add a `conditional` ProofTier.** Edit the `ProofTier` inductive in `Progress.lean`. `conditional` = fully proven on a precondition-restricted domain (DIV/MOD `b.getLimbN 3 = 0`, SDIV `hStack`); `partly` = half-built. The dashboard then shows *domain coverage*, not blurred existence. Anti-vacuity literature: don't conflate "restricted-domain proven" with "unfinished."

- **R-A3 `[P2][M]` Reachability/cover lemmas for every `conditional` entry.** Require each `conditional` witness to also reference a `..._precondition_reachable` lemma (`decide`-checked on representative real inputs) proving the antecedent is satisfiable. This is the hardware-FV cover-property remedy for near-vacuity. Enforced via a second witness slot in `OpcodeEntry`.

- **R-A4 `[P2][S]` Graded sub-lemma milestones per opcode.** In `OpcodeEntry`, record optional milestone refs (decode / stack-effect / memory-effect / gas / composed-triple). Fixes RLVR sparse-credit-assignment: a long opcode push emits incremental signal, so a stalled agent (zero milestone progress) is detectable early.

- **R-A5 `[P2][S]` Per-tag count snapshots → velocity (implemented, advisory).** Append `{commit, date, EEST_tag, provenCount, partialCount, conditionalCount, execSpecCount, provenBytes, fullMatchCount}` to a `progress-history.jsonl` on an orphan branch (mirror `benchmark-history`) and surface `scripts/progress-velocity.sh` in the post-merge job summary. Detects the DIV-style silent downgrade after merge; it is not a blocking PR gate. Mathlib "code growth" trend model.

### (b) Per-PR scorecard for approve-by-exception

- **R-B1 `[P3][S]` Deterministic risk label + scorecard.** Extend `scripts/progress-delta.sh` (already deterministic, no-LLM, and already invoked in `summary.yml` lines 37–40 with output folded into the PR comment — keep it deterministic) to emit a structured scorecard: `{new_top_level_triples, Δtier_counts, net_axioms_sorries, Δfull_match, touches_trusted_core, statement_diff}`. Compute a `risk: high|medium|low` label: HIGH if it touches `EvmAsm/Progress.lean`/`Rv64/Basic.lean`/spec-statement files, is XL-diff, or changes codegen without a changed round-trip script. Post as a one-glance PR header. **Integration is a payload change, not new plumbing** — the existing `summary.yml` → Gemini-summary → PR-comment flow already consumes this script's stdout. This is the per-agent objective scorecard that GitHub Agent HQ / Devin demonstrably *lack*.

- **R-B2 `[P3][S]` Path + size auto-labeling.** `.github/labeler.yml` + `actions/labeler` to tag `area:verified-core` vs `area:codegen`; a size labeler excluding `codegen-*.sh` from the diff count (so bulk script regens aren't mislabeled XL).

- **R-B3 `[P3][S]` Statement-strength rubric as a layered review section.** Add to `docs/pr-summary-progress-prompt.md` an LLM rubric: does each new/changed triple match EVM semantics, avoid vacuous preconditions, cover stack+memory+gas+halting? Layer the LLM *only* on the un-kernel-checkable spec-quality question (Agentic-Rubrics pattern) — never on correctness, where the kernel is the perfect oracle. Emit a one-liner sign-off.

### (c) Drift detectors

- **R-C1 `[P1][S]` Axiom audit gate.** `scripts/check-axioms.sh`: run `#print axioms` over every witness theorem in `Progress.lean`; fail on anything beyond `{propext, Classical.choice, Quot.sound}` or any `sorryAx`/`Lean.trustCompiler`. This *mechanizes* the `0-axiom/0-sorry` claim **and** the `native_decide`/`bv_decide` ban (currently convention-only) in one check. Optionally `lean4checker --fresh` as a nightly full kernel replay. (Lean Reference "Validating a Lean Proof".)

- **R-C2 `[P1][S]` Statement/verifier-config tamper scan.** `scripts/check-statement-tamper.sh`: on each PR diff, flag (warn or require label) any change to a theorem *type/statement* (vs body), to `Progress.lean` tiers, or to verifier configs (EEST harness, ziskemu invocation, `lakefile.toml`). Statement + config edits are the highest-signal tamper indicators (RewardHackingAgents). Require a `skip-statement-check: <reason>` in the PR body to bypass.

- **R-C3 `[P2][S]` Conformance non-regression gate.** Wire `codegen-eest-stateless-check.sh --min-full <baseline>` into `build.yml` on `merge_group`. Add to `check-progress.sh`/`progress-report.sh` an assertion that `allConformanceVectors_length` never *decreases* vs the pinned baseline (catches silent vector deletion). Monotonic ratchet — bump the baseline up as conformance improves. **Pin `EEST_FIXTURE_TAG` per measurement window** so the signal reflects code, not vectors (see non-goals for cadence/ownership). (Hive/EthProofs trend model.)

- **R-C4 `[P1][M]` Kernel-check cycle bounds.** Add `cycleBound : Option Nat` to `OpcodeEntry`; require the witness theorem's `cpsTripleWithin N` to bind that `N`. Then `progress-report.sh` extracts `N` automatically and a silent `30→100` inflation fails the build. Eliminates the hand-transcription drift in `PROGRESS.md §C.1`.

- **R-C5 `[P1][M]` Trusted-core gating.** Net-new `.github/CODEOWNERS` mapping verified-core dirs (`EvmAsm/Progress.lean`, `EvmAsm/Rv64/`, spec/statement files, EEST/ziskemu config) to maintainers; a ruleset requiring 2 approvals there, 1 for codegen. CODEOWNERS without a ruleset is advisory — the ruleset makes the trust boundary an *enforced* merge gate. (GitHub rulesets, Nov-2025 team-required-review.)

- **R-C6 `[P1][S]` Churn/hotspot + duplication watch.** `scripts/churn-report.sh` (pure `git log`, no deps): top-churn `.lean`/`scripts/` files per month + short-lived churn (reverted within ~2 weeks). Add `jscpd` over `scripts/` and `.lean` with a duplication *budget* that fails only on **new** sprawl. Apply the Rule of Three: tolerate deliberate per-opcode/per-fixture boilerplate; apply abstraction pressure only to convergent proof tactics/lemmas. Start advisory (CI output), promote to gate after calibration. (CodeScene behavioral analysis; GitClear AI-churn data; Code Red empirical justification.)

### (d) Making prose conventions executable (fitness functions)

- **R-D1 `[P3][S]` Reframe + grow the suite.** Document in `AGENTS.md` that `check-*.sh` *are* architecture fitness functions (Ford/Parsons). Add: `check-opcode-structure.sh` (new `Evm64/<Op>/` lands with unified-dispatch param + `@[irreducible]` Post def + `AddrNormAttr.lean`/`AddrNorm.lean` pair + FullPath spec — the four `OPCODE_TEMPLATE.md` essentials, so new opcodes don't recreate the DivMod retrofit tax of #262–#312); `check-naming.sh` (regex for camelCase hypotheses in `have/obtain/intro`, catching PR #1497 regressions); `check-heartbeats-approved.sh` (allowlist `scripts/approved-heartbeat-overrides.txt`); a layering check (`EL/` must not import `Rv64/`). **Grandfather the two existing overrides** — seed `approved-heartbeat-overrides.txt` with `Swap/Spec.lean` (800000) and `ALUProofs.lean` (4000000) at first commit so the gate goes green on day one; file a follow-up bead to relitigate each. Do *not* retroactively remove them in the same PR (that risks breaking the build). While here, **either delete or repurpose the orphaned `check-unbounded-cps.sh`** (verified unwired since the CPS specs were removed in `6e7ce6dec`) so the suite contains no dead gates.

- **R-D2 `[P3][S]` Codify mechanical review rules as hard CI fails.** A Danger-JS-style step (or a bash gate) that *fails* on: banned `native_decide`/`bv_decide` (overlaps R-C1), core edits without maintainer label, codegen opcode change with no round-trip script change. Reserve hard `fail` for true invariants; `warn` for `PLAN.md` drift. (Danger JS; keep noise low or agents/humans learn to ignore.)

### (e) Differential / fuzz testing vs execution-specs (DIV-class bugs)

- **R-E1 `[P2][M]` Boundary-biased arithmetic differential fuzzer.** `scripts/fuzz-arith-diff.sh`: compare `evm_div/sdiv/mod/smod/mulmod/addmod` against the `execution-specs` Python oracle over operands **biased toward the Knuth Algorithm D rare paths** — divisor top word just below 2^64, dividends forcing the qhat over-estimate + add-back, divisor word-counts 1..4, and `y>x`/`y==0`/`x==0` edges. Uniform-random fuzzing *will not* hit these (this is exactly why the v4 bug survived). Maintain a persistent **regression corpus** seeded with every historical failing case (`fbe14508b` counterexamples). This is the proven `holiman/uint256`/OpDiffer mitigation. Run native on PR, longer nightly. Complement to, not replacement for, the Lean proof (must stay kernel-checkable). **Pin `EEST_FIXTURE_TAG`** when the fuzzer consumes released fixtures (see non-goals).

- **R-E2 `[P2][M]` Dual-path differential check.** Run the same EEST input through the two evm-asm code surfaces that *already exist* — the build-time emitter path (`Instr` semantics exercised by `RoundTripTests`) vs the codegen→RISC-V→ziskemu round-trip — and assert equality. **What I verified / scoped down:** there is no standalone "native EVM-ASM evaluator" binary, and the draft's framing implied one. Do **not** ship or maintain a second native interpreter (cost/maintenance burden, and it would itself be unverified). Instead, contrast the existing in-Lean emitter-semantics path against the ziskemu output on shared inputs — both already live in the repo. This is the Hive Engine-vs-RLP analog and catches codegen/lowering bugs a single path hides, with zero new trusted components.

- **R-E3 `[P2][S]` Trace/region-level localization + budget distinction.** Extend the `[root/succ/tail/full]` decomposition toward per-opcode/per-step comparison so a divergence pinpoints the failing opcode, not just "block failed." In the EEST metric, **distinguish "wrong answer" from "ran out of `--steps` budget"** so sha256-heavy merkleization timeouts aren't miscounted as failures.

- **R-E4 `[P3][XS]` Confirm — not expand — `RoundTripTests.lean` coverage.** **What I verified / downgraded:** `RoundTripTests.lean` already has **61 `#guard` checks against 59 `Instr` constructors (~103%)** — coverage is effectively complete, not ~40% as earlier drafted, so this is **not a gap**. Reframe to a one-time `check-roundtrip-coverage.sh` audit that asserts *every* current `Rv64/Basic.lean` constructor has a guard and **fails when a new `Instr` shape lands without one** (e.g. future `emitDispatcher*` variants). Effort drops from M to XS — a regression fence, not an expansion.

### (f) Cost / cycle trend tracking

- **R-F1 `[P3][S]` ziskemu cycle instrumentation.** Parse the executed-step/cycle count from ziskemu runs in `codegen-*.sh`; append to a `cycles-history.jsonl`. This is the *only* path to validating the project's founding "better zkVM performance" claim — currently entirely unmeasured.
- **R-F2 `[P3][M]` Per-module build-time/proof-size trend.** Extend `benchmark.yml` `lakeprof` to record per-target time so the `n=4` division proofs (prime build-time suspects) surface as regressions. Keep the *deliberate* no-hard-threshold stance from `docs/benchmark-workflow-design.md` (proof times are noisy) — trend + weekly human read, not a PR gate, and **never a heartbeat bump to force a proof green**.
- **R-F3 `[P3][S]` External export scaffold.** Monthly job pushing `benchmark-history` + cycle data toward `eth-act/zkevm-benchmark-workload` (the stated "eventual home"). Note: EthProofs measures *performance*, not correctness — never treat "proves 99.7% of blocks" as a conformance signal.

---

## 5. Proposed implementation plan (phased, ordered by dependency + ROI)

**Phase 0 — Integrity hardening (P1, fast, high ROI). Extensions of existing CI.**
1. `scripts/check-axioms.sh` + wire into `build.yml` — *mechanizes the no-axiom/no-`native_decide` claim* (R-C1). **Net-new script, extends existing CI.**
2. `scripts/check-statement-tamper.sh` (R-C2). **Net-new.**
3. Conformance non-regression: add `--min-full` baseline to `build.yml` (on `merge_group`) + `allConformanceVectors_length` monotonic check in `progress-report.sh` (R-C3). **Extends existing harness + script.**

**Phase 1 — Registry semantics (P1/P2). Extensions of `Progress.lean`.**
4. Add `conditional` ProofTier; reclassify DIV/MOD/SDIV/SMOD (R-A2). **Edit existing.**
5. Add `cycleBound` + milestone fields to `OpcodeEntry`; bulk-fill; require witness binding (R-C4, R-A4). **Edit existing.**
6. Per-tier rubric in `PROGRESS.md` + `CLAUDE.md`/`AGENTS.md`; cover-lemma slot for `conditional` (R-A3). **Doc + edit.**

**Phase 2 — Direction tracking (P2). Net-new module.**
7. `EvmAsm/Progress/Obligations.lean` — kernel-checked 9-obligation × blocking-opcode tracker; render matrix into `PROGRESS.md` (R-A1). **Net-new, depends on Phase 1 tiers.**
8. `progress-history.jsonl` orphan branch + `scripts/progress-velocity.sh` (R-A5). **Implemented as a post-merge advisory, mirrors `benchmark-history`; no PR-time gate.**
9. `DRIFT.md` / TCB ledger: 9 obligations one-line status + explicit "NOT proven" list (deferred codegen phases, execSpec opcodes, RV64-model/EVM-spec/gas trust boundaries) (R-C3 doc, G3.3). **Net-new doc, can be CI-generated from the tracker.**

**Phase 3 — DIV-class defense (P2). Net-new + extends existing paths.**
10. `scripts/fuzz-arith-diff.sh` + regression corpus seeded from `fbe14508b` (R-E1). **Net-new.**
11. Trace-level localization + budget-vs-wrong distinction in EEST metric (R-E3). **Extends existing harness.**
12. Dual-path differential check using the two *existing* surfaces — no native evaluator (R-E2); `check-roundtrip-coverage.sh` regression fence (R-E4). **Extends existing.**

**Phase 4 — Review throughput & merge safety (P3). Extends `summary.yml`, net-new config.**
13. `.github/CODEOWNERS` + ruleset (2-approval core / 1 codegen) (R-C5). **Net-new.**
14. Activate GitHub merge queue on the already-present `merge_group` trigger; batch + auto-eject. **Write `docs/merge-queue-design.md` *first*** documenting the TAP test-and-bisect pattern (on batch failure, bisect the batch to eject the offending PR rather than re-running the full ~490-script ziskemu suite per PR) before flipping the queue on, so the team understands eviction behavior and avoids friction. **Extends `build.yml`.**
15. Risk label + scorecard in `progress-delta.sh`/`summary.yml` (payload change to the existing lines 37–40 path); `actions/labeler` path+size labels (R-B1, R-B2). **Extends existing.**
16. Statement-strength rubric + sign-off line in `pr-summary-progress-prompt.md` (R-B3). **Edit existing.**
17. Bead-claim tracking in `PLAN.md`, stale-PR nudge workflow (G2.6). **Net-new.**

**Phase 5 — Conventions-as-gates + cost (P1/P3). Extends suite + benchmark.**
18. `check-opcode-structure.sh`, `check-naming.sh`, `check-heartbeats-approved.sh` (seed allowlist with the two grandfathered overrides), layering check; reframe suite as fitness functions in `AGENTS.md`; retire/repurpose orphaned `check-unbounded-cps.sh` (R-D1). **Net-new scripts + cleanup.**
19. `scripts/churn-report.sh` + `jscpd` duplication budget (advisory → gate after calibration) (R-C6). **Net-new.**
20. ziskemu cycle instrumentation + `cycles-history.jsonl`; per-module proof-size trend; external export scaffold (R-F1/2/3). **Extends `codegen-*.sh` + `benchmark.yml`.**

---

## 6. Risks & non-goals

- **Do NOT introduce a single "% verified" headline number.** It is gameable and hides domain coverage — an opcode can be "proven" on a restricted sub-domain (the DIV `b.getLimbN 3 = 0` trap). Always publish multiple orthogonal kernel-checked counts + trends (Mathlib model).
- **Do NOT use `native_decide`/`bv_decide`** anywhere, including in fuzz oracles that could leak into the trusted base. Differential fuzzing is a *complement* to, never a replacement for, kernel-checked proofs. R-C1 enforces this mechanically.
- **Do NOT ship a second native EVM-ASM interpreter for R-E2.** No such evaluator exists today; building one adds an unverified, maintenance-heavy trusted component. The dual-path check must contrast the two *existing* surfaces (in-Lean emitter semantics vs codegen→ziskemu), nothing more.
- **Do NOT bump `maxHeartbeats` to force a proof green.** The heartbeat allowlist (R-D1) is a *ceiling and audit log*, not a license to inflate. Grandfather the two current overrides; relitigate them as separate beads. Build-time/proof-size trends (R-F2) stay advisory precisely so nobody is tempted to paper over a slow proof with a bump.
- **Do NOT use an LLM as a correctness oracle.** The kernel is perfect and cheap; LLM judges are themselves gameable and overoptimizable. Use the LLM rubric *only* for the spec-strength layer the kernel cannot judge (R-B3).
- **Do NOT make CI gates that exceed the Lean build budget.** A full clean build + ~490 ziskemu scripts is heavy; serial per-PR gating bottlenecks to ~4 merges/hour. Use the **merge queue with batching + auto-bisect** (TAP, documented in `docs/merge-queue-design.md` before activation), not serial re-runs. Run the heavy fuzz/dual-path suites nightly + on `merge_group`, lighter checks on PR push. Keep checks cheap/cached.
- **Do NOT hard-gate on noisy heuristics prematurely.** Churn, hotspot, duplication, and proof-time are *leading indicators*. Ship them as advisory CI output first; promote to gates only after thresholds are calibrated, or they generate false-positive friction that trains agents and humans to ignore CI.
- **Do NOT over-abstract the ~490 codegen scripts or per-opcode files.** Rule of Three: deliberate low-coupling boilerplate is cheaper duplicated than behind a brittle macro. Apply dedup pressure to convergent proof tactics/lemmas only.
- **Do NOT let the EEST fixture tag float during trend measurement.** Pin `EEST_FIXTURE_TAG` per window and record it with each datapoint, or pass-rate changes will reflect vectors, not code. **Operational cadence:** rotate the pin on a fixed biweekly schedule, bump it deliberately in its own PR (never bundled with code changes so the delta is attributable), and keep the current tag in a single `scripts/eest-fixture-tag.txt` registry owned by the maintainer. (EEST stopped accepting test PRs 2025-11-01 — derive new tests via `execution-specs`, consume released fixtures.)
- **Codegen is unverified by design.** The RISC-V lowering, ziskemu, and the deferred codegen phases are explicitly outside the kernel-checked core. Recommendations here *measure and fence* that boundary (conformance gate, dual-path, fuzzer, TCB ledger) — they do not promise to verify it, and the TCB ledger (step 9) must state this plainly.
- **Non-goal: replacing the human reviewer entirely.** The goal is *approve-by-exception* — automated trust on the kernel + conformance + tamper/drift scans, with scarce human review rationed to high-risk-labeled and statement-diff PRs. Risk scores are triage ordering, not auto-merge authority for the verified core.

---

## Appendix — what the feasibility check changed

The draft was stress-tested against the actual repo; these corrections were applied:

- `build.yml` invokes **4** check scripts, not 5; `check-unbounded-cps.sh` is unwired and orphaned since the CPS specs were removed in `6e7ce6dec` — §2 and R-D1 corrected accordingly.
- `RoundTripTests.lean` has **61 `#guard`s against 59 constructors (~103%)** — coverage is already complete; R-E4 downgraded from "expand to 100% [M]" to a "regression-fence audit [XS]."
- `EvmAsm/Progress/Obligations.lean` **does not exist**; the 9 obligations are a `PROGRESS.md` table only — §2 no longer implies a kernel-checked obligations module exists; R-A1 remains net-new.
- `progress-delta.sh` is **already called in `summary.yml` (lines 37–40)** and its output already lands in the PR comment — R-B1 / step 15 reframed as a payload change into the existing flow, not new plumbing.
- No native EVM-ASM evaluator exists — R-E2 rescoped to two existing surfaces, with an explicit non-goal forbidding a new interpreter.

**Key files referenced:** `EvmAsm/Progress.lean`, `scripts/check-progress.sh`, `scripts/progress-report.sh`, `scripts/progress-delta.sh`, `scripts/check-unbounded-cps.sh` (orphaned — retire/repurpose), `scripts/codegen-eest-stateless-check.sh`, `.github/workflows/build.yml` (already triggers on `merge_group`), `.github/workflows/summary.yml` (progress-delta wired at lines 37–40), `.github/workflows/review.yml`, `.github/workflows/benchmark.yml`, `EvmAsm/EL/Conformance/All.lean`, `EvmAsm/Codegen/RoundTripTests.lean` (~103% Instr coverage), `EvmAsm/Rv64/Basic.lean` (59 Instr constructors), `docs/pr-summary-progress-prompt.md`, `docs/benchmark-workflow-design.md`, `EvmAsm/Evm64/OPCODE_TEMPLATE.md`. Net-new artifacts: `EvmAsm/Progress/Obligations.lean`, `.github/CODEOWNERS`, `docs/merge-queue-design.md`, `scripts/eest-fixture-tag.txt`, `scripts/approved-heartbeat-overrides.txt`.
