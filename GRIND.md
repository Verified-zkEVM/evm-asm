# GRIND.md — simp/grind set conventions

This document is the single source of truth for how this repo organizes `grind`-based and `simp`-based proof automation. Read it before writing a new closing tactic, before adding a new `@[simp]`/`@[grind =]` lemma that other proofs will share, and before opening a follow-up issue to consolidate repetitive proof patterns.

`CLAUDE.md` and `AGENTS.md` link here from their proof-conventions sections — do not duplicate this content elsewhere.

---

## 1. Why we are doing this

A large class of proofs in this repo close goals that mix concrete bitvector evaluations (e.g., `signExtend12 4056 = 18446744073709551576`), small shift/`.toNat` reductions, and bitvector arithmetic. Historically these were closed by inline chains:

```lean
simp only [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
           show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
           show (3 : BitVec 6).toNat = 3 from by decide,
           show (1 : Word) <<< 3 = (8 : Word) from by decide,
           ...]
bv_omega
```

That style has three problems:

1. **Per-proof maintenance.** Every theorem repeats the same `show … from by decide` block. Adding a new concrete offset means editing every downstream proof.
2. **Cascade fragility.** When the assembly program shifts by one instruction, address literals change and dozens of inline chains have to be manually re-derived.
3. **Reviewer cost.** Identical 6–10-line chains drown signal in noise.

The fix is to register the atomic facts once in a named set, expose a single tactic that closes the class of goals, and migrate consumers to `by <tactic_name>`. New atomic facts are then a one-line `@[set_name, grind =]` declaration that every consumer picks up automatically.

`grind` is the right primary engine for these goals because it composes simp + congruence + cutsat in one step and is *resilient to vocabulary growth* — adding a fact to the set does not require revisiting any consumer. `grind` is kernel-checkable and therefore compatible with this repo's ban on `native_decide` / `bv_decide`.

## 2. Canonical example: `divmod_addr` (issue #263, PR #304)

The reference implementation lives at `EvmAsm/Evm64/DivMod/AddrNorm.lean` (+ `AddrNormAttr.lean`). It closes DivMod address-arithmetic equalities of the shape
`(sp + signExtend12 N₁ ± k <<< 3) ± signExtend12 N₂ = sp + signExtend12 N₃`.

```lean
-- GOOD: one-line, atomic facts in the shared `divmod_addr` set
theorem u_j1_0_eq_j0_4088 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

-- BAD: inline show-from-by-decide chain (per-proof maintenance burden)
theorem u_j1_0_eq_j0_4088' (sp : Word) : … := by
  simp only [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, …]
  bv_omega
```

When inventing a new grindset, copy the structure of `AddrNorm.lean` / `AddrNormAttr.lean` rather than reinventing it.

## 3. Pattern: registering a new grind/simp set

A grindset has at most three moving parts. Pick the layout that matches what you need.

### Layout A — Grind-only (simplest)

Use this if your tactic only needs `grind` to close goals — no consumer ever calls `simp only [my_set]` directly.

```lean
namespace MyDomain

@[grind =] theorem foo_eval_0 : foo 0 = bar := by decide
@[grind =] theorem foo_eval_1 : foo 1 = baz := by decide
-- ...

/-- Close a MyDomain equality. -/
macro "my_domain" : tactic => `(tactic| grind)

end MyDomain
```

### Layout B — Grind + named simp set (preferred when you also want `simp only [my_set]`)

Lean 4 forbids using an attribute in the same file in which it is declared. So a named simp attribute requires two files:

- `MyDomainAttr.lean`:
    ```lean
    import Mathlib.Tactic.Attr.Register

    /-- Simp set for MyDomain. -/
    register_simp_attr my_domain
    ```
- `MyDomain.lean`:
    ```lean
    import MyDomainAttr

    namespace MyDomain

    @[my_domain, grind =] theorem foo_eval_0 : foo 0 = bar := by decide
    -- ...

    /-- Close a MyDomain equality. Grind first (fastest, most resilient);
        simp+bv_omega fallback covers shapes grind can't fully reduce. -/
    macro "my_domain" : tactic =>
      `(tactic| first
        | grind
        | (simp only [my_domain]; bv_omega))

    end MyDomain
    ```

### Layout choice

- If consumers will only ever call `by my_domain` (the macro), prefer **Layout A**.
- If consumers may also want `simp only [my_domain]` for partial reductions or composition, use **Layout B**. The split file cost is small.
- The `divmod_addr` set uses **Layout B** because `simp only [divmod_addr]` may eventually be useful in larger composition proofs that don't want to invoke grind.

## 4. Rules of thumb

These are the durable lessons. Follow them unless you have a documented reason to deviate, and update this document if the deviation is general enough to be a new rule.

### Registration

- **Dual-register atomic facts** as `@[my_attr, grind =]`. Both `simp only [my_attr]` users and `grind` users see the same vocabulary, and the set stays in sync trivially.
- **Put atomic facts in a sub-namespace** (e.g., `EvmAsm.Evm64.DivMod.AddrNorm`) so file-private shadows in consumer files don't collide. `@[grind =]` and `@[my_attr]` are namespace-agnostic, so the macro keeps working without any `open`.
- **Tactic macros are syntactically global.** A `macro "my_domain" : tactic => …` declaration is reachable from any file that imports yours — no `open` needed.
- **Keep the set complete on first landing.** If a new concrete literal turns up later, add it as a one-line `@[my_attr, grind =]` fact in the set's file. Do **not** scatter inline `show … from by decide` lemmas in proof bodies as a workaround.

### Tactic macro

- **Grind-first, simp-second.** When grind and `simp only [...]; bv_omega` close the goal at comparable speed (within ~1.5×), put `grind` as the first branch of the `first` block and the simp+omega path as fallback. This matches the maintainability priority — see §5 for the empirical justification.
- **Fallback closer matches the goal class.** For arithmetic goals use `bv_omega`; for pure rewrite goals use `rfl`; for decidable propositions use `decide`. Don't reflexively reach for `bv_omega`.
- **Don't add a third branch unless you have evidence it's needed.** A `first | grind | simp+omega` pair is enough for the `divmod_addr` workload.

### Don'ts

- **Don't `grind` separation-logic permutations.** That is `xperm`'s job. Grind's congruence reasoning interacts badly with the 30+ atom assertions common in this repo and will time out.
- **Don't `grind` through `@[irreducible] def`s.** Grind respects irreducibility, so it cannot see through e.g. `loopBodyPostN4`. Use `delta` first or use a different mechanism.
- **Don't register broad `@[simp]` on signExtend / shift evaluations.** They are too aggressive for the global default simp set and will derail unrelated proofs. Always scope them under a named attribute (`@[divmod_addr]`, etc.) and let the macro pull them in via `simp only [name]` or `grind`.
- **Don't replace already-one-liner proofs.** If a proof is already `by decide` or `by rfl`, leave it alone. The grindset rollout is for collapsing *repetitive multi-line chains*, not for stylistic uniformity.
- **Don't replace specialized tactics** like `xperm`, `runBlock`, `seqFrame`, `liftSpec`, `pcFree`. They are tuned for their workloads and grind would be either slower, less precise, or both.

### Performance

- **Benchmark before bulk migration.** Before migrating a heavy file, run `lake build <module>` before and after. Reject the migration if it slows the module by more than ~10%.
- **Cap atomic-fact files at ~50 entries.** If a set grows beyond, split by sub-domain (e.g., `divmod_addr_se12`, `divmod_addr_shift`).
- **Watch grind's `@[grind =]` global index.** Many cheap facts are fine; complex unfolding rules in `@[grind =]` slow every `grind` call repo-wide. If a fact is heavy or domain-specific, prefer adding it to the *named simp set only* and reaching it via `grind [my_attr]` rather than the global `@[grind =]` index. We don't have a measured threshold yet — flag in PR review if a new set adds >100 global grind facts at once.

## 5. Empirical evidence (Lean v4.30.0-rc1)

The decision to default to `grind` over `simp only [...]; bv_omega` is grounded in this experiment, run during PR #304 on three representative DivMod address lemmas (`u_j1_0_eq_j0_4088`, `n3_ub1_off4088`, `n3_ub1_off4080`):

| Approach | Result | Time |
|---|---|---|
| `by grind` (bare, no hints) | **FAIL** — needs hints | — |
| `by grind [signExtend12]` (unfold hint) | pass | ~23ms |
| `by grind` with atomic facts as `@[grind =]` | pass | ~23ms |
| `simp only [inline]; bv_omega` (the original style) | pass | ~23ms |

**Conclusion:** grind and simp+omega are performance-equivalent on this workload. The maintainability win — adding a new offset is one line of `@[divmod_addr, grind =]` instead of a per-proof edit — is what tips the choice toward grind. Re-run a similar small experiment whenever you propose a new set; do not assume the conclusion generalizes blindly.

## 6. When to open a new grindset (vs. extend an existing one)

- **Extend an existing set** if the new fact is semantically the same domain (e.g., a new `signExtend12` offset → add to `divmod_addr` or, for non-DivMod usage, to the future `rv64_addr` set).
- **Open a new set** if the goal class is genuinely different — e.g., byte-extract algebra, register-operation rewrites, RLP encoding lemmas. Each new set should:
  - Solve a class of goals that recurs in ≥3 unrelated files (otherwise the inline lemma is fine).
  - Have ≤50 atomic facts at first landing.
  - Come with a tactic macro and one migrated file as proof-of-value, per §3.

When in doubt, write a short throwaway test demonstrating the duplication is real, link it in the issue, and propose the new set.

## 7. Sets currently in the repo

| Set | File | Status | Issue / PR |
|---|---|---|---|
| `divmod_addr` | `EvmAsm/Evm64/DivMod/AddrNorm.lean` (+ `AddrNormAttr.lean`) | landed (infrastructure + 1 file migrated) | #263 / #304 |
| `reg_ops` | `EvmAsm/Rv64/RegOps.lean` (+ `RegOpsAttr.lean`) | infrastructure landed (sanity proofs only, migrations pending) | GRIND.md Phase 5 |
| `rv64_addr` | `EvmAsm/Rv64/AddrNorm.lean` (+ `AddrNormAttr.lean`) | infrastructure landed (~47 signExtend13 / signExtend21 atomic facts + associativity, sanity proofs only, migrations pending) | GRIND.md Phase 3 |

Add new rows here as sets land. Each row should link the issue and the introducing PR.

## 8. Rollout roadmap

The methodology is rolled out in small, independently-reviewable phases. Each phase = one issue + one PR (or a small series of ≤3-file PRs).

**Design caveat.** Phase 1 choices (sub-namespace placement, `@[attr, grind =]` dual-registration, grind-first tactic macro, two-file attr-decl split) are *tentative pending validation in production*. Later phases adopt them only after Phase 1 has been in use long enough to expose problems. If experience updates a choice, revise §4 ("Rules of thumb") and note the revision in §8.2's relevant phase entry.

**Status legend:** ✅ landed · 🚧 in progress · ⏳ pending.

### 8.1 Per-phase recipe

Every phase follows the same seven-step shape. Deviate only with a documented reason.

1. **Identify** a class of repetitive proofs. Find them by grep on the closing-tactic shape (e.g., `simp only [show … from by decide]; bv_omega`, or `rfl` chains, or `simp only [getReg_setReg_*]`).
2. **Inventory** the atomic facts shared across the class. List concrete literals, base lemmas, and any unfolding hints needed.
3. **Land infrastructure** in a single small PR: `XyzSet.lean` (+ `XyzSetAttr.lean` if using Layout B from §3), atomic facts as `@[xyz_set, grind =]`, and a tactic macro following the `first | grind | (simp only [xyz_set]; <closer>)` shape.
4. **Migrate one heavy file** (≤10 lemmas) in the same PR as proof-of-value.
5. **Document** by adding a row to §7 and updating the phase's status in §8.2.
6. **Open a bulk-migration issue**, keeping each follow-up PR to ≤3 files to avoid review fatigue and merge conflicts.
7. **Retrospective**: count proof-line reduction, measure `lake build` time delta, decide whether to keep/extend/retire the set.

### 8.2 Phases

#### Phase 1 ✅ — DivMod address arithmetic
- **Goal:** close DivMod address-equality goals with `by divmod_addr`.
- **Targets:** `EvmAsm/Evm64/DivMod/AddrNorm.lean`, `AddrNormAttr.lean`. First migration: 4 `u_j1_*` lemmas in `LoopComposeN3.lean`.
- **Issue/PR:** #263 / #304.

#### Phase 2 ⏳ — Bulk DivMod address migration
- **Goal:** collapse the remaining ~108 one-off address-equality lemmas in DivMod to `by divmod_addr`.
- **Sub-PRs** (each ≤3 files, grouped to cluster related files):
  1. `LoopComposeN1.lean` (12) + `LoopComposeN2.lean` (4)
  2. `FullPathN1Loop.lean` (15) — **blocked on PR #300 merge**
  3. `FullPathN2Loop.lean` (13) + `FullPathN3Loop.lean` (13) — **blocked on PR #300 merge**
  4. `ModPhaseB.lean` (15) + `Compose/ModPhaseBn21.lean` + `Compose/ModPhaseBn3.lean` — file-private `mod_divK_se12_*` shadows dropped (use `AddrNorm.se12_1..4` / Base.lean `se12_32`); one-off address lemmas remain.
  5. `Compose/NormA.lean` + `Compose/Norm.lean` + `Compose/Epilogue.lean` — also delete their file-private `se12_*` shadows, which collide-by-name with `AddrNorm.lean`'s globals. (Partial: NormA/Epilogue/ModNorm shadows removed — Norm.lean already uses Base.lean's public `se12_32..56` directly.)
  6. Sweep: grep for any remaining `simp only [show signExtend12 .* by decide]` in `EvmAsm/Evm64/DivMod/` and clean up. (✅ Landed: the 9 residual `signExtend12 0 = 0` rewrites at `hCopy` across `FullPath{,N1,N2,N3}.lean` / `ModFullPath{,N1,N2,N3}.lean` now reference `AddrNorm.se12_0`; `FullPathN4Beq.lean`'s two compound `signExtend12 4 - 4 = 0` rewrites use `AddrNorm.se12_4` + `BitVec.sub_self`.)
- **Dependencies:** PR #300 (double-addback) for sub-PRs 2–3. Sub-PRs 1, 4, 5, 6 are unblocked today.
- **Stop criterion:** `grep -r "show signExtend12 .* by decide" EvmAsm/Evm64/DivMod/` returns zero matches. ✅ Met (2026-04-17).

#### Phase 3 🚧 — `rv64_addr` (generalize `bv_addr`)
- **Goal:** a richer Rv64-wide address simp/grind set, subsuming today's `bv_addr` (`simp only [BitVec.add_assoc]; rfl`, 578 callsites in DivMod alone).
- **Targets:** new `EvmAsm/Rv64/AddrNorm.lean` (+ `AddrNormAttr.lean`, Layout B). Atomic facts: `signExtend13`/`signExtend21` evaluations on common branch/jump offsets, `BitVec.add_assoc` rewrites (via the tactic fallback), `Word + 0 = Word` identities.
- **Proof-of-value:** migrate one file inside `EvmAsm/Rv64/` (e.g., specs in `Rv64/SyscallSpecs.lean`).
- **Dependencies:** none (independent of DivMod work).
- **Stop criterion:** `bv_addr` is either gone or a deprecated alias; bulk migration tracked via the Phase 3 follow-up issue.
- **Status:** Infrastructure landed + `signExtend1?` inline migration complete. `EvmAsm/Rv64/AddrNorm.lean` (+ `AddrNormAttr.lean`) register ~47 atomic facts: 29 `signExtend13` evaluations (27 small-offset `se13_*`, 2 large-offset), 19 `signExtend21` evaluations, plus `word_zero_add` and `word_add_zero` identities. The `rv64_addr` tactic macro tries `grind` first and falls back to `simp only [rv64_addr, BitVec.add_assoc]; rfl` — subsumes the legacy `bv_addr` shape. Four sanity `example`s exercise pure associativity, small-offset signExtend13, large-offset signExtend13, and signExtend21.
  - Migration PRs collapsing `rw [show signExtend1? N = <const> from by decide]` to `rw [se13_N]` / `rw [se21_N]`: **#385** (DivMod/Compose/, 28 sites), **#388** (SignExtend/Compose, 9 sites), **#390** (DivMod/LoopBody + DivMod/Compose/{Epilogue, FullPath}, 9 sites), **#392** (Shift/{Compose, ShlCompose, SarCompose}, 27 sites), **#395** (Byte/Spec, 9 sites) — 82 sites total across 11 files. Remaining: a single `signExtend12 31` site in `SignExtend/Compose.lean:748` (value 31 is not in the grindset — leave it or backfill separately).
  - Bulk migration of the pure-associativity `bv_addr` call-sites (578 in DivMod alone) is the remaining follow-up and can happen incrementally: `rv64_addr` already subsumes `bv_addr` via the simp fallback, so any call-site can switch in place.

#### Phase 4 ⏳ — `byte_alg`
- **Goal:** close `extractByte`/`replaceByte` algebra goals with one tactic.
- **Targets:** new `EvmAsm/Rv64/ByteAlg.lean`. Atomic facts: `extractByte_replaceByte_same`, `extractByte_replaceByte_diff`, `replaceByte_replaceByte_same`, byte-index arithmetic, `extractByte` of concrete word literals.
- **Proof-of-value:** one file in `EvmAsm/Evm64/Byte/` (e.g., `Byte/Spec.lean`).
- **Dependencies:** none.

#### Phase 5 🚧 — `reg_ops`
- **Goal:** close register-read-after-write chains (`getReg (setReg s r v) r' = …`, `setReg_setReg` commute/idempotent) with one tactic.
- **Targets:** the existing `@[simp]` lemmas on `getReg`/`setReg`/`getPC`/`setPC` in `Rv64/Basic.lean` are *augmented* with `@[grind =]` — behavior of existing simp-based proofs does not change. Tactic macro wraps `grind` over the set.
- **Proof-of-value:** migrate proofs in `Rv64/Tactics/RunBlock.lean` that hand-chain these lemmas.
- **Risk:** **lowest** of any phase — adding `@[grind =]` to already-`@[simp]` lemmas cannot break existing proofs.
- **Sequencing note:** can run in parallel with Phase 2 — no merge-conflict exposure.
- **Status:** Infrastructure landed. `EvmAsm/Rv64/RegOps.lean` (+ `RegOpsAttr.lean`) register ~40 projection lemmas (`pc_set<Field>`, `code_set<Field>`, `getReg_setPC`, `getMem_set<Field>`, `committed_*`, `publicValues_*`, `privateInput_*`, plus `_append{Commit,PublicValues}`) in the `reg_ops` simp set and the `grind` equational index. Two sanity `example`s exercise the tactic. Deliberately excluded: the inductive `*_writeWords` / `*_writeBytesAsWords` family (grind-loop risk on open-ended list arguments). Bulk migration of `RunBlock.lean` call-sites is the pending follow-up.

#### Phase 6 ⏳ — `bv_eval`
- **Goal:** close concrete BitVec/Word arithmetic evaluations (`(1 : Word) <<< 6 = 64`, `BitVec.toNat` of small literals, `Word + 0 = Word`, `BitVec.add_assoc/comm` chain rewrites).
- **Risk:** **highest scope-blowup risk** — easy to over-include and slow `grind` globally. Approach cautiously: identify the top 5–10 repeated atomic facts via grep, ship just those, expand only if a follow-up survey shows demand. Cap the file at ~30 entries; split by sub-domain if larger.
- **Dependencies:** gate on experience from Phases 2–5 (what worked, what didn't, what atomic-fact density the grind index tolerates).

#### Phase 7 ⏳ — Retrospective & policy hardening
- **Measure:**
  - total proof-line reduction across the repo (pre-Phase-1 baseline vs. end state),
  - `lake build` wall-time delta per affected module,
  - count of cases where the simp-fallback branch fired (signal that grind isn't sufficient alone).
- **Decide:** keep per-domain macros (`divmod_addr`, `rv64_addr`, `byte_alg`, `reg_ops`, `bv_eval`) — explicit, scoped, predictable — or unify into a single `evm_grind` tactic that tries all sets.
- **Update §4** ("Rules of thumb") with lessons learned.
- **Open governance issue** for per-set ownership and contribution rules.

### 8.3 Sequencing

```
Phase 1 (PR #304) ──┬→ Phase 5 (reg_ops)     [lowest risk, independent, can run now]
                    │
                    ├→ Phase 2 (DivMod bulk) [some files wait on #300]
                    │
                    ├→ Phase 3 (rv64_addr)   [independent of P2]
                    │
                    ├→ Phase 4 (byte_alg)    [independent]
                    │
                    ├→ Phase 6 (bv_eval)     [gated on P3-P5 evidence]
                    │
                    └→ Phase 7 (retro)       [after others]
```

### 8.4 Cross-cutting risks & mitigations

| Risk | Mitigation |
|---|---|
| Conflict with active DivMod PRs (#300, #303, future double-addback) | Schedule Phase 2 sub-PRs around their merges. Never touch a file in flight. |
| Build-time regression from broad `grind` invocation | Benchmark each phase's PR on the affected file(s) before/after; reject if >10% slowdown. The simp-fallback in the macro means `grind` is never the only path. |
| `grind` closes the wrong way (silent incorrect rewrite) | The macro's `first` block makes the fallback deterministic — not a replacement for review. Add a regression test if it ever happens in practice. Avoid registering broad `@[simp]` on the same lemmas (see §4). |
| Atomic-fact-file sprawl | Cap individual sets at ~50 entries (§4). If a set grows beyond, split by sub-domain. |
| Design churn invalidates earlier phases | The §8 preamble flags Phase 1 choices as tentative. Phases 2+ adopt only after Phase 1 review lands. Update §4 if lessons generalize. |

## 9. Maintenance & contribution

### 9.1 Reactive updates (when something changes)

- **Update §7** (live sets table) when a new set lands.
- **Update §8.2** (phase entries) when a phase moves between pending → in-progress → landed, or when phases are added/removed.
- **Update §4** ("Rules of thumb") when a new lesson generalizes from a single PR to a repo-wide convention. If the lesson invalidates an earlier Phase 1 design choice (see §8 preamble), note the revision in the relevant §8.2 phase entry too.
- **Do not duplicate this content** in CLAUDE.md, AGENTS.md, or PR descriptions. Link here instead.

### 9.2 Periodic audits (scheduled refactoring review)

Every grind/simp set accumulates drift over time: dead facts, redundant lemmas, convention drift from when §4 was tighter, and tactic-macro shapes that `grind` may no longer need. A short, scheduled audit keeps the sets lean.

**Cadence.** Run an audit whenever any of these triggers fires — whichever comes first:

- **Calendar:** every ~6 months (track via a recurring GitHub issue).
- **Activity:** after every second *new* set lands (i.e., audit when about to add the 3rd, 5th, 7th, … set).
- **Preflight:** as part of opening a new set, briefly check the nearest existing set for duplicated facts. This is a ~5-minute check, not a full audit — just prevents the obvious misses.

**Per-set checklist.** Go set-by-set in §7 table order. For each set, answer:

1. **Dead facts?** Temporarily remove a suspect lemma, `lake build` the dependent modules, see if any proof fails. If none, the fact is dead — delete it. (Cheap, because `lake build` is incremental.)
2. **Redundant facts?** Two lemmas that are definitionally equal or where one implies the other via a shorter path. Remove the weaker one.
3. **Fallback misfires?** Where does the macro's `first` block actually fall through to `simp only […]; bv_omega`? If the fallback fires on a recurring shape, either add a grind hint or accept the fallback as permanent for that shape (and note it in §8.2).
4. **Convention drift?** Does the set conform to §4 *today*? Sets created before a §4 rule tightened may not — fix, or record the deviation in the relevant §8.2 entry.
5. **Merge or split?** If two sets have substantial overlap in *consumer files*, consider merging. If one set covers two disjoint fact clusters (e.g., `signExtend12` evaluations vs. shift evaluations), consider splitting by sub-domain.
6. **Entry-count cap (§4).** Sets should stay ≤50 entries (`bv_eval` ≤30). Over cap → split.
7. **Build-time regression?** Re-benchmark one representative dependent module (e.g., `lake build EvmAsm.Evm64.DivMod.LoopComposeN3` for `divmod_addr`) against the baseline captured when the set landed. If >10% slower with no offsetting proof-line reduction, shrink or retire.
8. **Consumer count.** `grep` for callers of the tactic macro. Fewer than 3 consumer files → consider inlining and retiring (the inverse of §6's entry criterion).

**Artifacts.** Open one issue per cycle titled `Grindset audit YYYY-Qx` containing:

- a findings table (set · check · action · rationale),
- one sub-task (linked PR) per action.

The audit issue itself should *not* land changes. Findings become follow-up PRs, one per action, keeping each change small and independently reviewable.

**First audit.** Runs after Phase 4 or Phase 5 lands (enough sets in §7 to make comparisons worthwhile). Before that, the preflight trigger is enough.

### 9.3 PR conventions for new sets

- **Filename:** `<DomainName>Set.lean` or `<DomainName>Norm.lean`, matching `AddrNorm.lean`.
- **Attr-decl file:** if using Layout B (§3), place the attr-decl alongside as `<DomainName>SetAttr.lean` or `<DomainName>NormAttr.lean`.
- **Proof-of-value:** provide one migrated file in the same PR.
- **Documentation:** add a row to §7; update the relevant §8.2 phase status; if the set introduces a new convention, update §4.
- **Benchmark:** record the baseline `lake build` time for the migrated file in the PR description. The §9.2 audits compare against this baseline.

## 10. References

- Lean 4 grind tactic: <https://leanprover.github.io/theorem_proving_in_lean4/> (search for grind), and `Init.Grind` in the Lean source for the `@[grind =]` / `@[grind ←]` / `@[grind →]` annotations.
- Mathlib `register_simp_attr`: `Mathlib/Tactic/Attr/Register.lean` — the canonical example of declaring named simp attributes.
- This repo's `bv_addr` precedent: `EvmAsm/Rv64/Tactics/SeqFrame.lean` — the original tiny-tactic-wrapper pattern (`simp only [BitVec.add_assoc]; rfl`) that the grindset methodology generalizes.
