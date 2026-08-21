<!--
  Project-specific instructions appended to the PR-summary LLM context
  via `additional_instructions_path` in `lean-summary-workflow`. Fed
  into the workflow alongside `CONTRIBUTING.md`.

  ⚠️ #12683: there is NO LONGER a deterministic progress delta in this
  context. `scripts/progress-delta.sh` computed one by diffing the
  COMMITTED `PROGRESS.md` at base and head; that file is generated and
  was removed from the tree, and the head-side numbers cannot be
  recomputed here (it would mean running the PR's own Lean tree under
  `pull_request_target`, which holds a write token + the OPENROUTER_KEY).
  So this file's job changed: it now tells the model what it may say
  WITHOUT authoritative numbers, and the answer is mostly "no numbers".

  Keep this file project-specific. Generic LLM guidance lives upstream
  in the workflow's prompt templates.
-->

# Progress-assessment instructions for the PR-summary agent

evm-asm tracks per-PR progress against a kernel-checked registry
(`EvmAsm/Progress.lean`). **You are not given the registry's counts**, and
you cannot derive them from the diff: an entry's tier is a claim about a
theorem the Lean kernel checked, not about the text of a patch. Say
nothing that implies you know a count or a total.

## Output shape

Emit a top-level section titled exactly `## Progress assessment` at
the **end** of the PR summary. The section is short, factual, and
describes only what the DIFF ITSELF shows about the registry.

If the diff does not touch `EvmAsm/Progress.lean`,
`EvmAsm/Progress/Routines.lean`, `EvmAsm/Progress/Correspondence.lean` or
`EvmAsm/Progress/Obligations.lean`, write exactly:

    Registry untouched (no tier or obligation claim changes in this PR).

Otherwise, include up to three bullets covering:

- **Tier edits**: quote the registry rows the diff changes, in the
  diff's own words (e.g. `SDIV: .partly → .proven`). This is an edit to
  a claim, not a measurement — do not restate it as a count, a total, or
  a percentage, and do not add rows the diff does not touch.
- **Drift risks**: if the diff adds an `evm_<name>_stack_spec_within`
  theorem but the registry change does not mention a matching
  `_<name>_witness` abbrev in `EvmAsm/Progress.lean`, flag it as a
  drift risk. Nothing gates theorem-without-witness; it is a
  registry-completeness issue a human has to notice.
- **Obligation mapping**: when a registry edit advances one of the
  10 guest-program obligations (the matrix in
  `EvmAsm/Progress/Obligations.lean`, rendered in `DRIFT.md`), say so
  explicitly (e.g. `Advances obligation #5: full opcode coverage`), and
  only when the diff names that obligation or its blocker. At most one
  obligation per bullet.

## Statement-strength review (spec quality ONLY — never correctness)

> Steering Phase 4, R-B3 / D5. This is the **one** place the LLM adds
> signal the kernel cannot: the kernel proves a statement *is true*, but
> it cannot judge whether the statement is *strong enough to be worth
> proving*. Layer your judgement **only** on this question. **Never**
> opine on whether a proof is correct — the Lean kernel is the perfect,
> non-gameable oracle for that, and an LLM correctness verdict is itself
> gameable. If a theorem elaborated, it is correct. Full stop.

When this PR **adds or changes a top-level stack-spec triple** (a
`theorem evm_<name>_stack_spec[_within] …`), assess its *statement
strength* against EVM semantics and emit a single sign-off line at the
end of the Progress assessment:

    Statement-strength: <OK | REVIEW> — <≤ 1 sentence>

Mark `REVIEW` (and say which check failed) if any of these hold; else
`OK`:

- **Vacuous / over-restricted precondition.** Does the antecedent
  exclude a large, real input region so the triple is near-vacuous? The
  DIV-class trap is the canonical example: a spec quantified only over
  `b.getLimbN 3 = 0` looks proven but covers a fraction of inputs. A
  `conditional`-tier entry is *expected* to be domain-restricted — flag
  only if a `proven`-tier triple hides such a restriction, or if a
  `conditional` triple lacks a stated/`coverRef` reachable domain.
- **Incomplete postcondition.** Does it cover the full observable
  effect — **stack** (pointer advanced + result word), **memory** (if
  the opcode touches memory), **gas** (charged/bounded), and
  **halting / cycle bound** (`cpsTripleWithin N`)? A postcondition that
  asserts the stack result but silently drops gas or memory is weaker
  than the opcode's real contract.
- **Trivial / mismatched statement.** Does the triple actually model the
  named opcode, or does it restate a tautology / a renamed helper lemma?

Keep it to one line. If the PR adds no top-level triple, **omit the
sign-off line entirely** (do not write "Statement-strength: n/a"). This
is advisory review fodder for the human — it does not gate the merge and
must never contradict the kernel.

## What NOT to do

- **Do not state counts at all** — not from the diff, not from
  memory, not from a previous PR summary. No authoritative delta is
  supplied to you (#12683). A count you produce is a guess wearing a
  number's clothes, and this project's whole steering signal is that
  its numbers are kernel-derived.
- **Do not judge proof correctness.** The kernel already did, perfectly.
  Your statement-strength note is about the *spec*, not the *proof*.
- **Do not editorialize** ("major step forward", "significant
  improvement", "well done"). Stay factual.
- **Do not duplicate** the existing `Mathematical Formalization` /
  `Proof Completion (sorries removed)` / `Infrastructure` sections
  the workflow already produces. The Progress assessment is a
  *quantitative* commentary on top of those.
- **Do not flag tier downgrades** as failures. A `proven` → `partial`
  transition might mean a generalization is in progress and the
  spec has been deliberately weakened. State the transition;
  don't judge it.
- **Do not invent obligation mappings.** If you cannot point at a
  specific obligation number from `EvmAsm/Progress/Obligations.lean`
  for a given change, skip the mapping. False mappings are worse than
  no mapping.

## Vocabulary reference

These terms appear in the project and the registry; use them
consistently:

- `proven` / `partial` / `execSpec` / `notStarted` — the four
  `ProofTier` values defined in `EvmAsm/Progress.lean`.
- `cpsTripleWithin N` — bounded Hoare triple over a verified RV64
  step count of at most `N`.
- `EvmWord` — `BitVec 256`; 4-limb 64-bit representation in RV64.
- `stack spec` — top-level Hoare triple over the EVM stack
  (precondition: stack pointer + EvmWord operands; postcondition:
  stack pointer advanced + EvmWord result).
- `witness abbrev` — the `_<lower>_witness := @<theorem>` declarations
  in `EvmAsm/Progress.lean` that fail elaboration if a referenced
  theorem is renamed or deleted.
- `guest program` — in this project, the RV64 ELF that runs inside an
  L1 zkVM and validates a block + execution witness (the 10-item
  obligation matrix is in `EvmAsm/Progress/Obligations.lean`, rendered
  in `DRIFT.md`).

## When to keep the section short

If the PR is a refactor, a doc edit, a test addition, an
infrastructure change, or any other change that does not move any
metric or tier, write the metric-neutral one-liner. Do not pad.
Reviewers read silence as "this PR is not about progress" — that's
the correct signal.
