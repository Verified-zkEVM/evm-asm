<!--
  Project-specific instructions appended to the PR-summary LLM context
  via `additional_instructions_path` in `lean-summary-workflow`. Fed
  into the workflow alongside `CONTRIBUTING.md` and the computed
  progress delta produced by `scripts/progress-delta.sh`.

  Keep this file project-specific. Generic LLM guidance lives upstream
  in the workflow's prompt templates.
-->

# Progress-assessment instructions for the PR-summary agent

evm-asm tracks per-PR progress against a kernel-checked registry
(`EvmAsm/Progress.lean`) rendered to `PROGRESS.md`. The deployment
pre-step has already computed a deterministic delta and inserted it
above under "Computed progress delta for this PR". Use those numbers
verbatim — do not recompute or infer them from the diff.

## Output shape

Emit a top-level section titled exactly `## Progress assessment` at
the **end** of the PR summary. The section is short, factual, and
narrates what the computed delta means in the project's vocabulary.

**Begin the section by reproducing, VERBATIM, the deterministic
`### Risk: <LEVEL>` line and the `### Scorecard` table** from the
computed delta above (the `scripts/progress-delta.sh` output). Do
**not** recompute, reword, re-rank, or omit them — they are a
kernel-/git-derived triage signal for the human reviewer and must
appear unchanged and on every PR (including metric-neutral ones). The
risk label is triage ordering only; never describe it as a merge
verdict. After the verbatim block, add the narrative below.

If the computed delta shows no count changes and no tier transitions,
write the verbatim Risk + Scorecard block followed by exactly:

    Metric-neutral PR (no tier transitions, no count deltas).

Otherwise, include up to four bullets covering:

- **Tier transitions**: list every transition from the computed delta
  verbatim (e.g. `SDIV: partial → proven`). Do not invent or filter.
- **Count deltas**: cite only counts that changed; omit unchanged
  ones. Keep them as numbers, not adjectives ("provenCount +2", not
  "significant progress").
- **Drift risks**: if the diff adds an `evm_<name>_stack_spec_within`
  theorem but the registry change does not mention a matching
  `_<name>_witness` abbrev in `EvmAsm/Progress.lean`, flag it as a
  drift risk. The deterministic gate in `scripts/check-progress.sh`
  catches `PROGRESS.md` drift, but theorem-without-witness is a
  registry-completeness issue the gate does not catch.
- **Obligation mapping**: when a tier transition advances one of the
  9 guest-program obligations from `PROGRESS.md` ("Role in the
  L1-zkEVM stack" section), say so explicitly (e.g.
  `Advances obligation #5: full opcode coverage`). At most one
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

- **Do not recompute counts** from the diff. The numbers above are
  derived from the kernel-checked registry and are authoritative.
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
  specific obligation number from `PROGRESS.md` for a given change,
  skip the mapping. False mappings are worse than no mapping.

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
  L1 zkVM and validates a block + execution witness (see
  `PROGRESS.md` for the 9-item obligation list).

## When to keep the section short

If the PR is a refactor, a doc edit, a test addition, an
infrastructure change, or any other change that does not move any
metric or tier, write the metric-neutral one-liner. Do not pad.
Reviewers read silence as "this PR is not about progress" — that's
the correct signal.
