this is a claude skill to generate a markdown report in the reports directory that gives a high-level, executive summary of the status of the repository. this should be readable by devs who are familiar with the EVM but aren't in the weeds on this project. it should be concise, easy to scan, and totally accurate.

before generating a report, sync this branch with main: merge main into dhsorens/reports so the report reflects the latest state of main. the report header's commit must be the post-merge tip of main.

source all numbers from the kernel-checked source of truth (the registry in EvmAsm/Progress.lean, EvmAsm/Progress/Obligations.lean, EvmAsm/EL/Conformance/All.lean, and the generated PROGRESS.md / DRIFT.md), not the prose docstrings in PLAN.md/CODEGEN.md, which can lag.

data in the header: a "report" header with today's date and the latest git commit on main.

it should begin with an executive summary that gives a one-paragraph, readable, high-level summary of where we are at regarding the roadmap.

the report should then come in three sections:
1. EVM Opcodes, which overs the number of opcodes implemented and verified,
2. STF, which covers the state of the state transition function. for each STF area, be specific about what is *modeled* (data structures / predicates defined, no computation), what is *executable* (a computable Lean def that evaluates), and what is *proven* (theorems / conformance checks) vs not. call out the honest gaps explicitly (e.g. abstract executor hooks, no closed top-level state_transition, gas schedule modeled not proven against the yellow paper). 
3. Codegen, which covers what is possible with codegen

the Codegen section must open with a "Codegen at a glance" subsection containing a compact visual that summarizes the section's bullet points, so it can be dropped into a presentation slide. it has two parts, both sourced from the same kernel-checked numbers used in the bullets:

- a single-row mermaid `flowchart LR` of the stateless-guest pipeline (read_input → RLP decode → dispatch loop → handlers + precompiles → receipts + verdict → post-state root), each node colored by status via `classDef`,
- a small status table (one row per codegen capability: dispatch loop, core handlers, storage, child frames, precompiles, receipts + verdict, scale, lowering proofs, RLP input decoder, MPT pre-state, verified post-state root), each with a one-phrase detail and a status emoji.

use a consistent legend across both: 🟩 done · 🟢 shipped & runnable (unverified) · 🟨 in progress · 🟥 blocked · ⬜ not started. keep it small and scannable — it is meant to be screenshotted onto a slide. update the node/row contents and status colors each cycle to reflect the latest numbers. see the 2026-06-12 report for the canonical layout.

the report should then give a short "what is next" which summarizes some high-level immediate next steps.

the report should then end with a "Development activity since the last report" section that summarizes what the commits in this cycle have actually been focused on. compute the window from the *previous* report: find the most recent existing file in [docs/reports/](docs/reports/) (the report dated before today), read the commit hash in its header, and run `git log <that-commit>..<post-merge-tip-of-main>` over that range. (if no prior report exists, fall back to roughly the last two weeks.) from that range:

- report the raw commit volume (total commits, and the conventional `feat`/`fix` subset) so the cadence is honest,
- group commits by scope (the `feat(scope)` / `fix(scope)` prefix) and collapse them into a small table of 2–4 dominant themes, each with its contributing scopes + counts and a one-phrase description of what the work is — exclude mechanical/housekeeping scopes like `progress` (PROGRESS.md regenerations) from the themes, but you may note their count in passing,
- close with a one-line "in one line:" takeaway naming the single primary focus of the cycle,
- note how many PRs are open at report time (`gh pr list --state open`) and whether they fall in the same themes.

keep this section concise and scannable — a table plus a sentence or two, not a commit-by-commit log.

the report is written in markdown and stored in the [docs/reports/](docs/reports/) directory, and pushed to this branch (dhsorens/reports). we will keep reports just on this branch, so there is never a need for a pull request to main.