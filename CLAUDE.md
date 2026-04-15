# CLAUDE.md

See AGENTS.md for full project context, build instructions, and coding patterns.

## PLAN.md Maintenance

Read PLAN.md at the start of each session. Keep it updated as you work:

- **Completed a task/opcode**: Move it to Done, update the status table and counts
- **Discovered new sub-tasks or blockers**: Add them to the relevant phase
- **Added new infrastructure**: Update the Infrastructure section
- **Before committing**: Check if PLAN.md needs updates for the work in this session

## Proof Conventions

- **No `native_decide` or `bv_decide`**: All proofs must be kernel-checkable. Use `decide` for concrete decidable propositions, or `omega`/`simp`/`ext` for bitvector reasoning. `native_decide` bypasses the kernel via code generation, introducing a soundness gap.

## Simp/Grind sets

See **[GRIND.md](GRIND.md)** for the full conventions on registering simp/grind sets, the canonical `divmod_addr` reference implementation, layout patterns, rules of thumb, empirical justification, and the rollout roadmap. Do **not** duplicate that content here or in AGENTS.md — link to GRIND.md instead.
