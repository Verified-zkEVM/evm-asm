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


<!-- BEGIN BEADS INTEGRATION v:1 profile:minimal hash:ca08a54f -->
## Beads Issue Tracker

This project uses **bd (beads)** for issue tracking. Run `bd prime` to see full workflow context and commands.

### Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --claim  # Claim work
bd close <id>         # Complete work
```

### Rules

- Use `bd` for ALL task tracking — do NOT use TodoWrite, TaskCreate, or markdown TODO lists
- Run `bd prime` for detailed command reference and session close protocol
- Use `bd remember` for persistent knowledge — do NOT use MEMORY.md files

## Session Completion

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd dolt push
   git push
   git status  # MUST show "up to date with origin"
   ```
5. **Clean up** - Clear stashes, prune remote branches
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds
<!-- END BEADS INTEGRATION -->
