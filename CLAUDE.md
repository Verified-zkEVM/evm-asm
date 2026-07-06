# CLAUDE.md

See AGENTS.md for full project context, build instructions, and coding patterns.

## PLAN.md Maintenance

Read PLAN.md at the start of each session. Keep it updated as you work:

- **Completed a task/opcode**: Move it to Done, update the status table and counts
- **Discovered new sub-tasks or blockers**: Add them to the relevant phase
- **Added new infrastructure**: Update the Infrastructure section
- **Before committing**: Check if PLAN.md needs updates for the work in this session

## Proof Conventions

- **No `native_decide` or `bv_decide`** (or any TCB-expanding tactic): All proofs must be kernel-checkable. Both tactics seal their result behind a native-compiler trust axiom (`Lean.ofReduceBool` / `Lean.trustCompiler`) instead of a kernel-checked proof term, introducing a soundness gap. Both have been **fully eliminated** (`native_decide` 206→0, `bv_decide` 290→0); the trusted base is now only the three classical axioms (`propext`, `Classical.choice`, `Quot.sound`).
  - **Use instead**: `decide` for concrete decidable propositions (the Lean kernel's `Nat` is GMP-backed, so `decide` is fast even on concrete 256-bit `BitVec` goals); `omega`/`bv_omega` for linear (bit)vector arithmetic; `simp`/`ext`/`BitVec.eq_of_getLsbD_eq` for bitvector identities (per-bit `getLsbD` reasoning, with `BitVec.getLsbD_of_ge`/`getLsbD_add`/`carry_zero` and block-splits). For multi-limb two's-complement, reuse `EvmWordArith.add_carry_chain_correct`. See `PLAN.md` ("`bv_decide` purge") for the full toolkit.
  - **CI enforcement** (two complementary gates): `scripts/check-forbidden-tactics.sh` is a fast source scan that fails on any `bv_decide`/`native_decide` tactic invocation in `EvmAsm/**.lean` (prose mentions must be wrapped in `` `backticks` ``); `scripts/check-axioms.sh` is the kernel-truth backstop that runs `#print axioms` on the witnessed proofs and rejects any non-classical axiom (including `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, and `bv_decide`/`native_decide` trust axioms). To forbid an additional TCB-expanding tactic, add its token to `FORBIDDEN` in `check-forbidden-tactics.sh`.

## Simp/Grind sets

See **[GRIND.md](GRIND.md)** for the full conventions on registering simp/grind sets, the canonical `divmod_addr` reference implementation, layout patterns, rules of thumb, empirical justification, and the rollout roadmap. Do **not** duplicate that content here or in AGENTS.md — link to GRIND.md instead.
