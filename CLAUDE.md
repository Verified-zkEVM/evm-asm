# CLAUDE.md

See AGENTS.md for full project context, build instructions, and coding patterns.

## PLAN.md Maintenance

Read PLAN.md at the start of each session. Keep it updated as you work:

- **Completed a task/opcode**: Move it to Done, update the status table and counts
- **Discovered new sub-tasks or blockers**: Add them to the relevant phase
- **Added new infrastructure**: Update the Infrastructure section
- **Before committing**: Check if PLAN.md needs updates for the work in this session
- **Progress cockpit** (`docs/index.html`): not a PLAN.md-class hand update.
  Counts are generated (`scripts/progress-cockpit.sh`) and published by CI
  on merge to `main`. Do not copy registry numbers into the HTML.

## Proof-first (DCode) ports

To port another guest routine to the proof-first paradigm (code
generated from a separation-logic derivation, byte-identical to the
deployed bytes), follow **[docs/dcode-porting-playbook.md](docs/dcode-porting-playbook.md)**
end to end — shape selection, proof idioms, the byte gate
(`scripts/check-byte-identity.sh`), and the remaining-routine ledger
live there.  The paradigm itself is documented in `docs/sasm-deriv.md`.

## Proof Conventions

- **No `native_decide` or `bv_decide`** (or any TCB-expanding tactic): All proofs must be kernel-checkable. Both tactics seal their result behind a native-compiler trust axiom (`Lean.ofReduceBool` / `Lean.trustCompiler`) instead of a kernel-checked proof term, introducing a soundness gap. Both have been **fully eliminated** (`native_decide` 206→0, `bv_decide` 290→0); the trusted base is now only the three classical axioms (`propext`, `Classical.choice`, `Quot.sound`) — with one **scoped, documented exception**: the release-pinned [`riscv-zkvm`](https://github.com/Verified-zkEVM/riscv-zkvm) dependency axiomatizes its platform primitives (`RiscvZkvm/Sail/RiscvExtras.lean` declares 75 `axiom`s — terminal I/O, reservations, softfloat hooks). Exactly four reach EvmAsm (`sys_enable_experimental_extensions`, `plat_term_write`, `load_reservation`, `match_reservation`), and only on the Sail-correspondence surface: the 74 `EvmAsm.Rv64.SailEquiv.*` declarations (the single `import RiscvZkvm.Sail.InstsEnd` site is `EvmAsm/Rv64/SailEquiv/StateRel.lean`). All four are non-Prop uninterpreted constants of inhabited types — no proposition is assumed, consistency is unaffected, and the SailEquiv theorems are effectively parametric over the platform hooks. **Any proof that does not touch the Sail layer carries none of these axioms**; the per-declaration accounting is pinned in `scripts/axiom_baseline.json` and audited by `lake exe axiomsweep --check`.
  - **Use instead**: `decide` for concrete decidable propositions (the Lean kernel's `Nat` is GMP-backed, so `decide` is fast even on concrete 256-bit `BitVec` goals); `omega`/`bv_omega` for linear (bit)vector arithmetic; `simp`/`ext`/`BitVec.eq_of_getLsbD_eq` for bitvector identities (per-bit `getLsbD` reasoning, with `BitVec.getLsbD_of_ge`/`getLsbD_add`/`carry_zero` and block-splits). For multi-limb two's-complement, reuse `EvmWordArith.add_carry_chain_correct`. See `PLAN.md` ("`bv_decide` purge") for the full toolkit.
  - **CI enforcement** (two complementary gates): `scripts/check-forbidden-tactics.sh` is a fast source scan that fails on any `bv_decide`/`native_decide` tactic invocation in `EvmAsm/**.lean` (prose mentions must be wrapped in `` `backticks` ``); `scripts/check-axioms.sh` is the kernel-truth backstop that runs `#print axioms` on the witnessed proofs and rejects any non-classical axiom (including `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, and `bv_decide`/`native_decide` trust axioms). To forbid an additional TCB-expanding tactic, add its token to `FORBIDDEN` in `check-forbidden-tactics.sh`. A third, whole-library backstop, `lake exe axiomsweep --check` (report-only in CI during its initial soak), sweeps every reportable `EvmAsm.*` declaration (private declarations included; compiler-generated auxiliaries are traversed, surfacing on their parents) — not just the witnessed registry surface — for kernel-level axiom/`sorryAx` taint against the committed baseline `scripts/axiom_baseline.json`; after intentionally adding or closing a `sorry`, run `lake exe axiomsweep --update-baseline` and commit the diff.

## Module system

See **[MODULES.md](MODULES.md)** for the full conventions on the Lean 4.33
module system: the required file header, `public import` vs plain `import`, why
files carry both `public import X` and `meta import X`, when `@[expose]` is
warranted and how it relates to `@[irreducible]`/`unfold`/`simp [<def>]`, the
`private`-inside-an-exposed-body rule, the mixed metaprogramming trap, the Sail
boundary, and how to read `import-graph-metrics.py --private-cone` in review. Do
**not** duplicate that content here or in AGENTS.md — link to MODULES.md instead.

## Simp/Grind sets

See **[GRIND.md](GRIND.md)** for the full conventions on registering simp/grind sets, the canonical `divmod_addr` reference implementation, layout patterns, rules of thumb, empirical justification, and the rollout roadmap. Do **not** duplicate that content here or in AGENTS.md — link to GRIND.md instead.
