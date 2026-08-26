module

/-
`divK_mulsub_correction_addback_beq_v4_spec_within_noNop` used to be declared
BOTH here and in `CorrectionAddbackBeq.lean` — the same statement, proved twice
with different tactic scripts, under the same namespace `EvmAsm.Evm64`. Pre-module
Lean silently tolerated the collision; the module system's import merge rejects
it outright:

    import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq failed,
    environment already contains
    'EvmAsm.Evm64.divK_mulsub_correction_addback_beq_v4_spec_within_noNop'
    from EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeqV4NoNop

Both modules are in `EvmAsm.Evm64`'s import closure, so this was a latent defect
on `main`, not something the migration introduced — the migration is only what
made it visible. The proof now lives once, in `CorrectionAddbackBeq.lean`
alongside its two `..._beq_spec_within` siblings. This module is kept as a
re-export so its four importers do not have to change.
-/

public import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq

@[expose] public section
