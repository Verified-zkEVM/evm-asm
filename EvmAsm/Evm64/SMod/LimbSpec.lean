/-
  EvmAsm.Evm64.SMod.LimbSpec

  Per-block / per-limb cpsTriple specs for SMOD sub-blocks.

  The leaf save-`ra` and saved-`ra` return blocks live here. The
  multi-instruction sign extraction, abs negation, callable-modulo JAL,
  and sign-correction blocks are exposed through the `SMod.Compose`
  layer, where their code handles and caller frame are pinned.
-/

module

public import EvmAsm.Evm64.SMod.Program
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.XSimp
public import EvmAsm.Rv64.Tactics.RunBlock

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for `evm_smod_save_ra_block` at byte offset `base`. -/
abbrev evm_smod_save_ra_block_code (savedRaReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_smod_save_ra_block savedRaReg)

/-- 1-instruction leaf spec: `ADDI savedRaReg, x1, 0` copies the current
    `x1` (return address) into a preserved scratch register. Used to save
    `ra` across the nested `JAL` to `evm_mod_callable` in the SMOD wrapper
    (mirror of `evm_sdiv_save_ra_block_spec_within`). -/
theorem evm_smod_save_ra_block_spec_within
    (savedRaReg : Reg) (vRa vSavedOld : Word) (base : Word)
    (hsaved_ne_x0 : savedRaReg ≠ .x0) :
    let code := evm_smod_save_ra_block_code savedRaReg base
    cpsTripleWithin 1 base (base + 4) code
      ((.x1 ↦ᵣ vRa) ** (savedRaReg ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) ** (savedRaReg ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base (evm_smod_save_ra_block savedRaReg)) _ _
  rw [show CodeReq.ofProg base (evm_smod_save_ra_block savedRaReg) =
      CodeReq.singleton base (.ADDI savedRaReg .x1 0) from CodeReq.ofProg_singleton]
  exact addi_spec_within savedRaReg .x1 vRa vSavedOld 0 base hsaved_ne_x0

/-- CodeReq for `evm_smod_saved_ra_ret_block` at byte offset `base`. -/
abbrev evm_smod_saved_ra_ret_block_code (savedRaReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_smod_saved_ra_ret_block savedRaReg)

/-- 1-instruction leaf spec: `JALR x0, savedRaReg, 0` returns to the
    address saved by `evm_smod_save_ra_block`. Exit pc is
    `(vSavedRa + 0) &&& ~~~1` per the standard `JALR x0` semantics. -/
theorem evm_smod_saved_ra_ret_block_spec_within
    (savedRaReg : Reg) (vSavedRa : Word) (base : Word) :
    let code := evm_smod_saved_ra_ret_block_code savedRaReg base
    cpsTripleWithin 1 base
        ((vSavedRa + signExtend12 (0 : BitVec 12)) &&& ~~~1) code
      (savedRaReg ↦ᵣ vSavedRa)
      (savedRaReg ↦ᵣ vSavedRa) := by
  show cpsTripleWithin 1 base _
    (CodeReq.ofProg base (evm_smod_saved_ra_ret_block savedRaReg)) _ _
  rw [show CodeReq.ofProg base (evm_smod_saved_ra_ret_block savedRaReg) =
      CodeReq.singleton base (.JALR .x0 savedRaReg 0) from CodeReq.ofProg_singleton]
  exact jalr_x0_spec_gen_within savedRaReg vSavedRa 0 base

end EvmAsm.Evm64
