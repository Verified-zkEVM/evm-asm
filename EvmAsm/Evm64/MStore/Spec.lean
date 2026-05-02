/-
  EvmAsm.Evm64.MStore.Spec

  Stack-level building blocks for the 256-bit EVM MSTORE program.
-/

import EvmAsm.Evm64.MStore.LimbSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the two-instruction MSTORE address prologue. -/
def mstorePrologueCode
    (offReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD offReg .x12 0)).union
    (CodeReq.singleton (base + 4) (.ADD addrReg memBaseReg offReg))

/--
  MSTORE prologue spec: load the low 64-bit offset limb from the EVM stack and
  compute the concrete byte address `memBase + offset` used by the four
  subsequent limb-store blocks.
-/
theorem mstore_prologue_spec_within
    (offReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mstorePrologueCode offReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  unfold mstorePrologueCode
  have h_ld := ld_spec_within offReg (.x12 : Reg) sp offOld offset 0 base h_off_ne_x0
  rw [show (sp + signExtend12 (0 : BitVec 12) : Word) = sp from by
    rw [signExtend12_0]; bv_omega] at h_ld
  have h_add := add_spec_gen_within addrReg memBaseReg offReg memBase offset addrOld
    (base + 4) h_addr_ne_x0
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at h_add
  runBlock h_ld h_add

/-- CodeReq for the final MSTORE stack-pop epilogue. -/
def mstoreEpilogueCode (base : Word) : CodeReq :=
  CodeReq.singleton base (.ADDI .x12 .x12 64)

/-- MSTORE epilogue spec: pop the offset and value words from the EVM stack. -/
theorem mstore_epilogue_spec_within (sp : Word) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (mstoreEpilogueCode base)
      (((.x12 : Reg) ↦ᵣ sp))
      (((.x12 : Reg) ↦ᵣ (sp + 64))) := by
  unfold mstoreEpilogueCode
  exact addi_spec_gen_same_within (.x12 : Reg) sp 64 base (by nofun)

end EvmAsm.Evm64
