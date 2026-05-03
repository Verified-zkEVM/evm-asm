/-
  EvmAsm.Evm64.MStore.Spec

  Stack-level building blocks for the 256-bit EVM MSTORE program.
-/

import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore.LimbSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for all four MSTORE value-limb byte-unpack blocks, placed after
    the two-instruction address prologue. -/
def mstoreFourLimbsCode
    (addrReg byteReg accReg : Reg) (base : Word) : CodeReq :=
  (mstoreOneLimbCode addrReg byteReg accReg
      32 24 25 26 27 28 29 30 31 (base + 8)).union
    ((mstoreOneLimbCode addrReg byteReg accReg
        40 16 17 18 19 20 21 22 23 (base + 76)).union
      ((mstoreOneLimbCode addrReg byteReg accReg
          48 8 9 10 11 12 13 14 15 (base + 144)).union
        (mstoreOneLimbCode addrReg byteReg accReg
          56 0 1 2 3 4 5 6 7 (base + 212))))

/-- Program form of the four MSTORE value-limb byte-unpack blocks. The source
    limbs are read from the stack in EVM big-endian order and written to memory
    starting at byte offsets 24, 16, 8, and 0 respectively. -/
def mstoreFourLimbsProg
    (addrReg byteReg accReg : Reg) : Program :=
  mstoreOneLimbProg addrReg byteReg accReg
    32 24 25 26 27 28 29 30 31 ;;
  mstoreOneLimbProg addrReg byteReg accReg
    40 16 17 18 19 20 21 22 23 ;;
  mstoreOneLimbProg addrReg byteReg accReg
    48 8 9 10 11 12 13 14 15 ;;
  mstoreOneLimbProg addrReg byteReg accReg
    56 0 1 2 3 4 5 6 7

/-- Public `ofProg` bridge for the four value-limb blocks used by MSTORE. -/
theorem mstoreFourLimbsCode_eq_ofProg
    (addrReg byteReg accReg : Reg) (base : Word) :
    mstoreFourLimbsCode addrReg byteReg accReg base =
      CodeReq.ofProg (base + 8) (mstoreFourLimbsProg addrReg byteReg accReg) := by
  unfold mstoreFourLimbsCode mstoreFourLimbsProg seq
  rw [mstoreOneLimbCode_eq_ofProg, mstoreOneLimbCode_eq_ofProg,
    mstoreOneLimbCode_eq_ofProg, mstoreOneLimbCode_eq_ofProg]
  let p0 := mstoreOneLimbProg addrReg byteReg accReg 32 24 25 26 27 28 29 30 31
  let p1 := mstoreOneLimbProg addrReg byteReg accReg 40 16 17 18 19 20 21 22 23
  let p2 := mstoreOneLimbProg addrReg byteReg accReg 48 8 9 10 11 12 13 14 15
  let p3 := mstoreOneLimbProg addrReg byteReg accReg 56 0 1 2 3 4 5 6 7
  change (CodeReq.ofProg (base + 8) p0).union
      ((CodeReq.ofProg (base + 76) p1).union
        ((CodeReq.ofProg (base + 144) p2).union
          (CodeReq.ofProg (base + 212) p3))) =
    CodeReq.ofProg (base + 8) (p0 ++ (p1 ++ (p2 ++ p3)))
  have h23 :
      (CodeReq.ofProg (base + 144) p2).union
          (CodeReq.ofProg (base + 212) p3) =
        CodeReq.ofProg (base + 144) (p2 ++ p3) := by
    rw [show base + 212 =
        (base + 144) + BitVec.ofNat 64 (4 * p2.length) by
      unfold p2 mstoreOneLimbProg mstoreByteUnpackEightProg LD SRLI SB single seq
      bv_addr]
    exact (CodeReq.ofProg_append (base := base + 144) (p1 := p2) (p2 := p3)).symm
  rw [h23]
  have h123 :
      (CodeReq.ofProg (base + 76) p1).union
          (CodeReq.ofProg (base + 144) (p2 ++ p3)) =
        CodeReq.ofProg (base + 76) (p1 ++ (p2 ++ p3)) := by
    rw [show base + 144 =
        (base + 76) + BitVec.ofNat 64 (4 * p1.length) by
      unfold p1 mstoreOneLimbProg mstoreByteUnpackEightProg LD SRLI SB single seq
      bv_addr]
    exact (CodeReq.ofProg_append (base := base + 76) (p1 := p1) (p2 := p2 ++ p3)).symm
  rw [h123]
  have h0123 :
      (CodeReq.ofProg (base + 8) p0).union
          (CodeReq.ofProg (base + 76) (p1 ++ (p2 ++ p3))) =
        CodeReq.ofProg (base + 8) (p0 ++ (p1 ++ (p2 ++ p3))) := by
    rw [show base + 76 =
        (base + 8) + BitVec.ofNat 64 (4 * p0.length) by
      unfold p0 mstoreOneLimbProg mstoreByteUnpackEightProg LD SRLI SB single seq
      bv_addr]
    exact (CodeReq.ofProg_append (base := base + 8) (p1 := p0) (p2 := p1 ++ (p2 ++ p3))).symm
  exact h0123

theorem mstoreFourLimbsCode_limb0_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        32 24 25 26 27 28 29 30 31 (base + 8)) a = some i →
      (mstoreFourLimbsCode addrReg byteReg accReg base) a = some i := by
  unfold mstoreFourLimbsCode
  exact CodeReq.union_mono_left

/-- CodeReq for the two-instruction MSTORE address prologue. -/
def mstorePrologueCode
    (offReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD offReg .x12 0)).union
    (CodeReq.singleton (base + 4) (.ADD addrReg memBaseReg offReg))

theorem mstorePrologueCode_eq_ofProg
    (offReg addrReg memBaseReg : Reg) (base : Word) :
    mstorePrologueCode offReg addrReg memBaseReg base =
      CodeReq.ofProg base
        (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg) := by
  unfold mstorePrologueCode LD ADD single seq
  change _ =
    CodeReq.ofProg base
      [.LD offReg .x12 0, .ADD addrReg memBaseReg offReg]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_singleton]

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

theorem mstore_prologue_ofProg_spec_within
    (offReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base
        (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  rw [← mstorePrologueCode_eq_ofProg]
  exact mstore_prologue_spec_within offReg addrReg memBaseReg
    sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0

theorem evm_mstore_code_prologue_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (CodeReq.ofProg base (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg)) a =
        some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a =
        some i := by
  unfold evm_mstore_code
  exact CodeReq.ofProg_mono_sub base base
    (evm_mstore offReg valReg byteReg accReg addrReg memBaseReg)
    (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg) 0
    (by bv_omega)
    (evm_mstore_prologue_slice offReg valReg byteReg accReg addrReg memBaseReg)
    (by
      rw [evm_mstore_length]
      change 2 ≤ 71
      norm_num)
    (by
      rw [evm_mstore_length]
      norm_num)

theorem mstore_prologue_evm_mstore_spec_within
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  exact cpsTripleWithin_extend_code
    (h := mstore_prologue_ofProg_spec_within offReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0)
    (hmono := evm_mstore_code_prologue_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

/-- CodeReq for the final MSTORE stack-pop epilogue. -/
def mstoreEpilogueCode (base : Word) : CodeReq :=
  CodeReq.singleton base (.ADDI .x12 .x12 64)

theorem mstoreEpilogueCode_eq_ofProg (base : Word) :
    mstoreEpilogueCode base =
      CodeReq.ofProg base (ADDI .x12 .x12 64) := by
  unfold mstoreEpilogueCode ADDI single
  rw [CodeReq.ofProg_singleton]

/-- MSTORE epilogue spec: pop the offset and value words from the EVM stack. -/
theorem mstore_epilogue_spec_within (sp : Word) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (mstoreEpilogueCode base)
      (((.x12 : Reg) ↦ᵣ sp))
      (((.x12 : Reg) ↦ᵣ (sp + 64))) := by
  unfold mstoreEpilogueCode
  exact addi_spec_gen_same_within (.x12 : Reg) sp 64 base (by nofun)

theorem mstore_epilogue_ofProg_spec_within (sp : Word) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base (ADDI .x12 .x12 64))
      (((.x12 : Reg) ↦ᵣ sp))
      (((.x12 : Reg) ↦ᵣ (sp + 64))) := by
  rw [← mstoreEpilogueCode_eq_ofProg]
  exact mstore_epilogue_spec_within sp base

theorem evm_mstore_code_epilogue_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (CodeReq.ofProg (base + 280) (ADDI .x12 .x12 (BitVec.ofNat 12 64))) a =
        some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a =
        some i := by
  unfold evm_mstore_code
  exact CodeReq.ofProg_mono_sub base (base + 280)
    (evm_mstore offReg valReg byteReg accReg addrReg memBaseReg)
    (ADDI .x12 .x12 (BitVec.ofNat 12 64)) 70
    (by bv_omega)
    (evm_mstore_epilogue_slice offReg valReg byteReg accReg addrReg memBaseReg)
    (by
      rw [evm_mstore_length]
      simp [ADDI, single])
    (by
      rw [evm_mstore_length]
      norm_num)

theorem mstore_epilogue_evm_mstore_spec_within
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp : Word) (base : Word) :
    cpsTripleWithin 1 (base + 280) (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp))
      (((.x12 : Reg) ↦ᵣ (sp + 64))) := by
  have h := mstore_epilogue_ofProg_spec_within sp (base + 280)
  rw [show (base + 280 : Word) + 4 = base + 284 from by bv_addr] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mstore_code_epilogue_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

/-- Compact CodeReq for the full MSTORE program, split into prologue, four
    one-limb byte-unpack blocks, and the final stack-pop epilogue. -/
def mstoreStackCode
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (mstorePrologueCode offReg addrReg memBaseReg base).union
    ((mstoreFourLimbsCode addrReg byteReg accReg base).union
      (mstoreEpilogueCode (base + 280)))

theorem mstoreStackCode_prologue_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mstorePrologueCode offReg addrReg memBaseReg base) a = some i →
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  unfold mstoreStackCode
  exact CodeReq.union_mono_left

theorem mstore_prologue_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  exact cpsTripleWithin_extend_code
    (h := mstore_prologue_spec_within offReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0)
    (hmono := mstoreStackCode_prologue_sub offReg byteReg accReg addrReg memBaseReg base)

end EvmAsm.Evm64
