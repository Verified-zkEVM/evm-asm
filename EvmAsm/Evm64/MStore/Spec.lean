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

theorem mstoreFourLimbsProg_length (addrReg byteReg accReg : Reg) :
    (mstoreFourLimbsProg addrReg byteReg accReg).length = 68 := by
  unfold mstoreFourLimbsProg mstoreOneLimbProg mstoreByteUnpackEightProg
    LD SRLI SB single seq
  rfl

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

/-- Compact CodeReq for the full MSTORE program, split into prologue, four
    one-limb byte-unpack blocks, and the final stack-pop epilogue. -/
def mstoreStackCode
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (mstorePrologueCode offReg addrReg memBaseReg base).union
    ((mstoreFourLimbsCode addrReg byteReg accReg base).union
      (mstoreEpilogueCode (base + 280)))

/-- Program form of the full MSTORE stack helper: compute the target memory
    address, unpack all four value limbs, then pop the two consumed EVM words. -/
def mstoreStackProg
    (offReg byteReg accReg addrReg memBaseReg : Reg) : Program :=
  (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg) ;;
  mstoreFourLimbsProg addrReg byteReg accReg ;;
  ADDI .x12 .x12 64

theorem mstoreStackProg_length
    (offReg byteReg accReg addrReg memBaseReg : Reg) :
    (mstoreStackProg offReg byteReg accReg addrReg memBaseReg).length = 71 := by
  unfold mstoreStackProg LD ADD ADDI single seq
  simp only [Program.length_append, List.length_cons, List.length_nil,
    mstoreFourLimbsProg_length]

/-- Public `ofProg` bridge for the full MSTORE stack helper code. -/
theorem mstoreStackCode_eq_ofProg
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    mstoreStackCode offReg byteReg accReg addrReg memBaseReg base =
      CodeReq.ofProg base
        (mstoreStackProg offReg byteReg accReg addrReg memBaseReg) := by
  unfold mstoreStackCode mstoreStackProg seq
  rw [mstorePrologueCode_eq_ofProg, mstoreFourLimbsCode_eq_ofProg,
    mstoreEpilogueCode_eq_ofProg]
  let p0 := LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg
  let p1 := mstoreFourLimbsProg addrReg byteReg accReg
  let p2 := ADDI .x12 .x12 64
  change (CodeReq.ofProg base p0).union
      ((CodeReq.ofProg (base + 8) p1).union
        (CodeReq.ofProg (base + 280) p2)) =
    CodeReq.ofProg base (p0 ++ (p1 ++ p2))
  have h12 :
      (CodeReq.ofProg (base + 8) p1).union
          (CodeReq.ofProg (base + 280) p2) =
        CodeReq.ofProg (base + 8) (p1 ++ p2) := by
    rw [show base + 280 =
        (base + 8) + BitVec.ofNat 64 (4 * p1.length) by
      rw [show p1.length = 68 by
        unfold p1
        exact mstoreFourLimbsProg_length addrReg byteReg accReg]
      bv_addr]
    exact (CodeReq.ofProg_append (base := base + 8) (p1 := p1) (p2 := p2)).symm
  rw [h12]
  have h012 :
      (CodeReq.ofProg base p0).union (CodeReq.ofProg (base + 8) (p1 ++ p2)) =
        CodeReq.ofProg base (p0 ++ (p1 ++ p2)) := by
    rw [show base + 8 = base + BitVec.ofNat 64 (4 * p0.length) by
      rw [show p0.length = 2 by
        unfold p0 LD ADD single seq
        rfl]
      change base + 8 = base + 8
      rfl]
    exact (CodeReq.ofProg_append (base := base) (p1 := p0) (p2 := p1 ++ p2)).symm
  exact h012

theorem mstoreStackProg_eq_evm_mstore
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) :
    mstoreStackProg offReg byteReg accReg addrReg memBaseReg =
      evm_mstore offReg valReg byteReg accReg addrReg memBaseReg := by
  unfold mstoreStackProg mstoreFourLimbsProg mstoreOneLimbProg
    mstoreByteUnpackEightProg evm_mstore
  rfl

theorem mstoreStackCode_eq_evm_mstore_code
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    mstoreStackCode offReg byteReg accReg addrReg memBaseReg base =
      evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base := by
  rw [mstoreStackCode_eq_ofProg,
    mstoreStackProg_eq_evm_mstore offReg valReg byteReg accReg addrReg memBaseReg]

theorem mstoreStackCode_prologue_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mstorePrologueCode offReg addrReg memBaseReg base) a = some i →
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  unfold mstoreStackCode
  exact CodeReq.union_mono_left

theorem mstoreStackCode_four_limbs_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mstoreFourLimbsCode addrReg byteReg accReg base) a = some i →
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  rw [mstoreStackCode_eq_ofProg, mstoreFourLimbsCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 8)
    (mstoreStackProg offReg byteReg accReg addrReg memBaseReg)
    (mstoreFourLimbsProg addrReg byteReg accReg) 2
    (by
      change base + 8 = base + 8
      rfl)
    (by
      rw [show (mstoreFourLimbsProg addrReg byteReg accReg).length = 68 from
        mstoreFourLimbsProg_length addrReg byteReg accReg]
      unfold mstoreStackProg mstoreFourLimbsProg mstoreOneLimbProg
        mstoreByteUnpackEightProg LD ADD ADDI SRLI SB single seq
      rfl)
    (by
      rw [mstoreFourLimbsProg_length, mstoreStackProg_length]
      decide)
    (by
      rw [mstoreStackProg_length]
      omega)

theorem evm_mstore_code_four_limbs_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mstoreFourLimbsCode addrReg byteReg accReg base) a = some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a = some i := by
  rw [← mstoreStackCode_eq_evm_mstore_code
    offReg valReg byteReg accReg addrReg memBaseReg base]
  exact mstoreStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base

theorem mstore_four_limbs_evm_mstore_spec_within
    {nSteps : Nat} {P Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin nSteps (base + 8) (base + 280)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P Q) :
    cpsTripleWithin nSteps (base + 8) (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (evm_mstore_code_four_limbs_sub offReg valReg byteReg accReg addrReg memBaseReg base)
    h

theorem mstoreStackCode_epilogue_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mstoreEpilogueCode (base + 280)) a = some i →
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  rw [mstoreStackCode_eq_ofProg, mstoreEpilogueCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 280)
    (mstoreStackProg offReg byteReg accReg addrReg memBaseReg)
    (ADDI .x12 .x12 64) 70
    (by
      change base + 280 = base + 280
      rfl)
    (by
      change ((mstoreStackProg offReg byteReg accReg addrReg memBaseReg).drop 70).take 1 =
        (ADDI .x12 .x12 64)
      unfold mstoreStackProg mstoreFourLimbsProg mstoreOneLimbProg
        mstoreByteUnpackEightProg LD ADD ADDI SRLI SB single seq
      rfl)
    (by
      rw [show (ADDI .x12 .x12 64).length = 1 from rfl]
      rw [mstoreStackProg_length])
    (by
      rw [mstoreStackProg_length]
      omega)

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
  rw [← mstoreStackCode_eq_evm_mstore_code
    offReg valReg byteReg accReg addrReg memBaseReg base]
  exact mstore_prologue_stack_spec_within offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0

theorem mstore_prologue_evm_mstore_frame_spec_within
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  exact cpsTripleWithin_frameR F hF
    (mstore_prologue_evm_mstore_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0)

theorem mstore_epilogue_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp : Word) (base : Word) :
    cpsTripleWithin 1 (base + 280) (base + 284)
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp))
      (((.x12 : Reg) ↦ᵣ (sp + 64))) := by
  have h := cpsTripleWithin_extend_code
    (h := mstore_epilogue_spec_within sp (base + 280))
    (hmono := mstoreStackCode_epilogue_sub offReg byteReg accReg addrReg memBaseReg base)
  rw [show (base + 280 : Word) + 4 = base + 284 from by bv_addr] at h
  exact h

theorem mstore_epilogue_evm_mstore_spec_within
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp : Word) (base : Word) :
    cpsTripleWithin 1 (base + 280) (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp))
      (((.x12 : Reg) ↦ᵣ (sp + 64))) := by
  rw [← mstoreStackCode_eq_evm_mstore_code
    offReg valReg byteReg accReg addrReg memBaseReg base]
  exact mstore_epilogue_stack_spec_within offReg byteReg accReg addrReg memBaseReg
    sp base

theorem mstore_epilogue_evm_mstore_frame_spec_within
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp : Word) (base : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (base + 280) (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** F)
      (((.x12 : Reg) ↦ᵣ (sp + 64)) ** F) := by
  exact cpsTripleWithin_frameR F hF
    (mstore_epilogue_evm_mstore_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg sp base)

end EvmAsm.Evm64
