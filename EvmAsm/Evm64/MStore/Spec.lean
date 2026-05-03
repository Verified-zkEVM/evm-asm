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

theorem mstoreFourLimbsCode_limb1_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        40 16 17 18 19 20 21 22 23 (base + 76)) a = some i →
      (mstoreFourLimbsCode addrReg byteReg accReg base) a = some i := by
  rw [mstoreFourLimbsCode_eq_ofProg, mstoreOneLimbCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub (base + 8) (base + 76)
    (mstoreFourLimbsProg addrReg byteReg accReg)
    (mstoreOneLimbProg addrReg byteReg accReg 40 16 17 18 19 20 21 22 23)
    17
    (by bv_addr)
    (by
      change ((mstoreFourLimbsProg addrReg byteReg accReg).drop 17).take 17 =
        mstoreOneLimbProg addrReg byteReg accReg 40 16 17 18 19 20 21 22 23
      unfold mstoreFourLimbsProg mstoreOneLimbProg mstoreByteUnpackEightProg
        LD SRLI SB single seq
      rfl)
    (by
      rw [show (mstoreOneLimbProg addrReg byteReg accReg
          40 16 17 18 19 20 21 22 23).length = 17 by
        unfold mstoreOneLimbProg mstoreByteUnpackEightProg LD SRLI SB single seq
        rfl]
      rw [mstoreFourLimbsProg_length]
      omega)
    (by
      rw [mstoreFourLimbsProg_length]
      omega)

theorem mstoreFourLimbsCode_limb2_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        48 8 9 10 11 12 13 14 15 (base + 144)) a = some i →
      (mstoreFourLimbsCode addrReg byteReg accReg base) a = some i := by
  rw [mstoreFourLimbsCode_eq_ofProg, mstoreOneLimbCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub (base + 8) (base + 144)
    (mstoreFourLimbsProg addrReg byteReg accReg)
    (mstoreOneLimbProg addrReg byteReg accReg 48 8 9 10 11 12 13 14 15)
    34
    (by bv_addr)
    (by
      change ((mstoreFourLimbsProg addrReg byteReg accReg).drop 34).take 17 =
        mstoreOneLimbProg addrReg byteReg accReg 48 8 9 10 11 12 13 14 15
      unfold mstoreFourLimbsProg mstoreOneLimbProg mstoreByteUnpackEightProg
        LD SRLI SB single seq
      rfl)
    (by
      rw [show (mstoreOneLimbProg addrReg byteReg accReg
          48 8 9 10 11 12 13 14 15).length = 17 by
        unfold mstoreOneLimbProg mstoreByteUnpackEightProg LD SRLI SB single seq
        rfl]
      rw [mstoreFourLimbsProg_length]
      omega)
    (by
      rw [mstoreFourLimbsProg_length]
      omega)

theorem mstoreFourLimbsCode_limb3_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        56 0 1 2 3 4 5 6 7 (base + 212)) a = some i →
      (mstoreFourLimbsCode addrReg byteReg accReg base) a = some i := by
  rw [mstoreFourLimbsCode_eq_ofProg, mstoreOneLimbCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub (base + 8) (base + 212)
    (mstoreFourLimbsProg addrReg byteReg accReg)
    (mstoreOneLimbProg addrReg byteReg accReg 56 0 1 2 3 4 5 6 7)
    51
    (by bv_addr)
    (by
      change ((mstoreFourLimbsProg addrReg byteReg accReg).drop 51).take 17 =
        mstoreOneLimbProg addrReg byteReg accReg 56 0 1 2 3 4 5 6 7
      unfold mstoreFourLimbsProg mstoreOneLimbProg mstoreByteUnpackEightProg
        LD SRLI SB single seq
      rfl)
    (by
      rw [show (mstoreOneLimbProg addrReg byteReg accReg
          56 0 1 2 3 4 5 6 7).length = 17 by
        unfold mstoreOneLimbProg mstoreByteUnpackEightProg LD SRLI SB single seq
        rfl]
      rw [mstoreFourLimbsProg_length])
    (by
      rw [mstoreFourLimbsProg_length]
      omega)

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

theorem mstore_four_limb_sequence_spec_within
    {n0 n1 n2 n3 : Nat} {P0 P1 P2 P3 P4 : Assertion}
    (addrReg byteReg accReg : Reg) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P0 P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P3 P4) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 280)
      (mstoreFourLimbsCode addrReg byteReg accReg base) P0 P4 := by
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr h0 h1)
      h2)
    h3

/-- Pure five-dword fold for the full 32-byte MSTORE body. The executable
    code stores source offsets 32, 40, 48, and 56 in that order, so adjacent
    dword pairs overlap and must be threaded through the fold. -/
def mstoreFourLimbStore
    (d0 d1 d2 d3 d4 limb32 limb40 limb48 limb56 : Word) (start : Nat) :
    Word × Word × Word × Word × Word :=
  let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
  let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
  let p2 := MStore.mstoreDwordPairStoreLimb d1 p1.1 limb48 start
  let p3 := MStore.mstoreDwordPairStoreLimb d0 p2.1 limb56 start
  (p3.1, p3.2, p2.2, p1.2, p0.2)

theorem mstoreFourLimbStore_unfold
    (d0 d1 d2 d3 d4 limb32 limb40 limb48 limb56 : Word) (start : Nat) :
    mstoreFourLimbStore d0 d1 d2 d3 d4 limb32 limb40 limb48 limb56 start =
      (let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
       let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
       let p2 := MStore.mstoreDwordPairStoreLimb d1 p1.1 limb48 start
       let p3 := MStore.mstoreDwordPairStoreLimb d0 p2.1 limb56 start
       (p3.1, p3.2, p2.2, p1.2, p0.2)) := by
  rfl

@[irreducible]
def mstoreFourLimbBodyPre
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ d2) **
  (d3Addr ↦ₘ d3) ** (d4Addr ↦ₘ d4) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)

theorem mstoreFourLimbBodyPre_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) :
    mstoreFourLimbBodyPre addrReg byteReg accReg
        addrPtr byteOld accOld d0 d1 d2 d3 d4
        d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56 =
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ d2) **
       (d3Addr ↦ₘ d3) ** (d4Addr ↦ₘ d4) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) := by
  delta mstoreFourLimbBodyPre
  rfl

@[irreducible]
def mstoreFourLimbBodyMid0
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) : Assertion :=
  let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb32) ** (accReg ↦ᵣ limb32) **
  (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ d2) **
  (d3Addr ↦ₘ p0.1) ** (d4Addr ↦ₘ p0.2) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)

theorem mstoreFourLimbBodyMid0_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) :
    mstoreFourLimbBodyMid0 addrReg byteReg accReg
        addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
        limb32 limb40 limb48 limb56 start =
      (let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
       (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb32) ** (accReg ↦ᵣ limb32) **
       (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ d2) **
       (d3Addr ↦ₘ p0.1) ** (d4Addr ↦ₘ p0.2) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) := by
  delta mstoreFourLimbBodyMid0
  rfl

@[irreducible]
def mstoreFourLimbBodyMid1
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) : Assertion :=
  let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
  let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb40) ** (accReg ↦ᵣ limb40) **
  (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ p1.1) **
  (d3Addr ↦ₘ p1.2) ** (d4Addr ↦ₘ p0.2) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)

theorem mstoreFourLimbBodyMid1_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) :
    mstoreFourLimbBodyMid1 addrReg byteReg accReg
        addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
        limb32 limb40 limb48 limb56 start =
      (let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
       let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
       (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb40) ** (accReg ↦ᵣ limb40) **
       (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ p1.1) **
       (d3Addr ↦ₘ p1.2) ** (d4Addr ↦ₘ p0.2) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) := by
  delta mstoreFourLimbBodyMid1
  rfl

@[irreducible]
def mstoreFourLimbBodyMid2
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) : Assertion :=
  let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
  let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
  let p2 := MStore.mstoreDwordPairStoreLimb d1 p1.1 limb48 start
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb48) ** (accReg ↦ᵣ limb48) **
  (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ p2.1) ** (d2Addr ↦ₘ p2.2) **
  (d3Addr ↦ₘ p1.2) ** (d4Addr ↦ₘ p0.2) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)

theorem mstoreFourLimbBodyMid2_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) :
    mstoreFourLimbBodyMid2 addrReg byteReg accReg
        addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
        limb32 limb40 limb48 limb56 start =
      (let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
       let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
       let p2 := MStore.mstoreDwordPairStoreLimb d1 p1.1 limb48 start
       (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb48) ** (accReg ↦ᵣ limb48) **
       (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ p2.1) ** (d2Addr ↦ₘ p2.2) **
       (d3Addr ↦ₘ p1.2) ** (d4Addr ↦ₘ p0.2) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) := by
  delta mstoreFourLimbBodyMid2
  rfl

@[irreducible]
def mstoreFourLimbBodyPost
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) : Assertion :=
  let stored := mstoreFourLimbStore d0 d1 d2 d3 d4 limb32 limb40 limb48 limb56 start
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb56) ** (accReg ↦ᵣ limb56) **
  (d0Addr ↦ₘ stored.1) ** (d1Addr ↦ₘ stored.2.1) **
  (d2Addr ↦ₘ stored.2.2.1) ** (d3Addr ↦ₘ stored.2.2.2.1) **
  (d4Addr ↦ₘ stored.2.2.2.2) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)

theorem mstoreFourLimbBodyPost_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) :
    mstoreFourLimbBodyPost addrReg byteReg accReg
        addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
        limb32 limb40 limb48 limb56 start =
      (let stored := mstoreFourLimbStore d0 d1 d2 d3 d4 limb32 limb40 limb48 limb56 start
       (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limb56) ** (accReg ↦ᵣ limb56) **
       (d0Addr ↦ₘ stored.1) ** (d1Addr ↦ₘ stored.2.1) **
       (d2Addr ↦ₘ stored.2.2.1) ** (d3Addr ↦ₘ stored.2.2.2.1) **
       (d4Addr ↦ₘ stored.2.2.2.2) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) := by
  delta mstoreFourLimbBodyPost
  rfl

theorem mstore_four_limb_body_sequence_spec_within
    {n0 n1 n2 n3 : Nat}
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word)
    (start : Nat) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreOneLimbPre addrReg byteReg accReg
          addrPtr byteOld accOld d3 d4 d3Addr d4Addr sp limb32 (32 : BitVec 12))
        (mstoreOneLimbPost addrReg byteReg accReg
          addrPtr d3 d4 d3Addr d4Addr sp limb32 start (32 : BitVec 12)))
    (h1 :
      let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreOneLimbPre addrReg byteReg accReg
          addrPtr limb32 limb32 d2 p0.1 d2Addr d3Addr sp limb40 (40 : BitVec 12))
        (mstoreOneLimbPost addrReg byteReg accReg
          addrPtr d2 p0.1 d2Addr d3Addr sp limb40 start (40 : BitVec 12)))
    (h2 :
      let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
      let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreOneLimbPre addrReg byteReg accReg
          addrPtr limb40 limb40 d1 p1.1 d1Addr d2Addr sp limb48 (48 : BitVec 12))
        (mstoreOneLimbPost addrReg byteReg accReg
          addrPtr d1 p1.1 d1Addr d2Addr sp limb48 start (48 : BitVec 12)))
    (h3 :
      let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
      let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
      let p2 := MStore.mstoreDwordPairStoreLimb d1 p1.1 limb48 start
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreOneLimbPre addrReg byteReg accReg
          addrPtr limb48 limb48 d0 p2.1 d0Addr d1Addr sp limb56 (56 : BitVec 12))
        (mstoreOneLimbPost addrReg byteReg accReg
          addrPtr d0 p2.1 d0Addr d1Addr sp limb56 start (56 : BitVec 12))) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 280)
      (mstoreFourLimbsCode addrReg byteReg accReg base)
      (mstoreFourLimbBodyPre addrReg byteReg accReg
        addrPtr byteOld accOld d0 d1 d2 d3 d4
        d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56)
      (mstoreFourLimbBodyPost addrReg byteReg accReg
        addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
        limb32 limb40 limb48 limb56 start) := by
  let p0 := MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start
  let p1 := MStore.mstoreDwordPairStoreLimb d2 p0.1 limb40 start
  let p2 := MStore.mstoreDwordPairStoreLimb d1 p1.1 limb48 start
  let rest0 : Assertion :=
    (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ d2) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)
  let h0Framed := cpsTripleWithin_frameR rest0 (by pcFree) h0
  have h0Body :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreFourLimbBodyPre addrReg byteReg accReg
          addrPtr byteOld accOld d0 d1 d2 d3 d4
          d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56)
        (mstoreFourLimbBodyMid0 addrReg byteReg accReg
          addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        rw [mstoreFourLimbBodyPre_unfold] at hp
        rw [mstoreOneLimbPre_unfold]
        unfold rest0
        xperm_hyp hp)
      (fun _ hp => by
        rw [mstoreOneLimbPost_unfold] at hp
        rw [mstoreFourLimbBodyMid0_unfold]
        unfold rest0 at hp
        dsimp only
        xperm_hyp hp)
      h0Framed
  let rest1 : Assertion :=
    (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d4Addr ↦ₘ p0.2) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)
  let h1Framed := cpsTripleWithin_frameR rest1 (by pcFree) h1
  have h1Body :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreFourLimbBodyMid0 addrReg byteReg accReg
          addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start)
        (mstoreFourLimbBodyMid1 addrReg byteReg accReg
          addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        rw [mstoreFourLimbBodyMid0_unfold] at hp
        rw [mstoreOneLimbPre_unfold]
        unfold rest1 p0
        xperm_hyp hp)
      (fun _ hp => by
        rw [mstoreOneLimbPost_unfold] at hp
        rw [mstoreFourLimbBodyMid1_unfold]
        unfold rest1 at hp
        dsimp only
        xperm_hyp hp)
      h1Framed
  let rest2 : Assertion :=
    (d0Addr ↦ₘ d0) ** (d3Addr ↦ₘ p1.2) ** (d4Addr ↦ₘ p0.2) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)
  let h2Framed := cpsTripleWithin_frameR rest2 (by pcFree) h2
  have h2Body :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreFourLimbBodyMid1 addrReg byteReg accReg
          addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start)
        (mstoreFourLimbBodyMid2 addrReg byteReg accReg
          addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        rw [mstoreFourLimbBodyMid1_unfold] at hp
        rw [mstoreOneLimbPre_unfold]
        unfold rest2 p0 p1
        xperm_hyp hp)
      (fun _ hp => by
        rw [mstoreOneLimbPost_unfold] at hp
        rw [mstoreFourLimbBodyMid2_unfold]
        unfold rest2 at hp
        dsimp only
        xperm_hyp hp)
      h2Framed
  let rest3 : Assertion :=
    (d2Addr ↦ₘ p2.2) ** (d3Addr ↦ₘ p1.2) ** (d4Addr ↦ₘ p0.2) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48)
  let h3Framed := cpsTripleWithin_frameR rest3 (by pcFree) h3
  have h3Body :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (mstoreFourLimbBodyMid2 addrReg byteReg accReg
          addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start)
        (mstoreFourLimbBodyPost addrReg byteReg accReg
          addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        rw [mstoreFourLimbBodyMid2_unfold] at hp
        rw [mstoreOneLimbPre_unfold]
        unfold rest3 p0 p1 p2
        xperm_hyp hp)
      (fun _ hp => by
        rw [mstoreOneLimbPost_unfold] at hp
        rw [mstoreFourLimbBodyPost_unfold, mstoreFourLimbStore_unfold]
        unfold rest3 at hp
        dsimp only
        xperm_hyp hp)
      h3Framed
  exact mstore_four_limb_sequence_spec_within addrReg byteReg accReg base
    h0Body h1Body h2Body h3Body

/-- Side conditions for one eight-byte MSTORE limb window. The destination
    byte offsets may cross from `loAddr` into `hiAddr` depending on `start`. -/
def mstoreLimbWindowOk
    (addrPtr loAddr hiAddr : Word) (start : Nat)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) : Prop :=
  alignToDword (addrPtr + signExtend12 off0) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 0 ∧
  isValidByteAccess (addrPtr + signExtend12 off0) = true ∧
  byteOffset (addrPtr + signExtend12 off0) = (start + 0) % 8 ∧
  alignToDword (addrPtr + signExtend12 off1) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 1 ∧
  isValidByteAccess (addrPtr + signExtend12 off1) = true ∧
  byteOffset (addrPtr + signExtend12 off1) = (start + 1) % 8 ∧
  alignToDword (addrPtr + signExtend12 off2) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 2 ∧
  isValidByteAccess (addrPtr + signExtend12 off2) = true ∧
  byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8 ∧
  alignToDword (addrPtr + signExtend12 off3) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 3 ∧
  isValidByteAccess (addrPtr + signExtend12 off3) = true ∧
  byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8 ∧
  alignToDword (addrPtr + signExtend12 off4) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 4 ∧
  isValidByteAccess (addrPtr + signExtend12 off4) = true ∧
  byteOffset (addrPtr + signExtend12 off4) = (start + 4) % 8 ∧
  alignToDword (addrPtr + signExtend12 off5) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 5 ∧
  isValidByteAccess (addrPtr + signExtend12 off5) = true ∧
  byteOffset (addrPtr + signExtend12 off5) = (start + 5) % 8 ∧
  alignToDword (addrPtr + signExtend12 off6) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 6 ∧
  isValidByteAccess (addrPtr + signExtend12 off6) = true ∧
  byteOffset (addrPtr + signExtend12 off6) = (start + 6) % 8 ∧
  alignToDword (addrPtr + signExtend12 off7) =
      MStore.mstoreDwordPairAddr loAddr hiAddr start 7 ∧
  isValidByteAccess (addrPtr + signExtend12 off7) = true ∧
  byteOffset (addrPtr + signExtend12 off7) = (start + 7) % 8

theorem mstore_limb0_four_code_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align0 :
      alignToDword (addrPtr + signExtend12 (24 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 0)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 (24 : BitVec 12)) = true)
    (h_byte0 : byteOffset (addrPtr + signExtend12 (24 : BitVec 12)) = (start + 0) % 8)
    (h_align1 :
      alignToDword (addrPtr + signExtend12 (25 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 1)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 (25 : BitVec 12)) = true)
    (h_byte1 : byteOffset (addrPtr + signExtend12 (25 : BitVec 12)) = (start + 1) % 8)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 (26 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 2)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 (26 : BitVec 12)) = true)
    (h_byte2 : byteOffset (addrPtr + signExtend12 (26 : BitVec 12)) = (start + 2) % 8)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 (27 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 3)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 (27 : BitVec 12)) = true)
    (h_byte3 : byteOffset (addrPtr + signExtend12 (27 : BitVec 12)) = (start + 3) % 8)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 (28 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 4)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 (28 : BitVec 12)) = true)
    (h_byte4 : byteOffset (addrPtr + signExtend12 (28 : BitVec 12)) = (start + 4) % 8)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 (29 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 5)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 (29 : BitVec 12)) = true)
    (h_byte5 : byteOffset (addrPtr + signExtend12 (29 : BitVec 12)) = (start + 5) % 8)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 (30 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 6)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 (30 : BitVec 12)) = true)
    (h_byte6 : byteOffset (addrPtr + signExtend12 (30 : BitVec 12)) = (start + 6) % 8)
    (h_align7 :
      alignToDword (addrPtr + signExtend12 (31 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 7)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 (31 : BitVec 12)) = true)
    (h_byte7 : byteOffset (addrPtr + signExtend12 (31 : BitVec 12)) = (start + 7) % 8) :
    cpsTripleWithin 17 (base + 8) (base + 76)
      (mstoreFourLimbsCode addrReg byteReg accReg base)
      (mstoreOneLimbPre addrReg byteReg accReg
        addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal (32 : BitVec 12))
      (mstoreOneLimbPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp limbVal start (32 : BitVec 12)) := by
  have h := cpsTripleWithin_extend_code
    (hmono := mstoreFourLimbsCode_limb0_sub addrReg byteReg accReg base)
    (h := mstore_one_limb_spec_within
      addrReg byteReg accReg addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal
      start (32 : BitVec 12) (24 : BitVec 12) (25 : BitVec 12) (26 : BitVec 12)
      (27 : BitVec 12) (28 : BitVec 12) (29 : BitVec 12) (30 : BitVec 12)
      (31 : BitVec 12) (base + 8) h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_byte0
      h_align1 h_valid1 h_byte1 h_align2 h_valid2 h_byte2 h_align3 h_valid3 h_byte3
      h_align4 h_valid4 h_byte4 h_align5 h_valid5 h_byte5 h_align6 h_valid6 h_byte6
      h_align7 h_valid7 h_byte7)
  rw [show (base + 8 : Word) + 68 = base + 76 from by bv_addr] at h
  exact h

theorem mstore_limb1_four_code_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align0 :
      alignToDword (addrPtr + signExtend12 (16 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 0)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 (16 : BitVec 12)) = true)
    (h_byte0 : byteOffset (addrPtr + signExtend12 (16 : BitVec 12)) = (start + 0) % 8)
    (h_align1 :
      alignToDword (addrPtr + signExtend12 (17 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 1)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 (17 : BitVec 12)) = true)
    (h_byte1 : byteOffset (addrPtr + signExtend12 (17 : BitVec 12)) = (start + 1) % 8)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 (18 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 2)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 (18 : BitVec 12)) = true)
    (h_byte2 : byteOffset (addrPtr + signExtend12 (18 : BitVec 12)) = (start + 2) % 8)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 (19 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 3)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 (19 : BitVec 12)) = true)
    (h_byte3 : byteOffset (addrPtr + signExtend12 (19 : BitVec 12)) = (start + 3) % 8)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 (20 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 4)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 (20 : BitVec 12)) = true)
    (h_byte4 : byteOffset (addrPtr + signExtend12 (20 : BitVec 12)) = (start + 4) % 8)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 (21 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 5)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 (21 : BitVec 12)) = true)
    (h_byte5 : byteOffset (addrPtr + signExtend12 (21 : BitVec 12)) = (start + 5) % 8)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 (22 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 6)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 (22 : BitVec 12)) = true)
    (h_byte6 : byteOffset (addrPtr + signExtend12 (22 : BitVec 12)) = (start + 6) % 8)
    (h_align7 :
      alignToDword (addrPtr + signExtend12 (23 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 7)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 (23 : BitVec 12)) = true)
    (h_byte7 : byteOffset (addrPtr + signExtend12 (23 : BitVec 12)) = (start + 7) % 8) :
    cpsTripleWithin 17 (base + 76) (base + 144)
      (mstoreFourLimbsCode addrReg byteReg accReg base)
      (mstoreOneLimbPre addrReg byteReg accReg
        addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal (40 : BitVec 12))
      (mstoreOneLimbPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp limbVal start (40 : BitVec 12)) := by
  have h := cpsTripleWithin_extend_code
    (hmono := mstoreFourLimbsCode_limb1_sub addrReg byteReg accReg base)
    (h := mstore_one_limb_spec_within
      addrReg byteReg accReg addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal
      start (40 : BitVec 12) (16 : BitVec 12) (17 : BitVec 12) (18 : BitVec 12)
      (19 : BitVec 12) (20 : BitVec 12) (21 : BitVec 12) (22 : BitVec 12)
      (23 : BitVec 12) (base + 76) h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_byte0
      h_align1 h_valid1 h_byte1 h_align2 h_valid2 h_byte2 h_align3 h_valid3 h_byte3
      h_align4 h_valid4 h_byte4 h_align5 h_valid5 h_byte5 h_align6 h_valid6 h_byte6
      h_align7 h_valid7 h_byte7)
  rw [show (base + 76 : Word) + 68 = base + 144 from by bv_addr] at h
  exact h

theorem mstore_limb2_four_code_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align0 :
      alignToDword (addrPtr + signExtend12 (8 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 0)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 (8 : BitVec 12)) = true)
    (h_byte0 : byteOffset (addrPtr + signExtend12 (8 : BitVec 12)) = (start + 0) % 8)
    (h_align1 :
      alignToDword (addrPtr + signExtend12 (9 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 1)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 (9 : BitVec 12)) = true)
    (h_byte1 : byteOffset (addrPtr + signExtend12 (9 : BitVec 12)) = (start + 1) % 8)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 (10 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 2)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 (10 : BitVec 12)) = true)
    (h_byte2 : byteOffset (addrPtr + signExtend12 (10 : BitVec 12)) = (start + 2) % 8)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 (11 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 3)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 (11 : BitVec 12)) = true)
    (h_byte3 : byteOffset (addrPtr + signExtend12 (11 : BitVec 12)) = (start + 3) % 8)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 (12 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 4)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 (12 : BitVec 12)) = true)
    (h_byte4 : byteOffset (addrPtr + signExtend12 (12 : BitVec 12)) = (start + 4) % 8)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 (13 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 5)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 (13 : BitVec 12)) = true)
    (h_byte5 : byteOffset (addrPtr + signExtend12 (13 : BitVec 12)) = (start + 5) % 8)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 (14 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 6)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 (14 : BitVec 12)) = true)
    (h_byte6 : byteOffset (addrPtr + signExtend12 (14 : BitVec 12)) = (start + 6) % 8)
    (h_align7 :
      alignToDword (addrPtr + signExtend12 (15 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 7)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 (15 : BitVec 12)) = true)
    (h_byte7 : byteOffset (addrPtr + signExtend12 (15 : BitVec 12)) = (start + 7) % 8) :
    cpsTripleWithin 17 (base + 144) (base + 212)
      (mstoreFourLimbsCode addrReg byteReg accReg base)
      (mstoreOneLimbPre addrReg byteReg accReg
        addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal (48 : BitVec 12))
      (mstoreOneLimbPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp limbVal start (48 : BitVec 12)) := by
  have h := cpsTripleWithin_extend_code
    (hmono := mstoreFourLimbsCode_limb2_sub addrReg byteReg accReg base)
    (h := mstore_one_limb_spec_within
      addrReg byteReg accReg addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal
      start (48 : BitVec 12) (8 : BitVec 12) (9 : BitVec 12) (10 : BitVec 12)
      (11 : BitVec 12) (12 : BitVec 12) (13 : BitVec 12) (14 : BitVec 12)
      (15 : BitVec 12) (base + 144) h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_byte0
      h_align1 h_valid1 h_byte1 h_align2 h_valid2 h_byte2 h_align3 h_valid3 h_byte3
      h_align4 h_valid4 h_byte4 h_align5 h_valid5 h_byte5 h_align6 h_valid6 h_byte6
      h_align7 h_valid7 h_byte7)
  rw [show (base + 144 : Word) + 68 = base + 212 from by bv_addr] at h
  exact h

theorem mstore_limb3_four_code_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align0 :
      alignToDword (addrPtr + signExtend12 (0 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 0)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 (0 : BitVec 12)) = true)
    (h_byte0 : byteOffset (addrPtr + signExtend12 (0 : BitVec 12)) = (start + 0) % 8)
    (h_align1 :
      alignToDword (addrPtr + signExtend12 (1 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 1)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 (1 : BitVec 12)) = true)
    (h_byte1 : byteOffset (addrPtr + signExtend12 (1 : BitVec 12)) = (start + 1) % 8)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 (2 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 2)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 (2 : BitVec 12)) = true)
    (h_byte2 : byteOffset (addrPtr + signExtend12 (2 : BitVec 12)) = (start + 2) % 8)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 (3 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 3)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 (3 : BitVec 12)) = true)
    (h_byte3 : byteOffset (addrPtr + signExtend12 (3 : BitVec 12)) = (start + 3) % 8)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 (4 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 4)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 (4 : BitVec 12)) = true)
    (h_byte4 : byteOffset (addrPtr + signExtend12 (4 : BitVec 12)) = (start + 4) % 8)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 (5 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 5)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 (5 : BitVec 12)) = true)
    (h_byte5 : byteOffset (addrPtr + signExtend12 (5 : BitVec 12)) = (start + 5) % 8)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 (6 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 6)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 (6 : BitVec 12)) = true)
    (h_byte6 : byteOffset (addrPtr + signExtend12 (6 : BitVec 12)) = (start + 6) % 8)
    (h_align7 :
      alignToDword (addrPtr + signExtend12 (7 : BitVec 12)) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 7)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 (7 : BitVec 12)) = true)
    (h_byte7 : byteOffset (addrPtr + signExtend12 (7 : BitVec 12)) = (start + 7) % 8) :
    cpsTripleWithin 17 (base + 212) (base + 280)
      (mstoreFourLimbsCode addrReg byteReg accReg base)
      (mstoreOneLimbPre addrReg byteReg accReg
        addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal (56 : BitVec 12))
      (mstoreOneLimbPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp limbVal start (56 : BitVec 12)) := by
  have h := cpsTripleWithin_extend_code
    (hmono := mstoreFourLimbsCode_limb3_sub addrReg byteReg accReg base)
    (h := mstore_one_limb_spec_within
      addrReg byteReg accReg addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal
      start (56 : BitVec 12) (0 : BitVec 12) (1 : BitVec 12) (2 : BitVec 12)
      (3 : BitVec 12) (4 : BitVec 12) (5 : BitVec 12) (6 : BitVec 12)
      (7 : BitVec 12) (base + 212) h_byte_ne_x0 h_acc_ne_x0 h_align0 h_valid0 h_byte0
      h_align1 h_valid1 h_byte1 h_align2 h_valid2 h_byte2 h_align3 h_valid3 h_byte3
      h_align4 h_valid4 h_byte4 h_align5 h_valid5 h_byte5 h_align6 h_valid6 h_byte6
      h_align7 h_valid7 h_byte7)
  rw [show (base + 212 : Word) + 68 = base + 280 from by bv_addr] at h
  exact h

theorem mstore_four_limb_body_concrete_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word)
    (start : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h32 : mstoreLimbWindowOk addrPtr d3Addr d4Addr start
      24 25 26 27 28 29 30 31)
    (h40 : mstoreLimbWindowOk addrPtr d2Addr d3Addr start
      16 17 18 19 20 21 22 23)
    (h48 : mstoreLimbWindowOk addrPtr d1Addr d2Addr start
      8 9 10 11 12 13 14 15)
    (h56 : mstoreLimbWindowOk addrPtr d0Addr d1Addr start
      0 1 2 3 4 5 6 7) :
    cpsTripleWithin 68 (base + 8) (base + 280)
      (mstoreFourLimbsCode addrReg byteReg accReg base)
      (mstoreFourLimbBodyPre addrReg byteReg accReg
        addrPtr byteOld accOld d0 d1 d2 d3 d4
        d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56)
      (mstoreFourLimbBodyPost addrReg byteReg accReg
        addrPtr d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
        limb32 limb40 limb48 limb56 start) := by
  obtain ⟨h32a0, h32v0, h32b0, h32a1, h32v1, h32b1, h32a2, h32v2, h32b2,
    h32a3, h32v3, h32b3, h32a4, h32v4, h32b4, h32a5, h32v5, h32b5,
    h32a6, h32v6, h32b6, h32a7, h32v7, h32b7⟩ := h32
  obtain ⟨h40a0, h40v0, h40b0, h40a1, h40v1, h40b1, h40a2, h40v2, h40b2,
    h40a3, h40v3, h40b3, h40a4, h40v4, h40b4, h40a5, h40v5, h40b5,
    h40a6, h40v6, h40b6, h40a7, h40v7, h40b7⟩ := h40
  obtain ⟨h48a0, h48v0, h48b0, h48a1, h48v1, h48b1, h48a2, h48v2, h48b2,
    h48a3, h48v3, h48b3, h48a4, h48v4, h48b4, h48a5, h48v5, h48b5,
    h48a6, h48v6, h48b6, h48a7, h48v7, h48b7⟩ := h48
  obtain ⟨h56a0, h56v0, h56b0, h56a1, h56v1, h56b1, h56a2, h56v2, h56b2,
    h56a3, h56v3, h56b3, h56a4, h56v4, h56b4, h56a5, h56v5, h56b5,
    h56a6, h56v6, h56b6, h56a7, h56v7, h56b7⟩ := h56
  have h := mstore_four_limb_body_sequence_spec_within
    addrReg byteReg accReg addrPtr byteOld accOld d0 d1 d2 d3 d4
    d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56
    start base
    (mstore_limb0_four_code_spec_within
      addrReg byteReg accReg addrPtr byteOld accOld d3 d4 d3Addr d4Addr sp limb32
      start base h_byte_ne_x0 h_acc_ne_x0 h32a0 h32v0 h32b0 h32a1 h32v1 h32b1
      h32a2 h32v2 h32b2 h32a3 h32v3 h32b3 h32a4 h32v4 h32b4 h32a5 h32v5
      h32b5 h32a6 h32v6 h32b6 h32a7 h32v7 h32b7)
    (mstore_limb1_four_code_spec_within
      addrReg byteReg accReg addrPtr limb32 limb32 d2
      (MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start).1
      d2Addr d3Addr sp limb40 start base h_byte_ne_x0 h_acc_ne_x0
      h40a0 h40v0 h40b0 h40a1 h40v1 h40b1 h40a2 h40v2 h40b2
      h40a3 h40v3 h40b3 h40a4 h40v4 h40b4 h40a5 h40v5 h40b5
      h40a6 h40v6 h40b6 h40a7 h40v7 h40b7)
    (mstore_limb2_four_code_spec_within
      addrReg byteReg accReg addrPtr limb40 limb40 d1
      (MStore.mstoreDwordPairStoreLimb d2
        (MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start).1 limb40 start).1
      d1Addr d2Addr sp limb48 start base h_byte_ne_x0 h_acc_ne_x0
      h48a0 h48v0 h48b0 h48a1 h48v1 h48b1 h48a2 h48v2 h48b2
      h48a3 h48v3 h48b3 h48a4 h48v4 h48b4 h48a5 h48v5 h48b5
      h48a6 h48v6 h48b6 h48a7 h48v7 h48b7)
    (mstore_limb3_four_code_spec_within
      addrReg byteReg accReg addrPtr limb48 limb48 d0
      (MStore.mstoreDwordPairStoreLimb d1
        (MStore.mstoreDwordPairStoreLimb d2
          (MStore.mstoreDwordPairStoreLimb d3 d4 limb32 start).1 limb40 start).1
        limb48 start).1
      d0Addr d1Addr sp limb56 start base h_byte_ne_x0 h_acc_ne_x0
      h56a0 h56v0 h56b0 h56a1 h56v1 h56b1 h56a2 h56v2 h56b2
      h56a3 h56v3 h56b3 h56a4 h56v4 h56b4 h56a5 h56v5 h56b5
      h56a6 h56v6 h56b6 h56a7 h56v7 h56b7)
  simpa using h

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

theorem mstore_prologue_body_evm_mstore_spec_within
    {nBody : Nat} {R : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (hBody :
      cpsTripleWithin nBody (base + 8) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        R) :
    cpsTripleWithin (2 + nBody) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      R := by
  exact cpsTripleWithin_seq_same_cr
    (mstore_prologue_evm_mstore_frame_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF h_off_ne_x0 h_addr_ne_x0)
    hBody

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

theorem mstore_full_evm_mstore_spec_within
    {nBody : Nat} {FPre FPost : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (hFPre : FPre.pcFree) (hFPost : FPost.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (hBody :
      cpsTripleWithin nBody (base + 8) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** FPre)
        (((.x12 : Reg) ↦ᵣ sp) ** FPost)) :
    cpsTripleWithin (2 + nBody + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** FPre)
      (((.x12 : Reg) ↦ᵣ (sp + 64)) ** FPost) := by
  exact cpsTripleWithin_seq_same_cr
    (mstore_prologue_body_evm_mstore_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base FPre hFPre
      h_off_ne_x0 h_addr_ne_x0 hBody)
    (mstore_epilogue_evm_mstore_frame_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg sp base FPost hFPost)

end EvmAsm.Evm64
