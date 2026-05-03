/-
  EvmAsm.Evm64.MStore.FullSpec

  Concrete full-program MSTORE stack specification.
-/

import EvmAsm.Evm64.MStore.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def mstoreFullValueFrame
    (byteReg accReg : Reg)
    (byteOld accOld d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) : Assertion :=
  (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ d2) **
  (d3Addr ↦ₘ d3) ** (d4Addr ↦ₘ d4) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)

theorem mstoreFullValueFrame_unfold
    (byteReg accReg : Reg)
    (byteOld accOld d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) :
    mstoreFullValueFrame byteReg accReg byteOld accOld d0 d1 d2 d3 d4
        d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56 =
      ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (d0Addr ↦ₘ d0) ** (d1Addr ↦ₘ d1) ** (d2Addr ↦ₘ d2) **
       (d3Addr ↦ₘ d3) ** (d4Addr ↦ₘ d4) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56)) := by
  delta mstoreFullValueFrame
  rfl

@[irreducible]
def mstoreFullPostFrame
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (offset memBase d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) : Assertion :=
  let stored := mstoreFourLimbStore d0 d1 d2 d3 d4 limb32 limb40 limb48 limb56 start
  (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
  (addrReg ↦ᵣ (memBase + offset)) **
  (byteReg ↦ᵣ limb56) ** (accReg ↦ᵣ limb56) **
  (d0Addr ↦ₘ stored.1) ** (d1Addr ↦ₘ stored.2.1) **
  (d2Addr ↦ₘ stored.2.2.1) ** (d3Addr ↦ₘ stored.2.2.2.1) **
  (d4Addr ↦ₘ stored.2.2.2.2) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56) **
  (sp ↦ₘ offset)

theorem mstoreFullPostFrame_unfold
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (offset memBase d0 d1 d2 d3 d4 : Word)
    (d0Addr d1Addr d2Addr d3Addr d4Addr sp : Word)
    (limb32 limb40 limb48 limb56 : Word) (start : Nat) :
    mstoreFullPostFrame offReg byteReg accReg addrReg memBaseReg
        offset memBase d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr sp
        limb32 limb40 limb48 limb56 start =
      (let stored := mstoreFourLimbStore d0 d1 d2 d3 d4 limb32 limb40 limb48 limb56 start
       (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
       (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ limb56) ** (accReg ↦ᵣ limb56) **
       (d0Addr ↦ₘ stored.1) ** (d1Addr ↦ₘ stored.2.1) **
       (d2Addr ↦ₘ stored.2.2.1) ** (d3Addr ↦ₘ stored.2.2.2.1) **
       (d4Addr ↦ₘ stored.2.2.2.2) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb32) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb40) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb48) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb56) **
       (sp ↦ₘ offset)) := by
  delta mstoreFullPostFrame
  rfl

theorem mstore_full_body_evm_mstore_spec_within
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (d0 d1 d2 d3 d4 d0Addr d1Addr d2Addr d3Addr d4Addr : Word)
    (limb32 limb40 limb48 limb56 : Word)
    (start : Nat) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h32 : mstoreLimbWindowOk (memBase + offset) d3Addr d4Addr start
      24 25 26 27 28 29 30 31)
    (h40 : mstoreLimbWindowOk (memBase + offset) d2Addr d3Addr start
      16 17 18 19 20 21 22 23)
    (h48 : mstoreLimbWindowOk (memBase + offset) d1Addr d2Addr start
      8 9 10 11 12 13 14 15)
    (h56 : mstoreLimbWindowOk (memBase + offset) d0Addr d1Addr start
      0 1 2 3 4 5 6 7) :
    cpsTripleWithin (2 + 68 + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) **
        mstoreFullValueFrame byteReg accReg byteOld accOld d0 d1 d2 d3 d4
          d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56)
      (((.x12 : Reg) ↦ᵣ (sp + 64)) **
        mstoreFullPostFrame offReg byteReg accReg addrReg memBaseReg
          offset memBase d0 d1 d2 d3 d4
          d0Addr d1Addr d2Addr d3Addr d4Addr sp
          limb32 limb40 limb48 limb56 start) := by
  let FBook : Assertion :=
    (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) ** (sp ↦ₘ offset)
  have hBody :
      cpsTripleWithin 68 (base + 8) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) **
          mstoreFullValueFrame byteReg accReg byteOld accOld d0 d1 d2 d3 d4
            d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56)
        (((.x12 : Reg) ↦ᵣ sp) **
          mstoreFullPostFrame offReg byteReg accReg addrReg memBaseReg
            offset memBase d0 d1 d2 d3 d4
            d0Addr d1Addr d2Addr d3Addr d4Addr sp
            limb32 limb40 limb48 limb56 start) := by
    exact cpsTripleWithin_weaken
      (fun h hp => by
        rw [mstoreFullValueFrame_unfold] at hp
        rw [mstoreFourLimbBodyPre_unfold]
        dsimp [FBook] at hp ⊢
        xperm_hyp hp)
      (fun h hq => by
        rw [mstoreFourLimbBodyPost_unfold] at hq
        rw [mstoreFullPostFrame_unfold]
        dsimp [FBook] at hq ⊢
        xperm_hyp hq)
      (mstore_four_limb_body_evm_mstore_frame_spec_within
        offReg valReg byteReg accReg addrReg memBaseReg
        (memBase + offset) byteOld accOld d0 d1 d2 d3 d4
        d0Addr d1Addr d2Addr d3Addr d4Addr sp limb32 limb40 limb48 limb56
        start base FBook (by
          dsimp [FBook]
          pcFree)
        h_byte_ne_x0 h_acc_ne_x0 h32 h40 h48 h56)
  exact mstore_full_evm_mstore_spec_within
    offReg valReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base
    (by
      delta mstoreFullValueFrame
      pcFree)
    (by
      delta mstoreFullPostFrame
      pcFree)
    h_off_ne_x0 h_addr_ne_x0 hBody

end EvmAsm.Evm64
