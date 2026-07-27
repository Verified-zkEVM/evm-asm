/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMMBorrowCarryMod

  MOD mirror of `FullPathN2V5NoNopComboMMMBorrowCarry`: the n=2 max×max×max source
  path over `modCode_noNop_v5`.  Byte-for-byte the DIV proof (file-copied; only the
  code surface + the two composed-theorem names swapped to `_modCode`) — composes
  the MOD max×max 2-combo (#7697) with the MOD j=0 max exit iter borrowCarry
  (#7702); the final-post def + `r{2,1}MMTN2V5_eq` simp lemmas are code-agnostic
  (reused from the DIV `FullPathN2V5NoNopComboMMM`).  Brick 17 of the n=2 MOD loop
  body (first 3-combo).  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMBorrowCarryMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxJ0BorrowCarryMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboChainB

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The n=2 v5/no-NOP max×max×max source path, carry required only on each
    digit's runtime-borrow branch. -/
theorem divK_loop_n2_max_max_max_from_source_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hcarry2_borrow_2 :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r2.2.2.1 v1)
    (hcarry2_borrow_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r2.2.2.2.2.1
        (mulsubN4_c3 (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1)
    (hbltu_0 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      let r1 := iterN2Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
      ¬BitVec.ult r1.2.2.1 v1)
    (hcarry2_borrow_0 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      let r1 := iterN2Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin (152 + 152 + 152) (base + loopBodyOff) (base + denormOff)
      (modCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2MaxMaxMaxSourceFinalPostNoX1V5 sp
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal
        retMem dMem dloMem scratchUn0 scratchMem) := by
  have JMM := divK_loop_n2_max_max_from_source_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    hbltu_2 hcarry2_borrow_2 hbltu_1 hcarry2_borrow_1
  have J0 := divK_loop_body_n2_max_j0_exact_loopIterScratch_v5_noNop_borrowCarry_modCode sp base
    (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1)
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    v0 v1 v2 v3 u0Orig0
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    hbltu_0 hcarry2_borrow_0
  have J0f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1)) **
     (((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
       (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)))
    (by pcFree) J0
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2MaxScratchX1_j1_to_max_j0_pre_with_j2_frame
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      u0Orig0 q0Old raVal
      (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    JMM J0f
  have hsteps : (152 + 152) + 152 = 152 + 152 + 152 := by decide
  rw [hsteps] at hcomp
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hcomp
  intro h hp
  rw [loopN2MaxMaxMaxSourceFinalPostNoX1V5_unfold]
  simp only [r2MMTN2V5_eq, r1MMTN2V5_eq] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
