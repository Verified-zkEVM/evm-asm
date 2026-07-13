/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMCBorrowCarryMod

  MOD mirror of `FullPathN2V5NoNopComboMCBorrowCarry`: the borrow-dispatched n=2
  max×call two-digit prefix over `modCode_noNop_v5`.  Byte-for-byte the DIV proof
  — chain the MOD j=2 max source borrowCarry (#7692) with the MOD j=1 call iter
  borrowCarry body (#7695) via the code-agnostic max→call source-pre bridge
  `loopIterPostN2MaxScratchX1_j2_to_call_j1_pre`.  Brick 12 of the n=2 MOD loop
  body (combo layer — max×call 2-combo; uses both chains).
  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxSourceBorrowCarryMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5CallIterShared

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=2 max×call prefix over `modCode_noNop_v5`, carry required only on each
    digit's runtime-borrow branch. -/
theorem divK_loop_n2_max_call_from_source_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hcarry2_borrow_2 :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2_borrow_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r2.2.2.2.2.1
        (mulsubN4_c3 (divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1)
          v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let qHat1 := divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1
    let dLo1 := divKTrialCallV5DLo v1
    let divUn01 := divKTrialCallV5Un0 r2.2.1
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 234) (base + loopBodyOff) (base + loopBodyOff)
      (modCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat1 dLo1 divUn01 scratch1
        v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
          (qAddr2 ↦ₘ r2.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) := by
  intro r2 qHat1 dLo1 divUn01 scratch1 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_max_j2_from_source_exact_loopIterScratch_v5_noNop_borrowCarry_modCode
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_2 hcarry2_borrow_2
  subst r2
  subst qHat1
  subst dLo1
  subst divUn01
  subst scratch1
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_call_j1_exact_loopIterScratch_v5_noNop_borrowCarry_modCode sp base
    (2 : Word)
    ((2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_1 hcarry2_borrow_1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2MaxScratchX1_j2_to_call_j1_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

end EvmAsm.Evm64
