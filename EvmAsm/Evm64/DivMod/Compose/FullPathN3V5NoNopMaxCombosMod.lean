/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopMaxCombosMod  (MOD mirror of FullPathN3V5NoNopMaxCombos)

  v5/no-NOP n=3 two-iteration loop combos whose FIRST iteration is a max:
  `divK_loop_n3_max_{max,call}_from_source_exact_loopIterScratch_v5_noNop_modCode`.
  Mirror of the v4 analogs (`FullPathN3V4NoNopMaxCall` :131/:211) over
  `modCode_noNop_v5`, composing the v5 max/call exact-jN dispatch bodies (#7512
  max, #7516 call) through the SHARED version-agnostic source-pre / j1→j0 post
  bridges reused from the v4 files (`loopN3PreWithScratchV4NoX1_to_max_j1_pre`,
  `loopIterPostN3MaxScratchX1_j1_to_{max,call}_j0_pre`).  `max_max` is fully
  version-agnostic (pure `iterN3Max`, shared `isAddbackCarry2NzN3Max`); `max_call`
  feeds the v5 call-j0 dispatch its inline carry hypothesis.  Completes the 4
  n=3 v5 loop combos (call_call/call_max in #7517 + max_max/max_call here).
  Bead `evm-asm-wbc4i.9.3.3.2.3`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopMaxExactX1Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallExactX1Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopMaxCall

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=3 max×max path from the callable-ready v5 loop source, preserving
    concrete `x1`, scratch, and the j=1 stored u4/q atoms. -/
theorem divK_loop_n3_max_max_from_source_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hcarry2_nz_1 : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_nz_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      isAddbackCarry2NzN3Max v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 152) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_body_n3_max_j1_exact_loopIterScratch_v5_noNop_modCode sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_1 hcarry2_nz_1
  subst r1
  subst uBase1
  subst qAddr1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_max_j0_exact_loopIterScratch_v5_noNop_modCode sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal retMem dMem dloMem scratchUn0 scratchMem hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3MaxScratchX1_j1_to_max_j0_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    (cpsTripleWithin_weaken
      (loopN3PreWithScratchV4NoX1_to_max_j1_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem)
      (fun h hp => hp)
      J1f)
    J0f

/-- Full n=3 max×call path from the callable-ready v5 loop source, preserving
    concrete `x1`, scratch, and the j=1 stored u4/q atoms. -/
theorem divK_loop_n3_max_call_from_source_exact_loopIterScratch_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hcarry2_nz_1 : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_nz_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      let qHat := divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (r1.2.2.2.2.1 - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 234) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
        (divKTrialCallV5DLo v2)
        (divKTrialCallV5Un0 r1.2.2.1)
        (divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 v2 scratchMem)
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_body_n3_max_j1_exact_loopIterScratch_v5_noNop_modCode sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_1 hcarry2_nz_1
  subst r1
  subst uBase1
  subst qAddr1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_call_j0_exact_loopIterScratch_v5_noNop_modCode sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3MaxScratchX1_j1_to_call_j0_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    (cpsTripleWithin_weaken
      (loopN3PreWithScratchV4NoX1_to_max_j1_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem)
      (fun h hp => hp)
      J1f)
    J0f

end EvmAsm.Evm64
