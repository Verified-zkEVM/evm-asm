/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopSource

  Source-level v4/no-NOP wrappers for the n=2 DIV loop.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- First n=2 call iteration from the callable-ready v4 loop source, preserving
    concrete `x1` and carrying the j=1/j=0 source atoms as a frame. -/
theorem divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) := by
  have J2 := divK_loop_body_n2_call_j2_exact_loopIterScratch_v4_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz
  have J2f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig1) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := loopN2PreWithScratchV4NoX1_to_call_j2_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem h hp
      xperm_hyp hp')
    (fun h hp => hp)
    J2f

/-- First n=2 max iteration from the callable-ready v4 loop source, preserving
    concrete `x1`, scratch, and the j=1/j=0 source atoms as a frame. -/
theorem divK_loop_n2_max_j2_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) := by
  have J2 := divK_loop_body_n2_max_j2_exact_loopIterScratch_v4_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu hcarry2_nz
  have J2f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig1) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := loopN2PreWithScratchV4NoX1_to_max_j2_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem h hp
      xperm_hyp hp')
    (fun h hp => hp)
    J2f

/-- Full n=2 call×call prefix from the callable-ready v4 loop source,
    preserving concrete `x1` and carrying the j=2 stored u4/q atoms plus the
    j=0 source atoms. -/
theorem divK_loop_n2_call_call_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u2 v1)
    (hcarry2_nz_2 : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      BitVec.ult
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2_nz_1 :
      let r2 := iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let qHat1 := divKTrialCallV4QHat r2.2.2.1 r2.2.1 v1
    let dLo1 := divKTrialCallV4DLo v1
    let divUn01 := divKTrialCallV4Un0 r2.2.1
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (224 + 224) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v4 base)
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
  intro r2 qHat1 dLo1 divUn01 scratch2 scratch1 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_2 hcarry2_nz_2
  subst r2
  subst qHat1
  subst dLo1
  subst divUn01
  subst scratch2
  subst scratch1
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_call_j1_exact_loopIterScratch_v4_noNop sp base
    (2 : Word)
    ((2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q1Old raVal
    (base + div128CallRetOff) v1 (divKTrialCallV4DLo v1)
    (divKTrialCallV4Un0 u1) (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
    halign hbltu_1 hcarry2_nz_1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2CallScratchNoX1_j2_to_call_j1_pre
      sp base (divKTrialCallV4QHat u2 u1 v1) (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 u1) (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

/-- Full n=2 call×max prefix from the callable-ready v4 loop source,
    preserving concrete `x1`, scratch, j=2 stored u4/q atoms, and the j=0
    source atoms. -/
theorem divK_loop_n2_call_max_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u2 v1)
    (hcarry2_nz_2 : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      let r2 := iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r2.2.2.1 v1)
    (hcarry2_nz_1 :
      let r2 := iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      isAddbackCarry2NzN2Max v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (224 + 152) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v1) **
        (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v1)) **
        (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 u1)) **
        (sp + signExtend12 3936 ↦ₘ scratch2) **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
          (qAddr2 ↦ₘ r2.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) := by
  intro r2 scratch2 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_2 hcarry2_nz_2
  subst r2
  subst scratch2
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_max_j1_exact_loopIterScratch_v4_noNop sp base
    (2 : Word)
    ((2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q1Old raVal
    (base + div128CallRetOff) v1 (divKTrialCallV4DLo v1)
    (divKTrialCallV4Un0 u1) (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
    hbltu_1 hcarry2_nz_1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2CallScratchNoX1_j2_to_max_j1_pre
      sp base (divKTrialCallV4QHat u2 u1 v1) (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 u1) (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

/-- Full n=2 max×call prefix from the callable-ready v4 loop source,
    preserving concrete `x1`, scratch, j=2 stored u4/q atoms, and the j=0
    source atoms. -/
theorem divK_loop_n2_max_call_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hcarry2_nz_2 : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2_nz_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let qHat1 := divKTrialCallV4QHat r2.2.2.1 r2.2.1 v1
    let dLo1 := divKTrialCallV4DLo v1
    let divUn01 := divKTrialCallV4Un0 r2.2.1
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 224) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v4 base)
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
  have J2 := divK_loop_n2_max_j2_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_2 hcarry2_nz_2
  subst r2
  subst qHat1
  subst dLo1
  subst divUn01
  subst scratch1
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_call_j1_exact_loopIterScratch_v4_noNop sp base
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
    halign hbltu_1 hcarry2_nz_1
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

/-- Full n=2 max×max prefix from the callable-ready v4 loop source,
    preserving concrete `x1`, scratch, j=2 stored u4/q atoms, and the j=0
    source atoms. -/
theorem divK_loop_n2_max_max_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hcarry2_nz_2 : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r2.2.2.1 v1)
    (hcarry2_nz_1 :
      let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      isAddbackCarry2NzN2Max v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 152) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
          (qAddr2 ↦ₘ r2.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) := by
  intro r2 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_max_j2_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_2 hcarry2_nz_2
  subst r2
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_max_j1_exact_loopIterScratch_v4_noNop sp base
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
    hbltu_1 hcarry2_nz_1
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
    (loopIterPostN2MaxScratchX1_j2_to_max_j1_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

/-- A j=1 call iteration postcondition with v4 scratch cells specializes to the
    j=0 call-body precondition, retaining exact `x1` and j=1 carried u4/q
    atoms as frame. -/
theorem loopIterPostN2CallScratchNoX1_j1_to_call_j0_pre
    (sp base qHat dLo divUn0 scratchOut : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word) :
    let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat dLo divUn0 scratchOut v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) h) →
      (((loopBodyN2CallSkipJ0NormPreV4NoX1 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old
          (base + div128CallRetOff) v1 dLo divUn0 scratchOut **
          (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
         (qAddr1 ↦ₘ r.1))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2CallScratchNoX1 loopExitPostN2 loopExitPost at hp
  delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=1 call iteration postcondition with v4 scratch cells specializes to the
    j=0 call-body precondition while retaining both the j=1 and j=2 carried
    u4/q atoms as frame. -/
theorem loopIterPostN2CallScratchNoX1_j1_to_call_j0_pre_with_j2_frame
    (sp base qHat dLo divUn0 scratchOut : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word)
    (uBase2 qAddr2 u4J2 q2 : Word) :
    let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat dLo divUn0 scratchOut v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) h) →
      (((loopBodyN2CallSkipJ0NormPreV4NoX1 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old
          (base + div128CallRetOff) v1 dLo divUn0 scratchOut **
          (.x1 ↦ᵣ raVal)) **
        (((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr1 ↦ₘ r.1)) **
         ((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2CallScratchNoX1 loopExitPostN2 loopExitPost at hp
  delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=1 call iteration postcondition with v4 scratch cells specializes to the
    j=0 max-body precondition, retaining scratch, exact `x1`, and j=1 carried
    u4/q atoms as frame. -/
theorem loopIterPostN2CallScratchNoX1_j1_to_max_j0_pre
    (sp base qHat dLo divUn0 scratchOut : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word) :
    let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat dLo divUn0 scratchOut v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) h) →
      (((loopBodyN2MaxSkipJ0NormPreV4 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old **
          (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
          (sp + signExtend12 3960 ↦ₘ v1) **
          (sp + signExtend12 3952 ↦ₘ dLo) **
          (sp + signExtend12 3944 ↦ₘ divUn0) **
          (sp + signExtend12 3936 ↦ₘ scratchOut) **
          (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
         (qAddr1 ↦ₘ r.1))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2CallScratchNoX1 loopExitPostN2 loopExitPost at hp
  delta loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=1 call iteration postcondition with v4 scratch cells specializes to the
    j=0 max-body precondition while retaining both the j=1 and j=2 carried
    u4/q atoms as frame. -/
theorem loopIterPostN2CallScratchNoX1_j1_to_max_j0_pre_with_j2_frame
    (sp base qHat dLo divUn0 scratchOut : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word)
    (uBase2 qAddr2 u4J2 q2 : Word) :
    let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat dLo divUn0 scratchOut v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) h) →
      (((loopBodyN2MaxSkipJ0NormPreV4 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old **
          (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
          (sp + signExtend12 3960 ↦ₘ v1) **
          (sp + signExtend12 3952 ↦ₘ dLo) **
          (sp + signExtend12 3944 ↦ₘ divUn0) **
          (sp + signExtend12 3936 ↦ₘ scratchOut) **
          (.x1 ↦ᵣ raVal)) **
        (((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr1 ↦ₘ r.1)) **
         ((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2CallScratchNoX1 loopExitPostN2 loopExitPost at hp
  delta loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=1 max iteration postcondition with v4 scratch cells specializes to the
    j=0 call-body precondition, retaining exact `x1` and j=1 carried u4/q
    atoms as frame. -/
theorem loopIterPostN2MaxScratchX1_j1_to_call_j0_pre
    (sp retMem dMem dloMem scratchUn0 scratchMem : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word) :
    let r := iterN2Max v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) h) →
      (((loopBodyN2CallSkipJ0NormPreV4NoX1 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
         (qAddr1 ↦ₘ r.1))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
  delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=1 max iteration postcondition with v4 scratch cells specializes to the
    j=0 call-body precondition while retaining both the j=1 and j=2 carried
    u4/q atoms as frame. -/
theorem loopIterPostN2MaxScratchX1_j1_to_call_j0_pre_with_j2_frame
    (sp retMem dMem dloMem scratchUn0 scratchMem : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word)
    (uBase2 qAddr2 u4J2 q2 : Word) :
    let r := iterN2Max v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) h) →
      (((loopBodyN2CallSkipJ0NormPreV4NoX1 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal)) **
        (((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr1 ↦ₘ r.1)) **
         ((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
  delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=1 max iteration postcondition with v4 scratch cells specializes to the
    j=0 max-body precondition, retaining exact `x1` and j=1 carried u4/q
    atoms as frame. -/
theorem loopIterPostN2MaxScratchX1_j1_to_max_j0_pre
    (sp retMem dMem dloMem scratchUn0 scratchMem : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word) :
    let r := iterN2Max v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) h) →
      (((loopBodyN2MaxSkipJ0NormPreV4 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old **
          (sp + signExtend12 3968 ↦ₘ retMem) **
          (sp + signExtend12 3960 ↦ₘ dMem) **
          (sp + signExtend12 3952 ↦ₘ dloMem) **
          (sp + signExtend12 3944 ↦ₘ scratchUn0) **
          (sp + signExtend12 3936 ↦ₘ scratchMem) **
          (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
         (qAddr1 ↦ₘ r.1))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
  delta loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=1 max iteration postcondition with v4 scratch cells specializes to the
    j=0 max-body precondition while retaining both the j=1 and j=2 carried
    u4/q atoms as frame. -/
theorem loopIterPostN2MaxScratchX1_j1_to_max_j0_pre_with_j2_frame
    (sp retMem dMem dloMem scratchUn0 scratchMem : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig0 q0Old raVal : Word)
    (uBase2 qAddr2 u4J2 q2 : Word) :
    let r := iterN2Max v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) h) →
      (((loopBodyN2MaxSkipJ0NormPreV4 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig0 r.2.1 r.2.2.1 r.2.2.2.1
          r.2.2.2.2.1 q0Old **
          (sp + signExtend12 3968 ↦ₘ retMem) **
          (sp + signExtend12 3960 ↦ₘ dMem) **
          (sp + signExtend12 3952 ↦ₘ dloMem) **
          (sp + signExtend12 3944 ↦ₘ scratchUn0) **
          (sp + signExtend12 3936 ↦ₘ scratchMem) **
          (.x1 ↦ᵣ raVal)) **
        (((uBase1 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr1 ↦ₘ r.1)) **
         ((uBase2 + signExtend12 4064 ↦ₘ u4J2) **
          (qAddr2 ↦ₘ q2)))) h) := by
  intro r c3 uBase1 qAddr1 h hp
  subst uBase1
  subst qAddr1
  subst c3
  subst r
  delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
  delta loopBodyN2MaxSkipJ0NormPreV4
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_1
  rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
      u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at hp ⊢
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- Unified j=0 N2 call iteration over v4/no-NOP code, preserving concrete
    `x1` and exposing the v4 scratch cell in the final loop postcondition. -/
theorem divK_loop_body_n2_call_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      simp [loopBodyN2CallAddbackBorrowV4, hborrow]
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJ0PostV4NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_j0_beq_norm_v4_noNop_exact_x1
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        loopBodyN2CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold loopBodyN2CallSkipJ0BorrowV4 mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJ0PostV4NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_j0_norm_v4_noNop_exact_x1
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=0 N2 max iteration over v4/no-NOP code, preserving concrete
    `x1` and carrying the v4 scratch cell as frame. -/
theorem divK_loop_body_n2_max_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      ((loopBodyN2MaxSkipJ0NormPreV4 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    have J := divK_loop_body_n2_max_addback_j0_beq_norm_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow_nz
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        rw [loopIterPostN2Max_addback hborrow] at hp
        xperm_hyp hp)
      Jf
  · have hborrow_zero :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := by
      rw [if_neg hborrow]
    have J := divK_loop_body_n2_max_skip_j0_norm_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow_zero
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by
          rw [loopIterPostN2Max_skip hborrow] at hp
          xperm_hyp hp)
        Jf

end EvmAsm.Evm64
