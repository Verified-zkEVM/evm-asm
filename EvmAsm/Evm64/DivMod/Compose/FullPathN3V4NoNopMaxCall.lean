/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopMaxCall

  Split-out n=3 max×call exact-source theorem for the v4 no-NOP loop.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Unified n=3 v4 no-`x1` loop postcondition.  It mirrors
    `loopN3UnifiedPost`, but keeps the v4 div128 scratch cell at `sp+3936`
    explicit and leaves the caller-owned `x1` outside the post. -/
@[irreducible]
def loopN3UnifiedPostV4NoX1 (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  match bltu_1, bltu_0 with
  | false, false =>
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
      u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (sp + signExtend12 3968 ↦ₘ retMem) **
    (sp + signExtend12 3960 ↦ₘ dMem) **
    (sp + signExtend12 3952 ↦ₘ dloMem) **
    (sp + signExtend12 3944 ↦ₘ scratchUn0) **
    (sp + signExtend12 3936 ↦ₘ scratchMem) **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))
  | false, true =>
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
      (divKTrialCallV4DLo v2)
      (divKTrialCallV4Un0 r1.2.2.1)
      (divKTrialCallV4ScratchOut r1.2.2.2.1 r1.2.2.1 v2 scratchMem)
      v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))
  | true, false =>
    let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
      u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v2) **
    (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v2)) **
    (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 u2)) **
    (sp + signExtend12 3936 ↦ₘ (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)) **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))
  | true, true =>
    let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    loopIterPostN3CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
      (divKTrialCallV4DLo v2)
      (divKTrialCallV4Un0 r1.2.2.1)
      (divKTrialCallV4ScratchOut r1.2.2.2.1 r1.2.2.1 v2
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem))
      v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
     (qAddr1 ↦ₘ r1.1))

/-- A j=1 max iteration postcondition with v4 scratch cells specializes to the
    j=0 max-body precondition, retaining exact `x1` and j=1 carried u4/q
    atoms as frame. -/
theorem loopIterPostN3MaxScratchX1_j1_to_max_j0_pre
    (sp retMem dMem dloMem scratchUn0 scratchMem : Word)
    (v0 v1 v2 v3 u0J1 u1 u2 u3 uTop u0Orig q0Old raVal : Word) :
    let r := iterN3Max v0 v1 v2 v3 u0J1 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN3Max sp (1 : Word) v0 v1 v2 v3 u0J1 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) h) →
      (((loopBodyN3MaxSkipJ0NormPreV4 sp (1 : Word)
          ((1 : Word) <<< (3 : BitVec 6).toNat) uBase1 qAddr1 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig r.2.1 r.2.2.1 r.2.2.2.1
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
  delta loopIterPostN3Max loopExitPostN3 loopExitPost at hp
  delta loopBodyN3MaxSkipJ0NormPreV4
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

/-- Full n=3 max×max path from the callable-ready v4 loop source, preserving
    concrete `x1`, scratch, and the j=1 stored u4/q atoms. -/
theorem divK_loop_n3_max_max_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
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
    cpsTripleWithin (152 + 152) (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
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
  have J1 := divK_loop_body_n3_max_j1_exact_loopIterScratch_v4_noNop sp base
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
  have J0 := divK_loop_body_n3_max_j0_exact_loopIterScratch_v4_noNop sp base
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

/-- Full n=3 max×call path from the callable-ready v4 loop source, preserving
    concrete `x1`, scratch, and the j=1 stored u4/q atoms. -/
theorem divK_loop_n3_max_call_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
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
      loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 224) (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 r1.2.2.1)
        (divKTrialCallV4ScratchOut r1.2.2.2.1 r1.2.2.1 v2 scratchMem)
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_body_n3_max_j1_exact_loopIterScratch_v4_noNop sp base
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
  have J0 := divK_loop_body_n3_call_j0_exact_loopIterScratch_v4_noNop sp base
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

/-- Unified n=3 v4 no-NOP loop path from the callable-ready no-`x1` source,
    selecting the max/call branch for both iterations and preserving concrete
    caller `x1`.

    Legacy compatibility surface: this still consumes the raw `Carry2NzAll`
    package. New v4 n=3 work should use the selected-carry/R1 siblings below. -/
theorem divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · have hb1 : ¬BitVec.ult u3 v2 := by
      rw [← hbltu_1]
      decide
    have hb0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      rw [← hbltu_0]
      decide
    have hc1 : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop :=
      hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop
    have hc0 :
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        isAddbackCarry2NzN3Max v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
      intro r1
      exact hcarry2 (signExtend12 4095) u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV4NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_max_from_source_exact_loopIterScratch_v4_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem hb1 hc1 hb0 hc0)
  · have hb1 : ¬BitVec.ult u3 v2 := by
      rw [← hbltu_1]
      decide
    have hb0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      exact hbltu_0.symm
    have hc1 : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop :=
      hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop
    have hc0 :
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
      intro r1
      unfold loopBodyN3CallAddbackCarry2NzV4
      exact hcarry2 (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV4NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_call_from_source_exact_loopIterScratch_v4_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0)
  · have hb1 : BitVec.ult u3 v2 := by
      exact hbltu_1.symm
    have hb0 :
        ¬BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      rw [← hbltu_0]
      decide
    have hc1 : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold loopBodyN3CallAddbackCarry2NzV4
      exact hcarry2 (divKTrialCallV4QHat u3 u2 v2) u0 u1 u2 u3 uTop
    have hc0 :
        let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
        isAddbackCarry2NzN3Max v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
      intro r1
      exact hcarry2 (signExtend12 4095) u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV4NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_call_max_from_source_exact_loopIterScratch_v4_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0)
  · have hb1 : BitVec.ult u3 v2 := by
      exact hbltu_1.symm
    have hb0 :
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      exact hbltu_0.symm
    have hc1 : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold loopBodyN3CallAddbackCarry2NzV4
      exact hcarry2 (divKTrialCallV4QHat u3 u2 v2) u0 u1 u2 u3 uTop
    have hc0 :
        let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
        loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
      intro r1
      unfold loopBodyN3CallAddbackCarry2NzV4
      exact hcarry2 (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        unfold loopN3UnifiedPostV4NoX1
        simp only at hp ⊢
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      (divK_loop_n3_call_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0)

/-- Selected-carry variant of
    `divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop`.
    This is the lower-loop replacement surface for the false universal
    `Carry2NzAll` package: callers provide only the carry fact selected by
    each concrete branch. -/
theorem divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      else
        isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_j0 :
      match bltu_1 with
      | false =>
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      | true =>
        let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · have hb1 : ¬BitVec.ult u3 v2 := by
      rw [← hbltu_1]
      decide
    have hb0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      rw [← hbltu_0]
      decide
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV4NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_max_from_source_exact_loopIterScratch_v4_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : ¬BitVec.ult u3 v2 := by
      rw [← hbltu_1]
      decide
    have hb0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      exact hbltu_0.symm
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV4NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_call_from_source_exact_loopIterScratch_v4_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : BitVec.ult u3 v2 := by
      exact hbltu_1.symm
    have hb0 :
        ¬BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      rw [← hbltu_0]
      decide
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV4NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_call_max_from_source_exact_loopIterScratch_v4_noNop
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : BitVec.ult u3 v2 := by
      exact hbltu_1.symm
    have hb0 :
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0
      exact hbltu_0.symm
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        unfold loopN3UnifiedPostV4NoX1
        simp only at hp ⊢
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      (divK_loop_n3_call_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)

/-- R1-shaped selected-carry variant of
    `divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry`.
    The `j=0` carry premise names the first loop result with `iterN3V4`
    instead of exposing the expanded match-on-`bltu_1` proposition. -/
theorem divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarryR1
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      else
        isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_j0 :
      let r1 := iterN3V4 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      if bltu_0 then
        loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      else
        isAddbackCarry2NzN3Max v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      false false sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 (by simpa [iterN3V4] using hcarry2_j0)
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      false true sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 (by simpa [iterN3V4] using hcarry2_j0)
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      true false sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 (by simpa [iterN3V4] using hcarry2_j0)
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      true true sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 (by simpa [iterN3V4] using hcarry2_j0)

/-- Helper: instantiate the v4 no-NOP exact-`x1` n=3 loop with explicit
    normalized values. This is the callable-ready analogue of
    `evm_div_n3_loop_unified_inst_noNop`, with the v4 div128 scratch cell and
    caller-owned `x1` split out of the loop source.

    Legacy compatibility surface: this still consumes the raw `Carry2NzAll`
    package. New v4 n=3 work should use the selected-carry/R1 sibling. -/
theorem evm_div_n3_loop_unified_inst_noNop_exact_x1_v4
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2'
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u4 u3 b2')
            b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry2 : Carry2NzAll b0' b1' b2' b3') :
    cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop
    bltu_1 bltu_0 sp base
    jMem (3 : Word) shift u0 v10Old v11Old antiShift
    b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_1 hbltu_0 hcarry2

/-- Selected-carry instantiation helper for the v4 no-NOP exact-`x1` n=3
    loop.  This is the explicit-normalized-value form used by the preloop
    composition once the false universal `Carry2NzAll` package is removed. -/
theorem evm_div_n3_loop_unified_inst_noNop_exact_x1_v4_selectedCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2'
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u4 u3 b2')
            b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV4 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
      else
        isAddbackCarry2NzN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word))
    (hcarry2_j0 :
      match bltu_1 with
      | false =>
        let r1 := iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4 b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      | true =>
        let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u4 u3 b2')
          b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV4 b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      false false sp base
      jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      false true sp base
      jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      true false sp base
      jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
      true true sp base
      jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0

/-- R1-shaped selected-carry instantiation helper for the v4 no-NOP exact-`x1`
    n=3 loop. This keeps the `j=0` carry premise in the same `iterN3V4`
    shape used by the selected path package. -/
theorem evm_div_n3_loop_unified_inst_noNop_exact_x1_v4_selectedCarryR1
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2'
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV4QHat u4 u3 b2')
            b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV4 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
      else
        isAddbackCarry2NzN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word))
    (hcarry2_j0 :
      let r1 := iterN3V4 bltu_1 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
      if bltu_0 then
        loopBodyN3CallAddbackCarry2NzV4 b0' b1' b2' b3'
          u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      else
        isAddbackCarry2NzN3Max b0' b1' b2' b3'
          u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 448 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV4NoX1 bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  divK_loop_n3_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarryR1
    bltu_1 bltu_0 sp base
    jMem (3 : Word) shift u0 v10Old v11Old antiShift
    b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0

/-- Handoff from the n=3 preloop postcondition to the v4 no-`x1` loop source,
    preserving caller-owned `x1` and the v4 div128 scratch cell. -/
theorem loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed
    (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v11Old : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    ∀ h,
      (loopSetupPost sp (3 : Word) (clzResult b2).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) h →
      (((loopN3PreWithScratchV4NoX1 sp
        jMem (3 : Word) (fullDivN3Shift b2)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old (fullDivN3AntiShift b2)
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) := by
  intro h hp
  delta loopN3PreWithScratchV4NoX1 loopN3PreWithScratchNoX1 loopN3Pre at ⊢
  delta loopSetupPost fullDivN3NormV fullDivN3NormU fullDivN3Shift fullDivN3AntiShift at hp ⊢
  simp only [x1_val_n3] at hp
  simp only [n3_ub1_off0, n3_ub1_off4088, n3_ub1_off4080,
              n3_ub1_off4072, n3_ub1_off4064, n3_ub0_off0,
              n3_qa1, n3_qa0, se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
