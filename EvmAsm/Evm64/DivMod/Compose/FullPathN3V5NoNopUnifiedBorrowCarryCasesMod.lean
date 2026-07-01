/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedBorrowCarryCasesMod

  Per-case unified-post wrappers for the n=3 v5 borrowCarry dispatch: each takes
  the per-iteration borrow flags and (named) carry obligations as FRESH inputs and
  weakens the matching combo's per-shape post to `loopN3UnifiedPostV5NoX1`.  By
  keeping the combo application in this clean context (fresh `hc0`, no
  bundle-extraction `rw`), the combo isDefEq stays syntactic — the dispatch then
  only feeds the (rewritten) bundle obligations to these wrappers' parameters,
  avoiding the per-case isDefEq explosion seen when the combo was applied directly
  to the rewritten `hc0`.  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopRestCombosBorrowCarryMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallCombosBorrowCarryNamedMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopRestCombosBorrowCarryNamedMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedMod

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- max×max case → unified post. -/
theorem divK_loop_n3_unified_maxmax_borrowCarry_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb1 : ¬BitVec.ult u3 v2)
    (hc1 :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hb0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r1.2.2.2.1 v2)
    (hc0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 false false sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        unfold loopN3UnifiedPostV5NoX1
        simp only at hp ⊢
        xperm_hyp hp)
      (divK_loop_n3_max_max_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem hb1 hc1 hb0 hc0)

/-- max×call case → unified post. -/
theorem divK_loop_n3_unified_maxcall_borrowCarry_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hb1 : ¬BitVec.ult u3 v2)
    (hc1 :
      BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hb0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.1 v2)
    (hc0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
          v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 false true sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        unfold loopN3UnifiedPostV5NoX1
        simp only at hp ⊢
        xperm_hyp hp)
      (divK_loop_n3_max_call_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry_named
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0)

/-- call×max case → unified post. -/
theorem divK_loop_n3_unified_callmax_borrowCarry_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hb1 : BitVec.ult u3 v2)
    (hc1 :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hb0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r1.2.2.2.1 v2)
    (hc0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 true false sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        unfold loopN3UnifiedPostV5NoX1
        simp only at hp ⊢
        xperm_hyp hp)
      (divK_loop_n3_call_max_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry_named
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0)

/-- call×call case → unified post. -/
theorem divK_loop_n3_unified_callcall_borrowCarry_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hb1 : BitVec.ult u3 v2)
    (hc1 :
      BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hb0 :
      BitVec.ult
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hc0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
          v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 true true sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopN3UnifiedPostV5NoX1
      simp only at hp ⊢
      xperm_hyp hp)
    (divK_loop_n3_call_call_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry_named
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0)

end EvmAsm.Evm64
