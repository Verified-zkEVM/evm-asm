/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExactShift0Mod

  The n=1 v5 x1-preserving (callable exact-frame) MOD full path, **shift=0 arm**,
  over `modCode_noNop_v5`.  MOD mirror of the DIV
  `FullPathN1V5CallableExactShift0` and the shiftNz MOD
  `FullPathN1V5CallableExactMod`: the shift=0 preloop + x1-preserving shift=0 loop
  land the *shared* op-agnostic `loopN1UnifiedPostV5NoX1` (identical to DIV), so
  the `to_denorm_shift0` rung is a verbatim DIV mirror with only the code surface
  (`divCode_noNop_v5` → `modCode_noNop_v5`), the shift=0 preloop leaf
  (`evm_mod_n1_to_loopSetup_shift0_spec_v5_noNop`), and the code extension
  (`sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5`) changed.  Step toward
  `evm_mod_callable_v5` correctness (SMOD `.proven` track).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExactShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExactMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5ToDenormShift0Mod

namespace EvmAsm.Evm64
open EvmAsm.Rv64 EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56 word_add_zero)

/-- x1-preserving twin of `evm_mod_n1_to_denorm_shift0_spec_v5_noNop`: shift=0
    entry→denorm over `modCode_noNop_v5` with the concrete `x1Val` framed through
    the shift=0 preloop and the x1-free shift=0 loop, free incoming `x9In`/`x2In`.
    Op-agnostic through denorm → the shared `loopN1UnifiedPostV5NoX1` post (verbatim
    DIV mirror). -/
theorem evm_mod_n1_to_denorm_shift0_spec_v5_noNop_preserving_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x1Val x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_z : (clzResult b0).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (((8 + 21 + 24 + 4) + 13) + 632) base (base + denormOff)
      (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       (.x9 ↦ᵣ x9In) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
      ((loopN1UnifiedPostV5NoX1 sp base b0 0 0 0 a3 0 0 0 0 a2 a1 a0 scratchMem) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) ** (.x1 ↦ᵣ x1Val)) := by
  have hb0nz : b0 ≠ 0 := fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z
  have hPre := evm_mod_n1_to_loopSetup_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In x2In
    hbnz hb3z hb2z hb1z hshift_z
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     ((sp + signExtend12 3968) ↦ₘ retMem) **
     ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) **
     ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
    (by pcFree) hPre
  have hLoop0 := divK_loop_n1_call_unified_v5_shift0_of_shape_preserving_x1 sp jMem (1 : Word)
    (clzResult b0).1 ((clzResult b0).2 >>> (63 : Nat)) b3 v11Old
    (signExtend12 (0 : BitVec 12) - (clzResult b0).1)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) x1Val retMem dMem dloMem scratch_un0 scratchMem
    base halign a0 a1 a2 a3 b0 hb0nz hshift_z
  have hLoop := cpsTripleWithin_extend_code sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5 hLoop0
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))
    (by pcFree) hLoop
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1UnifiedPreV5NoX1 loopN1PreWithScratchNoX1 loopN1Pre
      rw [hb1z, hb2z] at hp
      rw [hb3z] at hp ⊢
      rw [show (signExtend12 (4 : BitVec 12) - (1 : Word) : Word) = (3 : Word) from by decide] at hp
      simp only [n1_ub3_off0, n1_ub3_off4088, n1_ub3_off4080,
                  n1_ub3_off4072, n1_ub3_off4064,
                  n2_ub2_off0, n3_ub1_off0, n3_ub0_off0,
                  n1_qa3, n2_qa2, n3_qa1, n3_qa0,
                  se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

attribute [local irreducible] EvmWord.val256 div128Quot_v5 iterWithDoubleAddback mulsubN4 clzResult

/-- `fullModN1FrameShift0V5Rest` minus the trailing `regOwn .x1` (the concrete
    return address is framed outside instead). -/
@[irreducible] def fullModN1FrameShift0V5RestNoX1 (sp base a0 a1 a2 a3 b0 scratchMem : Word) : Assertion :=
  let R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0
  let R2 := fullN1S2 b0 0 0 0 a3 0 0 0 0 a2
  let R1 := fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1
  let R0 := fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b0) **
  ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b0) **
  ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a0) **
  ((sp + signExtend12 3936) ↦ₘ
    divKTrialCallV5ScratchOut R1.2.1 a0 b0
      (divKTrialCallV5ScratchOut R2.2.1 a1 b0
        (divKTrialCallV5ScratchOut R3.2.1 a2 b0
          (divKTrialCallV5ScratchOut 0 a3 b0 scratchMem))))

theorem fullModN1FrameShift0V5RestNoX1_unfold {sp base a0 a1 a2 a3 b0 scratchMem : Word} :
    fullModN1FrameShift0V5RestNoX1 sp base a0 a1 a2 a3 b0 scratchMem =
    (let R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0
     let R2 := fullN1S2 b0 0 0 0 a3 0 0 0 0 a2
     let R1 := fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1
     let R0 := fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
     ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b0) **
     ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b0) **
     ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a0) **
     ((sp + signExtend12 3936) ↦ₘ
       divKTrialCallV5ScratchOut R1.2.1 a0 b0
         (divKTrialCallV5ScratchOut R2.2.1 a1 b0
           (divKTrialCallV5ScratchOut R3.2.1 a2 b0
             (divKTrialCallV5ScratchOut 0 a3 b0 scratchMem))))) := by
  delta fullModN1FrameShift0V5RestNoX1; rfl

theorem fullModN1FrameShift0V5RestNoX1_pcFree {sp base a0 a1 a2 a3 b0 scratchMem : Word} :
    (fullModN1FrameShift0V5RestNoX1 sp base a0 a1 a2 a3 b0 scratchMem).pcFree := by
  rw [fullModN1FrameShift0V5RestNoX1_unfold]; pcFree

private theorem iterN1Call_v5_unfoldModShift0 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5; rfl

/-- x1-free twin of the MOD shift=0 loop-post → epilogue-pre bridge
    (`loopN1UnifiedPostV5_shift0_to_modEpiloguePre`): from the x1-free loop post
    `loopN1UnifiedPostV5NoX1` (+ concrete `.x1 ↦ raVal`) to the MOD shift=0
    epilogue precondition, the quotient output cells split out, and the x1-free
    rest-frame `fullModN1FrameShift0V5RestNoX1`, the concrete return address riding
    through. -/
theorem loopN1UnifiedPostV5NoX1_shift0_to_modEpiloguePre
    (sp base a0 a1 a2 a3 b0 scratchMem raVal : Word) (h : PartialState)
    (hp : (loopN1UnifiedPostV5NoX1 sp base b0 0 0 0 a3 0 0 0 0 a2 a1 a0 scratchMem **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) ** (.x1 ↦ᵣ raVal)) h) :
    (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (sp + signExtend12 4056)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (sp + signExtend12 4088)) **
       (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
       (.x10 ↦ᵣ (mulsubN4
            (div128Quot_v5 (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 a0 b0)
            b0 0 0 0 a0
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1).2.2.2.2) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
       ((sp + signExtend12 4056) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
       ((sp + signExtend12 4048) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
       ((sp + signExtend12 4040) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
       ((sp + signExtend12 4032) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) **
     (((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
       ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
       ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
       ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
     fullModN1FrameShift0V5RestNoX1 sp base a0 a1 a2 a3 b0 scratchMem **
     (.x1 ↦ᵣ raVal)) h := by
  rw [fullModN1FrameShift0V5RestNoX1_unfold]
  delta loopN1UnifiedPostV5NoX1 loopN1Iter210PostV5NoX1 loopN1Iter10PostV5NoX1
    loopIterPostN1V5NoX1 loopIterPostN1CallV5NoX1 at hp
  dsimp only [] at hp
  rw [loopExitPostN1_j0_eq] at hp
  rw [← iterN1Call_v5_unfoldModShift0] at hp
  delta fullN1S0 fullN1S1 fullN1S2
  dsimp only []
  simp only [n1_ub3_off4064, n1_qa3, n2_ub2_off4064, n2_qa2,
      n3_ub1_off4064, n3_qa1, iterN1V5_true, if_true,
      se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp ⊢
  set R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0 with hR3
  set R2 := iterN1Call_v5 b0 0 0 0 a2 R3.2.1 R3.2.2.1 R3.2.2.2.1 R3.2.2.2.2.1 with hR2
  set R1 := iterN1Call_v5 b0 0 0 0 a1 R2.2.1 R2.2.2.1 R2.2.2.2.1 R2.2.2.2.2.1 with hR1
  set R0 := iterN1Call_v5 b0 0 0 0 a0 R1.2.1 R1.2.2.1 R1.2.2.2.1 R1.2.2.2.2.1 with hR0
  xperm_chunked hp

/-- x1-preserving twin of `evm_mod_n1_full_shift0_spec_v5_noNop`: full shift=0
    n=1 MOD path `base → nopOff` over `modCode_noNop_v5` with concrete `x1Val`
    framed and free incoming `x9In`/`x2In`. -/
theorem evm_mod_n1_full_shift0_spec_v5_noNop_preserving_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x1Val x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_z : (clzResult b0).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin ((((8 + 21 + 24 + 4) + 13) + 632) + 12) base (base + nopOff)
      (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       (.x9 ↦ᵣ x9In) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
      (((.x12 ↦ᵣ (sp + 32)) **
         (.x5 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         (.x6 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         (.x7 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
         ((sp + signExtend12 4056) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         ((sp + signExtend12 4048) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         ((sp + signExtend12 4040) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         ((sp + signExtend12 4032) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         ((sp + 32) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         ((sp + 40) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         ((sp + 48) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         ((sp + 56) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1)) **
        (((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
          ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
          ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
          ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
        fullModN1FrameShift0V5RestNoX1 sp base a0 a1 a2 a3 b0 scratchMem **
        (.x1 ↦ᵣ x1Val)) := by
  have hA := evm_mod_n1_to_denorm_shift0_spec_v5_noNop_preserving_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x1Val x9In x2In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_z halign
  have hB := evm_mod_shift0_epilogue_spec_v5_noNop sp base
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1
    (clzResult b0).1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (mulsubN4
        (div128Quot_v5 (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 a0 b0)
        b0 0 0 0 a0
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1).2.2.2.2
    b0 (0 : Word) (0 : Word) (0 : Word) hshift_z
  have hBf := cpsTripleWithin_frameR
    ((((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
       ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
       ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
       ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
      fullModN1FrameShift0V5RestNoX1 sp base a0 a1 a2 a3 b0 scratchMem **
      (.x1 ↦ᵣ x1Val))
    (by rw [fullModN1FrameShift0V5RestNoX1_unfold]; pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hbr := loopN1UnifiedPostV5NoX1_shift0_to_modEpiloguePre sp base a0 a1 a2 a3 b0
        scratchMem x1Val h hp
      xperm_hyp hbr) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
