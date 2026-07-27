/-
  Shared declaration home for the ADDMOD Lc/Ld carry stages and CondSub adapters.
-/

import EvmAsm.Evm64.AddMod.CarryLowShared
import EvmAsm.Evm64.EvmWordArith.AddMod
import EvmAsm.Evm64.AddMod.Compose.CallAdapter
import EvmAsm.Evm64.AddMod.Compose.TotalBase
import EvmAsm.Evm64.EvmWordArith.AddModCondSub
import EvmAsm.Evm64.Add.Spec
import EvmAsm.Evm64.AddMod.CarryLowShared

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- Frame carried through `stage_low_args`: `x0`, the return address, the
    registers untouched by the block (`x2/x6/x7/x9/x10/x11`, carried at generic
    values), and the owned div-scratch band + its `F−160` cell. -/
def addmodLcStageLowFrame (F raVal x2v x6v x7v x9v x10v x11v : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
  (.x2 ↦ᵣ x2v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) **
  (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12))

theorem addmodLcStageLowFrame_pcFree (F raVal x2v x6v x7v x9v x10v x11v : Word) :
    (addmodLcStageLowFrame F raVal x2v x6v x7v x9v x10v x11v).pcFree := by
  unfold addmodLcStageLowFrame divScratchOwnCallNoX1 divScratchOwn
  pcFree

/-- Link 1 of Lc: `stage_low_args` framed, over `C`. Consumes the (owned from
    the callable return) `x5` at a generic value; parks `m` (=`pow256ModN N`
    limbs `p0..p3`) from F+32..56 into S3, reloads `r` from S2 into F+0..24, and
    reloads `N` from S1 into F+32..56. -/
theorem lc_stage_low_in_C
    (bt F raVal x2v x6v x7v x9v x10v x11v : Word)
    (p0 p1 p2 p3 n0 n1 n2 n3 r0 r1 r2 r3 dd0 dd1 dd2 dd3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 24 (bt + 356) ((bt + 356) + 96)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ p3) **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ dd0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ dd1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ dd2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ dd3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLcStageLowFrame F raVal x2v x6v x7v x9v x10v x11v)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ n3) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLcStageLowFrame F raVal x2v x6v x7v x9v x10v x11v) := by
  simp only [sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x5o => ?_)
  have hblk := carry_block_in_C
    (blockCode := evm_addmod_carry_stage_low_args_code (bt + 356))
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun a i h => evm_addmod_total_program_code_carry_stage_low_args_sub a i
      (by rw [← evm_addmod_carry_stage_low_args_code_eq_ofProg]; exact h))
    (cpsTripleWithin_frameR
      (addmodLcStageLowFrame F raVal x2v x6v x7v x9v x10v x11v)
      (addmodLcStageLowFrame_pcFree F raVal x2v x6v x7v x9v x10v x11v)
      (evm_addmod_carry_stage_low_args_spec_within F (bt + 356) x5o
        p0 p1 p2 p3 sm0 sm1 sm2 sm3 r0 r1 r2 r3 dd0 dd1 dd2 dd3 n0 n1 n2 n3))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hblk
  · simp only [addmodLcStageLowFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp
  · simp only [addmodLcStageLowFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp

-- ============================================================================
-- Lc link 2: the third MOD near-call (byte 452 → 456)
-- ============================================================================

/-- Link 2 of Lc: the third MOD near-call (`JAL@452 → evm_mod_callable_v5 →
    ret@456`), discharged by the adapter. Dividend is the reloaded low sum
    `r = fromLimbs ![r0..r3]`, divisor is the modulus `fromLimbs ![n0..n3]`.
    The div-scratch band arrives OWNED (callable return) and is generic-valued
    via `cpsTripleWithin_pre_divScratchValued`. Mirror of `lb_call2_in_C`, with
    S3 holding the parked carry contribution `p0..p3`. -/
theorem lc_call3_in_C
    (bt F calleeEntry raVal x2v x9v x10v x11v x5v x6v x7v : Word)
    (r0 r1 r2 r3 n0 n1 n2 n3 p0 p1 p2 p3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21)
    (hoffset : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin (1 + (unifiedDivBound + 1)) (bt + 452) ((bt + 452) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((divScratchOwnCallNoX1 F **
        memOwn (F + signExtend12 (3936 : BitVec 12)) **
        (.x12 ↦ᵣ F) ** (.x9 ↦ᵣ x9v) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ x2v) **
        (.x5 ↦ᵣ x5v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) **
        (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x0 ↦ᵣ (0 : Word)) **
        evmWordIs F (EvmWord.fromLimbs ![r0, r1, r2, r3]) **
        evmWordIs (F + 32) (EvmWord.fromLimbs ![n0, n1, n2, n3])) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
      ((modStackDispatchPostCallableX9Owned F (EvmWord.fromLimbs ![r0, r1, r2, r3])
          (EvmWord.fromLimbs ![n0, n1, n2, n3]) ((bt + 452) + 4) **
        memOwn (F + signExtend12 (3936 : BitVec 12))) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3) := by
  refine cpsTripleWithin_frameR _
    (addmodCall1Frame_pcFree F n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3) ?_
  refine cpsTripleWithin_pre_divScratchValued (fun dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 => ?_)
  refine cpsTripleWithin_pre_memOwn_under (fun scratchMem => ?_)
  have hadapter := evm_addmod_v5_call_adapter_in_C (bt + 452) F calleeEntry mo3
    (EvmWord.fromLimbs ![r0, r1, r2, r3]) (EvmWord.fromLimbs ![n0, n1, n2, n3])
    x9v raVal x2v x5v x6v x7v x10v x11v
    dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    hoffset callerAlign retAlign hdisj
    (fun a i h => evm_addmod_total_program_code_carry_call3_sub a i h)
    hdisjTC
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => hp) hadapter
  rw [divModStackDispatchPreNoX1_unfold]
  simp only [sepConj_assoc'] at hp ⊢
  xperm_hyp hp

-- ============================================================================
-- Lc link 3: call_mod_restore (byte 456 → 460), and the full Lc sub-chain
-- ============================================================================

/-- The call-3 post minus `x12`: the callable's x9-owned return frame (x12
    peeled), the scratch cell, and the S1/S2/S3 park cells (`p` = carry
    contribution at S3). -/
def addmodAfterCall3Rest (F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word) : Assertion :=
  (regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
   evmWordIs F d ** evmWordIs (F + 32) v **
   divScratchOwnCallNoX1 F ** (.x1 ↦ᵣ raVal) ** regOwn .x9) **
  memOwn (F + signExtend12 (3936 : BitVec 12)) **
  addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3

theorem addmodAfterCall3Rest_pcFree (F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word) :
    (addmodAfterCall3Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3).pcFree := by
  unfold addmodAfterCall3Rest addmodCall1Frame divScratchOwnCallNoX1 divScratchOwn evmWordIs
  pcFree

/-- Full Lc post bundle: after the third MOD call and the frame-pointer restore,
    `x12 = F`, the reduced low sum `EvmWord.mod r N` sits at F+32..56, with the
    carry contribution `p` (=`pow256ModN N` limbs) parked at S3, N at S1, r at
    S2, and the callable frame shed. -/
def addmodCarryAfterCall3 (F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word) : Assertion :=
  (.x12 ↦ᵣ F) **
  addmodAfterCall3Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3

/-- Link 3 of Lc: `call_mod_restore` (`ADDI x12 x12 −32` at byte 456) framed with
    the callable return frame, over `C`. Restores `x12 = F+32 → F`. Mirror of
    `lb_restore_in_C`. -/
theorem lc_restore_in_C
    (bt F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 1 (bt + 456) ((bt + 456) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((.x12 ↦ᵣ (F + 32)) **
       addmodAfterCall3Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
      (addmodCarryAfterCall3 F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3) := by
  have hsubRestore : ∀ a i,
      CodeReq.singleton (bt + 456) (.ADDI .x12 .x12 (4064 : BitVec 12)) a = some i →
      (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC) a = some i := by
    intro a i ha
    refine evm_addmod_total_program_code_carry_call3_sub a i ?_
    rw [← evm_addmod_carry_call_mod_code_eq_ofProg]
    show (CodeReq.union (CodeReq.singleton (bt + 452) (.JAL .x1 mo3))
        (CodeReq.singleton ((bt + 452) + 4) (.ADDI .x12 .x12 (4064 : BitVec 12)))) a = some i
    refine CodeReq.mono_union_right
      (CodeReq.Disjoint.singleton (by
        rw [show (bt + 452) + 4 = bt + 456 from by bv_omega]; bv_omega))
      (fun a' i' h => h) a i ?_
    rw [show (bt + 452) + 4 = bt + 456 from by bv_omega]; exact ha
  have hrestore := cpsTripleWithin_frameR
    (addmodAfterCall3Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
    (addmodAfterCall3Rest_pcFree F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
    (evm_addmod_carry_call_mod_restore_spec_within (F + 32) (bt + 456))
  rw [show (F + 32) + signExtend12 (4064 : BitVec 12) = F from by
    rw [show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide]
    bv_omega] at hrestore
  exact carry_block_in_C hsubRestore hrestore

/-- **Lc complete** (chain form): `stage_low_args ;; [call3] ;; restore` over
    `C`, byte 356 → 460. Post `addmodCarryAfterCall3`: `x12 = F`,
    `EvmWord.mod r N` at F+32..56, carry contribution `p` parked at S3. -/
theorem lc_spec_within
    (bt F raVal x2v x6v x7v x9v x10v x11v : Word)
    (p0 p1 p2 p3 n0 n1 n2 n3 r0 r1 r2 r3 dd0 dd1 dd2 dd3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hoffset : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin ((24 + (1 + (unifiedDivBound + 1))) + 1) (bt + 356) (((bt + 452) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ p3) **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ dd0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ dd1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ dd2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ dd3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLcStageLowFrame F raVal x2v x6v x7v x9v x10v x11v)
      (addmodCarryAfterCall3 F ((bt + 452) + 4)
        (EvmWord.fromLimbs ![r0, r1, r2, r3])
        (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) (EvmWord.fromLimbs ![n0, n1, n2, n3]))
        n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3) := by
  -- link 1: stage_low (356→452)
  have hs := lc_stage_low_in_C bt F raVal x2v x6v x7v x9v x10v x11v
    p0 p1 p2 p3 n0 n1 n2 n3 r0 r1 r2 r3 dd0 dd1 dd2 dd3 sm0 sm1 sm2 sm3
    mo1 mo2 mo3 moNC calleeEntry
  rw [show (bt + 356) + 96 = bt + 452 from by bv_omega] at hs
  -- link 2: call3 (452→456); stage_low leaves x5=n3
  have hc := lc_call3_in_C bt F calleeEntry raVal x2v x9v x10v x11v
    n3 x6v x7v r0 r1 r2 r3 n0 n1 n2 n3 p0 p1 p2 p3
    mo1 mo2 mo3 moNC hoffset callerAlign retAlign hdisj hdisjTC
  -- link 3: restore (456→460)
  have hr := lc_restore_in_C bt F ((bt + 452) + 4)
    (EvmWord.fromLimbs ![r0, r1, r2, r3])
    (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) (EvmWord.fromLimbs ![n0, n1, n2, n3]))
    n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 mo1 mo2 mo3 moNC calleeEntry
  rw [show bt + 456 = (bt + 452) + 4 from by bv_omega] at hr
  have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
  have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
  have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
  have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
  refine cpsTripleWithin_seq_perm_same_cr ?_
    (cpsTripleWithin_seq_perm_same_cr ?_ hs hc) hr
  · -- call3 post → restore pre
    intro h hp2
    simp only [addmodCall1Frame, addmodAfterCall3Rest,
      modStackDispatchPostCallableX9Owned_unfold, modStackDispatchPostCallable_unfold] at hp2 ⊢
    xperm_hyp hp2
  · -- stage_low post → call3 pre (fold r/n cells → fromLimbs, permute scratch to lead)
    intro h hp1
    simp only [addmodLcStageLowFrame, addmodCall1Frame,
      evmWordIs, EvmWord.getLimbN_fromLimbs_gen_0, EvmWord.getLimbN_fromLimbs_gen_1,
      EvmWord.getLimbN_fromLimbs_gen_2, EvmWord.getLimbN_fromLimbs_gen_3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      e0, e8, e16, e24, e32, e40, e48, e56,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp1 ⊢
    xperm_hyp hp1

/-- La;;Lb over `C`: carry entry (byte 160) through the second MOD call
    (byte 356). Post: `x12 = F`, `EvmWord.pow256ModN N` at F+32..56 (the
    `2^256 mod N` carry contribution), N parked at S1, r at S2. -/
theorem evm_addmod_carry_after_call2_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hN : EvmWord.fromLimbs ![n0, n1, n2, n3] ≠ 0)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      (((21 + (1 + (unifiedDivBound + 1))) + 1) + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
      (bt + 160) (((bt + 348) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodCarryAfterCall2 F ((bt + 348) + 4)
        (EvmWord.mod (-1 : EvmWord) (EvmWord.fromLimbs ![n0, n1, n2, n3]) + 1)
        (EvmWord.pow256ModN (EvmWord.fromLimbs ![n0, n1, n2, n3]))
        n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  -- La (160 → 248+4 = 252)
  have hla := la_spec_within bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem
    mo1 mo2 mo3 moNC calleeEntry hoffset1 callerAlign1 retAlign hdisj1 hdisjTC
  rw [show (bt + 248) + 4 = bt + 252 from by bv_omega] at hla
  set N := EvmWord.fromLimbs ![n0, n1, n2, n3] with hNdef
  -- Lb, re-derived with x2/x9/x10/x11 OWNED in its pre, instantiated at the
  -- concrete work-cell limbs m_i = getLimbN (mod (-1) N) i, w_i = getLimbN (-1) i.
  have hlb_ready : cpsTripleWithin (((24 + (1 + (unifiedDivBound + 1))) + 1))
      (bt + 252) (((bt + 348) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (addmodCarryAfterCall1 F (bt + 248) n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodCarryAfterCall2 F ((bt + 348) + 4)
        (EvmWord.mod (-1 : EvmWord) N + 1)
        (EvmWord.pow256ModN N) n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
    -- key: pre with the four sheddable regs OWNED, brought to the front.
    have key : cpsTripleWithin (((24 + (1 + (unifiedDivBound + 1))) + 1))
        (bt + 252) (((bt + 348) + 4) + 4)
        (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
        (regOwn .x2 ** regOwn .x9 ** regOwn .x10 ** regOwn .x11 **
          ((.x12 ↦ᵣ F) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           (.x0 ↦ᵣ (0 : Word)) **
           evmWordIs F (-1 : EvmWord) **
           evmWordIs (F + 32) (EvmWord.mod (-1 : EvmWord) N) **
           divScratchOwnCallNoX1 F ** (.x1 ↦ᵣ (bt + 248)) **
           memOwn (F + signExtend12 (3936 : BitVec 12)) **
           addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3))
        (addmodCarryAfterCall2 F ((bt + 348) + 4)
          (EvmWord.mod (-1 : EvmWord) N + 1)
          (EvmWord.pow256ModN N) n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
      refine cpsTripleWithin_pre_regOwn (fun x2gv => ?_)
      refine cpsTripleWithin_pre_regOwn_under (fun x9gv => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x10gv => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x11gv => ?_)
      have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
      have hqfold := addOne_via_incr_chain (EvmWord.mod (-1 : EvmWord) N)
      simp only at hqfold
      have hv := EvmWord.pow256ModN_runtime_construction N hN
      have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
      have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
      have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
      have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
      have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
      have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
      have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
      have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
        (lb_spec_within bt F (bt + 248) x2gv x9gv x10gv x11gv
          ((EvmWord.mod (-1 : EvmWord) N).getLimbN 0) ((EvmWord.mod (-1 : EvmWord) N).getLimbN 1)
          ((EvmWord.mod (-1 : EvmWord) N).getLimbN 2) ((EvmWord.mod (-1 : EvmWord) N).getLimbN 3)
          ((-1 : EvmWord).getLimbN 0) ((-1 : EvmWord).getLimbN 1)
          ((-1 : EvmWord).getLimbN 2) ((-1 : EvmWord).getLimbN 3)
          n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3
          mo1 mo2 mo3 moNC calleeEntry hoffset2 callerAlign2 retAlign hdisj2 hdisjTC)
      · -- pre: my peeled pre → Lb's pre (fold evmWordIs work cells, permute)
        simp only [addmodLbPlusOneFrame, addmodCall1Frame, evmWordIs,
          e0, e8, e16, e24, e32, e40, e48, e56,
          BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp ⊢
        xperm_hyp hp
      · -- post: Lb's post → goal post (rewrite dividend / remainder to pow256ModN N)
        simp only [hse] at hp
        rw [hqfold, hv] at hp
        exact hp
    -- Reshape addmodCarryAfterCall1 into key's pre (pure permutation).
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) key
    simp only [addmodCarryAfterCall1, addmodAfterCall1Rest, hNdef] at hp ⊢
    xperm_hyp hp
  -- Chain La ;; Lb.
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hla hlb_ready

/-- La;;Lb;;Lc over `C`: carry entry (byte 160) through the third MOD call
    (byte 460). Post: `x12 = F`, `EvmWord.mod r N` (the reduced low sum) at
    F+32..56, the carry contribution `pow256ModN N` parked at S3, N at S1,
    r at S2. -/
theorem evm_addmod_carry_after_call3_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hN : EvmWord.fromLimbs ![n0, n1, n2, n3] ≠ 0)
    (hoffset1 : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign1 : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (hoffset2 : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign2 : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (hoffset3 : (bt + 452) + signExtend21 mo3 = calleeEntry)
    (callerAlign3 : ((bt + 452) + 4) &&& ~~~(1 : Word) = (bt + 452) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj1 : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj2 : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisj3 : (CodeReq.singleton (bt + 452) (.JAL .x1 mo3)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin
      ((((21 + (1 + (unifiedDivBound + 1))) + 1) + (((24 + (1 + (unifiedDivBound + 1))) + 1)))
        + ((24 + (1 + (unifiedDivBound + 1))) + 1))
      (bt + 160) (((bt + 452) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodCarryAfterCall3 F ((bt + 452) + 4)
        (EvmWord.fromLimbs ![r0, r1, r2, r3])
        (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) (EvmWord.fromLimbs ![n0, n1, n2, n3]))
        n0 n1 n2 n3 r0 r1 r2 r3
        ((EvmWord.pow256ModN (EvmWord.fromLimbs ![n0, n1, n2, n3])).getLimbN 0)
        ((EvmWord.pow256ModN (EvmWord.fromLimbs ![n0, n1, n2, n3])).getLimbN 1)
        ((EvmWord.pow256ModN (EvmWord.fromLimbs ![n0, n1, n2, n3])).getLimbN 2)
        ((EvmWord.pow256ModN (EvmWord.fromLimbs ![n0, n1, n2, n3])).getLimbN 3)) := by
  set N := EvmWord.fromLimbs ![n0, n1, n2, n3] with hNdef
  -- La;;Lb (160 → 356)
  have hac2 := evm_addmod_carry_after_call2_spec_within
    bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem
    mo1 mo2 mo3 moNC calleeEntry hN
    hoffset1 callerAlign1 hoffset2 callerAlign2 retAlign hdisj1 hdisj2 hdisjTC
  rw [show ((bt + 348) + 4) + 4 = bt + 356 from by bv_omega] at hac2
  -- Lc, re-derived with x2/x6/x7/x9/x10/x11 OWNED in its pre, instantiated at the
  -- concrete work-cell limbs p_i = getLimbN (pow256ModN N) i (F+32..56), and the
  -- stale dividend dd_i = getLimbN (mod (-1) N + 1) i (F+0..24).
  have hlc_ready : cpsTripleWithin ((24 + (1 + (unifiedDivBound + 1))) + 1)
      (bt + 356) (((bt + 452) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (addmodCarryAfterCall2 F ((bt + 348) + 4)
        (EvmWord.mod (-1 : EvmWord) N + 1) (EvmWord.pow256ModN N)
        n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodCarryAfterCall3 F ((bt + 452) + 4)
        (EvmWord.fromLimbs ![r0, r1, r2, r3])
        (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) N)
        n0 n1 n2 n3 r0 r1 r2 r3
        ((EvmWord.pow256ModN N).getLimbN 0) ((EvmWord.pow256ModN N).getLimbN 1)
        ((EvmWord.pow256ModN N).getLimbN 2) ((EvmWord.pow256ModN N).getLimbN 3)) := by
    have key : cpsTripleWithin ((24 + (1 + (unifiedDivBound + 1))) + 1)
        (bt + 356) (((bt + 452) + 4) + 4)
        (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
        (regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** regOwn .x9 ** regOwn .x10 ** regOwn .x11 **
          ((.x12 ↦ᵣ F) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
           evmWordIs F (EvmWord.mod (-1 : EvmWord) N + 1) **
           evmWordIs (F + 32) (EvmWord.pow256ModN N) **
           divScratchOwnCallNoX1 F ** (.x1 ↦ᵣ ((bt + 348) + 4)) **
           memOwn (F + signExtend12 (3936 : BitVec 12)) **
           addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3))
        (addmodCarryAfterCall3 F ((bt + 452) + 4)
          (EvmWord.fromLimbs ![r0, r1, r2, r3])
          (EvmWord.mod (EvmWord.fromLimbs ![r0, r1, r2, r3]) N)
          n0 n1 n2 n3 r0 r1 r2 r3
          ((EvmWord.pow256ModN N).getLimbN 0) ((EvmWord.pow256ModN N).getLimbN 1)
          ((EvmWord.pow256ModN N).getLimbN 2) ((EvmWord.pow256ModN N).getLimbN 3)) := by
      refine cpsTripleWithin_pre_regOwn (fun x2g => ?_)
      refine cpsTripleWithin_pre_regOwn_under (fun x6g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x7g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x9g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x10g => ?_)
      rw [← sepConj_assoc']; refine cpsTripleWithin_pre_regOwn_under (fun x11g => ?_)
      have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
      have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
      have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
      have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
      have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
      have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
      have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
      have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp)
        (lc_spec_within bt F ((bt + 348) + 4) x2g x6g x7g x9g x10g x11g
          ((EvmWord.pow256ModN N).getLimbN 0) ((EvmWord.pow256ModN N).getLimbN 1)
          ((EvmWord.pow256ModN N).getLimbN 2) ((EvmWord.pow256ModN N).getLimbN 3)
          n0 n1 n2 n3 r0 r1 r2 r3
          ((EvmWord.mod (-1 : EvmWord) N + 1).getLimbN 0)
          ((EvmWord.mod (-1 : EvmWord) N + 1).getLimbN 1)
          ((EvmWord.mod (-1 : EvmWord) N + 1).getLimbN 2)
          ((EvmWord.mod (-1 : EvmWord) N + 1).getLimbN 3)
          sm0 sm1 sm2 sm3
          mo1 mo2 mo3 moNC calleeEntry hoffset3 callerAlign3 retAlign hdisj3 hdisjTC)
      -- pre: my peeled pre → Lc's pre (fold evmWordIs work cells to getLimbN, permute)
      simp only [addmodLcStageLowFrame, addmodCall1Frame, evmWordIs,
        e0, e8, e16, e24, e32, e40, e48, e56,
        BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp ⊢
      xperm_hyp hp
    -- Reshape addmodCarryAfterCall2 into key's pre (pure permutation).
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) key
    simp only [addmodCarryAfterCall2, addmodAfterCall2Rest, hNdef] at hp ⊢
    xperm_hyp hp
  -- Chain (La;;Lb) ;; Lc.
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hac2 hlc_ready

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Pass-1 ;; take with the dead `x5/x6/x7` outputs shed to `regOwn` and the
    mask folded to the opaque parameter `mask`. This is the shallow-intermediate
    feed for the whole-block composition. -/
theorem evm_addmod_cond_sub_pass1take_clean
    (base sp carry x6Old x7Old x10Old x11Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 mask : Word)
    (hmask : mask = (0 : Word) -
      ((carry + signExtend12 (0 : BitVec 12)) |||
       (((if BitVec.ult s3 n3 then (1 : Word) else 0) |||
          (if BitVec.ult (s3 - n3)
            ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
             (if BitVec.ult (s2 - n2)
               ((if BitVec.ult s1 n1 then (1 : Word) else 0) |||
                (if BitVec.ult (s1 - n1)
                  (if BitVec.ult s0 n0 then (1 : Word) else 0)
                  then (1 : Word) else 0))
               then (1 : Word) else 0))
            then (1 : Word) else 0))
         ^^^ signExtend12 (1 : BitVec 12)))) :
    cpsTripleWithin 25 base (base + 100)
      (CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 36) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 44) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 52) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 56) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 60) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 68) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x11))
      (CodeReq.union (CodeReq.singleton (base + 84) (.OR .x11 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 88) (.XORI .x11 .x11 (1 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 92) (.OR .x11 .x10 .x11))
       (CodeReq.singleton (base + 96) (.SUB .x11 .x0 .x11))))))))))))))))))))))))))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x10 ↦ᵣ (carry + signExtend12 (0 : BitVec 12))) ** (.x11 ↦ᵣ mask) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  have P1 := evm_addmod_cond_sub_pass1take_spec_within base sp carry x6Old x7Old
    x10Old x11Old s0 s1 s2 s3 n0 n1 n2 n3
  refine cpsTripleWithin_weaken (fun _ h => h) ?_ P1
  intro st hp
  simp only [← hmask] at hp
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7) (fun _ h => h)))) st hp

/-- Pass-2 with its dead-on-entry `x5/x6/x7` inputs merely `regOwn` (the
    cond-subtract's second pass reloads them immediately). This is the shape
    that joins onto `evm_addmod_cond_sub_pass1take_clean`'s shed post. Proven by
    peeling the three owned registers to generic values (the pass-2 spec is
    parametric in them) via `cpsTripleWithin_pre_regOwn(_under)`. -/
theorem evm_addmod_cond_sub_pass2_owned
    (base sp maskIn x10Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 : Word) :
    let mm0 := n0 &&& maskIn
    let c0 := if BitVec.ult s0 mm0 then (1 : Word) else 0
    let r0 := s0 - mm0
    let mm1 := n1 &&& maskIn
    let f1 := if BitVec.ult s1 mm1 then (1 : Word) else 0
    let e1 := s1 - mm1
    let g1 := if BitVec.ult e1 c0 then (1 : Word) else 0
    let r1 := e1 - c0
    let c1 := f1 ||| g1
    let mm2 := n2 &&& maskIn
    let f2 := if BitVec.ult s2 mm2 then (1 : Word) else 0
    let e2 := s2 - mm2
    let g2 := if BitVec.ult e2 c1 then (1 : Word) else 0
    let r2 := e2 - c1
    let c2 := f2 ||| g2
    let mm3 := n3 &&& maskIn
    let r3 := (s3 - mm3) - c2
    cpsTripleWithin 30 base (base + 120)
      (CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3872 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x10 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (0 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (3880 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 32) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 40) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x10 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (8 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 60) (.LD .x6 .x12 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x7 .x12 (3888 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 68) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 84) (.SUB .x6 .x6 .x10))
      (CodeReq.union (CodeReq.singleton (base + 88) (.OR .x10 .x5 .x7))
      (CodeReq.union (CodeReq.singleton (base + 92) (.SD .x12 .x6 (16 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 96) (.LD .x6 .x12 (24 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 100) (.LD .x7 .x12 (3896 : BitVec 12)))
      (CodeReq.union (CodeReq.singleton (base + 104) (.AND .x7 .x7 .x11))
      (CodeReq.union (CodeReq.singleton (base + 108) (.SUB .x6 .x6 .x7))
      (CodeReq.union (CodeReq.singleton (base + 112) (.SUB .x6 .x6 .x10))
       (CodeReq.singleton (base + 116) (.SD .x12 .x6 (24 : BitVec 12))))))))))))))))))))))))))))))))
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ f2) ** (.x6 ↦ᵣ r3) ** (.x7 ↦ᵣ mm3) **
       (.x10 ↦ᵣ c2) ** (.x11 ↦ᵣ maskIn) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  intro mm0 c0 r0 mm1 f1 e1 g1 r1 c1 mm2 f2 e2 g2 r2 c2 mm3 r3
  refine cpsTripleWithin_pre_regOwn (fun v5 => ?_)
  refine cpsTripleWithin_pre_regOwn_under (fun v6 => ?_)
  rw [← sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun v7 => ?_)
  rw [sepConj_assoc']
  have P := evm_addmod_cond_sub_pass2_spec_within base sp maskIn v5 v6 v7 x10Old
    s0 s1 s2 s3 n0 n1 n2 n3
  simp only [mm0, c0, r0, mm1, f1, e1, g1, r1, c1, mm2, f2, e2, g2, r2, c2,
    mm3, r3] at P ⊢
  exact cpsTripleWithin_weaken (fun st h => by xperm_hyp h) (fun _ h => h) P

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Slice-equation tactic (mirror of `TotalBase.evm_addmod_total_slice_rfl`):
    unfolds the total program to its concrete instruction list so a
    `List.take .. (List.drop ..)` slice reduces by `rfl`. -/
local macro "addmod_total_slice_rfl" : tactic =>
  `(tactic| (
      unfold evm_addmod_total evm_addmod_prologue evm_add
        evm_addmod_phase1_carry evm_addmod_phase2_n_zero_test
        evm_addmod_carry_save_operands evm_addmod_carry_minus_one_args
        evm_addmod_carry_call_mod evm_addmod_carry_plus_one_args
        evm_addmod_carry_stage_low_args evm_addmod_carry_mod_add_stage
        evm_addmod_carry_cond_sub evm_addmod_phase2_mod_call
        evm_addmod_phase2_zero_path evm_addmod_epilogue
      simp only [seq, single]
      rfl))

/-- The pass1take borrow-chain + mask program (first 25 instrs of
    `evm_addmod_carry_cond_sub`). -/
def condSubPass1Prog : List Instr :=
  [.ADDI .x10 .x5 0, .LD .x6 .x12 0, .LD .x7 .x12 3872, .SLTU .x11 .x6 .x7,
   .LD .x6 .x12 8, .LD .x7 .x12 3880, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7,
   .SLTU .x7 .x6 .x11, .OR .x11 .x5 .x7, .LD .x6 .x12 16, .LD .x7 .x12 3888,
   .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7, .SLTU .x7 .x6 .x11, .OR .x11 .x5 .x7,
   .LD .x6 .x12 24, .LD .x7 .x12 3896, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7,
   .SLTU .x7 .x6 .x11, .OR .x11 .x5 .x7, .XORI .x11 .x11 1, .OR .x11 .x10 .x11,
   .SUB .x11 .x0 .x11]

/-- The pass2 masked-subtract program (last 30 instrs of
    `evm_addmod_carry_cond_sub`). -/
def condSubPass2Prog : List Instr :=
  [.LD .x6 .x12 0, .LD .x7 .x12 3872, .AND .x7 .x7 .x11, .SLTU .x10 .x6 .x7,
   .SUB .x5 .x6 .x7, .SD .x12 .x5 0, .LD .x6 .x12 8, .LD .x7 .x12 3880,
   .AND .x7 .x7 .x11, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7, .SLTU .x7 .x6 .x10,
   .SUB .x6 .x6 .x10, .OR .x10 .x5 .x7, .SD .x12 .x6 8, .LD .x6 .x12 16,
   .LD .x7 .x12 3888, .AND .x7 .x7 .x11, .SLTU .x5 .x6 .x7, .SUB .x6 .x6 .x7,
   .SLTU .x7 .x6 .x10, .SUB .x6 .x6 .x10, .OR .x10 .x5 .x7, .SD .x12 .x6 16,
   .LD .x6 .x12 24, .LD .x7 .x12 3896, .AND .x7 .x7 .x11, .SUB .x6 .x6 .x7,
   .SUB .x6 .x6 .x10, .SD .x12 .x6 24]

/-- The 25-singleton union code of the `pass1take_clean` block. Matches the
    inline code term in `evm_addmod_cond_sub_pass1take_clean`. -/
abbrev condSubPass1Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x7 .x12 (3872 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x11 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x6 .x12 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (3880 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x7 .x6 .x11))
  (CodeReq.union (CodeReq.singleton (base + 36) (.OR .x11 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x6 .x12 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 44) (.LD .x7 .x12 (3888 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 52) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SLTU .x7 .x6 .x11))
  (CodeReq.union (CodeReq.singleton (base + 60) (.OR .x11 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x6 .x12 (24 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 68) (.LD .x7 .x12 (3896 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x11))
  (CodeReq.union (CodeReq.singleton (base + 84) (.OR .x11 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 88) (.XORI .x11 .x11 (1 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 92) (.OR .x11 .x10 .x11))
   (CodeReq.singleton (base + 96) (.SUB .x11 .x0 .x11)))))))))))))))))))))))))

/-- The 30-singleton union code of the `pass2_owned` block. Matches the inline
    code term in `evm_addmod_cond_sub_pass2_owned` / `..._spec_within`. -/
abbrev condSubPass2Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 (3872 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x10 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SUB .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 (0 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (3880 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 32) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 36) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SLTU .x7 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x6 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x10 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (8 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 60) (.LD .x6 .x12 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x7 .x12 (3888 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 68) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x5 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 80) (.SLTU .x7 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 84) (.SUB .x6 .x6 .x10))
  (CodeReq.union (CodeReq.singleton (base + 88) (.OR .x10 .x5 .x7))
  (CodeReq.union (CodeReq.singleton (base + 92) (.SD .x12 .x6 (16 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 96) (.LD .x6 .x12 (24 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 100) (.LD .x7 .x12 (3896 : BitVec 12)))
  (CodeReq.union (CodeReq.singleton (base + 104) (.AND .x7 .x7 .x11))
  (CodeReq.union (CodeReq.singleton (base + 108) (.SUB .x6 .x6 .x7))
  (CodeReq.union (CodeReq.singleton (base + 112) (.SUB .x6 .x6 .x10))
   (CodeReq.singleton (base + 116) (.SD .x12 .x6 (24 : BitVec 12)))))))))))))))))))))))))))))))

theorem condSubPass1Code_eq_ofProg (base : Word) :
    condSubPass1Code base = CodeReq.ofProg base condSubPass1Prog := by
  unfold condSubPass1Code condSubPass1Prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

theorem condSubPass2Code_eq_ofProg (base : Word) :
    condSubPass2Code base = CodeReq.ofProg base condSubPass2Prog := by
  unfold condSubPass2Code condSubPass2Prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

/-- The pass1take half (byte 612, instr 153, len 25) is subsumed by the total
    program code. -/
theorem evm_addmod_total_program_code_cond_sub_pass1_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, condSubPass1Code (base + 612) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  intro a i h
  rw [condSubPass1Code_eq_ofProg] at h
  revert a i h
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 612)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    condSubPass1Prog 153
    (by bv_omega) ?_ ?_ ?_
  · addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

/-- The pass2 half (byte 712, instr 178, len 30) is subsumed by the total
    program code. -/
theorem evm_addmod_total_program_code_cond_sub_pass2_sub
    {base : Word} {modOff1 modOff2 modOff3 modOffNC : BitVec 21} :
    ∀ a i, condSubPass2Code (base + 712) a = some i →
      (evm_addmod_total_program_code base modOff1 modOff2 modOff3 modOffNC) a
        = some i := by
  intro a i h
  rw [condSubPass2Code_eq_ofProg] at h
  revert a i h
  unfold evm_addmod_total_program_code
  refine CodeReq.ofProg_mono_sub base (base + 712)
    (evm_addmod_total modOff1 modOff2 modOff3 modOffNC)
    condSubPass2Prog 178
    (by bv_omega) ?_ ?_ ?_
  · addmod_total_slice_rfl
  · rw [evm_addmod_total_length]; decide
  · rw [evm_addmod_total_length]; decide

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- Frame carried through `mod_add_stage`: `x0`, the return address, the six
    registers untouched (`x2/x6/x7/x9/x10/x11`, generic), the owned div-scratch
    band + `F−160` cell, the reduced low sum at F+32..56 (`rMod`), and the
    S1/S2 park cells (N and r). -/
def addmodLdModAddFrame (F raVal x2v x6v x7v x9v x10v x11v : Word)
    (v : EvmWord) (n0 n1 n2 n3 r0 r1 r2 r3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
  (.x2 ↦ᵣ x2v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) **
  (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  evmWordIs (F + 32) v **
  ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
  ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
  ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
  ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3)

theorem addmodLdModAddFrame_pcFree (F raVal x2v x6v x7v x9v x10v x11v : Word)
    (v : EvmWord) (n0 n1 n2 n3 r0 r1 r2 r3 : Word) :
    (addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3).pcFree := by
  unfold addmodLdModAddFrame divScratchOwnCallNoX1 divScratchOwn evmWordIs
  pcFree

/-- Link 1 of Ld: `mod_add_stage` framed, over `C`. Copies the carry
    contribution `m` (limbs `p0..p3`, from S3) into F+0..24 (over the stale
    dividend `dd0..dd3`), leaving `rMod` at F+32..56. -/
theorem ld_mod_add_stage_in_C
    (bt F raVal x2v x6v x7v x9v x10v x11v : Word) (v : EvmWord)
    (p0 p1 p2 p3 n0 n1 n2 n3 r0 r1 r2 r3 dd0 dd1 dd2 dd3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 8 (bt + 460) ((bt + 460) + 32)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ dd0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ dd1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ dd2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ dd3)) **
       addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ p3) **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ p3)) **
       addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3) := by
  simp only [sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x5o => ?_)
  have hblk := carry_block_in_C
    (blockCode := evm_addmod_carry_mod_add_stage_code (bt + 460))
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun a i h => evm_addmod_total_program_code_carry_mod_add_stage_sub a i
      (by rw [← evm_addmod_carry_mod_add_stage_code_eq_ofProg]; exact h))
    (cpsTripleWithin_frameR
      (addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3)
      (addmodLdModAddFrame_pcFree F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3)
      (evm_addmod_carry_mod_add_stage_spec_within F (bt + 460) x5o
        p0 p1 p2 p3 dd0 dd1 dd2 dd3))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hblk
  · simp only [addmodLdModAddFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp
  · simp only [addmodLdModAddFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp

-- ============================================================================
-- Ld link 2: evm_add (byte 492 → 612)
-- ============================================================================

/-- The `evm_add` carry-out (`x5` of `evm_add_stack_spec_within`, the `carry3`
    let-chain over `getLimbN`) equals the 257th-bit overflow indicator. Bridges
    `evm_add_carry3_eq_overflow` (stated over `getLimb`) into the `getLimbN`
    form `evm_add_stack_spec_within` produces. -/
theorem evm_add_stack_carry3_eq_overflow (a b : EvmWord) :
    let b3 := b.getLimbN 3
    let a3 := a.getLimbN 3
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let psum2 := a.getLimbN 2 + b.getLimbN 2
    let carry2a := if BitVec.ult psum2 (b.getLimbN 2) then (1 : Word) else 0
    let psum1 := a.getLimbN 1 + b.getLimbN 1
    let carry1a := if BitVec.ult psum1 (b.getLimbN 1) then (1 : Word) else 0
    let sum0 := a.getLimbN 0 + b.getLimbN 0
    let carry0 := if BitVec.ult sum0 (b.getLimbN 0) then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    carry3 = if a.toNat + b.toNat ≥ 2 ^ 256 then (1 : Word) else 0 := by
  have h := EvmWord.evm_add_carry3_eq_overflow a b
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h
  exact h

/-- Frame carried through `evm_add`: everything the 4-limb add does not touch —
    `x0`, the return address, the three registers `x2/x9/x10` (generic), the
    owned div-scratch band + `F−160` cell, and the S1 (`N`) / S2 (`r`) / S3 (`m`)
    park cells. `evm_add` owns `x5/x6/x7/x11/x12` and the `F+0..56` work window. -/
def addmodLdAddFrame (F raVal x2v x9v x10v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
  (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
  ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
  ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
  ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
  ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
  ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
  ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
  ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)

theorem addmodLdAddFrame_pcFree (F raVal x2v x9v x10v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word) :
    (addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3).pcFree := by
  unfold addmodLdAddFrame divScratchOwnCallNoX1 divScratchOwn
  pcFree

/-- Link 2 of Ld: the verified 4-limb `evm_add`, framed, over `C`. From the
    two pre-reduced operands `m` (at F+0..24) and `rMod` (at F+32..56), forms
    the 257-bit sum `m + rMod` at the new top (`x12 = F+32`), leaving the add
    carry-out in `x5` (folded to the overflow bit) and the dead limb-3 outputs
    in `x7/x6/x11`. The carry3-chain→overflow fold is done here so downstream
    reads a clean `x5`; `x6/x7/x11` stay concrete (pass1take treats them as
    dead inputs). -/
theorem ld_evm_add_in_C
    (bt F raVal x2v x9v x10v v5 v6 v7 v11 : Word) (m rMod : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    let b0 := rMod.getLimbN 0; let a0 := m.getLimbN 0
    let b1 := rMod.getLimbN 1; let a1 := m.getLimbN 1
    let b2 := rMod.getLimbN 2; let a2 := m.getLimbN 2
    let b3 := rMod.getLimbN 3; let a3 := m.getLimbN 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    cpsTripleWithin 30 (bt + 492) ((bt + 492) + 120)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        evmWordIs F m ** evmWordIs (F + 32) rMod) **
       addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
      (((.x12 ↦ᵣ (F + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
        (.x5 ↦ᵣ (if m.toNat + rMod.toNat ≥ 2 ^ 256 then (1 : Word) else 0)) **
        (.x11 ↦ᵣ carry3a) **
        evmWordIs F m ** evmWordIs (F + 32) (m + rMod)) **
       addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3) := by
  intro b0 a0 b1 a1 b2 a2 b3 a3 sum0 carry0 psum1 carry1a result1 carry1b carry1
    psum2 carry2a result2 carry2b carry2 psum3 carry3a result3 carry3b
  have hadd := evm_add_stack_spec_within F (bt + 492) m rMod v7 v6 v5 v11
  simp only at hadd
  have hframed := cpsTripleWithin_frameR
    (addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
    (addmodLdAddFrame_pcFree F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
    hadd
  have hC := carry_block_in_C
    (blockCode := evm_add_code (bt + 492))
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun a i h => evm_addmod_total_program_code_carry_evm_add_sub a i h)
    hframed
  have hcarry := evm_add_stack_carry3_eq_overflow m rMod
  simp only at hcarry
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hC
  · simp only [addmodLdAddFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp
  · simp only [addmodLdAddFrame, sepConj_assoc'] at hq ⊢
    rw [hcarry] at hq
    xperm_hyp hq

-- ============================================================================
-- Ld links 3-4: cond-subtract (pass1take_clean 612→712, pass2_owned 712→832)
-- lifted onto C via the CarryLdCondSub sub-region subsumptions.
-- ============================================================================

/-- Link 3 of Ld: `pass1take_clean` over `C`. -/
theorem ld_pass1take_in_C
    (bt G carry x6Old x7Old x10Old x11Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 mask : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hmask : mask = (0 : Word) -
      ((carry + signExtend12 (0 : BitVec 12)) |||
       (((if BitVec.ult s3 n3 then (1 : Word) else 0) |||
          (if BitVec.ult (s3 - n3)
            ((if BitVec.ult s2 n2 then (1 : Word) else 0) |||
             (if BitVec.ult (s2 - n2)
               ((if BitVec.ult s1 n1 then (1 : Word) else 0) |||
                (if BitVec.ult (s1 - n1)
                  (if BitVec.ult s0 n0 then (1 : Word) else 0)
                  then (1 : Word) else 0))
               then (1 : Word) else 0))
            then (1 : Word) else 0))
         ^^^ signExtend12 (1 : BitVec 12)))) :
    cpsTripleWithin 25 (bt + 612) ((bt + 612) + 100)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((.x12 ↦ᵣ G) ** (.x5 ↦ᵣ carry) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((G + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((G + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((G + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((G + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((G + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((G + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((G + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((G + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ G) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x10 ↦ᵣ (carry + signExtend12 (0 : BitVec 12))) ** (.x11 ↦ᵣ mask) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((G + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((G + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((G + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((G + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((G + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((G + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((G + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((G + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) :=
  carry_block_in_C
    (fun a i h => evm_addmod_total_program_code_cond_sub_pass1_sub a i h)
    (evm_addmod_cond_sub_pass1take_clean (bt + 612) G carry x6Old x7Old
      x10Old x11Old s0 s1 s2 s3 n0 n1 n2 n3 mask hmask)

/-- Link 4 of Ld: `pass2_owned` over `C`. -/
theorem ld_pass2_in_C
    (bt G maskIn x10Old : Word)
    (s0 s1 s2 s3 n0 n1 n2 n3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    let mm0 := n0 &&& maskIn
    let c0 := if BitVec.ult s0 mm0 then (1 : Word) else 0
    let r0 := s0 - mm0
    let mm1 := n1 &&& maskIn
    let f1 := if BitVec.ult s1 mm1 then (1 : Word) else 0
    let e1 := s1 - mm1
    let g1 := if BitVec.ult e1 c0 then (1 : Word) else 0
    let r1 := e1 - c0
    let c1 := f1 ||| g1
    let mm2 := n2 &&& maskIn
    let f2 := if BitVec.ult s2 mm2 then (1 : Word) else 0
    let e2 := s2 - mm2
    let g2 := if BitVec.ult e2 c1 then (1 : Word) else 0
    let r2 := e2 - c1
    let c2 := f2 ||| g2
    let mm3 := n3 &&& maskIn
    let r3 := (s3 - mm3) - c2
    cpsTripleWithin 30 (bt + 712) ((bt + 712) + 120)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x12 ↦ᵣ G) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ maskIn) **
       ((G + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
       ((G + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
       ((G + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
       ((G + signExtend12 (24 : BitVec 12)) ↦ₘ s3) **
       ((G + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((G + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((G + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((G + signExtend12 (3896 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ G) ** (.x5 ↦ᵣ f2) ** (.x6 ↦ᵣ r3) ** (.x7 ↦ᵣ mm3) **
       (.x10 ↦ᵣ c2) ** (.x11 ↦ᵣ maskIn) **
       ((G + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((G + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((G + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((G + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((G + signExtend12 (3872 : BitVec 12)) ↦ₘ n0) **
       ((G + signExtend12 (3880 : BitVec 12)) ↦ₘ n1) **
       ((G + signExtend12 (3888 : BitVec 12)) ↦ₘ n2) **
       ((G + signExtend12 (3896 : BitVec 12)) ↦ₘ n3)) := by
  intro mm0 c0 r0 mm1 f1 e1 g1 r1 c1 mm2 f2 e2 g2 r2 c2 mm3 r3
  exact carry_block_in_C
    (fun a i h => evm_addmod_total_program_code_cond_sub_pass2_sub a i h)
    (evm_addmod_cond_sub_pass2_owned (bt + 712) G maskIn x10Old
      s0 s1 s2 s3 n0 n1 n2 n3)

end EvmAsm.Evm64.AddMod.Compose
