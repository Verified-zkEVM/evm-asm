/-
  EvmAsm.Evm64.AddMod.Compose.CarryLc

  Phase-3 M3d for total ADDMOD (issue #9704): the third carry-branch sub-chain.

  Lc runs from `addmodCarryAfterCall2` (byte 356) through the third MOD call:

    stage_low_args (356,24) ;;
    [adapter call3 : JAL@452 → evm_mod_callable_v5 → ret@456] ;;
    call_mod_restore (456,1)

  ending at byte 460 with `EvmWord.mod r N` (the reduced low sum `r mod N`) at
  F+32..56 and the carry contribution `pow256ModN N` parked at S3 (F−256).

  Direct mirror of `CarryLb`. The one structural difference: `stage_low_args`
  reads/writes the S2 (=r) and S3 (=m) park cells, so those live inside the
  block spec (not the framed tail); the tail carries only the registers, the
  div-scratch band, and the `F−160` cell.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryLb

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

end EvmAsm.Evm64.AddMod.Compose
