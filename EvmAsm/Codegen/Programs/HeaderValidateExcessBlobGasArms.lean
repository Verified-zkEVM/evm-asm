import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Rv64.SAsm.FramePort

/-! # K70's price-free arms at the caller's argument shape (#13135)

The status-0 under-target witness (#12849) pinned every argument to zero
— in particular `a3 = 0`, which no real caller satisfies
(`validate_header` passes `a3 = parentStructPtr + 96`).  This file
proves the arms that never touch the price path — and therefore never
dereference `a3` — at FULLY PARAMETRIC arguments:

* **overflow** — `parent.excess + parent.blob_gas_used` wraps: status 1;
* **under-target** — no wrap, total below the Amsterdam target:
  status 0 when `this.excess = 0`, status 2 otherwise (the mismatch arm);
* **boundary-guard** — no wrap, total at/above target, and
  `parent.excess ≥ 2 073 394 371` (the measured price-result boundary):
  expected `total − target`; status 0 on match, 2 on mismatch.

The still-open price arms (the `amsterdam_blob_gas_price_u256` route)
remain gated on `priceContract` (#12851). -/

namespace EvmAsm.Codegen.ValidateHeaderGasCorrespondence

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

/-- The Amsterdam blob target, in the exact form the machine's
    `LUI x5, 448` materializes. -/
def k70Target : Word := ((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64

theorem k70Target_eq : k70Target = (1835008 : Word) := by decide

/-- The full-routine image every arm is stated over. -/
def k70Cr : CodeReq := CodeReq.ofProg ExcessK headerValidateExcessBlobGas_prog

/-- The frame-register exit values shared by the price-free arms: the
    argument copies land in `s0..s3`, the total in `s4`, and `s5` holds
    the arm's expected-excess value (untouched on the overflow arm). -/
def k70ArmVals (ret a0 a1 a2 a3 x21v : Word) : Reg → Word :=
  fun r =>
    if r = .x1 then ret else if r = .x8 then a0 else if r = .x9 then a1
    else if r = .x18 then a2 else if r = .x19 then a3
    else if r = .x20 then a2 + a1 else if r = .x21 then x21v else 0

/-! ## The shared argument prefix (K+32 .. K+52) -/

set_option maxRecDepth 8000 in
theorem k70A_prefix_spec (a0 a1 a2 a3 v8 v9 v18 v19 v20 : Word) :
    cpsTripleWithin 5 (ExcessK + 32) (ExcessK + 52) k70Cr
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3)) := by
  have h8 := mv_spec_gen_within .x8 .x10 a0 v8 (ExcessK + 32) (by decide)
  have h9 := mv_spec_gen_within .x9 .x11 a1 v9 (ExcessK + 36) (by decide)
  have h18 := mv_spec_gen_within .x18 .x12 a2 v18 (ExcessK + 40) (by decide)
  have h19 := mv_spec_gen_within .x19 .x13 a3 v19 (ExcessK + 44) (by decide)
  have h20 := add_spec_gen_within .x20 .x18 .x9 a2 a1 v20
    (ExcessK + 48) (by decide)
  have h8' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) h8
  have h9' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) h9
  have h18' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) h18
  have h19' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) h19
  have h20' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) h20
  have h8F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) h8'
  have h9F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) h9'
  have h18F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x13 ↦ᵣ a3))
    (by pcf) h18'
  have h19F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2))
    (by pcf) h19'
  have h20F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x19 ↦ᵣ a3) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) h20'
  have h12 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h8F h9F
  have h123 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h12 h18F
  have h1234 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h123 h19F
  have h12345 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h1234 h20F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) h12345

/-! ## The overflow arm: `parentTotal` wrapped → status 1 -/

set_option maxRecDepth 8000 in
theorem k70_overflow_mid_spec (a0 a1 a2 a3 v8 v9 v18 v19 v20 : Word)
    (hwrap : BitVec.ult (a2 + a1) a2 = true) :
    cpsTripleWithin 8 (ExcessK + 32) (ExcessK + 260) k70Cr
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) **
        (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3)) := by
  have hpre := k70A_prefix_spec a0 a1 a2 a3 v8 v9 v18 v19 v20
  -- BLTU x20, x18 TAKEN → K+248
  have hbr := bltu_spec_gen_within .x20 .x18 (196 : BitVec 13)
    (a2 + a1) a2 (ExcessK + 52)
  rw [show (ExcessK + 52) + signExtend13 (196 : BitVec 13) = ExcessK + 248
      from by decide] at hbr
  have hbr' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem) hbr
  have hBr := cpsBranchWithin_takenStripPure2 hbr' (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQf
    exact ((sepConj_pure_right _).1 hInner).2 hwrap)
  have hBrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x19 ↦ᵣ a3) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hBr
  -- LI x10, 1 at K+248
  have hli := li_spec_gen_within .x10 a0 (1 : Word) (ExcessK + 248)
    (by decide)
  rw [show (ExcessK + 248 : Word) + 4 = ExcessK + 252 from by decide] at hli
  have hli' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) hli
  have hliF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) **
      (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hli'
  -- JAL x0, +8 at K+252 → K+260
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (ExcessK + 252)
  rw [show (ExcessK + 252) + signExtend21 (8 : BitVec 21) = ExcessK + 260
      from by decide] at hjal
  have hjal' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) **
      (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
      (.x13 ↦ᵣ a3))
    (by pcf) hjal'
  have s1 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hpre hBrF
  have s2 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s1 hliF
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_emp_left']; xperm_hyp hp) s2 hjalF
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) s3
  have hq1 := hq
  rw [sepConj_emp_left'] at hq1
  xperm_hyp hq1

set_option maxRecDepth 8000 in
/-- ⭐ **K70 overflow arm, whole-routine, at the caller's argument
    shape**: `parent.excess + parent.blob_gas_used` wraps, so the
    routine returns status 1 — for ANY `a3`. -/
theorem header_validate_excess_blob_gas_overflow_spec_within
    (sp0 ret a0 a1 a2 a3 : Word) (vals : Reg → Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hwrap : BitVec.ult (a2 + a1) a2 = true) :
    cpsTripleWithin 25 ExcessK ret k70Cr
      ((.x1 ↦ᵣ ret) **
        excessEntryRest sp0 vals a0 a1 a2 a3 empAssertion)
      (excessCalleePost sp0 vals (1 : Word) ret empAssertion) := by
  have hmid := k70_overflow_mid_spec a0 a1 a2 a3
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
    hwrap
  have hmidF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x21 ↦ᵣ vals .x21) **
      ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-64 : BitVec 12))) **
      frameSlotsSaved excessFrame (sp0 + signExtend12 (-64 : BitVec 12))
        (excessFrameVals ret vals) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hmid
  have habi := abiFrame_spec
    (base := ExcessK) (sp0 := sp0) (ret := ret)
    (negImm := (-64 : BitVec 12)) (posImm := (64 : BitVec 12))
    (frame := excessFrame) (raOfs := (0 : BitVec 12))
    (sregs := excessSavedFrame)
    (vals := excessFrameVals ret vals)
    (vals' := k70ArmVals ret a0 a1 a2 a3 (vals .x21))
    (body := EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec.k70Body) (bodySteps := 8)
    (callerPre := (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
      (.x13 ↦ᵣ a3) ** regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
      (.x0 ↦ᵣ (0 : Word)))
    (callerPost := (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) **
      (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
      regOwns [.x5, .x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
    (cr := k70Cr)
    (by rfl)
    (by decide)
    (by decide)
    (by decide)
    (by simp [excessFrameVals])
    halign
    (sext_frameRestore _ _ _ (by decide))
    (by pcf)
    (by pcf)
    (by intro a i h; exact h)
    (by
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hmidF
      · simp [excessFrame, regsAt, excessFrameVals] at hp ⊢
        simp only [sepConj_emp_right'] at hp ⊢
        xperm_hyp hp
      · simp [excessFrame, regsAt, excessFrameVals, k70ArmVals] at hq ⊢
        simp only [sepConj_emp_right'] at hq ⊢
        xperm_hyp hq)
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) habi
  · simp [excessEntryRest, excessFrame, excessSavedFrame, regsAt,
      frameSlotsOwn, excessFrameVals] at hp ⊢
    simp only [sepConj_emp_right'] at hp ⊢
    xperm_hyp hp
  · -- release the three argument registers to ownership, then reshape
    have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono (regIs_implies_regOwn (r := .x11))
          (sepConj_mono (regIs_implies_regOwn (r := .x12))
            (sepConj_mono (regIs_implies_regOwn (r := .x13))
              (fun _ hx => hx))))))) h hq
    simp [excessCalleePost, excessFrame, excessSavedFrame, excessFrameVals,
      regsAt, sepConj_emp_right'] at hq2 ⊢
    xperm_hyp hq2

private theorem cps_fuel_mono' {n m : Nat} {entry exit_ : Word}
    {cr : CodeReq} {P Q : Assertion} (hnm : n ≤ m)
    (h : cpsTripleWithin n entry exit_ cr P Q) :
    cpsTripleWithin m entry exit_ cr P Q := by
  intro R hR s hcr hp hpc
  obtain ⟨k, hk, rest⟩ := h R hR s hcr hp hpc
  exact ⟨k, Nat.le_trans hk hnm, rest⟩

/-! ## The under-target arm: total below target → status `if a0 = 0 then 0 else 2` -/

set_option maxRecDepth 8000 in
theorem k70_under_mid_spec (a0 a1 a2 a3 v8 v9 v18 v19 v20 v21 v5 : Word)
    (hnowrap : ¬ BitVec.ult (a2 + a1) a2 = true)
    (hunder : BitVec.ult (a2 + a1) k70Target = true) :
    cpsTripleWithin 12 (ExcessK + 32) (ExcessK + 260) k70Cr
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ (if a0 = 0 then (0 : Word) else 2)) ** (.x11 ↦ᵣ a1) **
        (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3)) := by
  have hpre := k70A_prefix_spec a0 a1 a2 a3 v8 v9 v18 v19 v20
  have hpreF := cpsTripleWithin_frameR ((.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5))
    (by pcf) hpre
  -- BLTU x20, x18 NOT taken
  have hbr1 := bltu_spec_gen_within .x20 .x18 (196 : BitVec 13)
    (a2 + a1) a2 (ExcessK + 52)
  rw [show (ExcessK + 52 : Word) + 4 = ExcessK + 56 from by decide] at hbr1
  have hbr1' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem) hbr1
  have hBr1 := cpsBranchWithin_ntakenStripPure2 hbr1' (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQt
    exact hnowrap (((sepConj_pure_right _).1 hInner).2))
  have hBr1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x19 ↦ᵣ a3) ** (.x21 ↦ᵣ v21) **
      (.x5 ↦ᵣ v5) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hBr1
  -- LUI x5, 448
  have hlui := lui_spec_gen_within .x5 v5 (448 : BitVec 20)
    (ExcessK + 56) (by decide)
  rw [show (ExcessK + 56 : Word) + 4 = ExcessK + 60 from by decide,
    show (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
      = k70Target from rfl] at hlui
  have hlui' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) hlui
  have hluiF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hlui'
  -- BLTU x20, x5 TAKEN → K+232
  have hbr2 := bltu_spec_gen_within .x20 .x5 (172 : BitVec 13)
    (a2 + a1) k70Target
    (ExcessK + 60)
  rw [show (ExcessK + 60) + signExtend13 (172 : BitVec 13) = ExcessK + 232
      from by decide] at hbr2
  have hbr2' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem) hbr2
  have hBr2 := cpsBranchWithin_takenStripPure2 hbr2' (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQf
    exact ((sepConj_pure_right _).1 hInner).2 hunder)
  have hBr2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hBr2
  -- LI x21, 0 at K+232
  have hli21 := li_spec_gen_within .x21 v21 (0 : Word) (ExcessK + 232)
    (by decide)
  rw [show (ExcessK + 232 : Word) + 4 = ExcessK + 236 from by decide] at hli21
  have hli21' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) hli21
  have hli21F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) **
      (.x5 ↦ᵣ k70Target) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hli21'
  have s1 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hpreF hBr1F
  have s2 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s1 hluiF
  have s3 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s2 hBr2F
  have s4 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s3 hli21F
  -- BNE x8, x21 splits on a0 = 0
  by_cases hz : a0 = 0
  case pos =>
    subst hz
    have hbne := bne_spec_gen_within .x8 .x21 (20 : BitVec 13)
      (0 : Word) (0 : Word) (ExcessK + 236)
    rw [show (ExcessK + 236 : Word) + 4 = ExcessK + 240 from by decide]
      at hbne
    have hbne' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem)
      hbne
    have hBne := cpsBranchWithin_ntakenStripPure2 hbne' (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hInner⟩ := hQt
      exact (((sepConj_pure_right _).1 hInner).2) rfl)
    have hBneF := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) **
        (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3))
      (by pcf) hBne
    have hli10 := li_spec_gen_within .x10 (0 : Word) (0 : Word)
      (ExcessK + 240) (by decide)
    rw [show (ExcessK + 240 : Word) + 4 = ExcessK + 244 from by decide]
      at hli10
    have hli10' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
      hli10
    have hli10F := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ k70Target) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      (by pcf) hli10'
    have hjal := jal_x0_spec_gen_within (16 : BitVec 21) (ExcessK + 244)
    rw [show (ExcessK + 244) + signExtend21 (16 : BitVec 21) = ExcessK + 260
        from by decide] at hjal
    have hjal' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
      hjal
    have hjalF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3))
      (by pcf) hjal'
    have s5 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s4 hBneF
    have s6 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s5 hli10F
    have s7 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by rw [sepConj_emp_left']; xperm_hyp hp) s6 hjalF
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ?_) s7
    have hq1 := hq
    rw [sepConj_emp_left'] at hq1
    rw [if_pos rfl]
    xperm_hyp hq1
  case neg =>
    have hbne := bne_spec_gen_within .x8 .x21 (20 : BitVec 13)
      a0 (0 : Word) (ExcessK + 236)
    rw [show (ExcessK + 236) + signExtend13 (20 : BitVec 13) = ExcessK + 256
        from by decide] at hbne
    have hbne' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem)
      hbne
    have hBne := cpsBranchWithin_takenStripPure2 hbne' (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hInner⟩ := hQf
      exact hz (((sepConj_pure_right _).1 hInner).2))
    have hBneF := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) **
        (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      (by pcf) hBne
    have hli10 := li_spec_gen_within .x10 a0 (2 : Word)
      (ExcessK + 256) (by decide)
    rw [show (ExcessK + 256 : Word) + 4 = ExcessK + 260 from by decide]
      at hli10
    have hli10' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
      hli10
    have hli10F := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ k70Target) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      (by pcf) hli10'
    have s5 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s4 hBneF
    have s6 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s5 hli10F
    refine cps_fuel_mono'
      (by norm_num : (5 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) ≤ 12)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => ?_) s6)
    rw [if_neg hz]
    xperm_hyp hq


set_option maxRecDepth 8000 in
/-- ⭐ **K70 under-target arm, whole-routine, at the caller's argument
    shape** — for ANY `a3`. -/
theorem header_validate_excess_blob_gas_under_target_spec_within
    (sp0 ret a0 a1 a2 a3 : Word) (vals : Reg → Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hnowrap : ¬ BitVec.ult (a2 + a1) a2 = true)
    (hunder : BitVec.ult (a2 + a1) k70Target = true) :
    cpsTripleWithin 29 ExcessK ret k70Cr
      ((.x1 ↦ᵣ ret) **
        excessEntryRest sp0 vals a0 a1 a2 a3 empAssertion)
      (excessCalleePost sp0 vals (if a0 = 0 then (0 : Word) else 2) ret empAssertion) := by
  have hcore : ∀ v5 : Word, cpsTripleWithin 29 ExcessK ret k70Cr
      (((.x1 ↦ᵣ ret) **
        ((.x2 : Reg) ↦ᵣ sp0) **
        frameSlotsOwn excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        regsAt excessSavedFrame vals **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x5 : Reg) ↦ᵣ v5))
      (excessCalleePost sp0 vals (if a0 = 0 then (0 : Word) else 2) ret empAssertion) := by
    intro v5
    have hmid := k70_under_mid_spec a0 a1 a2 a3
      (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
      (vals .x21) v5 hnowrap hunder
    have hmidF := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-64 : BitVec 12))) **
        frameSlotsSaved excessFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (excessFrameVals ret vals) **
        regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hmid
    have habi := abiFrame_spec
      (base := ExcessK) (sp0 := sp0) (ret := ret)
      (negImm := (-64 : BitVec 12)) (posImm := (64 : BitVec 12))
      (frame := excessFrame) (raOfs := (0 : BitVec 12))
      (sregs := excessSavedFrame)
      (vals := excessFrameVals ret vals)
      (vals' := k70ArmVals ret a0 a1 a2 a3 (0 : Word))
      (body := EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec.k70Body)
      (bodySteps := 12)
      (callerPre := (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) **
        (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
      (callerPost := (.x5 ↦ᵣ k70Target) ** (.x10 ↦ᵣ (if a0 = 0 then (0 : Word) else 2)) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
      (cr := k70Cr)
      (by rfl)
      (by decide)
      (by decide)
      (by decide)
      (by simp [excessFrameVals])
      halign
      (sext_frameRestore _ _ _ (by decide))
      (by pcf)
      (by pcf)
      (by intro a i h; exact h)
      (by
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hmidF
        · simp [excessFrame, regsAt, excessFrameVals] at hp ⊢
          simp only [sepConj_emp_right'] at hp ⊢
          xperm_hyp hp
        · simp [excessFrame, regsAt, excessFrameVals, k70ArmVals] at hq ⊢
          simp only [sepConj_emp_right'] at hq ⊢
          xperm_hyp hq)
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) habi
    · simp [excessFrame, excessSavedFrame, regsAt, excessFrameVals] at hp ⊢
      simp only [sepConj_emp_right'] at hp ⊢
      xperm_hyp hp
    · have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (regIs_implies_regOwn (r := .x5))
          (sepConj_mono_right
            (sepConj_mono (regIs_implies_regOwn (r := .x11))
              (sepConj_mono (regIs_implies_regOwn (r := .x12))
                (sepConj_mono (regIs_implies_regOwn (r := .x13))
                  (fun _ hx => hx)))))))) h hq
      simp [excessCalleePost, excessFrame, excessSavedFrame, excessFrameVals,
        regsAt, sepConj_emp_right'] at hq2 ⊢
      xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x1 ↦ᵣ ret) **
        ((.x2 : Reg) ↦ᵣ sp0) **
        frameSlotsOwn excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        regsAt excessSavedFrame vals **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] **
        (.x0 ↦ᵣ (0 : Word)))
      hcore)
  simp [excessEntryRest, excessFrame, excessSavedFrame, regsAt,
    frameSlotsOwn, regOwns_cons, regOwns_nil] at hp ⊢
  simp only [sepConj_emp_right'] at hp ⊢
  xperm_hyp hp

/-! ## The boundary-guard arm: `parent.excess` at/above the measured
    price-result boundary → the non-high branch directly -/

/-- The measured price-result boundary, in the exact form
    `LUI x5, 506200; ADDIW x5, x5, -829` materializes. -/
def k70Bound : Word :=
  (((((506200 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64).truncate 32
      + (signExtend12 (-829 : BitVec 12)).truncate 32 : BitVec 32).signExtend 64)

theorem k70Bound_eq : k70Bound = (2073394371 : Word) := by decide

set_option maxRecDepth 8000 in
theorem k70_boundary_mid_spec (a0 a1 a2 a3 v8 v9 v18 v19 v20 v21 v5 : Word)
    (hnowrap : ¬ BitVec.ult (a2 + a1) a2 = true)
    (hnotunder : ¬ BitVec.ult (a2 + a1) k70Target = true)
    (hge : ¬ BitVec.ult a2 k70Bound = true) :
    cpsTripleWithin 17 (ExcessK + 32) (ExcessK + 260) k70Cr
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ ((a2 + a1) - k70Target)) **
        (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ (if a0 = (a2 + a1) - k70Target then (0 : Word) else 2)) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3)) := by
  have hpre := k70A_prefix_spec a0 a1 a2 a3 v8 v9 v18 v19 v20
  have hpreF := cpsTripleWithin_frameR ((.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5))
    (by pcf) hpre
  -- BLTU x20, x18 NOT taken
  have hbr1 := bltu_spec_gen_within .x20 .x18 (196 : BitVec 13)
    (a2 + a1) a2 (ExcessK + 52)
  rw [show (ExcessK + 52 : Word) + 4 = ExcessK + 56 from by decide] at hbr1
  have hbr1' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem) hbr1
  have hBr1 := cpsBranchWithin_ntakenStripPure2 hbr1' (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQt
    exact hnowrap (((sepConj_pure_right _).1 hInner).2))
  have hBr1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x19 ↦ᵣ a3) ** (.x21 ↦ᵣ v21) **
      (.x5 ↦ᵣ v5) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hBr1
  -- LUI x5, 448
  have hlui := lui_spec_gen_within .x5 v5 (448 : BitVec 20)
    (ExcessK + 56) (by decide)
  rw [show (ExcessK + 56 : Word) + 4 = ExcessK + 60 from by decide,
    show (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
      = k70Target from rfl] at hlui
  have hlui' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) hlui
  have hluiF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hlui'
  -- BLTU x20, x5 NOT taken
  have hbr2 := bltu_spec_gen_within .x20 .x5 (172 : BitVec 13)
    (a2 + a1) k70Target (ExcessK + 60)
  rw [show (ExcessK + 60 : Word) + 4 = ExcessK + 64 from by decide] at hbr2
  have hbr2' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem) hbr2
  have hBr2 := cpsBranchWithin_ntakenStripPure2 hbr2' (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQt
    exact hnotunder (((sepConj_pure_right _).1 hInner).2))
  have hBr2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hBr2
  -- LUI x5, 506200
  have hlui2 := lui_spec_gen_within .x5 k70Target (506200 : BitVec 20)
    (ExcessK + 64) (by decide)
  rw [show (ExcessK + 64 : Word) + 4 = ExcessK + 68 from by decide] at hlui2
  have hlui2' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
    hlui2
  have hlui2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hlui2'
  -- ADDIW x5, x5, -829
  have haddiw := addiw_spec_gen_same_within .x5
    ((((506200 : BitVec 20).zeroExtend 32 <<< 12)).signExtend 64)
    (-829 : BitVec 12) (ExcessK + 68) (by decide)
  rw [show (ExcessK + 68 : Word) + 4 = ExcessK + 72 from by decide,
    show ((((((506200 : BitVec 20).zeroExtend 32 <<< 12)).signExtend 64).truncate 32
        + (signExtend12 (-829 : BitVec 12)).truncate 32 : BitVec 32).signExtend 64)
      = k70Bound from rfl] at haddiw
  have haddiw' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
    haddiw
  have haddiwF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) haddiw'
  -- BGEU x18, x5 TAKEN → K+220
  have hbge := bgeu_spec_gen_within .x18 .x5 (148 : BitVec 13)
    a2 k70Bound (ExcessK + 72)
  rw [show (ExcessK + 72) + signExtend13 (148 : BitVec 13) = ExcessK + 220
      from by decide] at hbge
  have hbge' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem) hbge
  have hBge := cpsBranchWithin_takenStripPure2 hbge' (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hInner⟩ := hQf
    exact hge (((sepConj_pure_right _).1 hInner).2))
  have hBgeF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hBge
  -- LUI x5, 448 (again) at K+220
  have hlui3 := lui_spec_gen_within .x5 k70Bound (448 : BitVec 20)
    (ExcessK + 220) (by decide)
  rw [show (ExcessK + 220 : Word) + 4 = ExcessK + 224 from by decide,
    show (((448 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
      = k70Target from rfl] at hlui3
  have hlui3' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
    hlui3
  have hlui3F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ v21) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hlui3'
  -- SUB x21, x20, x5 at K+224
  have hsub := sub_spec_gen_within .x21 .x20 .x5
    (a2 + a1) k70Target v21 (ExcessK + 224) (by decide)
  rw [show (ExcessK + 224 : Word) + 4 = ExcessK + 228 from by decide] at hsub
  have hsub' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) hsub
  have hsubF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hsub'
  -- JAL x0, +8 at K+228 → K+236
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (ExcessK + 228)
  rw [show (ExcessK + 228) + signExtend21 (8 : BitVec 21) = ExcessK + 236
      from by decide] at hjal
  have hjal' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem) hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ ((a2 + a1) - k70Target)) **
      (.x5 ↦ᵣ k70Target) **
      (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
    (by pcf) hjal'
  have s1 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hpreF hBr1F
  have s2 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s1 hluiF
  have s3 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s2 hBr2F
  have s4 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s3 hlui2F
  have s5 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s4 haddiwF
  have s6 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s5 hBgeF
  have s7 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s6 hlui3F
  have s8 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s7 hsubF
  have s9 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_emp_left']; xperm_hyp hp) s8 hjalF
  -- BNE x8, x21 splits on a0 = total - target
  by_cases hz : a0 = (a2 + a1) - k70Target
  case pos =>
    have hbne := bne_spec_gen_within .x8 .x21 (20 : BitVec 13)
      a0 ((a2 + a1) - k70Target) (ExcessK + 236)
    rw [show (ExcessK + 236 : Word) + 4 = ExcessK + 240 from by decide]
      at hbne
    have hbne' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem)
      hbne
    have hBne := cpsBranchWithin_ntakenStripPure2 hbne' (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hInner⟩ := hQt
      exact (((sepConj_pure_right _).1 hInner).2) hz)
    have hBneF := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      (by pcf) hBne
    have hli10 := li_spec_gen_within .x10 a0 (0 : Word)
      (ExcessK + 240) (by decide)
    rw [show (ExcessK + 240 : Word) + 4 = ExcessK + 244 from by decide]
      at hli10
    have hli10' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
      hli10
    have hli10F := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ ((a2 + a1) - k70Target)) **
        (.x5 ↦ᵣ k70Target) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      (by pcf) hli10'
    have hjal2 := jal_x0_spec_gen_within (16 : BitVec 21) (ExcessK + 244)
    rw [show (ExcessK + 244) + signExtend21 (16 : BitVec 21) = ExcessK + 260
        from by decide] at hjal2
    have hjal2' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
      hjal2
    have hjal2F := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ ((a2 + a1) - k70Target)) **
        (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3))
      (by pcf) hjal2'
    have s10 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by rw [sepConj_emp_left'] at hp; xperm_hyp hp) s9 hBneF
    have s11 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s10 hli10F
    have s12 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by rw [sepConj_emp_left']; xperm_hyp hp) s11 hjal2F
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ?_) s12
    have hq1 := hq
    rw [sepConj_emp_left'] at hq1
    rw [if_pos hz]
    xperm_hyp hq1
  case neg =>
    have hbne := bne_spec_gen_within .x8 .x21 (20 : BitVec 13)
      a0 ((a2 + a1) - k70Target) (ExcessK + 236)
    rw [show (ExcessK + 236) + signExtend13 (20 : BitVec 13) = ExcessK + 256
        from by decide] at hbne
    have hbne' := cpsBranchWithin_extend_code (cr' := k70Cr) (by code_mem)
      hbne
    have hBne := cpsBranchWithin_takenStripPure2 hbne' (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hInner⟩ := hQf
      exact hz (((sepConj_pure_right _).1 hInner).2))
    have hBneF := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x5 ↦ᵣ k70Target) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      (by pcf) hBne
    have hli10 := li_spec_gen_within .x10 a0 (2 : Word)
      (ExcessK + 256) (by decide)
    rw [show (ExcessK + 256 : Word) + 4 = ExcessK + 260 from by decide]
      at hli10
    have hli10' := cpsTripleWithin_extend_code (cr' := k70Cr) (by code_mem)
      hli10
    have hli10F := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ (a2 + a1)) ** (.x21 ↦ᵣ ((a2 + a1) - k70Target)) **
        (.x5 ↦ᵣ k70Target) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3))
      (by pcf) hli10'
    have s10 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by rw [sepConj_emp_left'] at hp; xperm_hyp hp) s9 hBneF
    have s11 := cpsTripleWithin_seq_perm_same_cr (by xsimp) s10 hli10F
    refine cps_fuel_mono'
      (by norm_num :
        (5 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) ≤ 17)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => ?_) s11)
    rw [if_neg hz]
    xperm_hyp hq

set_option maxRecDepth 8000 in
/-- ⭐ **K70 boundary-guard arm, whole-routine, at the caller's argument
    shape** — for ANY `a3`. -/
theorem header_validate_excess_blob_gas_boundary_spec_within
    (sp0 ret a0 a1 a2 a3 : Word) (vals : Reg → Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hnowrap : ¬ BitVec.ult (a2 + a1) a2 = true)
    (hnotunder : ¬ BitVec.ult (a2 + a1) k70Target = true)
    (hge : ¬ BitVec.ult a2 k70Bound = true) :
    cpsTripleWithin 34 ExcessK ret k70Cr
      ((.x1 ↦ᵣ ret) **
        excessEntryRest sp0 vals a0 a1 a2 a3 empAssertion)
      (excessCalleePost sp0 vals (if a0 = (a2 + a1) - k70Target then (0 : Word) else 2) ret empAssertion) := by
  have hcore : ∀ v5 : Word, cpsTripleWithin 34 ExcessK ret k70Cr
      (((.x1 ↦ᵣ ret) **
        ((.x2 : Reg) ↦ᵣ sp0) **
        frameSlotsOwn excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        regsAt excessSavedFrame vals **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] **
        (.x0 ↦ᵣ (0 : Word))) ** ((.x5 : Reg) ↦ᵣ v5))
      (excessCalleePost sp0 vals (if a0 = (a2 + a1) - k70Target then (0 : Word) else 2) ret empAssertion) := by
    intro v5
    have hmid := k70_boundary_mid_spec a0 a1 a2 a3
      (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
      (vals .x21) v5 hnowrap hnotunder hge
    have hmidF := cpsTripleWithin_frameR
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-64 : BitVec 12))) **
        frameSlotsSaved excessFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (excessFrameVals ret vals) **
        regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hmid
    have habi := abiFrame_spec
      (base := ExcessK) (sp0 := sp0) (ret := ret)
      (negImm := (-64 : BitVec 12)) (posImm := (64 : BitVec 12))
      (frame := excessFrame) (raOfs := (0 : BitVec 12))
      (sregs := excessSavedFrame)
      (vals := excessFrameVals ret vals)
      (vals' := k70ArmVals ret a0 a1 a2 a3 ((a2 + a1) - k70Target))
      (body := EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec.k70Body)
      (bodySteps := 17)
      (callerPre := (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) **
        (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
      (callerPost := (.x5 ↦ᵣ k70Target) ** (.x10 ↦ᵣ (if a0 = (a2 + a1) - k70Target then (0 : Word) else 2)) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] ** (.x0 ↦ᵣ (0 : Word)))
      (cr := k70Cr)
      (by rfl)
      (by decide)
      (by decide)
      (by decide)
      (by simp [excessFrameVals])
      halign
      (sext_frameRestore _ _ _ (by decide))
      (by pcf)
      (by pcf)
      (by intro a i h; exact h)
      (by
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hmidF
        · simp [excessFrame, regsAt, excessFrameVals] at hp ⊢
          simp only [sepConj_emp_right'] at hp ⊢
          xperm_hyp hp
        · simp [excessFrame, regsAt, excessFrameVals, k70ArmVals] at hq ⊢
          simp only [sepConj_emp_right'] at hq ⊢
          xperm_hyp hq)
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) habi
    · simp [excessFrame, excessSavedFrame, regsAt, excessFrameVals] at hp ⊢
      simp only [sepConj_emp_right'] at hp ⊢
      xperm_hyp hp
    · have hq2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (regIs_implies_regOwn (r := .x5))
          (sepConj_mono_right
            (sepConj_mono (regIs_implies_regOwn (r := .x11))
              (sepConj_mono (regIs_implies_regOwn (r := .x12))
                (sepConj_mono (regIs_implies_regOwn (r := .x13))
                  (fun _ hx => hx)))))))) h hq
      simp [excessCalleePost, excessFrame, excessSavedFrame, excessFrameVals,
        regsAt, sepConj_emp_right'] at hq2 ⊢
      xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x1 ↦ᵣ ret) **
        ((.x2 : Reg) ↦ᵣ sp0) **
        frameSlotsOwn excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        regsAt excessSavedFrame vals **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        regOwns [.x6, .x28, .x29, .x30, .x31] **
        (.x0 ↦ᵣ (0 : Word)))
      hcore)
  simp [excessEntryRest, excessFrame, excessSavedFrame, regsAt,
    frameSlotsOwn, regOwns_cons, regOwns_nil] at hp ⊢
  simp only [sepConj_emp_right'] at hp ⊢
  xperm_hyp hp

/-! ## Non-vacuity: each arm's gate is inhabited, and its boundary bites -/

-- overflow: max excess plus one blob of used gas wraps
example : BitVec.ult ((0xFFFFFFFFFFFFFFFF : Word) + 1)
    (0xFFFFFFFFFFFFFFFF : Word) = true := by decide
-- under-target admits both statuses (the mismatch sub-arm is real)
example : BitVec.ult ((0 : Word) + 0) k70Target = true := by decide
example : (1 : Word) ≠ 0 := by decide
-- boundary-guard: the measured bound admits, its predecessor refutes
example : ¬ BitVec.ult (2073394371 : Word) k70Bound = true := by decide
example : BitVec.ult (2073394370 : Word) k70Bound = true := by decide

end EvmAsm.Codegen.ValidateHeaderGasCorrespondence
