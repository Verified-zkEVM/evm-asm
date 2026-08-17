/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeBranches

  K73's post-division arithmetic branches.  The shared setup, multiply,
  status, divider-pair, zero-test, and tail adapters live in
  `HeaderBaseFeeWholeSpec`; this module keeps the remaining branch
  compositions and the eventual whole-routine assembly below the per-file
  size cap.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256BeFlat
open EvmAsm.Codegen.U256AddBeBInPlaceSAsm
open EvmAsm.Codegen.U256AddBeSAsm
private theorem k73_div_quot_length
    (a orig : List (BitVec 8)) (b : Word) (hlen : orig.length = 32) :
    (u256DivU64BeQuotBytes a orig b).length = 32 := by
  have h : ∀ k : Nat, (divState a orig b k).1.length = orig.length := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [divState, ih]
  simpa [u256DivU64BeQuotBytes, hlen] using h 32
/-! The replacement arm after the zero test.  The caller's x10--x12 -/
theorem k73_increase_replace_route_spec_within
    (ptr : Word) (q2 : List (BitVec 8)) (F : Assertion)
    (hrw : RwRegion.wf ⟨ptr, 32⟩) (hlen : q2.length = 32)
    (hF : F.pcFree) :
    cpsTripleWithin
      (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1)
      (K73 + 140) (K73 + 172) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        regOwns exposedRegs **
        bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) := by
  let Rest : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
      ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    pcf
    exact hF
  have hliAny : ∀ old10, cpsTripleWithin 1 (K73 + 140) (K73 + 144) wholeCode
      (Rest ** ((.x10 : Reg) ↦ᵣ old10))
      (Rest ** ((.x10 : Reg) ↦ᵣ (1 : Word))) := by
    intro old10
    have hli := li_spec_gen_within .x10 old10 (1 : Word) (K73 + 140)
      (by decide)
    have hliC := cpsTripleWithin_extend_code
      (k73_whole_mem 35 _ (K73 + 140) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hli
    have hliF := cpsTripleWithin_frameR Rest hRest hliC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hli := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x10) (P := Rest) (Q := Rest ** ((.x10 : Reg) ↦ᵣ (1 : Word))) hliAny
  let RestMv : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
      ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F
  have hRestMv : RestMv.pcFree := by
    dsimp [RestMv]
    pcf
    exact hF
  let RestMvFrame : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr q2 ** F
  have hRestMvFrame : RestMvFrame.pcFree := by
    dsimp [RestMvFrame]
    pcf
    exact hF
  have hmv := mv_spec_gen_within .x11 .x9 ptr (8 : Word) (K73 + 144)
    (by decide)
  have hmvC := cpsTripleWithin_extend_code
    (k73_whole_mem 36 _ (K73 + 144) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv
  have hmvF := cpsTripleWithin_frameR RestMvFrame hRestMvFrame hmvC
  have hmv' : cpsTripleWithin 1 (K73 + 144) (K73 + 148) wholeCode
      (RestMv ** ((.x11 : Reg) ↦ᵣ (8 : Word)))
      (RestMv ** ((.x11 : Reg) ↦ᵣ ptr)) := by
    simpa only [RestMv, RestMvFrame, sepConj_assoc', sepConj_comm',
      sepConj_left_comm'] using hmvF
  have hli' : cpsTripleWithin 1 (K73 + 140) (K73 + 144) wholeCode
      (Rest ** regOwn .x10)
      (RestMv ** ((.x11 : Reg) ↦ᵣ (8 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp [Rest, RestMv] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        dsimp [Rest, RestMv] at hq ⊢
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq) hli
  have hsetup := cpsTripleWithin_seq_same_cr hli' hmv'
  let Pcall : Assertion :=
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ ptr) **
      regOwns fromU64Scratch ** bytesRegion ptr q2
  let Qcall : Assertion :=
    regOwns exposedRegs **
      bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word))
  have hPcall : Pcall.pcFree := by
    dsimp [Pcall]
    pcf
  have htarget :
      (K73 + 148) + signExtend21
        (jalOff GuestAddrs.u256_from_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 148)) =
        (GuestAddrs.u256_from_u64_be : Word) := by
    change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 148 + _ = BitVec.ofNat 64 GuestAddrs.u256_from_u64_be
    exact jalOff_correct_add GuestAddrs.u256_from_u64_be
      GuestAddrs.eip1559_calc_base_fee_per_gas 148
      (by decide) (by decide) (by decide) (by decide)
  have hmem : ∀ a i, CodeReq.singleton (K73 + 148)
      (.JAL .x1 (jalOff GuestAddrs.u256_from_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 148))) a = some i →
      wholeCode a = some i := by
    intro a i hi
    exact k73_whole_mem 37 _ (K73 + 148) (by decide)
      (by rw [k73_length]; decide) (by rfl) a i hi
  have hcallee := u256FromU64BeFlat_spec
    (K73 + 152) (1 : Word) ptr q2 hrw hlen (by decide)
  have hcalleeC := cpsTripleWithin_extend_code fromU64_whole_mono hcallee
  have hcall := callWithin_spec
    (cr := wholeCode) (P := Pcall) (Q := Qcall)
    (K73 + 148) (GuestAddrs.u256_from_u64_be : Word) (K73 + 136)
    (jalOff GuestAddrs.u256_from_u64_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 148))
    ((U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)
    htarget hmem hPcall hcalleeC
  let Frame : Assertion := ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x9 : Reg) ↦ᵣ ptr) ** F
  have hFrame : Frame.pcFree := by
    dsimp [Frame]
    pcf
    exact hF
  have hcallF := cpsTripleWithin_frameR Frame hFrame hcall
  have hsetupCall : cpsTripleWithin
      ((1 + 1) : Nat) (K73 + 140) (K73 + 148) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** Pcall ** Frame) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => ?_) hsetup
    have hq0 :
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
          ((.x9 : Reg) ↦ᵣ ptr) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ ptr) **
          ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
          bytesRegion ptr q2 ** F) s := by
      xperm_hyp hq
    have hq1 :
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
          ((.x9 : Reg) ↦ᵣ ptr) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ ptr) **
          regOwns fromU64Scratch ** bytesRegion ptr q2 ** F) s := by
      have hq0' :
          (((.x12 : Reg) ↦ᵣ ptr) **
            (((.x0 : Reg) ↦ᵣ (0 : Word)) **
              ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
              ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ ptr) **
              regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F)) s := by
        xperm_hyp hq0
      have hq2 := sepConj_mono_left (regIs_to_regOwn .x12 ptr) s hq0'
      simp only [fromU64Scratch, u256DivU64BeScratch, regOwns] at hq2 ⊢
      xperm_hyp hq2
    dsimp [Pcall, Frame]
    simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq1
  have hj := jal_x0_spec_gen_within (20 : BitVec 21) (K73 + 152)
  have hjC := cpsTripleWithin_extend_code
    (k73_whole_mem 38 _ (K73 + 152) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hj
  have hjF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** Qcall ** Frame)
    (by dsimp [Qcall, Frame]; pcf; exact hF) hjC
  have hjump : cpsTripleWithin 1 (K73 + 152) (K73 + 172) wholeCode
      (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** Qcall ** Frame)
      (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** Qcall ** Frame) := by
    simpa [Qcall, Frame, sepConj_assoc', sepConj_comm', sepConj_left_comm',
      sepConj_emp_left', sepConj_emp_right'] using hjF
  have hcallF' : cpsTripleWithin
      (1 + ((U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1))
      (K73 + 148) (K73 + 152) wholeCode
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** Pcall ** Frame)
      (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** Qcall ** Frame) := by
    simpa only [show (K73 + 148) + 4 = K73 + 152 by bv_omega,
      sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hcallF
  have hseq := cpsTripleWithin_seq_same_cr hsetupCall hcallF'
  have hseq' := cpsTripleWithin_seq_same_cr hseq hjump
  dsimp [Qcall, Frame] at hseq' ⊢
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq'

/-! The second divider status is known to be one on the increase route.  The -/
theorem k73_increase_status2_spec_within
    (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 1 (K73 + 124) (K73 + 128) wholeCode
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P) := by
  have hbeq := beq_spec_gen_within .x20 .x0 (48 : BitVec 13)
    (1 : Word) (0 : Word) (K73 + 124)
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 31 _ (K73 + 124) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  rw [show signExtend13 (48 : BitVec 13) = (48 : Word) by decide,
    show (K73 + 124) + (48 : Word) = K73 + 172 by bv_omega,
    show (K73 + 124) + 4 = K73 + 128 by bv_omega] at hbeqC
  have hbeqF := cpsBranchWithin_frameR P hP hbeqC
  have hnt := cpsBranchWithin_ntakenPath hbeqF (fun s hq => by
    have hq' :
        (((((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
          ⌜(1 : Word) = (0 : Word)⌝) ** P) s := by
      xperm_hyp hq
    have hq'' :
        (⌜(1 : Word) = (0 : Word)⌝ **
          (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)) s := by
      xperm_hyp hq'
    exact (by
      have hfalse := (sepConj_pure_left s).1 hq''
      exact (by decide : ¬ ((1 : Word) = (0 : Word))) hfalse.1))
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun s hq => by
      have hq' :
          (((((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
            ⌜(1 : Word) ≠ (0 : Word)⌝) ** P) s := by
        xperm_hyp hq
      have hq'' :
          (⌜(1 : Word) ≠ (0 : Word)⌝ **
            (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** P)) s := by
        xperm_hyp hq'
      have hbase := (sepConj_pure_left s).1 hq'' |>.2
      xperm_hyp hbase) hnt

/-! The `u256_is_zero` branch joins the unchanged quotient path with the -/
theorem k73_increase_zero_branch_spec_within
    (ptr : Word) (q2 : List (BitVec 8)) (F : Assertion)
    (hrw : RwRegion.wf ⟨ptr, 32⟩) (hlen : q2.length = 32)
    (hF : F.pcFree) :
    cpsTripleWithin
      (1 + (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1))
      (K73 + 136) (K73 + 172) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (fun s =>
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
          ((.x9 : Reg) ↦ᵣ ptr) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
          ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
          bytesRegion ptr q2 ** F) s ∨
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
          ((.x9 : Reg) ↦ᵣ ptr) **
          regOwns exposedRegs **
          bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) s) := by
  let Base : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F
  let Rest : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Base
  have hBase : Base.pcFree := by
    dsimp [Base]
    pcf
    exact hF
  have hraw : ∀ old10, cpsBranchWithin 1 (K73 + 136) wholeCode
      (Rest ** ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 172) (Rest ** ((.x10 : Reg) ↦ᵣ (0 : Word)))
      (K73 + 140) (Rest ** ((.x10 : Reg) ↦ᵣ old10)) := by
    intro old10
    have hbeq := beq_spec_gen_within .x10 .x0 (36 : BitVec 13)
      old10 (0 : Word) (K73 + 136)
    have hbeqC := cpsBranchWithin_extend_code
      (k73_whole_mem 34 _ (K73 + 136) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hbeq
    have hbeqF := cpsBranchWithin_frameR Base hBase hbeqC
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
        have hq' :
            (((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
                Base) ** ⌜old10 = (0 : Word)⌝) s := by
          simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq
        obtain ⟨hq, hzero⟩ := (sepConj_pure_right _).1 hq'
        rw [hzero] at hq
        dsimp [Rest, Base] at hq ⊢
        xperm_hyp hq)
      (fun s hq => by
        have hq' :
            (((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
                Base) ** ⌜old10 ≠ (0 : Word)⌝) s := by
          simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq
        obtain ⟨hq, _hne⟩ := (sepConj_pure_right _).1 hq'
        dsimp [Rest, Base] at hq ⊢
        xperm_hyp hq) hbeqF
  have hraw' : ∀ old10, cpsBranchWithin 1 (K73 + 136) wholeCode
      (Rest ** ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 172) (Rest ** ((.x10 : Reg) ↦ᵣ (0 : Word)))
      (K73 + 140) (Rest ** regOwn .x10) := by
    intro old10
    have h := hraw old10
    exact cpsBranchWithin_weaken (fun _ hp => hp)
      (fun _ hq => hq)
      (fun s hq => sepConj_mono_right (regIs_implies_regOwn .x10) s hq) h
  have hbr := cpsBranchWithin_of_forall_regIs_to_regOwn
    (r := .x10) (P := Rest)
    (Q_t := Rest ** ((.x10 : Reg) ↦ᵣ (0 : Word)))
    (Q_f := Rest ** regOwn .x10) hraw'
  let TakenPost : Assertion :=
    Rest ** ((.x10 : Reg) ↦ᵣ (0 : Word))
  let ReplacePost : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 152)) **
      ((.x9 : Reg) ↦ᵣ ptr) **
      regOwns exposedRegs **
      bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F
  let JoinedPost : Assertion := fun s => TakenPost s ∨ ReplacePost s
  have ht0 := cpsTripleWithin_refl (addr := K73 + 172)
    (P := TakenPost) (Q := JoinedPost) (fun _ h => Or.inl h)
  have ht := cpsTripleWithin_extend_code
    (cr' := wholeCode)
    (fun a i hi => by simp [CodeReq.empty] at hi) ht0
  have hf0 := k73_increase_replace_route_spec_within ptr q2 F hrw hlen hF
  have hf := cpsTripleWithin_weaken (Q' := JoinedPost) (fun _ hp => hp)
    (fun s hq => Or.inr hq) hf0
  have ht' := cpsTripleWithin_mono_nSteps
    (nSteps' := 2 + (1 +
      (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1) + 1)
    (by omega) ht
  have hf' : cpsTripleWithin
      (2 + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1) + 1)
      (K73 + 140) (K73 + 172) wholeCode
      (Rest ** regOwn .x10) JoinedPost := by
    refine cpsTripleWithin_weaken
      (P' := Rest ** regOwn .x10) (Q' := JoinedPost)
      (fun _ hp => by
        dsimp [Rest, Base] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => hq) hf
  have hmerge := cpsBranchWithin_merge_same_cr hbr ht' hf'
  dsimp [Base, Rest, TakenPost, ReplacePost, JoinedPost] at hmerge ⊢
  simpa only [show (1 + 1 : Nat) = 2 by decide,
    sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hmerge

/-! Connect the second-divider fall-through to the linked `u256_is_zero` -/
theorem k73_increase_zero_test_spec_within
    (ptr oldRa old10 : Word) (q2 : List (BitVec 8)) (F : Assertion)
    (hlen : q2.length = 32) (hF : F.pcFree) :
    cpsTripleWithin 12 (K73 + 124) (K73 + 136) wholeCode
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        ((ptr ↦ₘ packBytes ((q2.drop 0).take 8)) **
          ((ptr + 8) ↦ₘ packBytes ((q2.drop 8).take 8)) **
          ((ptr + 16) ↦ₘ packBytes ((q2.drop 16).take 8)) **
          ((ptr + 24) ↦ₘ packBytes ((q2.drop 24).take 8))) ** F) := by
  let Cells : Assertion :=
    (ptr ↦ₘ packBytes ((q2.drop 0).take 8)) **
      ((ptr + 8) ↦ₘ packBytes ((q2.drop 8).take 8)) **
      ((ptr + 16) ↦ₘ packBytes ((q2.drop 16).take 8)) **
      ((ptr + 24) ↦ₘ packBytes ((q2.drop 24).take 8))
  have hcells : bytesRegion ptr q2 = Cells := by
    simpa [Cells] using k73_bytes4cells ptr q2 hlen
  let Pstatus : Assertion :=
    ((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr q2 ** F
  have hPstatus : Pstatus.pcFree := by
    dsimp [Pstatus]
    pcf
    exact hF
  have hstatus := k73_increase_status2_spec_within Pstatus hPstatus
  have hzero := k73_increase_is_zero_call_spec_within
    ptr oldRa
    (packBytes ((q2.drop 0).take 8))
    (packBytes ((q2.drop 8).take 8))
    (packBytes ((q2.drop 16).take 8))
    (packBytes ((q2.drop 24).take 8)) F hF old10
  let Frame : Assertion :=
    ((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))
  have hFrame : Frame.pcFree := by
    dsimp [Frame]
    pcf
  have hzeroF := cpsTripleWithin_frameR Frame hFrame hzero
  have hzeroF' : cpsTripleWithin 11 (K73 + 128) (K73 + 136) wholeCode
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch ** Cells ** F) := by
    refine cpsTripleWithin_weaken
      (P' := ((.x20 : Reg) ↦ᵣ (1 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Pstatus)
      (Q' := ((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch ** Cells ** F)
      (fun _ hp => by
        dsimp [Frame, Pstatus] at hp ⊢
        rw [hcells] at hp
        dsimp [Cells] at hp
        xperm_hyp hp)
      (fun _ hq => by
        dsimp [Frame, Cells] at hq ⊢
        xperm_hyp hq) hzeroF
  have hseq := cpsTripleWithin_seq_same_cr hstatus hzeroF'
  dsimp [Pstatus] at hseq ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp [Cells] at hq ⊢
      xperm_hyp hq) hseq

/-! Sequence the second-divider zero test with its two continuations.  The -/
theorem k73_increase_zero_test_branch_spec_within
    (ptr oldRa old10 : Word) (q2 : List (BitVec 8)) (F : Assertion)
    (hrw : RwRegion.wf ⟨ptr, 32⟩) (hlen : q2.length = 32)
    (hF : F.pcFree) :
    cpsTripleWithin
      (12 + (1 + (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1)))
      (K73 + 124) (K73 + 172) wholeCode
      (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ oldRa) ** ((.x9 : Reg) ↦ᵣ ptr) **
        ((.x10 : Reg) ↦ᵣ old10) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (fun s =>
        (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
          ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
          bytesRegion ptr q2 ** F) s ∨
        (((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (K73 + 152)) ** ((.x9 : Reg) ↦ᵣ ptr) **
          regOwns exposedRegs **
          bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) s) := by
  let Cells : Assertion :=
    (ptr ↦ₘ packBytes ((q2.drop 0).take 8)) **
      ((ptr + 8) ↦ₘ packBytes ((q2.drop 8).take 8)) **
      ((ptr + 16) ↦ₘ packBytes ((q2.drop 16).take 8)) **
      ((ptr + 24) ↦ₘ packBytes ((q2.drop 24).take 8))
  have hcells : bytesRegion ptr q2 = Cells := by
    simpa [Cells] using k73_bytes4cells ptr q2 hlen
  let Fbranch : Assertion := ((.x20 : Reg) ↦ᵣ (1 : Word)) ** F
  have hFbranch : Fbranch.pcFree := by
    dsimp [Fbranch]
    pcf
    exact hF
  let BranchPre : Assertion :=
    ((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch ** Cells ** F
  let TakenPost : Assertion :=
    ((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr q2 ** F
  let ReplacePost : Assertion :=
    ((.x20 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ (K73 + 152)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      regOwns exposedRegs **
      bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F
  let BranchPost : Assertion := fun s => TakenPost s ∨ ReplacePost s
  have hbranch := k73_increase_zero_branch_spec_within
    ptr q2 Fbranch hrw hlen hFbranch
  have hbranch' : cpsTripleWithin
      (1 + (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) ptr q2).body.steps + 1)) + 1))
      (K73 + 136) (K73 + 172) wholeCode BranchPre BranchPost := by
    refine cpsTripleWithin_weaken
      (P' := BranchPre) (Q' := BranchPost)
      (fun _ hp => by
        dsimp [BranchPre, Fbranch] at hp ⊢
        rw [← hcells] at hp
        xperm_hyp hp)
      (fun s hq => by
        dsimp [BranchPost, TakenPost, ReplacePost, Fbranch] at hq ⊢
        obtain hq | hq := hq
        · exact Or.inl (by xperm_hyp hq)
        · exact Or.inr (by xperm_hyp hq)) hbranch
  have hzero := k73_increase_zero_test_spec_within
    ptr oldRa old10 q2 F hlen hF
  have hseq := cpsTripleWithin_seq_same_cr hzero hbranch'
  dsimp [BranchPre, BranchPost, TakenPost, ReplacePost, Cells] at hseq ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

/-! The multiply return is immediately classified by its overflow status. -/
theorem k73_increase_mul_status_branch_spec_within
    (spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F)
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes F)) :
    cpsBranchWithin 3857 (K73 + 64) wholeCode
      (k73IncreaseMulPre spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10) := by
  have hmul := k73_increase_mul_spec_within
    spH raIn gasLimit gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
    baseBytes accBytes outBytes F hF hcallee
  have hmul' : cpsTripleWithin 3856 (K73 + 64) (K73 + 88) wholeCode
      (k73IncreaseMulPre spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun s hq => by
        have hq' := k73_increase_mul_post_factor
          spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F s hq
        xperm_hyp hq')
      hmul
  have hstatus := k73_increase_status_branch_spec_within
    spH raIn gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes accBytes outBytes F hF
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmul' hstatus
  simpa only [show 3856 + 1 = 3857 by decide] using hseq

/-! The carry post already contains every divider input except the four -/
theorem k73_increase_mul_carry_to_div_pre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion) : ∀ s,
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes
          (regOwns [.x14, .x15, .x16, .x17] ** G) ** regOwn .x10) s →
      ∃ k, k73IncreaseDivPairPre spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** G) k s := by
  intro s hs
  let Core : Nat → Assertion := fun k =>
    k73MulEpilogueNoRa
      (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
      basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion outPtr outBytes ** k73MulOverflowCoreNoStatus accBytes k
  have pull_nested : ∀ (A : Assertion) (B : Nat → Assertion)
      (C : Assertion) h,
      (A ** ((fun u => ∃ k, B k u) ** C)) h →
      ∃ k, (A ** (B k ** C)) h := by
    intro A B C h hh
    have hh' : (A ** (fun u => ∃ k, (B k ** C) u)) h := by
      exact sepConj_mono_right
        (fun h' hq => (sepConj_exists_left h').mp hq) h hh
    exact sepConj_exists_right h hh'
  let C : Assertion := regOwns [.x14, .x15, .x16, .x17] ** G
  let A : Assertion :=
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) **
          EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
            (gasUsed - target) outPtr baseBytes))) ** regOwn .x10
  have hsource :
      (A ** ((fun u => ∃ k, Core k u) ** C)) s := by
    dsimp [k73IncreaseMulCarryRest] at hs
    dsimp [A, C, Core, k73IncreaseMulCarryRest]
    xperm_hyp hs
  have hoverOwn : ∀ k h,
      k73MulOverflowCoreNoStatus accBytes k h →
      (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes) h := by
    intro k h hh
    dsimp [k73MulOverflowCoreNoStatus] at hh ⊢
    have h5 := sepConj_mono_left
      (regIs_to_regOwn .x5
        (EvmAsm.Codegen.U256MulU64Be.accBase +
          BitVec.ofNat 64 (32 + k))) h hh
    have h56 := sepConj_mono_right
      (fun h' hq => sepConj_mono_left
        (regIs_to_regOwn .x6 (BitVec.ofNat 64 (8 - k))) h' hq) h h5
    exact h56
  have hcoreOwn : ∀ k h, Core k h →
      (k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion outPtr outBytes **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes)) h := by
    intro k h hh
    dsimp [Core] at hh
    have hbytes : ∀ h',
        (bytesRegion outPtr outBytes **
          k73MulOverflowCoreNoStatus accBytes k) h' →
        (bytesRegion outPtr outBytes **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
            bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes)) h' := by
      intro h' hh'
      exact sepConj_mono_right (hoverOwn k) h' hh'
    exact sepConj_mono_right hbytes h hh
  obtain ⟨k, hk⟩ := pull_nested A Core C s hsource
  have hk' : (A ** (Core k ** C)) s := hk
  have hkOwn : (A **
      ((k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion outPtr outBytes **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes)) ** C)) s := by
    apply sepConj_mono_right
      (fun h' hq => sepConj_mono_left (hcoreOwn k) h' hq) s hk'
  let MulOwned : Assertion :=
    bytesRegion basePtr baseBytes ** regOwn .x7 **
      ((.x11 : Reg) ↦ᵣ (gasUsed - target)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have hMulOwn : ∀ h,
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
        (gasUsed - target) outPtr baseBytes h → MulOwned h := by
    intro h hh
    dsimp [MulOwned,
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra] at hh ⊢
    apply sepConj_mono_right
      (fun h' hq => sepConj_mono_left
        (regIs_to_regOwn .x7 (0 : Word)) h' hq) h hh
  let AOwned : Assertion :=
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** MulOwned))) **
      regOwn .x10
  have hAmap : ∀ h, A h → AOwned h := by
    intro h hh
    have hframe : ∀ h',
        (frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) **
          EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
            (gasUsed - target) outPtr baseBytes) h' →
        (frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) ** MulOwned) h' := by
      intro h' hh'
      exact sepConj_mono_right hMulOwn h' hh'
    have h1 : ∀ h',
        (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
            (frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19 v20) **
              EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
                (gasUsed - target) outPtr baseBytes)) h' →
        (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
            (frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19 v20) ** MulOwned)) h' := by
      intro h' hh'
      exact sepConj_mono_right hframe h' hh'
    have h2 : ∀ h',
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
              (frameSlotsSaved k73Frame spH
                (k73Saved raIn v8 v9 v18 v19 v20) **
                EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
                  (gasUsed - target) outPtr baseBytes))) h' →
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (((.x1 : Reg) ↦ᵣ (K73 + 88)) **
              (frameSlotsSaved k73Frame spH
                (k73Saved raIn v8 v9 v18 v19 v20) ** MulOwned))) h' := by
      intro h' hh'
      exact sepConj_mono_right h1 h' hh'
    dsimp [A, AOwned]
    apply sepConj_mono_left h2 h
    exact hh
  have hkOwnedA : (AOwned **
      ((k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion outPtr outBytes **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes)) ** C)) s := by
    exact sepConj_mono_left hAmap s hkOwn
  refine ⟨k, ?_⟩
  have hsp :
      (spH + signExtend12 (-48 : BitVec 12)) +
          signExtend12 (48 : BitVec 12) = spH := by
    have hneg :
        signExtend12 (-48 : BitVec 12) = (18446744073709551568 : Word) := by
      decide
    rw [hneg, signExtend12_48]
    bv_omega
  have hregx2 :
      ((.x2 : Reg) ↦ᵣ
          ((spH + signExtend12 (-48 : BitVec 12)) +
            signExtend12 (48 : BitVec 12))) =
        ((.x2 : Reg) ↦ᵣ spH) := by
    exact congrArg (fun v => (.x2 : Reg) ↦ᵣ v) hsp
  have hepi :
      k73MulEpilogueNoRa
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (gasUsed - target) (1 : Word) =
        (((.x2 : Reg) ↦ᵣ spH) **
          ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x18 : Reg) ↦ᵣ target) **
          ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
          ((.x20 : Reg) ↦ᵣ (1 : Word)) **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            basePtr outPtr target (gasUsed - target) (1 : Word)) := by
    unfold k73MulEpilogueNoRa
    rw [hregx2]
  rw [hepi] at hkOwnedA
  dsimp [k73IncreaseDivPairPre, k73IncreaseDivPairFrame,
    k73IncreaseDivPairCoreFrame,
    k73MulOverflowCoreNoStatus,
    EvmAsm.Codegen.U256MulU64Be.mulTailExtra, u256DivU64BeScratch,
    regOwns, A, AOwned, MulOwned, C, Core] at hkOwnedA ⊢
  xperm_hyp hkOwnedA

/-! Continue each concrete divider-pair post through the second zero test. -/
theorem k73_increase_div_zero_branch_spec_within
    (spH gasUsed basePtr outPtr target : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hq1 : q1 = u256DivU64BeQuotBytes outBytes outBytes target)
    (hq2 : q2 = u256DivU64BeQuotBytes q1 q1 8)
    (hlen1 : q1.length = 32) (hlen2 : q2.length = 32)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (htargetBound : target.toNat ≤ 2 ^ 56)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4) :
    cpsTripleWithin
      ((10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps) +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps + 1)) + 1))))
      (K73 + 92) (K73 + 172) wholeCode
      (fun s => ∃ k : Nat, k73IncreaseDivPairPre spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k s)
      (fun s => ∃ k : Nat,
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
          bytesRegion outPtr q2 **
          ((.x18 : Reg) ↦ᵣ target) **
          k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
            baseBytes accBytes G k) s ∨
        (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          regOwns exposedRegs **
          bytesRegion outPtr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) **
          ((.x18 : Reg) ↦ᵣ target) **
          k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
            baseBytes accBytes G k) s) := by
  let q1' := u256DivU64BeQuotBytes outBytes outBytes target
  let q2' := u256DivU64BeQuotBytes q1' q1' 8
  have hdiv := k73_increase_div_pair_spec_within
    spH gasUsed basePtr outPtr target baseBytes accBytes outBytes G hG hrw
    hlenOut hoverOut htargetPos htargetBound hsz1 hsz2 hret1 hret2
  have hdiv' : cpsTripleWithin
      (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps)
      (K73 + 92) (K73 + 124) wholeCode
      (fun s => ∃ k, k73IncreaseDivPairPre spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k s)
      (fun s => ∃ k, k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k s) := hdiv
  have hq1' : q1 = q1' := by simpa [q1'] using hq1
  have hlen1' : q1'.length = 32 := by
    simpa [hq1'] using hlen1
  have hlen2' : q2'.length = 32 := by
    dsimp [q2']
    exact k73_div_quot_length q1' q1' 8 hlen1'
  have hq2' : q2 = q2' := by
    calc
      q2 = u256DivU64BeQuotBytes q1 q1 8 := hq2
      _ = u256DivU64BeQuotBytes q1' q1' 8 := by rw [hq1']
      _ = q2' := by rfl
  have hcont : ∀ k, cpsTripleWithin
      (12 + (1 + (((1 + 1) + (1 +
        (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps + 1)) + 1)))
      (K73 + 124) (K73 + 172) wholeCode
      (k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k)
      (fun s => ∃ k' : Nat,
          (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
          bytesRegion outPtr q2 **
          ((.x18 : Reg) ↦ᵣ target) **
          k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
            baseBytes accBytes G k') s ∨
          (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          regOwns exposedRegs **
          bytesRegion outPtr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) **
          ((.x18 : Reg) ↦ᵣ target) **
          k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
            baseBytes accBytes G k') s) := by
    intro k
    let CoreFrame : Assertion :=
      k73IncreaseDivPairCoreFrame spH gasUsed basePtr outPtr target
        baseBytes accBytes G k
    have hframe_split : (k73IncreaseDivPairFrame spH gasUsed basePtr outPtr
        target baseBytes accBytes G k) =
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x20 : Reg) ↦ᵣ (1 : Word)) ** CoreFrame) := by
      rfl
    let Fbranch : Assertion := ((.x18 : Reg) ↦ᵣ target) ** CoreFrame
    have hCoreFrame : CoreFrame.pcFree := by
      dsimp [CoreFrame]
      pcf
      exact hG
    have hFbranch : Fbranch.pcFree := by
      dsimp [Fbranch]
      pcf
      exact hG
    have hbranch := k73_increase_zero_test_branch_spec_within
      outPtr (K73 + 124)
      (u256DivU64BeRemainder q1 q1 8) q2 Fbranch hrw hlen2 hFbranch
    refine cpsTripleWithin_weaken
      (P' := ((.x1 : Reg) ↦ᵣ (K73 + 124)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x18 : Reg) ↦ᵣ target) **
        ((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns u256DivU64BeScratch **
        bytesRegion outPtr (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8) **
        k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
          baseBytes accBytes G k)
      (Q' := fun s => ∃ k' : Nat,
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
          bytesRegion outPtr q2 **
          ((.x18 : Reg) ↦ᵣ target) **
          k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
            baseBytes accBytes G k') s ∨
          (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** ((.x9 : Reg) ↦ᵣ outPtr) **
          regOwns exposedRegs **
          bytesRegion outPtr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) **
          ((.x18 : Reg) ↦ᵣ target) **
          k73IncreaseDivPairFrame spH gasUsed basePtr outPtr target
            baseBytes accBytes G k') s)
      (fun _ hp => by
        rw [hframe_split] at hp
        dsimp [Fbranch, CoreFrame] at hp ⊢
        simp only [← hq1] at hp
        have hq2Word : q2 = u256DivU64BeQuotBytes q1 q1 (8 : Word) := hq2
        rw [hq2Word] at ⊢
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun s hq => by
        obtain hq | hq := hq
        · refine ⟨k, Or.inl ?_⟩
          simp only [k73IncreaseDivPairFrame, Fbranch, CoreFrame,
            sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
          xperm_hyp hq
        · refine ⟨k, Or.inr ?_⟩
          simp only [k73IncreaseDivPairFrame, Fbranch, CoreFrame,
            sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
          xperm_hyp hq) hbranch
  exact cpsTripleWithin_seq_exists_same_cr hdiv' hcont
private theorem add_target188 :
    (K73 + 188) + signExtend21
        (jalOff GuestAddrs.u256_add_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 188)) =
      (GuestAddrs.u256_add_be : Word) := by
  change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 188 + _ = BitVec.ofNat 64 GuestAddrs.u256_add_be
  exact jalOff_correct_add GuestAddrs.u256_add_be
    GuestAddrs.eip1559_calc_base_fee_per_gas 188
    (by decide) (by decide) (by decide) (by decide)
private theorem add_mem188 :
    ∀ a i, CodeReq.singleton (K73 + 188)
      (.JAL .x1 (jalOff GuestAddrs.u256_add_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 188))) a = some i →
      wholeCode a = some i := by
  intro a i hi
  exact k73_whole_mono a i (k73_mem 47 _ (K73 + 188) (by decide)
    (by rw [k73_length]; decide) (by rfl) a i hi)
@[irreducible] def k73AddBCallSteps
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  5 + (u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps
@[irreducible] def k73AddBBranchSteps
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  6 + (u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps
@[irreducible] def k73AddBSize
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  4 * ((u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.size + 1)
private theorem k73_in_place_add_b_move_spec_within
    (rDst rSrc : Reg) (src dstOld A : Word) (idx : Nat)
    (Rest : Assertion) (hRest : Rest.pcFree)
    (hrDst : rDst ≠ .x0)
    (hA : A = K73 + BitVec.ofNat 64 (4 * idx))
    (hk : idx < prog.length)
    (hins : prog[idx]'hk = .MV rDst rSrc) :
    cpsTripleWithin 1 A (A + 4) wholeCode
      ((rSrc ↦ᵣ src) ** (rDst ↦ᵣ dstOld) ** Rest)
      ((rSrc ↦ᵣ src) ** (rDst ↦ᵣ src) ** Rest) := by
  have hmv := mv_spec_gen_within rDst rSrc src dstOld A hrDst
  have hmem : ∀ a i, CodeReq.singleton A (.MV rDst rSrc) a = some i →
      fullCode a = some i := by
    intro a i hi
    exact k73_mono a i (k73_mem idx (.MV rDst rSrc) A hA hk hins a i hi)
  have hmvc := cpsTripleWithin_extend_code full_whole_mono
    (cpsTripleWithin_extend_code
      hmem hmv)
  have hmvf := cpsTripleWithin_frameR Rest hRest hmvc
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hmvf
private theorem k73_in_place_add_b_setup_spec_within_v2
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) :
    cpsTripleWithin 3 (K73 + 176) (K73 + 188) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes) ** F)
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ srcPtr) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes) ** F) := by
  let G : Assertion :=
    regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
      bytesRegion srcPtr srcBytes
  let R10 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
      (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** G
  let R11 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
      (.x8 ↦ᵣ srcPtr) ** (.x10 ↦ᵣ srcPtr) ** (.x12 ↦ᵣ v12) ** G
  let R12 : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
      (.x8 ↦ᵣ srcPtr) ** (.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ outPtr) ** G
  have hR10 : R10.pcFree := by dsimp [R10, G]; pcf
  have hR11 : R11.pcFree := by dsimp [R11, G]; pcf
  have hR12 : R12.pcFree := by dsimp [R12, G]; pcf
  have h10 := k73_in_place_add_b_move_spec_within
    .x10 .x8 srcPtr v10 (K73 + 176) 44 R10 hR10 (by decide)
    (by decide) (by rw [k73_length]; decide) (by rfl)
  have h11 := k73_in_place_add_b_move_spec_within
    .x11 .x9 outPtr v11 (K73 + 180) 45 R11 hR11 (by decide)
    (by decide) (by rw [k73_length]; decide) (by rfl)
  have h12 := k73_in_place_add_b_move_spec_within
    .x12 .x9 outPtr v12 (K73 + 184) 46 R12 hR12 (by decide)
    (by decide) (by rw [k73_length]; decide) (by rfl)
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h10 h11
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 h12
  have h012F := cpsTripleWithin_frameR F hF h012
  dsimp [R10, R11, R12, G] at h012F ⊢
  simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm',
    show (K73 + 184) + 4 = K73 + 188 by bv_omega] using h012F
theorem k73_in_place_add_b_spec_within
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hret : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsTripleWithin
      (k73AddBCallSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) (K73 + 192) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** F)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ (K73 + 192)) **
        (.x10 ↦ᵣ u256AddBeCarry srcBytes orig orig) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** F) := by
  have hsetup := k73_in_place_add_b_setup_spec_within_v2
    srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F hF
  have hadd := u256AddBeBInPlaceFlat_spec
    (K73 + 192) srcPtr outPtr srcBytes orig hrw hroSrc hlenSrc hlenOrig
    hovSrc hovOut hdisj (by
      simpa only [k73AddBSize] using hsz) hret
  have haddc := cpsTripleWithin_extend_code add_whole_mono hadd
  have hcall := callWithin_spec
    (cr := wholeCode)
    (P := ((.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
      bytesRegion srcPtr srcBytes))
    (Q := ((.x10 ↦ᵣ u256AddBeCarry srcBytes orig orig) **
      (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes))
    (K73 + 188) (GuestAddrs.u256_add_be : Word) oldRa
    (jalOff GuestAddrs.u256_add_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 188))
    ((u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps + 1)
    add_target188 add_mem188
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_regOwns _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (bytesRegion_pcFree _ _))))))
    (by simpa only [show (K73 + 188) + 4 = K73 + 192 by bv_omega] using haddc)
  have hcallf := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ srcPtr) **
      (.x9 ↦ᵣ outPtr) ** F)
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF))) hcall
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsetup hcallf
  have hseq' := cpsTripleWithin_mono_nSteps
    (nSteps' := k73AddBCallSteps srcPtr outPtr srcBytes orig)
    (by unfold k73AddBCallSteps; omega) hseq
  refine cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [show (K73 + 188) + 4 = K73 + 192 by bv_omega] at hq
      xperm_chunked hq) hseq'
theorem k73_in_place_add_b_branch_spec_within
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hret : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** F)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
          bytesRegion srcPtr srcBytes ** regOwn .x10 ** F)
      (K73 + 196)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
          bytesRegion srcPtr srcBytes ** regOwn .x10 ** F) := by
  let AddRest : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
      (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes ** F
  let BranchRest : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** AddRest
  have hAddRest : AddRest.pcFree := by
    dsimp [AddRest]
    pcf
    exact hF
  have hadd := k73_in_place_add_b_spec_within
    srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F hF hrw hroSrc
      hlenSrc hlenOrig hovSrc hovOut hdisj hsz hret
  have hadd0 : cpsTripleWithin
      (k73AddBCallSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) (K73 + 192) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** F)
      (BranchRest ** ((.x10 : Reg) ↦ᵣ u256AddBeCarry
        srcBytes orig orig)) := by
    refine cpsTripleWithin_weaken
      (P' :=
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
          bytesRegion srcPtr srcBytes ** F))
      (Q' := BranchRest ** ((.x10 : Reg) ↦ᵣ u256AddBeCarry
        srcBytes orig orig))
      (fun _ hp => by exact hp)
      (fun _ hq => by
        dsimp [BranchRest, AddRest] at hq ⊢
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        xperm_hyp hq)
      hadd
  have hraw : ∀ old10, cpsBranchWithin 1 (K73 + 192) wholeCode
      (BranchRest ** ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 272) (BranchRest ** regOwn .x10)
      (K73 + 196) (BranchRest ** regOwn .x10) := by
    intro old10
    have hbne := bne_spec_gen_within .x10 .x0 (80 : BitVec 13)
      old10 (0 : Word) (K73 + 192)
    have hbneC := cpsBranchWithin_extend_code
      (k73_whole_mem 48 _ (K73 + 192) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hbne
    rw [show signExtend13 (80 : BitVec 13) = (80 : Word) by decide,
      show (K73 + 192) + (80 : Word) = K73 + 272 by bv_omega,
      show (K73 + 192) + 4 = K73 + 196 by bv_omega] at hbneC
    have hbneF := cpsBranchWithin_frameR AddRest hAddRest hbneC
    refine cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
        have hq' :
            (((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest ** (⌜old10 ≠ (0 : Word)⌝)) s := by
          xperm_hyp hq
        have hq'' :
            ((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest) ** (⌜old10 ≠ (0 : Word)⌝)) s := by
          xperm_hyp hq'
        obtain ⟨hq0, _hne⟩ := (sepConj_pure_right _).1 hq''
        have hq1 := sepConj_mono_left (regIs_implies_regOwn .x10) s hq0
        xperm_hyp hq1
      )
      (fun s hq => by
        have hq' :
            (((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest ** (⌜old10 = (0 : Word)⌝)) s := by
          xperm_hyp hq
        have hq'' :
            ((((.x10 : Reg) ↦ᵣ old10) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              AddRest) ** (⌜old10 = (0 : Word)⌝)) s := by
          xperm_hyp hq'
        obtain ⟨hq0, _eq⟩ := (sepConj_pure_right _).1 hq''
        have hq1 := sepConj_mono_left (regIs_implies_regOwn .x10) s hq0
        xperm_hyp hq1
      ) hbneF
  have hbr := hraw (u256AddBeCarry srcBytes orig orig)
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_same_cr hadd0 hbr
  have hsteps :
      k73AddBCallSteps srcPtr outPtr srcBytes orig + 1 =
        k73AddBBranchSteps srcPtr outPtr srcBytes orig := by
    simp only [k73AddBCallSteps, k73AddBBranchSteps]
    omega
  have hseq' := cpsBranchWithin_mono_nSteps
    (by rw [hsteps]) hseq
  refine cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp [BranchRest, AddRest] at hq ⊢
      xperm_hyp hq)
    (fun _ hq => by
      dsimp [BranchRest, AddRest] at hq ⊢
      xperm_hyp hq)
    hseq'
@[irreducible] def k73AddBTailSteps
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8)) : Nat :=
  16 + (u256AddBeBInPlaceFn srcPtr outPtr srcBytes orig).body.steps
@[irreducible] def k73AddBBranchPost
    (srcPtr outPtr : Word) (srcBytes orig : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 192)) **
    (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
    (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
    regOwns u256AddBeBInPlaceScratch **
    bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
    bytesRegion srcPtr srcBytes ** regOwn .x10 ** F
@[irreducible] def k73AddBTailPost
    (spH : Word) (saved : Reg → Word)
    (TailP : Assertion) : Assertion :=
  ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
    frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP
private theorem k73_regsOwnAt_split :
    regsOwnAt k73Frame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regsOwnAt k73FrameRest3) := by
  simp [k73Frame, k73FrameRest3, regsOwnAt]
private theorem k73_in_place_add_tail_post_weaken
    (spH : Word) (saved : Reg → Word)
    (srcPtr outPtr : Word)
    (srcBytes orig : List (BitVec 8)) (F Fadd TailP : Assertion)
    (hFaddShape : Fadd =
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F))
    (hTailPShape : TailP =
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** F)) :
    ∀ h,
      (k73AddBBranchPost srcPtr outPtr srcBytes orig Fadd) h →
      (k73AddBTailPost spH saved TailP) h := by
  intro s hq
  simp only [k73AddBBranchPost] at hq
  have hq1 :
      (((.x1 : Reg) ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) **
        (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** Fadd) s := by
    simpa [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq
  have hq2 := sepConj_mono_left (regIs_implies_regOwn .x1) _ hq1
  have hq2' :
      (((.x8 : Reg) ↦ᵣ srcPtr) ** regOwn .x1 **
        (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** Fadd) s := by
    xperm_hyp hq2
  have hq3 := sepConj_mono_left (regIs_implies_regOwn .x8) _ hq2'
  have hq3' :
      (((.x9 : Reg) ↦ᵣ outPtr) ** regOwn .x8 ** regOwn .x1 **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x10 **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** Fadd) s := by
    xperm_hyp hq3
  have hq4 := sepConj_mono_left (regIs_implies_regOwn .x9) _ hq3'
  rw [hFaddShape] at hq4
  simp only [k73AddBTailPost]
  rw [hTailPShape]
  rw [k73_regsOwnAt_split]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq4 ⊢
  xperm_hyp hq4
private theorem k73_in_place_add_tail_branch_weaken
    (spH : Word) (saved : Reg → Word)
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F Fadd TailP : Assertion)
    (hFaddShape : Fadd =
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F))
    (hTailPShape : TailP =
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** F))
    (hbranch :
      cpsBranchWithin
        (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
        (K73 + 176) wholeCode
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
          (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
          bytesRegion srcPtr srcBytes ** Fadd)
        (K73 + 272)
          (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) **
            (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
            regOwns u256AddBeBInPlaceScratch **
            bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
            bytesRegion srcPtr srcBytes ** regOwn .x10 ** Fadd)
        (K73 + 196)
          (((.x0 : Reg) ↦ᵣ (0 : Word)) **
            (.x1 ↦ᵣ (K73 + 192)) ** (.x8 ↦ᵣ srcPtr) **
            (.x9 ↦ᵣ outPtr) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
            regOwns u256AddBeBInPlaceScratch **
            bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
            bytesRegion srcPtr srcBytes ** regOwn .x10 ** Fadd)) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd)
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP)
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP) := by
  have hpost := k73_in_place_add_tail_post_weaken
    spH saved srcPtr outPtr srcBytes orig F Fadd TailP
      hFaddShape hTailPShape
  have hbranchNamed :
      cpsBranchWithin
        (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
        (K73 + 176) wholeCode
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
          (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ v10) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
          bytesRegion srcPtr srcBytes ** Fadd)
        (K73 + 272) (k73AddBBranchPost srcPtr outPtr srcBytes orig Fadd)
        (K73 + 196) (k73AddBBranchPost srcPtr outPtr srcBytes orig Fadd) := by
    simpa only [k73AddBBranchPost] using hbranch
  have hbranch' := cpsBranchWithin_weaken
    (Q_t' := k73AddBTailPost spH saved TailP)
    (Q_f' := k73AddBTailPost spH saved TailP)
    (fun _ hp => by exact hp) hpost hpost hbranchNamed
  simpa only [k73AddBTailPost] using hbranch'
private theorem k73_in_place_add_tail_branch_spec_within
    (spH : Word) (saved : Reg → Word)
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F Fadd TailP : Assertion)
    (hFaddShape : Fadd =
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F))
    (hTailPShape : TailP =
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
        bytesRegion srcPtr srcBytes ** F))
    (hFadd : Fadd.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsBranchWithin
      (k73AddBBranchSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** Fadd)
      (K73 + 272)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP)
      (K73 + 196)
        (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** TailP) := by
  have hbranch := k73_in_place_add_b_branch_spec_within
    srcPtr outPtr oldRa v10 v11 v12 srcBytes orig Fadd hFadd hrw hroSrc
      hlenSrc hlenOrig hovSrc hovOut hdisj hsz hcallRet
  exact k73_in_place_add_tail_branch_weaken
    spH saved srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F Fadd TailP
      hFaddShape hTailPShape hbranch
private theorem k73_holdsFor_sepConj_mono_left
    {P P' Q : Assertion} {s : MachineState}
    (himpl : ∀ h, P h → P' h)
    (h : (P ** Q).holdsFor s) : (P' ** Q).holdsFor s := by
  rcases h with ⟨hmem, hcompat, hpq⟩
  exact ⟨hmem, hcompat,
    sepConj_mono_left (P := P) (P' := P') (Q := Q) himpl hmem hpq⟩
theorem k73_in_place_add_tail_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word)
    (srcPtr outPtr oldRa v10 v11 v12 : Word)
    (srcBytes orig : List (BitVec 8)) (F : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hsz : k73AddBSize srcPtr outPtr srcBytes orig ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = (K73 + 188) + 4) :
    cpsTripleWithin
      (k73AddBTailSteps srcPtr outPtr srcBytes orig)
      (K73 + 176) raIn wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes **
        ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH saved ** F)
      (fun s =>
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame saved **
          frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ (1 : Word)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
          (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
          bytesRegion srcPtr srcBytes ** F) s ∨
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame saved **
          frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ (0 : Word)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
          (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes ** F) s) := by
  let FrameRest : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
      frameSlotsSaved k73Frame spH saved
  let Fadd : Assertion := FrameRest ** F
  have hFrameRest : FrameRest.pcFree := by
    dsimp [FrameRest]
    pcf
  have hFadd : Fadd.pcFree := by
    dsimp [Fadd]
    exact pcFree_sepConj hFrameRest hF
  let TailP : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes srcBytes orig orig) **
      bytesRegion srcPtr srcBytes ** F
  have hTailP : TailP.pcFree := by
    dsimp [TailP]
    pcf
    exact hF
  have hbranch' := k73_in_place_add_tail_branch_spec_within
    spH saved srcPtr outPtr oldRa v10 v11 v12 srcBytes orig F Fadd TailP
      (by simp [Fadd, FrameRest, sepConj_assoc']) (by simp [TailP]) hFadd hrw hroSrc
      hlenSrc hlenOrig hovSrc hovOut
      hdisj hsz hcallRet
  have hfail := k73_failure_tail_spec_within
    sp0 spH raIn saved TailP hsp hret hsaved hTailP
  have hsucc := k73_success_tail_spec_within
    sp0 spH raIn saved TailP hsp hret hsaved hTailP
  have hbudget :
      k73AddBBranchSteps srcPtr outPtr srcBytes orig + 10 ≤
        k73AddBTailSteps srcPtr outPtr srcBytes orig := by
    simp only [k73AddBBranchSteps, k73AddBTailSteps]
    omega
  intro R hR s hcr hP hpc
  obtain ⟨k1, hk1, s1, hs1, hcase⟩ := hbranch' R hR s hcr
    (by simpa [Fadd, FrameRest, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hP)
    hpc
  rcases hcase with ⟨hpcFail, hFailPre⟩ | ⟨hpcSucc, hSuccPre⟩
  · obtain ⟨k2, hk2, s2, hs2, hFailPost⟩ :=
      hfail R hR s1 (CodeReq.SatisfiedBy_preserved hs1 hcr)
        hFailPre hpcFail
    refine ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2, ?_⟩
    refine ⟨hFailPost.1, ?_⟩
    apply k73_holdsFor_sepConj_mono_left (Q := R) (fun _ h => Or.inl h)
    exact hFailPost.2
  · obtain ⟨k2, hk2, s2, hs2, hSuccPost⟩ :=
      hsucc R hR s1 (CodeReq.SatisfiedBy_preserved hs1 hcr)
        hSuccPre hpcSucc
    refine ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2, ?_⟩
    refine ⟨hSuccPost.1, ?_⟩
    apply k73_holdsFor_sepConj_mono_left (Q := R) (fun _ h => Or.inr h)
    exact hSuccPost.2
end EvmAsm.Codegen.HeaderBaseFeeSpec
