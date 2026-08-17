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

private theorem k73_div_quot_length
    (a orig : List (BitVec 8)) (b : Word) (hlen : orig.length = 32) :
    (u256DivU64BeQuotBytes a orig b).length = 32 := by
  have h : ∀ k : Nat, (divState a orig b k).1.length = orig.length := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [divState, ih]
  simpa [u256DivU64BeQuotBytes, hlen] using h 32

/-! The replacement arm after the zero test.  The caller's x10--x12
    ownership is deliberately exposed at the common +172 join: the next
    add/subtract arm overwrites those ABI registers, while the arithmetic
    scratch remains caller-owned. -/
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

/-! The second divider status is known to be one on the increase route.  The
    BEQ at `+124` therefore takes its fall-through edge to `+128`; the pure
    equality on the impossible edge is consumed explicitly rather than being
    left as a latent branch post. -/
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

/-! The `u256_is_zero` branch joins the unchanged quotient path with the
    replacement path above.  The result is intentionally a disjunction: the
    taken arm retains the quotient, while the fall-through arm has written the
    canonical one-word value. -/
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

/-! Connect the second-divider fall-through to the linked `u256_is_zero`
    call.  The public input remains one `bytesRegion`; only the callee-facing
    post exposes its four dword cells. -/
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

/-! Sequence the second-divider zero test with its two continuations.  The
    frame register `x20` is carried as ambient state through the branch; the
    branch itself only owns the quotient/result registers. -/
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

/-! The multiply return is immediately classified by its overflow status.
    This is the first increase-path seam that exposes both the failure tail
    and the post-division continuation without duplicating the multiply call. -/
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

/-! Continue each concrete divider-pair post through the second zero test.
    The divider's existential carry is retained until the common `+172` join;
    this is the shape needed by the later frame/tail composition. -/
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
      ((.x2 : Reg) ↦ᵣ spH) ** ((.x8 : Reg) ↦ᵣ basePtr) **
      ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
      frameSlotsSaved k73Frame spH (k73Saved (K73 + 88) basePtr outPtr
        target (gasUsed - target) (1 : Word)) **
      bytesRegion basePtr baseBytes **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      k73MulOverflowCoreNoStatus accBytes k ** G
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
      (P' := k73IncreaseDivPairPost spH gasUsed basePtr outPtr target
        baseBytes accBytes outBytes G k)
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
        dsimp [k73IncreaseDivPairPost, k73IncreaseDivPairFrame,
          Fbranch, CoreFrame] at hp ⊢
        simp only [← hq1] at hp
        have hq2Word : q2 = u256DivU64BeQuotBytes q1 q1 (8 : Word) := hq2
        rw [hq2Word] at ⊢
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun s hq => by
        dsimp [Fbranch, CoreFrame, k73IncreaseDivPairFrame] at hq ⊢
        obtain hq | hq := hq
        · exact ⟨k, Or.inl (by xperm_hyp hq)⟩
        · exact ⟨k, Or.inr (by xperm_hyp hq)⟩) hbranch
  exact cpsTripleWithin_seq_exists_same_cr hdiv' hcont

end EvmAsm.Codegen.HeaderBaseFeeSpec
