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
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 152)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        regOwns exposedRegs **
        bytesRegion ptr (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ** F) := by
  let Rest : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
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
    ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x12 : Reg) ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch ** bytesRegion ptr q2 ** F
  have hRestMv : RestMv.pcFree := by
    dsimp [RestMv]
    pcf
    exact hF
  let RestMvFrame : Assertion :=
    ((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
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
        xperm_hyp hq) hli
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
  let Frame : Assertion := ((.x9 : Reg) ↦ᵣ ptr) ** F
  have hFrame : Frame.pcFree := by
    dsimp [Frame]
    pcf
    exact hF
  have hcallF := cpsTripleWithin_frameR Frame hFrame hcall
  have hsetupCall : cpsTripleWithin
      ((1 + 1) : Nat) (K73 + 140) (K73 + 148) wholeCode
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
        regOwn .x10 ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr q2 ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** Pcall ** Frame) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => ?_) hsetup
    have hq0 :
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ ptr) **
          ((.x12 : Reg) ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
          bytesRegion ptr q2 ** F) s := by
      xperm_hyp hq
    have hq1 :
        (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ ptr) **
          regOwns fromU64Scratch ** bytesRegion ptr q2 ** F) s := by
      have hq0' :
          (((.x12 : Reg) ↦ᵣ ptr) **
            (((.x1 : Reg) ↦ᵣ (K73 + 136)) ** ((.x9 : Reg) ↦ᵣ ptr) **
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

end EvmAsm.Codegen.HeaderBaseFeeSpec
