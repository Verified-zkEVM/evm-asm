/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeSpec

  First K73 whole-routine composition checkpoint.  The two consecutive
  divisions on the increase path are both exact in-place calls: at +104 and
  +120 the source and destination are the saved output pointer `x9`.  The
  later decrease-path call at +168 is intentionally not folded into this
  lemma; it consumes the disjoint-source theorem instead.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.U256DivU64BeSAsm
import EvmAsm.Codegen.Programs.U256MulU64Be.WholeTop
import EvmAsm.Codegen.Programs.U256AddBeSAsm
import EvmAsm.Codegen.Programs.U256SubBeSAsm
import EvmAsm.Codegen.Programs.U256IsZeroSAsm
import EvmAsm.Codegen.Programs.U256FromU64BeSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.U256DivU64BeSAsm

abbrev K73 : Word := (GuestAddrs.eip1559_calc_base_fee_per_gas : Word)
abbrev prog : List Instr := eip1559CalcBaseFeePerGas_prog
abbrev k73Code : CodeReq := CodeReq.ofProg K73 eip1559CalcBaseFeePerGas_prog
abbrev divCode : CodeReq := u256DivU64BeCr
abbrev fullCode : CodeReq := k73Code.union divCode

abbrev mulCode : CodeReq := CodeReq.ofProg
  (GuestAddrs.u256_mul_u64_be : Word) u256MulU64Be_prog
abbrev isZeroCode : CodeReq := CodeReq.ofProg
  (GuestAddrs.u256_is_zero : Word) u256IsZero_prog
abbrev fromU64Code : CodeReq := CodeReq.ofProg
  (GuestAddrs.u256_from_u64_be : Word) u256FromU64Be_prog
abbrev addCode : CodeReq := CodeReq.ofProg
  (GuestAddrs.u256_add_be : Word) u256AddBe_prog
abbrev subCode : CodeReq := CodeReq.ofProg
  (GuestAddrs.u256_sub_be : Word) u256SubBe_prog

abbrev wholeCode : CodeReq := CodeReq.unionAll
  [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]

private theorem whole_components_disjoint :
    ∀ j (hj : j <
      [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode].length),
      ∀ k (hk : k < j),
        ([k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode].get
          ⟨k, Nat.lt_trans hk hj⟩).Disjoint
        ([k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode].get
          ⟨j, hj⟩) := by
  intro j hj k hk
  have hj7 : j < 7 := by simpa using hj
  have hk7 : k < 7 := lt_trans hk hj7
  interval_cases j <;> interval_cases k <;>
    simp_all [List.get] <;>
    apply CodeReq.Disjoint.ofProg_ranges <;> decide

theorem k73_whole_mono : ∀ a i, k73Code a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll
    [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]
    0 (by decide) (fun j hj => by omega) a i h

theorem mul_whole_mono : ∀ a i, mulCode a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll
    [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]
    1 (by decide) (fun j hj => whole_components_disjoint 1 (by decide) j hj) a i h

theorem div_whole_mono : ∀ a i, divCode a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll
    [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]
    2 (by decide) (fun j hj => whole_components_disjoint 2 (by decide) j hj) a i h

theorem isZero_whole_mono : ∀ a i, isZeroCode a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll
    [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]
    3 (by decide) (fun j hj => whole_components_disjoint 3 (by decide) j hj) a i h

theorem fromU64_whole_mono : ∀ a i, fromU64Code a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll
    [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]
    4 (by decide) (fun j hj => whole_components_disjoint 4 (by decide) j hj) a i h

theorem add_whole_mono : ∀ a i, addCode a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll
    [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]
    5 (by decide) (fun j hj => whole_components_disjoint 5 (by decide) j hj) a i h

theorem sub_whole_mono : ∀ a i, subCode a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.mono_unionAll
    [k73Code, mulCode, divCode, isZeroCode, fromU64Code, addCode, subCode]
    6 (by decide) (fun j hj => whole_components_disjoint 6 (by decide) j hj) a i h

theorem full_whole_mono : ∀ a i, fullCode a = some i → wholeCode a = some i := by
  intro a i h
  exact CodeReq.union_split_mono k73_whole_mono div_whole_mono a i h

theorem k73_length : eip1559CalcBaseFeePerGas_prog.length = 77 := by decide

theorem k73_prog_bound : 4 * prog.length < 2 ^ 64 := by
  rw [k73_length]
  norm_num

private theorem div_disjoint : k73Code.Disjoint divCode := by
  unfold k73Code divCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [k73_length]
    decide
  · decide
  · rw [k73_length]
    decide

theorem k73_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = K73 + BitVec.ofNat 64 (4 * k))
    (hk : k < prog.length)
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → k73Code a = some i := by
  intro a i hi
  exact CodeReq.ofProg_mem_at K73 A eip1559CalcBaseFeePerGas_prog k ins hA hk hins
    k73_prog_bound a i hi

theorem k73_mono : ∀ a i, k73Code a = some i → fullCode a = some i := by
  intro a i hi
  exact CodeReq.union_mono_left a i hi

theorem div_mono : ∀ a i, divCode a = some i → fullCode a = some i := by
  intro a i hi
  exact CodeReq.mono_union_right div_disjoint (fun _ _ h => h) a i hi

private theorem div_target104 :
    (K73 + 104) + signExtend21
        (jalOff GuestAddrs.u256_div_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 104)) =
      (GuestAddrs.u256_div_u64_be : Word) := by
  change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 104 + _ = BitVec.ofNat 64 GuestAddrs.u256_div_u64_be
  exact jalOff_correct_add GuestAddrs.u256_div_u64_be
    GuestAddrs.eip1559_calc_base_fee_per_gas 104
    (by decide) (by decide) (by decide) (by decide)

private theorem div_target120 :
    (K73 + 120) + signExtend21
        (jalOff GuestAddrs.u256_div_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 120)) =
      (GuestAddrs.u256_div_u64_be : Word) := by
  change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 120 + _ = BitVec.ofNat 64 GuestAddrs.u256_div_u64_be
  exact jalOff_correct_add GuestAddrs.u256_div_u64_be
    GuestAddrs.eip1559_calc_base_fee_per_gas 120
    (by decide) (by decide) (by decide) (by decide)

private theorem div_mem104 :
    ∀ a i, CodeReq.singleton (K73 + 104)
      (.JAL .x1 (jalOff GuestAddrs.u256_div_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 104))) a = some i →
      fullCode a = some i := by
  intro a i hi
  exact k73_mono a i (k73_mem 26 _ (K73 + 104) (by decide)
    (by rw [k73_length]; decide) (by rfl) a i hi)

private theorem div_mem120 :
    ∀ a i, CodeReq.singleton (K73 + 120)
      (.JAL .x1 (jalOff GuestAddrs.u256_div_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 120))) a = some i →
      fullCode a = some i := by
  intro a i hi
  exact k73_mono a i (k73_mem 30 _ (K73 + 120) (by decide)
    (by rw [k73_length]; decide) (by rfl) a i hi)

private theorem div_target168 :
    (K73 + 168) + signExtend21
        (jalOff GuestAddrs.u256_div_u64_be
          (GuestAddrs.eip1559_calc_base_fee_per_gas + 168)) =
      (GuestAddrs.u256_div_u64_be : Word) := by
  change BitVec.ofNat 64 GuestAddrs.eip1559_calc_base_fee_per_gas +
      BitVec.ofNat 64 168 + _ = BitVec.ofNat 64 GuestAddrs.u256_div_u64_be
  exact jalOff_correct_add GuestAddrs.u256_div_u64_be
    GuestAddrs.eip1559_calc_base_fee_per_gas 168
    (by decide) (by decide) (by decide) (by decide)

private theorem div_mem168 :
    ∀ a i, CodeReq.singleton (K73 + 168)
      (.JAL .x1 (jalOff GuestAddrs.u256_div_u64_be
        (GuestAddrs.eip1559_calc_base_fee_per_gas + 168))) a = some i →
      fullCode a = some i := by
  intro a i hi
  exact k73_mono a i (k73_mem 42 _ (K73 + 168) (by decide)
    (by rw [k73_length]; decide) (by rfl) a i hi)

private theorem mv_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = K73 + BitVec.ofNat 64 (4 * k))
    (hk : k < prog.length)
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  intro a i hi
  exact k73_mono a i (k73_mem k ins A hA hk hins a i hi)

private theorem divState_length
    (a orig : List (BitVec 8)) (b : Word) (k : Nat) :
    (divState a orig b k).1.length = orig.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [divState, ih]

set_option maxRecDepth 8000 in
theorem k73_in_place_div_pair_spec_within
    (ptr target oldRa v10 v11 v12 : Word)
    (aBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hrw : RwRegion.wf ⟨ptr, 32⟩)
    (hlen : aBytes.length = 32)
    (hptr : ptr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (htargetBound : target.toNat ≤ 2 ^ 56)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn ptr target aBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn ptr 8
        (u256DivU64BeQuotBytes aBytes aBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4) :
    cpsTripleWithin
      (10 + (u256DivU64BeInPlaceFn ptr target aBytes).body.steps +
        (u256DivU64BeInPlaceFn ptr 8
          (u256DivU64BeQuotBytes aBytes aBytes target)).body.steps)
      (K73 + 92) (K73 + 124) fullCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr aBytes ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 124)) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
        (.x10 ↦ᵣ u256DivU64BeRemainder
          (u256DivU64BeQuotBytes aBytes aBytes target)
          (u256DivU64BeQuotBytes aBytes aBytes target) 8) **
        (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes aBytes aBytes target)
            (u256DivU64BeQuotBytes aBytes aBytes target) 8) ** F) := by
  have hmv10 := mv_spec_gen_within .x10 .x9 ptr v10 (K73 + 92) (by decide)
  have hmv10c := cpsTripleWithin_extend_code
    (mv_mem 23 _ (K73 + 92) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv10
  have hmv10f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldRa) ** (.x18 ↦ᵣ target) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr aBytes ** F)
    (by pcf; exact hF) hmv10c
  have hmv11 := mv_spec_gen_within .x11 .x18 target v11 (K73 + 96) (by decide)
  have hmv11c := cpsTripleWithin_extend_code
    (mv_mem 24 _ (K73 + 96) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv11
  have hmv11f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldRa) ** (.x9 ↦ᵣ ptr) ** (.x10 ↦ᵣ ptr) **
      (.x12 ↦ᵣ v12) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr aBytes ** F)
    (by pcf; exact hF) hmv11c
  have hmv12 := mv_spec_gen_within .x12 .x9 ptr v12 (K73 + 100) (by decide)
  have hmv12c := cpsTripleWithin_extend_code
    (mv_mem 25 _ (K73 + 100) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv12
  have hmv12f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldRa) ** (.x18 ↦ᵣ target) **
      (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ target) **
      regOwns u256DivU64BeScratch **
      bytesRegion ptr aBytes ** F)
    (by pcf; exact hF) hmv12c
  have hsetup : cpsTripleWithin 3 (K73 + 92) (K73 + 104) fullCode
      (((.x1 ↦ᵣ oldRa) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr aBytes ** F))
      (((.x1 ↦ᵣ oldRa) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
        (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ target) ** (.x12 ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr aBytes ** F)) := by
    have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      hmv10f hmv11f
    have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      h01 hmv12f
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h012
  have hdiv1 := u256DivU64BeInPlaceFlat_spec
    (K73 + 108) ptr target aBytes hrw hlen hptr htargetPos htargetBound hsz1
    hret1
  have hdiv1c := cpsTripleWithin_extend_code div_mono hdiv1
  have hdiv1' : cpsTripleWithin
      ((u256DivU64BeInPlaceFn ptr target aBytes).body.steps + 1)
      (GuestAddrs.u256_div_u64_be : Word) (K73 + 108) fullCode
      (((.x1 : Reg) ↦ᵣ (K73 + 108)) **
        (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ target) ** (.x12 ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch ** bytesRegion ptr aBytes)
      (((.x1 : Reg) ↦ᵣ (K73 + 108)) **
        (.x10 ↦ᵣ u256DivU64BeRemainder aBytes aBytes target) **
        (.x11 ↦ᵣ target) ** (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hdiv1c
  have hcall1 := callWithin_spec
    (cr := fullCode)
    (P := ((.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ target) ** (.x12 ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch ** bytesRegion ptr aBytes))
    (Q := ((.x10 ↦ᵣ u256DivU64BeRemainder aBytes aBytes target) **
      (.x11 ↦ᵣ target) ** (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target)))
    (K73 + 104) (GuestAddrs.u256_div_u64_be : Word)
    oldRa (jalOff GuestAddrs.u256_div_u64_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 104))
    ((u256DivU64BeInPlaceFn ptr target aBytes).body.steps + 1)
    div_target104 div_mem104
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_regOwns _)
              (bytesRegion_pcFree _ _)))))
    (by simpa only [show (K73 + 104) + 4 = K73 + 108 by bv_omega] using hdiv1')
  have hcall1f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF)) hcall1
  have hmv20 := mv_spec_gen_within .x10 .x9 ptr
    (u256DivU64BeRemainder aBytes aBytes target) (K73 + 108) (by decide)
  have hmv20c := cpsTripleWithin_extend_code
    (mv_mem 27 _ (K73 + 108) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv20
  have hmv20f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K73 + 108)) ** (.x18 ↦ᵣ target) **
      (.x11 ↦ᵣ target) ** (.x12 ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target) ** F)
    (by pcf; exact hF) hmv20c
  have hli21 := li_spec_gen_within .x11 target 8 (K73 + 112) (by decide)
  have hli21c := cpsTripleWithin_extend_code
    (mv_mem 28 _ (K73 + 112) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hli21
  have hli21f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K73 + 108)) ** (.x9 ↦ᵣ ptr) ** (.x10 ↦ᵣ ptr) **
      (.x12 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target) ** F)
    (by pcf; exact hF) hli21c
  have hmv22 := mv_spec_gen_within .x12 .x9 ptr ptr (K73 + 116) (by decide)
  have hmv22c := cpsTripleWithin_extend_code
    (mv_mem 29 _ (K73 + 116) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv22
  have hmv22f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K73 + 108)) ** (.x10 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
      (.x11 ↦ᵣ 8) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target) ** F)
    (by pcf; exact hF) hmv22c
  have hsetup2 : cpsTripleWithin 3 (K73 + 108) (K73 + 120) fullCode
      (((.x1 ↦ᵣ (K73 + 108)) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
        (.x10 ↦ᵣ u256DivU64BeRemainder aBytes aBytes target) **
        (.x11 ↦ᵣ target) ** (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target) ** F))
      (((.x1 ↦ᵣ (K73 + 108)) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
        (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target) ** F)) := by
    have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      hmv20f hli21f
    have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      h01 hmv22f
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h012
  have hdiv2 := u256DivU64BeInPlaceFlat_spec
    (K73 + 124) ptr 8 (u256DivU64BeQuotBytes aBytes aBytes target)
    hrw (by
      unfold u256DivU64BeQuotBytes
      rw [divState_length, hlen]) hptr (by decide) (by decide) hsz2
    hret2
  have hdiv2c := cpsTripleWithin_extend_code div_mono hdiv2
  have hdiv2' : cpsTripleWithin
      ((u256DivU64BeInPlaceFn ptr 8
        (u256DivU64BeQuotBytes aBytes aBytes target)).body.steps + 1)
      (GuestAddrs.u256_div_u64_be : Word) (K73 + 124) fullCode
      (((.x1 : Reg) ↦ᵣ (K73 + 124)) **
        (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target))
      (((.x1 : Reg) ↦ᵣ (K73 + 124)) **
        (.x10 ↦ᵣ u256DivU64BeRemainder
          (u256DivU64BeQuotBytes aBytes aBytes target)
          (u256DivU64BeQuotBytes aBytes aBytes target) 8) **
        (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes aBytes aBytes target)
          (u256DivU64BeQuotBytes aBytes aBytes target) 8)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hdiv2c
  have hcall2 := callWithin_spec
    (cr := fullCode)
    (P := ((.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target)))
    (Q := ((.x10 ↦ᵣ u256DivU64BeRemainder
        (u256DivU64BeQuotBytes aBytes aBytes target)
        (u256DivU64BeQuotBytes aBytes aBytes target) 8) **
      (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes
        (u256DivU64BeQuotBytes aBytes aBytes target)
        (u256DivU64BeQuotBytes aBytes aBytes target) 8)))
    (K73 + 120) (GuestAddrs.u256_div_u64_be : Word)
    (K73 + 108) (jalOff GuestAddrs.u256_div_u64_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 120))
    ((u256DivU64BeInPlaceFn ptr 8
      (u256DivU64BeQuotBytes aBytes aBytes target)).body.steps + 1)
    div_target120 div_mem120
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_regOwns _)
              (bytesRegion_pcFree _ _)))))
    (by simpa only [show (K73 + 120) + 4 = K73 + 124 by bv_omega] using hdiv2')
  have hcall2f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF)) hcall2
  let midP : Assertion :=
    ((.x1 ↦ᵣ (K73 + 108)) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
      (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) **
      regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes target) ** F)
  let finalPost : Assertion :=
    ((.x1 ↦ᵣ (K73 + 124)) ** (.x9 ↦ᵣ ptr) ** (.x18 ↦ᵣ target) **
      (.x10 ↦ᵣ u256DivU64BeRemainder
        (u256DivU64BeQuotBytes aBytes aBytes target)
        (u256DivU64BeQuotBytes aBytes aBytes target) 8) **
      (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
      bytesRegion ptr (u256DivU64BeQuotBytes
        (u256DivU64BeQuotBytes aBytes aBytes target)
        (u256DivU64BeQuotBytes aBytes aBytes target) 8) ** F)
  have hcall2f' : cpsTripleWithin
      (1 + ((u256DivU64BeInPlaceFn ptr 8
        (u256DivU64BeQuotBytes aBytes aBytes target)).body.steps + 1))
      (K73 + 120) (K73 + 120 + 4) fullCode midP finalPost := by
    unfold midP finalPost
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        simp only [show (K73 + 120) + 4 = K73 + 124 by bv_omega] at hq
        xperm_hyp hq) hcall2f
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsetup hcall1f
  have hseq2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [show (K73 + 104) + 4 = K73 + 108 by bv_omega] at hp
      xperm_hyp hp) hseq hsetup2
  have hseq3 := cpsTripleWithin_seq_same_cr hseq2 hcall2f'
  have hseq3' := cpsTripleWithin_mono_nSteps
    (nSteps' := 10 + (u256DivU64BeInPlaceFn ptr target aBytes).body.steps +
      (u256DivU64BeInPlaceFn ptr 8
        (u256DivU64BeQuotBytes aBytes aBytes target)).body.steps)
    (by omega) hseq3
  simpa [midP, finalPost, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hseq3'

theorem k73_disjoint_setup_spec_within
    (srcPtr outPtr oldRa v10 v11 v12 : Word) (G : Assertion)
    (hG : G.pcFree) :
    cpsTripleWithin 3 (K73 + 156) (K73 + 168) fullCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** G)
      (((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ outPtr) ** G) := by
  have hmv10 := mv_spec_gen_within .x10 .x8 srcPtr v10 (K73 + 156) (by decide)
  have hmv10c := cpsTripleWithin_extend_code
    (mv_mem 39 _ (K73 + 156) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv10
  have hmv10f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldRa) ** (.x9 ↦ᵣ outPtr) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** G)
    (by pcf; exact hG) hmv10c
  have hli11 := li_spec_gen_within .x11 v11 8 (K73 + 160) (by decide)
  have hli11c := cpsTripleWithin_extend_code
    (mv_mem 40 _ (K73 + 160) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hli11
  have hli11f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
      (.x10 ↦ᵣ srcPtr) ** (.x12 ↦ᵣ v12) ** G)
    (by pcf; exact hG) hli11c
  have hmv12 := mv_spec_gen_within .x12 .x9 outPtr v12 (K73 + 164) (by decide)
  have hmv12c := cpsTripleWithin_extend_code
    (mv_mem 41 _ (K73 + 164) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hmv12
  have hmv12f := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) **
      (.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ 8) ** G)
    (by pcf; exact hG) hmv12c
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hmv10f hli11f
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h01 hmv12f
  refine cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h012

theorem k73_disjoint_setup_ordered_spec_within
    (srcPtr outPtr oldRa v10 v11 v12 : Word) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree) :
    cpsTripleWithin 3 (K73 + 156) (K73 + 168) fullCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) **
        (.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** G ** F)
      ((((.x1 : Reg) ↦ᵣ oldRa) ** (.x10 ↦ᵣ srcPtr) **
        (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ outPtr) ** G) **
        (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** F) := by
  let H : Assertion := G ** F
  have hH : H.pcFree := by
    unfold H
    exact pcFree_sepConj hG hF
  have hsetup := k73_disjoint_setup_spec_within
    srcPtr outPtr oldRa v10 v11 v12 H hH
  refine cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hsetup

theorem k73_disjoint_div_spec_within
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
    (hsz : 4 * ((u256DivU64BeFn srcPtr outPtr 8 srcBytes orig).body.size + 1)
      ≤ 2 ^ 64)
    (hret : ((K73 + 168) + 4) &&& ~~~(1 : Word) = (K73 + 168) + 4) :
    cpsTripleWithin
      (5 + (u256DivU64BeFn srcPtr outPtr 8 srcBytes orig).body.steps)
      (K73 + 156) (K73 + 172) fullCode
      (((.x1 : Reg) ↦ᵣ oldRa) ** (.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns u256DivU64BeScratch ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes ** F)
      (((.x1 : Reg) ↦ᵣ (K73 + 172)) **
        (.x10 ↦ᵣ u256DivU64BeRemainder srcBytes orig 8) **
        (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256DivU64BeScratch **
        bytesRegion outPtr (u256DivU64BeQuotBytes srcBytes orig 8) **
        bytesRegion srcPtr srcBytes ** (.x8 ↦ᵣ srcPtr) **
        (.x9 ↦ᵣ outPtr) ** F) := by
  let G : Assertion :=
    regOwns u256DivU64BeScratch ** bytesRegion outPtr orig **
      bytesRegion srcPtr srcBytes
  have hG : G.pcFree := by
    unfold G
    pcf
  have hsetup := k73_disjoint_setup_ordered_spec_within
    srcPtr outPtr oldRa v10 v11 v12 G F hG hF
  dsimp [G] at hsetup
  have hdiv := u256DivU64BeFlat_spec
    (K73 + 172) srcPtr outPtr 8 srcBytes orig hrw hroSrc hlenSrc hlenOrig
    hovSrc hovOut hdisj (by decide) (by decide) hsz hret
  have hdivc := cpsTripleWithin_extend_code div_mono hdiv
  have hcall := callWithin_spec
    (cr := fullCode)
    (P := ((.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256DivU64BeScratch ** bytesRegion outPtr orig **
      bytesRegion srcPtr srcBytes))
    (Q := ((.x10 ↦ᵣ u256DivU64BeRemainder srcBytes orig 8) **
      (.x11 ↦ᵣ 8) ** (.x12 ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
      bytesRegion outPtr (u256DivU64BeQuotBytes srcBytes orig 8) **
      bytesRegion srcPtr srcBytes))
    (K73 + 168) (GuestAddrs.u256_div_u64_be : Word) oldRa
    (jalOff GuestAddrs.u256_div_u64_be
      (GuestAddrs.eip1559_calc_base_fee_per_gas + 168))
    ((u256DivU64BeFn srcPtr outPtr 8 srcBytes orig).body.steps + 1)
    div_target168 div_mem168
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs
            (pcFree_sepConj (pcFree_regOwns _)
              (pcFree_sepConj (bytesRegion_pcFree _ _)
                (bytesRegion_pcFree _ _))))))
    (by simpa only [show (K73 + 168) + 4 = K73 + 172 by bv_omega] using hdivc)
  have hcallf := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ srcPtr) ** (.x9 ↦ᵣ outPtr) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF)) hcall
  have hseq := cpsTripleWithin_seq_same_cr hsetup hcallf
  have hseq' := cpsTripleWithin_mono_nSteps
    (nSteps' := 5 + (u256DivU64BeFn srcPtr outPtr 8 srcBytes orig).body.steps)
    (by omega) hseq
  refine cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [show (K73 + 168) + 4 = K73 + 172 by bv_omega] at hq
      xperm_chunked hq) hseq'

/-! ## Whole-routine frame and the equal-target path

The first whole-routine assembly checkpoint keeps the caller-visible frame
explicit.  The equal-target arm is the byte-for-byte copy path: it does not
call an arithmetic helper, but it still exercises the K73 prologue and the
shared restore/return tail.  The arithmetic arms below use the two division
contracts above and are added to the same frame contract in the next
composition step.
-/

def k73Frame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

def k73FrameRest1 : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

def k73FrameRest2 : FrameDesc :=
  [(.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

def k73FrameRest3 : FrameDesc :=
  [(.x18, 24), (.x19, 32), (.x20, 40)]

def k73FrameRest4 : FrameDesc :=
  [(.x19, 32), (.x20, 40)]

def k73FrameRest5 : FrameDesc :=
  [(.x20, 40)]

def k73FrameRest6 : FrameDesc :=
  []

def k73Saved (vRa v8 v9 v18 v19 v20 : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => vRa
  | .x8 => v8
  | .x9 => v9
  | .x18 => v18
  | .x19 => v19
  | .x20 => v20
  | _ => 0

def k73HeadPre
    (sp0 spH raIn gasLimit gasUsed basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
  (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) **
  (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
  frameSlotsOwn k73Frame spH ** bytesRegion basePtr baseBytes **
  bytesRegion outPtr outBytes ** F

def k73HeadPost
    (spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) **
  (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ target) **
  (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) **
  (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
  frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
  bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F

theorem k73_head_spec_within
    (sp0 spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1) (hF : F.pcFree) :
    cpsTripleWithin 10 K73 (K73 + 40) wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outBytes F)
      (k73HeadPost spH raIn gasLimit gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes outBytes F) := by
  have h0 := addi_spec_gen_same_within .x2 sp0 (-56 : BitVec 12) K73 (by decide)
  rw [← hspH] at h0
  have h0' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 0 _ (K73 + 0) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h0
  have h1 := sd_spec_gen_own_within .x2 .x1 spH raIn (0 : BitVec 12) (K73 + 4)
  have h1' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 1 _ (K73 + 4) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h1
  have h2 := sd_spec_gen_own_within .x2 .x8 spH v8 (8 : BitVec 12) (K73 + 8)
  have h2' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 2 _ (K73 + 8) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h2
  have h3 := sd_spec_gen_own_within .x2 .x9 spH v9 (16 : BitVec 12) (K73 + 12)
  have h3' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 3 _ (K73 + 12) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h3
  have h4 := sd_spec_gen_own_within .x2 .x18 spH v18 (24 : BitVec 12) (K73 + 16)
  have h4' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 4 _ (K73 + 16) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h4
  have h5 := sd_spec_gen_own_within .x2 .x19 spH v19 (32 : BitVec 12) (K73 + 20)
  have h5' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 5 _ (K73 + 20) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h5
  have h6 := sd_spec_gen_own_within .x2 .x20 spH v20 (40 : BitVec 12) (K73 + 24)
  have h6' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 6 _ (K73 + 24) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h6
  have h7 := mv_spec_gen_within .x8 .x12 basePtr v8 (K73 + 28) (by decide)
  have h7' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 7 _ (K73 + 28) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h7
  have h8 := mv_spec_gen_within .x9 .x13 outPtr v9 (K73 + 32) (by decide)
  have h8' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 8 _ (K73 + 32) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h8
  have h9 := srli_spec_gen_within .x18 .x10 v18 gasLimit (1 : BitVec 6)
    (K73 + 36) (by decide)
  have h9' := cpsTripleWithin_extend_code
    (fun a i hi => k73_whole_mono a i
      (k73_mem 9 _ (K73 + 36) (by decide) (by rw [k73_length]; decide)
        (by rfl) a i hi)) h9
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) **
      (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ 0) ** frameSlotsOwn k73Frame spH **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h0'
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
      (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) **
      (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ 0) ** frameSlotsOwn k73FrameRest1 spH **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      ((spH + signExtend12 0) ↦ₘ raIn) ** frameSlotsOwn k73FrameRest2 spH **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ v8) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      ((spH + signExtend12 0) ↦ₘ raIn) **
      ((spH + signExtend12 8) ↦ₘ v8) ** frameSlotsOwn k73FrameRest3 spH **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h3'
  have h4F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      ((spH + signExtend12 0) ↦ₘ raIn) **
      ((spH + signExtend12 8) ↦ₘ v8) **
      ((spH + signExtend12 16) ↦ₘ v9) ** frameSlotsOwn k73FrameRest4 spH **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h4'
  have h5F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      ((spH + signExtend12 0) ↦ₘ raIn) **
      ((spH + signExtend12 8) ↦ₘ v8) **
      ((spH + signExtend12 16) ↦ₘ v9) **
      ((spH + signExtend12 24) ↦ₘ v18) ** frameSlotsOwn k73FrameRest5 spH **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h5'
  have h6F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      ((spH + signExtend12 0) ↦ₘ raIn) **
      ((spH + signExtend12 8) ↦ₘ v8) **
      ((spH + signExtend12 16) ↦ₘ v9) **
      ((spH + signExtend12 24) ↦ₘ v18) **
      ((spH + signExtend12 32) ↦ₘ v19) ** frameSlotsOwn k73FrameRest6 spH **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h6'
  have h7F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ 0) ** frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h7'
  have h8F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ basePtr) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ 0) ** frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h8'
  have h9F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ 0) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F) (by pcf; exact hF) h9'
  simp [k73Frame, k73FrameRest1, k73FrameRest2, k73FrameRest3,
    k73FrameRest4, k73FrameRest5, k73FrameRest6, k73Saved,
    frameSlotsOwn, frameSlotsSaved]
    at h0F h1F h2F h3F h4F h5F h6F h7F h8F h9F
  have h01 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h0F h1F
  have h02 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h01 h2F
  have h03 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h02 h3F
  have h04 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h03 h4F
  have h05 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h04 h5F
  have h06 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h05 h6F
  have h07 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h06 h7F
  have h08 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h07 h8F
  have h09 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h08 h9F
  unfold k73HeadPre k73HeadPost at *
  rw [htarget]
  simp [k73Frame, k73Saved, frameSlotsOwn, frameSlotsSaved]
  exact cpsTripleWithin_weaken (by xsimp) (by xsimp) h09

theorem k73_whole_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = K73 + BitVec.ofNat 64 (4 * k))
    (hk : k < prog.length)
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → wholeCode a = some i := by
  intro a i hi
  exact k73_whole_mono a i (k73_mem k ins A hA hk hins a i hi)

def k73CopyOut (srcBytes outBytes : List (BitVec 8)) : List (BitVec 8) :=
  setBytes (setBytes (setBytes (setBytes outBytes 0
    (dwordBytes (packBytes ((srcBytes.drop 0).take 8)))) 8
    (dwordBytes (packBytes ((srcBytes.drop 8).take 8)))) 16
    (dwordBytes (packBytes ((srcBytes.drop 16).take 8)))) 24
    (dwordBytes (packBytes ((srcBytes.drop 24).take 8)))

theorem k73_equal_copy_spec_within
    (basePtr outPtr old5 old10 : Word)
    (srcBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hsrc : srcBytes.length = 32) (hout : outBytes.length = 32)
    (hF : F.pcFree) :
    cpsTripleWithin 10 (K73 + 232) (K73 + 276) wholeCode
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) ** (.x5 ↦ᵣ old5) **
        (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr srcBytes ** bytesRegion outPtr outBytes ** F)
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ packBytes ((srcBytes.drop 24).take 8)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr srcBytes ** bytesRegion outPtr (k73CopyOut srcBytes outBytes) ** F) := by
  let c0 := packBytes ((srcBytes.drop 0).take 8)
  let c1 := packBytes ((srcBytes.drop 8).take 8)
  let c2 := packBytes ((srcBytes.drop 16).take 8)
  let c3 := packBytes ((srcBytes.drop 24).take 8)
  let o1 := setBytes outBytes 0 (dwordBytes c0)
  let o2 := setBytes o1 8 (dwordBytes c1)
  let o3 := setBytes o2 16 (dwordBytes c2)
  let o4 := setBytes o3 24 (dwordBytes c3)
  have hld0 := bytesRegion_ld_within .x5 .x8 basePtr old5 (K73 + 232)
    srcBytes 0 (by decide) (by simpa [hsrc]) (by decide)
  have hld0c := cpsTripleWithin_extend_code
    (k73_whole_mem 58 _ (K73 + 232) (by decide) (by rw [k73_length]; decide) (by rfl)) hld0
  have hld0f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hld0c
  have hsd0 := bytesRegion_sd_within .x9 .x5 outPtr c0 (K73 + 236)
    outBytes 0 (by simpa [hout]) (by decide)
  have hsd0c := cpsTripleWithin_extend_code
    (k73_whole_mem 59 _ (K73 + 236) (by decide) (by rw [k73_length]; decide) (by rfl)) hsd0
  have hsd0f := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ basePtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion basePtr srcBytes ** F)
    (by pcf; exact hF) hsd0c
  have hld1 := bytesRegion_ld_within .x5 .x8 basePtr c0 (K73 + 240)
    srcBytes 1 (by decide) (by simpa [hsrc]) (by decide)
  have hld1c := cpsTripleWithin_extend_code
    (k73_whole_mem 60 _ (K73 + 240) (by decide) (by rw [k73_length]; decide) (by rfl)) hld1
  have hld1f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion outPtr o1 ** F)
    (by pcf; exact hF) hld1c
  have hsd1 := bytesRegion_sd_within .x9 .x5 outPtr c1 (K73 + 244)
    o1 1 (by simpa [o1, hout]) (by decide)
  have hsd1c := cpsTripleWithin_extend_code
    (k73_whole_mem 61 _ (K73 + 244) (by decide) (by rw [k73_length]; decide) (by rfl)) hsd1
  have hsd1f := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ basePtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion basePtr srcBytes ** F)
    (by pcf; exact hF) hsd1c
  have hld2 := bytesRegion_ld_within .x5 .x8 basePtr c1 (K73 + 248)
    srcBytes 2 (by decide) (by simpa [hsrc]) (by decide)
  have hld2c := cpsTripleWithin_extend_code
    (k73_whole_mem 62 _ (K73 + 248) (by decide) (by rw [k73_length]; decide) (by rfl)) hld2
  have hld2f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion outPtr o2 ** F)
    (by pcf; exact hF) hld2c
  have hsd2 := bytesRegion_sd_within .x9 .x5 outPtr c2 (K73 + 252)
    o2 2 (by simpa [o2, o1, hout]) (by decide)
  have hsd2c := cpsTripleWithin_extend_code
    (k73_whole_mem 63 _ (K73 + 252) (by decide) (by rw [k73_length]; decide) (by rfl)) hsd2
  have hsd2f := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ basePtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion basePtr srcBytes ** F)
    (by pcf; exact hF) hsd2c
  have hld3 := bytesRegion_ld_within .x5 .x8 basePtr c2 (K73 + 256)
    srcBytes 3 (by decide) (by simpa [hsrc]) (by decide)
  have hld3c := cpsTripleWithin_extend_code
    (k73_whole_mem 64 _ (K73 + 256) (by decide) (by rw [k73_length]; decide) (by rfl)) hld3
  have hld3f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ outPtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion outPtr o3 ** F)
    (by pcf; exact hF) hld3c
  have hsd3 := bytesRegion_sd_within .x9 .x5 outPtr c3 (K73 + 260)
    o3 3 (by simpa [o3, o2, o1, hout]) (by decide)
  have hsd3c := cpsTripleWithin_extend_code
    (k73_whole_mem 65 _ (K73 + 260) (by decide) (by rw [k73_length]; decide) (by rfl)) hsd3
  have hsd3f := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ basePtr) ** (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion basePtr srcBytes ** F)
    (by pcf; exact hF) hsd3c
  have hli := li_spec_gen_within .x10 old10 (0 : Word) (K73 + 264) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (k73_whole_mem 66 _ (K73 + 264) (by decide) (by rw [k73_length]; decide) (by rfl)) hli
  have hlif := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) ** (.x5 ↦ᵣ c3) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion basePtr srcBytes **
      bytesRegion outPtr o4 ** F)
    (by pcf; exact hF) hlic
  have hj := jal_x0_spec_gen_within (8 : BitVec 21) (K73 + 268)
  rw [show (K73 + 268 : Word) + signExtend21 (8 : BitVec 21) = K73 + 276 by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
    bv_omega] at hj
  have hjc := cpsTripleWithin_extend_code
    (k73_whole_mem 67 _ (K73 + 268) (by decide) (by rw [k73_length]; decide) (by rfl)) hj
  have hjf := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) ** (.x5 ↦ᵣ c3) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion basePtr srcBytes ** bytesRegion outPtr o4 ** F)
    (by pcf; exact hF) hjc
  simp only [sepConj_emp_left'] at hjf
  have h01 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hld0f hsd0f
  have h23 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hld1f hsd1f
  have h45 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hld2f hsd2f
  have h67 := cpsTripleWithin_seq_perm_same_cr (by xsimp) hld3f hsd3f
  have h0123 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h01 h23
  have h4567 := cpsTripleWithin_seq_perm_same_cr (by xsimp) h45 h67
  have hcopy := cpsTripleWithin_seq_perm_same_cr (by xsimp) h0123 h4567
  have hcopyli := cpsTripleWithin_seq_perm_same_cr (by xsimp) hcopy hlif
  have hall := cpsTripleWithin_seq_perm_same_cr (by xsimp) hcopyli hjf
  have hfinal : cpsTripleWithin 10 (K73 + 232) (K73 + 276) wholeCode
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) ** (.x5 ↦ᵣ old5) **
        (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr srcBytes ** bytesRegion outPtr outBytes ** F)
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ c3) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr srcBytes ** bytesRegion outPtr o4 ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hall
  unfold k73CopyOut
  simpa [c0, c1, c2, c3, o1, o2, o3, o4] using hfinal

/-! The first complete route is the equal-target route.  It is deliberately
    kept as a named composition seam: the remaining arithmetic routes reuse
    exactly this prologue/dispatch/epilogue shape, but carry the corresponding
    callee post through the dispatch branches. -/
theorem k73_equal_route_spec_within
    (sp0 spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes outBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (heq : gasUsed = target)
    (hsrc : baseBytes.length = 32) (hout : outBytes.length = 32)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) (hF : F.pcFree) :
    cpsTripleWithin 29 K73 raIn wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outBytes F)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ packBytes ((baseBytes.drop 24).take 8)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) **
        bytesRegion basePtr baseBytes **
        bytesRegion outPtr (k73CopyOut baseBytes outBytes) ** F) := by
  have hhead := k73_head_spec_within sp0 spH raIn gasLimit gasUsed
    basePtr outPtr target v8 v9 v18 v19 v20 baseBytes outBytes F hspH htarget hF
  have hbeq := beq_spec_gen_within .x11 .x18 (192 : BitVec 13)
    gasUsed target (K73 + 40)
  rw [show (K73 + 40) + signExtend13 (192 : BitVec 13) = K73 + 232 by
    rw [show signExtend13 (192 : BitVec 13) = (192 : Word) from by decide]
    bv_omega] at hbeq
  have hbeqC := cpsBranchWithin_extend_code
    (k73_whole_mem 10 _ (K73 + 40) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hbeq
  have hbeqF := cpsBranchWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
      (.x9 ↦ᵣ outPtr) ** (.x19 ↦ᵣ v19) **
      (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ basePtr) **
      (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F)
    (by pcf; exact hF) hbeqC
  have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      dsimp [k73HeadPost] at hp ⊢
      xperm_chunked hp) hhead hbeqF
  let FcopyRest : Assertion :=
    (.x2 ↦ᵣ spH) ** (.x18 ↦ᵣ target) **
    (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x11 ↦ᵣ gasUsed) **
    (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    F
  let Fcopy : Assertion := (.x1 ↦ᵣ raIn) ** FcopyRest
  have hFcopy : Fcopy.pcFree := by
    dsimp [Fcopy]
    pcf
    exact hF
  have hcopy := k73_equal_copy_spec_within basePtr outPtr 0 gasLimit
    baseBytes outBytes Fcopy hsrc hout hFcopy
  have hcopyAny : ∀ old5, cpsTripleWithin 10 (K73 + 232) (K73 + 276) wholeCode
      (((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ gasLimit) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** Fcopy) **
        (.x5 ↦ᵣ old5))
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ packBytes ((baseBytes.drop 24).take 8)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr baseBytes **
        bytesRegion outPtr (k73CopyOut baseBytes outBytes) ** Fcopy) := by
    intro old5
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (k73_equal_copy_spec_within basePtr outPtr old5 gasLimit
        baseBytes outBytes Fcopy hsrc hout hFcopy)
  have hcopyOwn : cpsTripleWithin 10 (K73 + 232) (K73 + 276) wholeCode
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) ** regOwn .x5 **
        (.x10 ↦ᵣ gasLimit) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** Fcopy)
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ packBytes ((baseBytes.drop 24).take 8)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr baseBytes **
        bytesRegion outPtr (k73CopyOut baseBytes outBytes) ** Fcopy) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
        (P := (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
          (.x10 ↦ᵣ gasLimit) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** Fcopy)
        hcopyAny)
  have hcopyBranch : cpsTripleWithin 10 (K73 + 232) (K73 + 276) wholeCode
      (((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        regOwn .x5 ** (.x10 ↦ᵣ gasLimit) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** Fcopy))
      ((.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ packBytes ((baseBytes.drop 24).take 8)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion basePtr baseBytes **
        bytesRegion outPtr (k73CopyOut baseBytes outBytes) ** Fcopy) := by
    exact hcopyOwn
  let F_E : Assertion :=
    (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** bytesRegion basePtr baseBytes **
    bytesRegion outPtr (k73CopyOut baseBytes outBytes) ** F
  have hFE : F_E.pcFree := by
    dsimp [F_E]
    pcf
    exact hF
  let hpreE : Assertion :=
    (.x5 ↦ᵣ packBytes ((baseBytes.drop 24).take 8)) **
    (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F_E
  let savedE : Reg → Word := k73Saved raIn v8 v9 v18 v19 v20
  have hE : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH savedE ** hpreE)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame savedE **
        frameSlotsSaved k73Frame spH savedE ** hpreE) := by
    have hload_mem : ∀ a i,
        CodeReq.ofProg (K73 + 276) (loadProg k73Frame) a = some i →
          wholeCode a = some i := by
      intro a i hi
      apply k73_whole_mono
      apply CodeReq.ofProg_mono_sub K73 (K73 + 276) prog (loadProg k73Frame) 69
      · decide
      · decide
      · rw [k73_length]
        decide
      · exact k73_prog_bound
      · exact hi
    have hbound : 4 * k73Frame.length < 2 ^ 64 := by
      simp [k73Frame]
    have hne : ∀ p ∈ k73Frame, p.1 ≠ .x0 := by
      intro p hp
      simp [k73Frame] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hload := loadSeq_spec_own k73Frame spH savedE (K73 + 276)
      hbound hne
    have hloadC := cpsTripleWithin_extend_code hload_mem hload
    have hloadF := cpsTripleWithin_frameR hpreE
      (by dsimp [hpreE, F_E]; pcf; exact hF) hloadC
    have hsp : spH + signExtend12 (56 : BitVec 12) = sp0 := by
      rw [hspH]
      rw [BitVec.add_assoc]
      have hz : signExtend12 (-56 : BitVec 12) +
          signExtend12 (56 : BitVec 12) = (0 : Word) := by decide
      rw [hz]
      simp
    have hadd := addi_spec_gen_same_within .x2 spH (56 : BitVec 12)
      (K73 + 300) (by decide)
    rw [hsp] at hadd
    have haddC := cpsTripleWithin_extend_code
      (k73_whole_mem 75 _ (K73 + 300) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hadd
    have haddF := cpsTripleWithin_frameR
      (regsAt k73Frame savedE ** frameSlotsSaved k73Frame spH savedE ** hpreE)
        (pcFree_sepConj (pcFree_regsAt _ _)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) (by
          dsimp [hpreE, F_E]; pcf; exact hF))) haddC
    have hloadAdd := cpsTripleWithin_seq_perm_same_cr (by xsimp) hloadF haddF
    have hsaved : savedE .x1 = raIn := by
      rfl
    have hReg : regsAt k73Frame savedE =
        ((.x1 ↦ᵣ raIn) ** regsAt k73FrameRest1 savedE) := by
      simp [k73Frame, k73FrameRest1, regsAt, savedE, hsaved, k73Saved]
    have hloadAdd' : cpsTripleWithin (k73Frame.length + 1) (K73 + 276)
        (K73 + 304) wholeCode
        (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH savedE) ** hpreE)
        (((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 savedE **
          frameSlotsSaved k73Frame spH savedE) ** hpreE) := by
      apply cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
        rw [hReg] at hq
        xperm_chunked hq) hloadAdd
    have hret0 := Fn.jalr_ret_spec (K73 + 304) raIn hret
      (P := (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 savedE **
        frameSlotsSaved k73Frame spH savedE)
      (pcFree_sepConj (pcFree_regIs (r := .x2) (v := sp0))
        (pcFree_sepConj (pcFree_regsAt k73FrameRest1 savedE)
          (pcFree_frameSlotsSaved _ _ _)))
    have hretC := cpsTripleWithin_extend_code
      (k73_whole_mem 76 _ (K73 + 304) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hret0
    have hretF := cpsTripleWithin_frameR hpreE
      (by dsimp [hpreE, F_E]; pcf; exact hF) hretC
    have hfull := cpsTripleWithin_seq_perm_same_cr (by xsimp) hloadAdd' hretF
    have hfull8 : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
        (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH savedE) ** hpreE)
        (((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 savedE **
          frameSlotsSaved k73Frame spH savedE) ** hpreE) := by
      simpa [k73Frame] using hfull
    have hfull' := cpsTripleWithin_weaken
      (P := (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH savedE) ** hpreE))
      (Q := (((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 savedE **
        frameSlotsSaved k73Frame spH savedE) ** hpreE))
      (P' := ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH savedE ** hpreE))
      (Q' := ((.x2 ↦ᵣ sp0) ** regsAt k73Frame savedE **
        frameSlotsSaved k73Frame spH savedE ** hpreE))
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        simp [hReg]
        xperm_chunked hq) hfull8
    exact hfull'
  have hroute := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    let currentRegs : Reg → Word := fun r => match r with
      | .x1 => raIn
      | .x8 => basePtr
      | .x9 => outPtr
      | .x18 => target
      | .x19 => v19
      | .x20 => v20
      | _ => 0
    let FrouteRest : Assertion :=
      (.x5 ↦ᵣ packBytes ((baseBytes.drop 24).take 8)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ basePtr) ** (.x13 ↦ᵣ outPtr) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 **
      bytesRegion basePtr baseBytes **
      bytesRegion outPtr (k73CopyOut baseBytes outBytes) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** F
    have hp' : ((.x2 ↦ᵣ spH) ** regsAt k73Frame currentRegs ** FrouteRest) h := by
      simp only [FrouteRest, Fcopy, FcopyRest] at hp ⊢
      dsimp [currentRegs, frameSlotsSaved, k73Frame, k73Saved] at hp ⊢
      simp only [sepConj_emp_right', sepConj_emp_left'] at hp ⊢
      xperm_chunked hp
    have hp'' : ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame ** FrouteRest) h := by
      exact sepConj_mono_right
        (sepConj_mono_left (regsAt_implies_regsOwnAt k73Frame currentRegs)) h hp'
    simp only [FrouteRest] at hp''
    dsimp [currentRegs, hpreE, F_E, savedE, regsOwnAt,
      regsAt, frameSlotsSaved, k73Frame, k73FrameRest1, k73Saved] at hp'' ⊢
    simp only [sepConj_emp_right', sepConj_emp_left'] at hp'' ⊢
    xperm_chunked hp'') hcopyBranch hE
  have hrouteStart : cpsTripleWithin (10 + 8) (K73 + 232) raIn wholeCode
      (((.x11 ↦ᵣ gasUsed) ** (.x18 ↦ᵣ target) **
        ⌜gasUsed = target⌝) **
        ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) **
          (.x9 ↦ᵣ outPtr) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
          (.x10 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ basePtr) **
          (.x13 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          bytesRegion basePtr baseBytes ** bytesRegion outPtr outBytes ** F))
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame savedE **
        frameSlotsSaved k73Frame spH savedE ** hpreE) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Fcopy] at hp ⊢
      extract_pure_deep hp
      obtain ⟨_, hp⟩ := hp
      xperm_chunked hp) (fun _ hq => hq) hroute
  have hbranchSwap := cpsBranchWithin_swap hbranch
  have hseqSwap := cpsBranchWithin_seq_cpsTripleWithin_same_cr
    hbranchSwap hrouteStart (fun _ hq => hq)
  have hseq := cpsBranchWithin_swap hseqSwap
  have hmerged := cpsBranchWithin_takenPath hseq (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact h_ne heq)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      dsimp [hpreE, F_E, savedE, regsAt, frameSlotsSaved,
        k73Frame, k73FrameRest1, k73Saved] at hq ⊢
      simp only [sepConj_emp_right', sepConj_emp_left'] at hq ⊢
      xperm_chunked hq) hmerged

theorem k73_epilogue_load_mem :
    ∀ a i, CodeReq.ofProg (K73 + 276) (loadProg k73Frame) a = some i →
      wholeCode a = some i := by
  intro a i hi
  apply k73_whole_mono
  apply CodeReq.ofProg_mono_sub K73 (K73 + 276) prog (loadProg k73Frame) 69
  · decide
  · decide
  · rw [k73_length]
    decide
  · exact k73_prog_bound
  · exact hi

theorem k73_epilogue_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn) (hP : P.pcFree) :
    cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** P) := by
  have hbound : 4 * k73Frame.length < 2 ^ 64 := by
    simp [k73Frame]
  have hne : ∀ p ∈ k73Frame, p.1 ≠ .x0 := by
    intro p hp
    simp [k73Frame] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hload := loadSeq_spec_own k73Frame spH saved (K73 + 276) hbound hne
  have hloadC := cpsTripleWithin_extend_code k73_epilogue_load_mem hload
  have hloadF := cpsTripleWithin_frameR P hP hloadC
  have hadd := addi_spec_gen_same_within .x2 spH (56 : BitVec 12)
    (K73 + 300) (by decide)
  rw [hsp] at hadd
  have haddC := cpsTripleWithin_extend_code
    (k73_whole_mem 75 _ (K73 + 300) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hadd
  have haddF := cpsTripleWithin_frameR
    (regsAt k73Frame saved ** frameSlotsSaved k73Frame spH saved ** P)
    (pcFree_sepConj (pcFree_regsAt _ _)
      (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hP)) haddC
  have hloadAdd := cpsTripleWithin_seq_perm_same_cr (by xsimp) hloadF haddF
  have hReg : regsAt k73Frame saved =
      ((.x1 ↦ᵣ raIn) ** regsAt k73FrameRest1 saved) := by
    simp [k73Frame, k73FrameRest1, regsAt, hsaved]
  have hloadAdd' : cpsTripleWithin (k73Frame.length + 1) (K73 + 276)
      (K73 + 304) wholeCode
      (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved) ** P)
      (((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 saved **
        frameSlotsSaved k73Frame spH saved ** P)) := by
    apply cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      rw [hReg] at hq
      xperm_chunked hq) hloadAdd
  have hret0 := Fn.jalr_ret_spec (K73 + 304) raIn hret
    (P := (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 saved **
      frameSlotsSaved k73Frame spH saved)
    (pcFree_sepConj (pcFree_regIs (r := .x2) (v := sp0))
      (pcFree_sepConj (pcFree_regsAt k73FrameRest1 saved)
        (pcFree_frameSlotsSaved _ _ _)))
  have hretC := cpsTripleWithin_extend_code
    (k73_whole_mem 76 _ (K73 + 304) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hret0
  have hretF := cpsTripleWithin_frameR P hP hretC
  have hfull := cpsTripleWithin_seq_perm_same_cr (by xsimp) hloadAdd' hretF
  have hfull8 : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved) ** P)
      (((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 saved **
        frameSlotsSaved k73Frame spH saved) ** P) := by
    simpa [k73Frame] using hfull
  have hfull' := cpsTripleWithin_weaken
    (P := (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved) ** P))
    (Q := (((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** regsAt k73FrameRest1 saved **
      frameSlotsSaved k73Frame spH saved) ** P))
    (P' := ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved ** P))
    (Q' := ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
      frameSlotsSaved k73Frame spH saved ** P))
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp [hReg]
      xperm_chunked hq) hfull8
  exact hfull'

end EvmAsm.Codegen.HeaderBaseFeeSpec
