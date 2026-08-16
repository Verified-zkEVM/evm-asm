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
import EvmAsm.Rv64.SAsm.AbiFrameCall
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

theorem k73_length : eip1559CalcBaseFeePerGas_prog.length = 77 := by decide

private theorem k73_prog_bound : 4 * prog.length < 2 ^ 64 := by
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

private theorem k73_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = K73 + BitVec.ofNat 64 (4 * k))
    (hk : k < prog.length)
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → k73Code a = some i := by
  intro a i hi
  exact CodeReq.ofProg_mem_at K73 A eip1559CalcBaseFeePerGas_prog k ins hA hk hins
    k73_prog_bound a i hi

private theorem k73_mono : ∀ a i, k73Code a = some i → fullCode a = some i := by
  intro a i hi
  exact CodeReq.union_mono_left a i hi

private theorem div_mono : ∀ a i, divCode a = some i → fullCode a = some i := by
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

private theorem k73_disjoint_setup_spec_within
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

private theorem k73_disjoint_setup_ordered_spec_within
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

end EvmAsm.Codegen.HeaderBaseFeeSpec
