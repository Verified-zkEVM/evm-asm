import EvmAsm.Rv64.RLP.Field0ToU64
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.StmtSoundCall

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.SAsm

/-! Completion of the caller-facing `rlp_field0_to_u64` theorem.  This is
split from `Field0ToU64.lean` so the leaf/call adapters remain below the core
file-size gate while the outcome-merging proof stays reviewable. -/

/-- A successful `rlp_walk_next` result, starting after the wrapper's status
branch, is transformed into the unified four-way scalar result. -/
theorem rlp_field0_to_u64_content_spec_within
    (base srcBase savedRa x1Val t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (advanced contentLen : Word) (srcOff len : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hlen64 : len < 2 ^ 64) (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hadvanced : advanced = srcBase + BitVec.ofNat 64 (srcOff + len))
    (hcontentLen : contentLen = BitVec.ofNat 64 len) :
    cpsTripleWithin (7 * len + 17) (base + 20) (savedRa &&& ~~~1)
      (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ advanced) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ contentLen) **
       (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
       (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
       (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
      (rlpField0ContentRest srcBase contentLen t4Old t5Old t6Old srcBytes srcOff len **
       (.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa)) := by
  subst hadvanced
  subst hcontentLen
  have hcp : (srcBase + BitVec.ofNat 64 (srcOff + len)) - BitVec.ofNat 64 len =
      srcBase + BitVec.ofNat 64 srcOff := by bv_omega
  have hsub0 := sub_spec_gen_rd_eq_rs1_within .x10 .x12
    (srcBase + BitVec.ofNat 64 (srcOff + len)) (BitVec.ofNat 64 len) (base + 20) (by decide)
  rw [hcp] at hsub0
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.SUB .x10 .x10 .x12) a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 5 (base + 20)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hA := cpsTripleWithin_extend_code hmono5 hsub0
  rw [show (base + 20 + 4 : Word) = base + 24 from by bv_omega] at hA
  have hA' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) **
      (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) ** bytesRegion srcBase srcBytes)
    (by pcFree) hA
  have hmv11 := mv_spec_gen_within .x11 .x12 (BitVec.ofNat 64 len) (0 : Word)
    (base + 24) (by decide)
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.MV .x11 .x12) a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 6 (base + 24)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hB := cpsTripleWithin_extend_code hmono6 hmv11
  rw [show (base + 24 + 4 : Word) = base + 28 from by bv_omega] at hB
  have hB' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x13 ↦ᵣ savedRa) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) **
      bytesRegion srcBase srcBytes)
    (by pcFree) hB
  have hmv6 := mv_spec_gen_within .x6 .x10 (srcBase + BitVec.ofNat 64 srcOff) t1Old
    (base + 28) (by decide)
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.MV .x6 .x10) a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 7 (base + 28)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hC := cpsTripleWithin_extend_code hmono7 hmv6
  rw [show (base + 28 + 4 : Word) = base + 32 from by bv_omega] at hC
  have hC' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ BitVec.ofNat 64 len) **
      (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ t0Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) **
      (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ x1Val) **
      bytesRegion srcBase srcBytes)
    (by pcFree) hC
  have hD := rlp_field0_to_u64_content_call_spec_within base srcBase savedRa x1Val
    t0Old (srcBase + BitVec.ofNat 64 srcOff) t2Old t3Old t4Old t5Old t6Old srcBytes
    (BitVec.ofNat 64 len) srcOff len hbase0 hlen64 hsalign hslen hsover hsvalid rfl
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA' hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC'
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s3)

#print axioms rlp_field0_to_u64_content_spec_within

/-- Successful first-item walk continuation, with the walk relation retained
as a pure semantic witness.  The bridge theorem converts the walk's word
outputs into the natural offset/length view required by the scalar callee. -/
theorem rlp_field0_to_u64_decode_success_exact_spec_within
    (base srcBase savedRa next len v5 v6 v7 v28 v29 v30 v31 : Word)
    (srcBytes : List (BitVec 8)) (itemOff endOff : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hoff : itemOff ≤ endOff)
    (hdecode : rlpItemDecode srcBytes itemOff
      (srcBase + BitVec.ofNat 64 itemOff)
      (srcBase + BitVec.ofNat 64 endOff) next len) :
    cpsTripleWithin (7 * len.toNat + 18) (base + 16) (savedRa &&& ~~~1)
      (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x1 ↦ᵣ (base + 16)) ** bytesRegion srcBase srcBytes)
      ((rlpField0ContentRest srcBase len v29 v30 v31 srcBytes
          (next - len - srcBase).toNat len.toNat **
        (.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa)) **
       ⌜rlpItemDecode srcBytes itemOff (srcBase + BitVec.ofNat 64 itemOff)
          (srcBase + BitVec.ofNat 64 endOff) next len⌝) := by
  have hspan := rlpItemDecode_field0_content_span hdecode hoff (by omega)
  have hlenWord : (BitVec.ofNat 64 len.toNat : Word) = len := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hadvanced : next = srcBase +
      BitVec.ofNat 64 ((next - len - srcBase).toNat + len.toNat) := by
    rcases hspan with ⟨hstart, _, hbound⟩
    rw [BitVec.ofNat_add]
    bv_omega
  have hslen : (next - len - srcBase).toNat + len.toNat ≤ srcBytes.length := by
    omega
  have hsover : srcBase.toNat +
      ((next - len - srcBase).toNat + len.toNat) ≤ 2 ^ 64 := by
    omega
  have hsvalid : ∀ k, k < len.toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64
        ((next - len - srcBase).toNat + k)) = true := by
    intro k hk
    exact hvalid _ (by omega)
  have hbr0 := bne_spec_gen_within .x11 .x0 (28 : BitVec 13)
    (0 : Word) (0 : Word) (base + 16)
  have hmono4 : ∀ a i,
      CodeReq.singleton (base + 16) (.BNE .x11 .x0 (28 : BitVec 13)) a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 4 (base + 16)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hbr := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x13 ↦ᵣ savedRa) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (.x1 ↦ᵣ (base + 16)) ** bytesRegion srcBase srcBytes)
    (by pcFree) (cpsBranchWithin_extend_code hmono4 hbr0)
  have hfall := cpsBranchWithin_ntakenPath hbr (fun h hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, _⟩ := hp
    exact h_ne rfl)
  rw [show (base + 16 + 4 : Word) = base + 20 from by bv_omega] at hfall
  have hcontent0 := rlp_field0_to_u64_content_spec_within base srcBase savedRa
    (base + 16) v5 v6 v7 v28 v29 v30 v31 srcBytes next len
    (next - len - srcBase).toNat len.toNat hbase0 len.isLt hsalign hslen hsover
    hsvalid hadvanced hlenWord.symm
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    extract_pure_deep hp
    obtain ⟨_, hp'⟩ := hp
    xperm_hyp hp') hfall hcontent0
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => (sepConj_pure_right h).2 ⟨hp, hdecode⟩) hseq)

#print axioms rlp_field0_to_u64_decode_success_exact_spec_within

/-- Caller-visible result after the first field has either been decoded by
the scalar routine or rejected by one of the strict walk checks. -/
def rlpField0Result (srcBase endPtr savedRa : Word)
    (srcBytes : List (BitVec 8)) : Assertion := fun h =>
  (∃ itemOff next len v29 v30 v31,
    ((rlpField0ContentRest srcBase len v29 v30 v31 srcBytes
        (next - len - srcBase).toNat len.toNat **
      (.x1 ↦ᵣ savedRa) ** (.x13 ↦ᵣ savedRa) **
      ⌜rlpItemDecode srcBytes itemOff (srcBase + BitVec.ofNat 64 itemOff)
        endPtr next len⌝) h)) ∨
  (∃ status,
    (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ status) ** bytesRegion srcBase srcBytes) **
      rlp_field0_to_u64_parse_fail_post savedRa) h))

/-- Eliminate the six-way `rlp_walk_next` post for fixed clobbered-register
values: the success arm runs the scalar continuation, while all five strict
walk failures use the shared public parse-failure tail. -/
theorem rlp_field0_to_u64_next_outcome_exact_spec_within
    (base srcBase savedRa v5 v6 v7 v28 v29 v30 v31 : Word)
    (srcBytes : List (BitVec 8)) (itemOff endOff : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hoff : itemOff ≤ endOff) :
    cpsTripleWithin (7 * (2 ^ 64 - 1) + 18) (base + 16)
      (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      (((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 16)) ** (.x13 ↦ᵣ savedRa) **
        bytesRegion srcBase srcBytes) **
       rlpField0NextOutcome srcBase (srcBase + BitVec.ofNat 64 endOff)
         srcBytes itemOff)
      (rlpField0Result srcBase (srcBase + BitVec.ofNat 64 endOff)
        savedRa srcBytes) := by
  let common : Assertion :=
    (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
    (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x1 ↦ᵣ (base + 16)) ** (.x13 ↦ᵣ savedRa) ** bytesRegion srcBase srcBytes
  let final := rlpField0Result srcBase (srcBase + BitVec.ofNat 64 endOff)
    savedRa srcBytes
  have hsuccessFamily : ∀ next len,
      cpsTripleWithin (7 * (2 ^ 64 - 1) + 18) (base + 16)
        (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
        (⌜rlpItemDecode srcBytes itemOff (srcBase + BitVec.ofNat 64 itemOff)
            (srcBase + BitVec.ofNat 64 endOff) next len⌝ **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** common))
        final := by
    intro next len
    refine cpsTripleWithin_pure_pre (fun hdecode => ?_)
    have hs := rlp_field0_to_u64_decode_success_exact_spec_within
      base srcBase savedRa next len v5 v6 v7 v28 v29 v30 v31 srcBytes
      itemOff endOff hbase0 hsalign hslack hover hvalid hoff hdecode
    refine cpsTripleWithin_mono_nSteps (by have := len.isLt; omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hp => ?_) hs)
    exact Or.inl ⟨itemOff, next, len, v29, v30, v31, by
      xperm_hyp hp⟩
  have hsuccess0 := cpsTripleWithin_exists_pre_gen (fun next =>
    cpsTripleWithin_exists_pre_gen (fun len => hsuccessFamily next len))
  have hsuccess : cpsTripleWithin (7 * (2 ^ 64 - 1) + 18) (base + 16)
      (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      (common ** rlpWalkNextOk (srcBase + BitVec.ofNat 64 itemOff)
        (srcBase + BitVec.ofNat 64 endOff) srcBytes itemOff) final :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold rlpWalkNextOk at hp
      obtain ⟨hc, hok, hd, hu, hcommon, next, len, hout⟩ := hp
      refine ⟨next, len, ?_⟩
      have hcombined : (common **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            ⌜rlpItemDecode srcBytes itemOff (srcBase + BitVec.ofNat 64 itemOff)
              (srcBase + BitVec.ofNat 64 endOff) next len⌝)) h :=
        ⟨hc, hok, hd, hu, hcommon, hout⟩
      xperm_hyp hcombined) (fun _ hp => hp) hsuccess0
  have hcommonOwned : ∀ h, common h →
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 16)) ** (.x13 ↦ᵣ savedRa) **
        bytesRegion srcBase srcBytes) h := by
    intro h hp
    exact sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7)
          (sepConj_mono (regIs_implies_regOwn .x28)
            (sepConj_mono (regIs_implies_regOwn .x29)
              (sepConj_mono (regIs_implies_regOwn .x30)
                (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x))))))) h hp
  have hfailure (status : Word) (hstatus : status ≠ 0) :
      cpsTripleWithin (7 * (2 ^ 64 - 1) + 18) (base + 16)
        (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
        (common ** ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 itemOff)) **
          (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)))) final := by
    have hf := rlp_field0_to_u64_next_failure_spec_within base savedRa
      (srcBase + BitVec.ofNat 64 itemOff) status (0 : Word) srcBase srcBytes hstatus
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by
        have hp'' := sepConj_mono_left hcommonOwned h hp
        xperm_hyp hp'') (fun h hp => ?_) hf)
    exact Or.inr ⟨0, hp⟩
  have h2 := hfailure (2 : Word) (by decide)
  have h3 := hfailure (3 : Word) (by decide)
  have h4 := hfailure (4 : Word) (by decide)
  have h5 := hfailure (5 : Word) (by decide)
  have h6 := hfailure (6 : Word) (by decide)
  have hall := cpsTripleWithin_pre_or hsuccess
    (cpsTripleWithin_pre_or h2
      (cpsTripleWithin_pre_or h3
        (cpsTripleWithin_pre_or h4 (cpsTripleWithin_pre_or h5 h6))))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hall
  unfold rlpField0NextOutcome at hp
  rcases hp with ⟨hc, ho, hd, hu, hcommon, hout⟩
  have dropGuard (status : Word) (guard : Prop) : ∀ h,
      (common ** ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 itemOff)) **
        (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)) ** ⌜guard⌝)) h →
      (common ** ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 itemOff)) **
        (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)))) h := by
    intro h hp
    extract_pure_deep hp
    obtain ⟨_, hp'⟩ := hp
    xperm_hyp hp'
  rcases hout with hout | hout | hout | hout | hout | hout
  · exact Or.inl ⟨hc, ho, hd, hu, hcommon, hout⟩
  · exact Or.inr (Or.inl (dropGuard 2 _ h ⟨hc, ho, hd, hu, hcommon, hout⟩))
  · exact Or.inr (Or.inr (Or.inl (dropGuard 3 _ h ⟨hc, ho, hd, hu, hcommon, hout⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (dropGuard 4 _ h ⟨hc, ho, hd, hu, hcommon, hout⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (dropGuard 5 _ h ⟨hc, ho, hd, hu, hcommon, hout⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (dropGuard 6 _ h ⟨hc, ho, hd, hu, hcommon, hout⟩)))))

#print axioms rlp_field0_to_u64_next_outcome_exact_spec_within

/-- Introduce the seven scratch-register values owned by the walk-next
continuation.  This local adapter keeps the generic SAsm framework unchanged. -/
private theorem field0_ownify7
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 r4 r5 r6 r7 : Reg} {P Q : Assertion}
    (hspec : ∀ v1 v2 v3 v4 v5 v6 v7, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact hspec v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

/-- The walk-next continuation consumes only ownership of its seven scratch
registers, matching the post exported by the call-composition theorem. -/
theorem rlp_field0_to_u64_next_outcome_spec_within
    (base srcBase savedRa : Word) (srcBytes : List (BitVec 8))
    (itemOff endOff : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hoff : itemOff ≤ endOff) :
    cpsTripleWithin (7 * (2 ^ 64 - 1) + 18) (base + 16)
      (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      (rlpField0NextCommon base srcBase savedRa srcBytes **
       rlpField0NextOutcome srcBase (srcBase + BitVec.ofNat 64 endOff)
         srcBytes itemOff)
      (rlpField0Result srcBase (srcBase + BitVec.ofNat 64 endOff)
        savedRa srcBytes) := by
  let P : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 16)) ** (.x13 ↦ᵣ savedRa) **
    bytesRegion srcBase srcBytes **
    rlpField0NextOutcome srcBase (srcBase + BitVec.ofNat 64 endOff)
      srcBytes itemOff
  have hs : ∀ v5 v6 v7 v28 v29 v30 v31,
      cpsTripleWithin (7 * (2 ^ 64 - 1) + 18) (base + 16)
        (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
        (P ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
         (.x31 ↦ᵣ v31))
        (rlpField0Result srcBase (srcBase + BitVec.ofNat 64 endOff)
          savedRa srcBytes) := by
    intro v5 v6 v7 v28 v29 v30 v31
    exact cpsTripleWithin_weaken (fun h hp => by
      dsimp only [P] at hp
      xperm_hyp hp) (fun _ hp => hp)
      (rlp_field0_to_u64_next_outcome_exact_spec_within
        base srcBase savedRa v5 v6 v7 v28 v29 v30 v31 srcBytes
        itemOff endOff hbase0 hsalign hslack hover hvalid hoff)
  have ho := field0_ownify7
    (r1 := .x5) (r2 := .x6) (r3 := .x7) (r4 := .x28)
    (r5 := .x29) (r6 := .x30) (r7 := .x31) hs
  exact cpsTripleWithin_weaken (fun h hp => by
    unfold rlpField0NextCommon rlpField0NextCalleeCommon at hp
    dsimp only [P]
    xperm_hyp hp) (fun _ hp => hp) ho

#print axioms rlp_field0_to_u64_next_outcome_spec_within

end EvmAsm.Rv64.RLP
