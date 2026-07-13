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

/-- Compose the successful init fallthrough with the complete walk-next and
scalar continuation, from the wrapper's status branch through final return. -/
theorem rlp_field0_to_u64_after_init_success_spec_within
    (base srcBase savedRa v5 v6 v7 v28 v29 v30 v31 oldRa : Word)
    (srcBytes : List (BitVec 8)) (itemOff endOff : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hoff : itemOff ≤ endOff) :
    cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18)) (base + 8)
      (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 itemOff)) **
       (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 endOff)) **
       (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ oldRa) **
       bytesRegion srcBase srcBytes)
      (rlpField0Result srcBase (srcBase + BitVec.ofNat 64 endOff)
        savedRa srcBytes) := by
  have hcall := rlp_field0_to_u64_walk_next_call_spec_within
    base srcBase savedRa (srcBase + BitVec.ofNat 64 endOff)
    v5 v6 v7 v28 v29 v30 v31 oldRa srcBytes itemOff endOff
    hbase0 hsalign hslack hover hvalid hoff
  have hcont := rlp_field0_to_u64_next_outcome_spec_within
    base srcBase savedRa srcBytes itemOff endOff hbase0 hsalign hslack
    hover hvalid hoff
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hcall hcont

#print axioms rlp_field0_to_u64_after_init_success_spec_within

/-- Ownership-only form of the successful-init continuation, matching the
scratch ownership returned by `rlp_walk_init`. -/
theorem rlp_field0_to_u64_after_init_success_owned_spec_within
    (base srcBase savedRa : Word) (srcBytes : List (BitVec 8))
    (itemOff endOff : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : endOff + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (hoff : itemOff ≤ endOff) :
    cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18)) (base + 8)
      (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (base + 8)) ** bytesRegion srcBase srcBytes) **
       ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 itemOff)) **
        (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 endOff)) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa)))
      (rlpField0Result srcBase (srcBase + BitVec.ofNat 64 endOff)
        savedRa srcBytes) := by
  let P : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 8)) **
    bytesRegion srcBase srcBytes **
    (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 itemOff)) **
    (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 endOff)) **
    (.x12 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ savedRa)
  have hs : ∀ v5 v6 v7 v28 v29 v30 v31,
      cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18)) (base + 8)
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
      (rlp_field0_to_u64_after_init_success_spec_within
        base srcBase savedRa v5 v6 v7 v28 v29 v30 v31 (base + 8)
        srcBytes itemOff endOff hbase0 hsalign hslack hover hvalid hoff)
  have ho := field0_ownify7
    (r1 := .x5) (r2 := .x6) (r3 := .x7) (r4 := .x28)
    (r5 := .x29) (r6 := .x30) (r7 := .x31) hs
  exact cpsTripleWithin_weaken (fun h hp => by
    dsimp only [P]
    xperm_hyp hp) (fun _ hp => hp) ho

#print axioms rlp_field0_to_u64_after_init_success_owned_spec_within

/-- Resources common to all nine strict walk-init outcomes at wrapper index 2. -/
def rlpField0InitCommon (base srcBase savedRa : Word)
    (srcBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  (.x1 ↦ᵣ (base + 8)) ** bytesRegion srcBase srcBytes **
  (.x13 ↦ᵣ savedRa)

/-- Exact nine-way post exported by `rlp_walk_init`, specialized to a list at
offset zero.  Keeping the guards preserves the strict emitted semantics. -/
def rlpField0InitOutcome (srcBase : Word) (srcBytes : List (BitVec 8))
    (listLen : Nat) (hoff : 0 < srcBytes.length) : Assertion := fun h =>
  (((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
    ⌜BitVec.ofNat 64 listLen = (0 : Word)⌝) h) ∨
  (((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (1 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
  (((.x10 ↦ᵣ (srcBase + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)) = srcBase + BitVec.ofNat 64 listLen⌝) h) ∨
  (((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (3 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)) ≠ srcBase + BitVec.ofNat 64 listLen⌝) h) ∨
  (((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (4 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
        (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true⌝) h) ∨
  (((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (5 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
        (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧
      srcBytes[1]? = some (0 : BitVec 8)⌝) h) ∨
  (((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (6 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
        (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧
      srcBytes[1]? ≠ some (0 : BitVec 8) ∧
      BitVec.ult (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
        (56 : Word) = true⌝) h) ∨
  (((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (7 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
        (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧
      srcBytes[1]? ≠ some (0 : BitVec 8) ∧
      ¬ BitVec.ult (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
        (56 : Word) = true ∧
      srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE ((srcBytes.drop 1).take
          ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) ≠
        srcBase + BitVec.ofNat 64 listLen⌝) h) ∨
  (((.x10 ↦ᵣ (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12)))) **
    (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
        (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧
      srcBytes[1]? ≠ some (0 : BitVec 8) ∧
      ¬ BitVec.ult (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
        (56 : Word) = true ∧
      srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE ((srcBytes.drop 1).take
          ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) =
        srcBase + BitVec.ofNat 64 listLen⌝) h)

/-- Call `rlp_walk_init` from wrapper index 1 and expose its exact nine-way
post together with the saved outer return address. -/
theorem rlp_field0_to_u64_init_call_spec_within
    (base srcBase savedRa indexW v5 v6 v7 v28 v29 v30 v31 oldRa : Word)
    (srcBytes : List (BitVec 8)) (listLen : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 82 (base + 4) (base + 8)
      (rlp_field0_to_u64_full_code base)
      ((.x1 ↦ᵣ oldRa) ** (.x10 ↦ᵣ srcBase) **
       (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      (rlpField0InitCommon base srcBase savedRa srcBytes **
       rlpField0InitOutcome srcBase srcBytes listLen (by omega)) := by
  have hoff : 0 < srcBytes.length := by omega
  have hwi := rlp_walk_init_spec_within (base + (256 : Word)) srcBase
    (base + 8) (BitVec.ofNat 64 listLen) indexW v5 v6 v7 v28 v29 v30 v31
    srcBytes 0 hsalign hoff (by omega) (hvalid 0 hoff)
    (fun hf8 => by
      have hb := (srcBytes[0]'hoff).isLt
      simp only [BitVec.ult, decide_eq_true_eq] at hf8
      have hlo : ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        bv_omega
      omega)
    (fun hf8 => by
      have hb := (srcBytes[0]'hoff).isLt
      simp only [BitVec.ult, decide_eq_true_eq] at hf8
      have hlo : ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        bv_omega
      omega)
    (fun hf8 => by
      intro k hk
      have hb := (srcBytes[0]'hoff).isLt
      simp only [BitVec.ult, decide_eq_true_eq] at hf8
      have hlo : ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        bv_omega
      exact hvalid _ (by omega))
  rw [show srcBase + BitVec.ofNat 64 0 = srcBase from by bv_omega] at hwi
  have hwiF := cpsTripleWithin_frameR ((.x13 ↦ᵣ savedRa)) (by pcFree) hwi
  let Prest : Assertion :=
    (.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
    (.x12 ↦ᵣ indexW) ** (.x13 ↦ᵣ savedRa) ** (.x5 ↦ᵣ v5) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
    (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes
  let Q : Assertion := rlpField0InitCommon base srcBase savedRa srcBytes **
    rlpField0InitOutcome srcBase srcBytes listLen hoff
  have hwi' : cpsTripleWithin 81 (base + (256 : Word))
      ((base + 8) &&& ~~~(1 : Word))
      (rlp_walk_init_code (base + (256 : Word)))
      ((.x1 ↦ᵣ (base + 8)) ** Prest) Q :=
    cpsTripleWithin_weaken (fun h hp => by
      dsimp only [Prest] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      dsimp only [Q]
      unfold rlpField0InitCommon rlpField0InitOutcome
      simp only [Nat.zero_add] at hp ⊢
      xperm_hyp hp) hwiF
  have hwiCall : cpsTripleWithin 81 (base + (256 : Word))
      ((base + 4 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code (base + (256 : Word)))
      ((.x1 ↦ᵣ (base + 4 + 4)) ** Prest) Q := by
    simpa only [show (base + 4 + 4 : Word) = base + 8 from by bv_omega] using hwi'
  exact cpsTripleWithin_weaken (fun h hp => by
    dsimp only [Prest]
    xperm_hyp hp) (fun h hp => by
      change Q h at hp
      exact hp)
    (rlp_field0_to_u64_call_walk_init (nSteps := 81) (Prest := Prest) (Q := Q)
      base oldRa hbase0 (by
      show Prest.pcFree
      dsimp only [Prest]
      pcFree) hwiCall)

#print axioms rlp_field0_to_u64_init_call_spec_within

/-- Eliminate all nine strict walk-init outcomes: seven failures normalize to
public status 1, while the short- and long-list successes continue at field 0. -/
theorem rlp_field0_to_u64_init_outcome_spec_within
    (base srcBase savedRa : Word) (srcBytes : List (BitVec 8))
    (listLen : Nat) (hoff : 0 < srcBytes.length)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18)) (base + 8)
      (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      (rlpField0InitCommon base srcBase savedRa srcBytes **
       rlpField0InitOutcome srcBase srcBytes listLen hoff)
      (rlpField0Result srcBase (srcBase + BitVec.ofNat 64 listLen)
        savedRa srcBytes) := by
  let common := rlpField0InitCommon base srcBase savedRa srcBytes
  let final := rlpField0Result srcBase (srcBase + BitVec.ofNat 64 listLen)
    savedRa srcBytes
  have hfailure (status cursor endPtr : Word) (guard : Prop)
      (hstatus : status ≠ 0) :
      cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18)) (base + 8)
        (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
        (common ** ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ status) ** ⌜guard⌝)) final := by
    have hf := rlp_field0_to_u64_init_failure_spec_within
      base savedRa cursor endPtr status srcBase srcBytes hstatus
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by
        extract_pure_deep hp
        obtain ⟨_, hp'⟩ := hp
        unfold common rlpField0InitCommon at hp'
        xperm_hyp hp') (fun h hp => ?_) hf)
    exact Or.inr ⟨status, hp⟩
  have hf2 := hfailure (2 : Word) srcBase (0 : Word)
    (BitVec.ofNat 64 listLen = (0 : Word)) (by decide)
  have hf1 := hfailure (1 : Word) srcBase
    (srcBase + BitVec.ofNat 64 listLen)
    (BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (by decide)
  let shortGuard : Prop :=
    BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
      signExtend12 (1 : BitVec 12)) = srcBase + BitVec.ofNat 64 listLen
  have hshort0 : shortGuard →
      cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18)) (base + 8)
        (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
        (common ** ((.x10 ↦ᵣ (srcBase + signExtend12 (1 : BitVec 12))) **
          (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
          (.x12 ↦ᵣ (0 : Word)))) final := by
    intro hg
    have hlen64 : listLen < 2 ^ 64 := by omega
    have hlenPos : 1 ≤ listLen := by
      by_contra h
      have hz : listLen = 0 := by omega
      subst listLen
      exact hg.1 rfl
    have hs := rlp_field0_to_u64_after_init_success_owned_spec_within
      base srcBase savedRa srcBytes 1 listLen hbase0 hsalign hslack hover
      hvalid hlenPos
    refine cpsTripleWithin_weaken (fun h hp => by
      unfold common rlpField0InitCommon at hp
      rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide] at hp
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun _ hp => hp) hs
  have hshort : cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18))
      (base + 8) (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      (common ** ((.x10 ↦ᵣ (srcBase + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
        (.x12 ↦ᵣ (0 : Word)) ** ⌜shortGuard⌝)) final :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold shortGuard
      xperm_hyp hp) (fun _ hp => hp)
    (cpsTripleWithin_pure_pre hshort0)
  let g3 : Prop :=
    BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
      signExtend12 (1 : BitVec 12)) ≠ srcBase + BitVec.ofNat 64 listLen
  have hf3 := hfailure (3 : Word) srcBase
    (srcBase + BitVec.ofNat 64 listLen) g3 (by decide)
  let g4 : Prop :=
    BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
      (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true
  have hf4 := hfailure (4 : Word) srcBase
    (srcBase + BitVec.ofNat 64 listLen) g4 (by decide)
  let g5 : Prop :=
    BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
      (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true ∧
    srcBytes[1]? = some (0 : BitVec 8)
  have hf5 := hfailure (5 : Word) srcBase
    (srcBase + BitVec.ofNat 64 listLen) g5 (by decide)
  let g6 : Prop :=
    BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
      (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true ∧
    srcBytes[1]? ≠ some (0 : BitVec 8) ∧
    BitVec.ult (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
      ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
      (56 : Word) = true
  have hf6 := hfailure (6 : Word) srcBase
    (srcBase + BitVec.ofNat 64 listLen) g6 (by decide)
  let g7 : Prop :=
    BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
      (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true ∧
    srcBytes[1]? ≠ some (0 : BitVec 8) ∧
    ¬ BitVec.ult (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
      ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
      (56 : Word) = true ∧
    srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12)) +
      BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) ≠
      srcBase + BitVec.ofNat 64 listLen
  have hf7 := hfailure (7 : Word) srcBase
    (srcBase + BitVec.ofNat 64 listLen) g7 (by decide)
  let cursorOff := 1 +
    ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
  let longGuard : Prop :=
    BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
    ¬ BitVec.ult ((srcBytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
    ¬ BitVec.ult (srcBase + BitVec.ofNat 64 listLen)
      (srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true ∧
    srcBytes[1]? ≠ some (0 : BitVec 8) ∧
    ¬ BitVec.ult (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
      ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
      (56 : Word) = true ∧
    srcBase + (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12)) +
      BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE ((srcBytes.drop 1).take
        ((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) =
      srcBase + BitVec.ofNat 64 listLen
  have hlong0 : longGuard →
      cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18)) (base + 8)
        (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
        (common ** ((.x10 ↦ᵣ (srcBase +
          (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12)))) **
          (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
          (.x12 ↦ᵣ (0 : Word)))) final := by
    intro hg
    unfold longGuard at hg
    have hb := (srcBytes[0]'hoff).isLt
    have hnlt248 := hg.2.2.1
    have hge : 0xf8 ≤ ((srcBytes[0]'hoff).zeroExtend 64).toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hnlt248
      bv_omega
    have hcursorBound : cursorOff ≤ 9 := by
      unfold cursorOff
      bv_omega
    have hcur : srcBase +
        (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) =
        srcBase + BitVec.ofNat 64 cursorOff := by
      unfold cursorOff
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    have hcursorLe : cursorOff ≤ listLen := by
      have hnltCursor := hg.2.2.2.1
      simp only [BitVec.ult, decide_eq_true_eq] at hnltCursor
      have hendNoWrap : srcBase.toNat + listLen < 2 ^ 64 := by omega
      have hcursorNoWrap : srcBase.toNat + cursorOff < 2 ^ 64 := by omega
      rw [hcur] at hnltCursor
      bv_omega
    have hs := rlp_field0_to_u64_after_init_success_owned_spec_within
      base srcBase savedRa srcBytes cursorOff listLen hbase0 hsalign hslack
      hover hvalid hcursorLe
    refine cpsTripleWithin_weaken (fun h hp => by
      unfold common rlpField0InitCommon at hp
      rw [hcur] at hp
      xperm_hyp hp)
      (fun _ hp => hp) hs
  have hlong : cpsTripleWithin (89 + (7 * (2 ^ 64 - 1) + 18))
      (base + 8) (savedRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      (common ** ((.x10 ↦ᵣ (srcBase +
        (((srcBytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ (srcBase + BitVec.ofNat 64 listLen)) **
        (.x12 ↦ᵣ (0 : Word)) ** ⌜longGuard⌝)) final :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold longGuard
      xperm_hyp hp) (fun _ hp => hp)
    (cpsTripleWithin_pure_pre hlong0)
  have hall := cpsTripleWithin_pre_or hf2
    (cpsTripleWithin_pre_or hf1
      (cpsTripleWithin_pre_or hshort
        (cpsTripleWithin_pre_or hf3
          (cpsTripleWithin_pre_or hf4
            (cpsTripleWithin_pre_or hf5
              (cpsTripleWithin_pre_or hf6
                (cpsTripleWithin_pre_or hf7 hlong)))))))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hall
  unfold rlpField0InitOutcome at hp
  unfold common rlpField0InitCommon
  rcases hp with ⟨h1, h2, hd, hu, hc, hout⟩
  rcases hout with hout | hout | hout | hout | hout | hout | hout | hout | hout
  · exact Or.inl ⟨h1, h2, hd, hu, hc, hout⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hd, hu, hc, hout⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hd, hu, hc, hout⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, hd, hu, hc, hout⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨h1, h2, hd, hu, hc, hout⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨h1, h2, hd, hu, hc, hout⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨h1, h2, hd, hu, hc, hout⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨h1, h2, hd, hu, hc, hout⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨h1, h2, hd, hu, hc, hout⟩)))))))

#print axioms rlp_field0_to_u64_init_outcome_spec_within

/-- Caller-facing unified specification for the complete emitted
`rlp_field0_to_u64` wrapper.  The postcondition reports either a strict parse
failure or the decoded field-0 scalar and its exact source span. -/
theorem rlp_field0_to_u64_spec_within
    (base srcBase callerRa indexW old13 v5 v6 v7 v28 v29 v30 v31 : Word)
    (srcBytes : List (BitVec 8)) (listLen : Nat)
    (hbase0 : base &&& (1 : Word) = 0)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ srcBytes.length)
    (hover : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (82 + (89 + (7 * (2 ^ 64 - 1) + 18)))) base
      (callerRa &&& ~~~1) (rlp_field0_to_u64_full_code base)
      ((.x1 ↦ᵣ callerRa) ** (.x10 ↦ᵣ srcBase) **
       (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ old13) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      (rlpField0Result srcBase (srcBase + BitVec.ofNat 64 listLen)
        callerRa srcBytes) := by
  have hsave0 := mv_spec_gen_within .x13 .x1 callerRa old13 base (by decide)
  have hmono0 : ∀ a i, CodeReq.singleton base (.MV .x13 .x1) a = some i →
      rlp_field0_to_u64_full_code base a = some i :=
    fun a i h => CodeReq.union_mono_left a i (CodeReq.union_mono_left a i
      (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr base rlp_field0_to_u64_prog 0 base
          (by rw [rlp_field0_to_u64_prog_length]; norm_num)
          (by rw [rlp_field0_to_u64_prog_length]; norm_num) (by bv_omega)) a i h))
  have hsave := cpsTripleWithin_extend_code hmono0 hsave0
  have hsaveF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ srcBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
      (.x12 ↦ᵣ indexW) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes) (by pcFree) hsave
  have hinit := rlp_field0_to_u64_init_call_spec_within
    base srcBase callerRa indexW v5 v6 v7 v28 v29 v30 v31 callerRa
    srcBytes listLen hbase0 hsalign hslack hover hvalid
  have hcont := rlp_field0_to_u64_init_outcome_spec_within
    base srcBase callerRa srcBytes listLen (by omega) hbase0 hsalign hslack
    hover hvalid
  have hafter := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hinit hcont
  have hsave' : cpsTripleWithin 1 base (base + 4)
      (rlp_field0_to_u64_full_code base)
      ((.x1 ↦ᵣ callerRa) ** (.x10 ↦ᵣ srcBase) **
       (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ old13) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      ((.x1 ↦ᵣ callerRa) ** (.x10 ↦ᵣ srcBase) **
       (.x11 ↦ᵣ BitVec.ofNat 64 listLen) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ callerRa) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes) :=
    cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) hsaveF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hsave' hafter

#print axioms rlp_field0_to_u64_spec_within

end EvmAsm.Rv64.RLP
