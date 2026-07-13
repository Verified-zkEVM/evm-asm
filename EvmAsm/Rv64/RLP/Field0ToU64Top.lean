import EvmAsm.Rv64.RLP.Field0ToU64
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

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

end EvmAsm.Rv64.RLP
