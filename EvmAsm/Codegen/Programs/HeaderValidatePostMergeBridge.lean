/-
  K67 `header_validate_post_merge` — the SpecRef correspondence bridge.

  The machine triple deliberately carries a complete status-0 guard rather than
  assuming that the caller's decoder has already done the work.  This bridge
  consumes that guard together with a successful `_decode_header` inversion.
  The decode-success premise is an explicit restriction: decoder-failure
  inputs are outside this theorem and require the status-4 correspondence.

  The only remaining non-computational premise is `EmptyOmmerHashPinned`, the
  named residual for the Keccak digest baked into the guest's data section.
  Keeping it visible is preferable to silently turning a literal drift pin into
  a cryptographic theorem.
-/

import EvmAsm.Codegen.Programs.HeaderValidatePostMergeFinal
import EvmAsm.Codegen.Programs.ChainValidatePostMergeFullSpec
import EvmAsm.Codegen.Programs.RlpDecodeFullyForward
import EvmAsm.Codegen.Programs.RlpWalkDeterminism
import EvmAsm.Stateless.SpecRef.Stateless

namespace EvmAsm.Codegen.HeaderValidatePostMergeCorrespondenceBridge

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

/-- Identify a model field with the bytes read by the machine at a known offset.

    The bounds are stated separately from the content equation so callers do
    not smuggle a length claim into a slice rewrite. -/
private theorem content_eq_target {α : Type} (xs p target : List α) (off len : Nat)
    (zero : α)
    (hcontent : (xs.drop off).take len = p)
    (hbound : off + len ≤ xs.length)
    (hp : p.length = len) (ht : target.length = len)
    (hget : ∀ k, k < len → xs.getD (off + k) zero = target.getD k zero) :
    p = target := by
  apply List.ext_getElem
  · rw [hp, ht]
  · intro i hiP hiT
    have hi : i < len := by rw [hp] at hiP; exact hiP
    have hxi : off + i < xs.length := by omega
    have hpi0 := congrArg (fun l => l[i]?) hcontent.symm
    change p[i]? = ((xs.drop off).take len)[i]? at hpi0
    rw [List.getElem?_eq_getElem hiP] at hpi0
    have hslicei : i < ((xs.drop off).take len).length := by
      rw [List.length_take, List.length_drop]
      omega
    rw [List.getElem?_eq_getElem hslicei, List.getElem_take, List.getElem_drop] at hpi0
    have hpi : p[i] = xs[off + i] := Option.some.inj hpi0
    have hxiD : xs.getD (off + i) zero = xs[off + i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxi]
      rfl
    have htiD : target.getD i zero = target[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiT]
      rfl
    calc
      p[i] = xs[off + i] := hpi
      _ = xs.getD (off + i) zero := hxiD.symm
      _ = target.getD i zero := hget i hi
      _ = target[i] := htiD

open EvmAsm.Stateless.SpecRef in
/-- **K67 status-0 correspondence.**

    This is the positive arm only: `hdec` restricts the theorem to inputs on
    which `_decode_header` succeeds.  Failure inputs are intentionally not
    hidden under this statement; their correspondence belongs to the status-4
    bridge.  The machine guard supplies the outer-list cursor relation, so the
    forward decoder facts and the machine walk are compared at the same start.

    `EmptyOmmerHashPinned` remains explicit because the guest data literal is
    pinned to bytes, while the equality to `SpecRef.EMPTY_OMMER_HASH` is the
    separate Keccak residual documented by `ChainValidatePostMergeFullSpec`.
    The named `k67GuardOk_constructive_witness` in
    `HeaderValidatePostMergeBridgeWitness` proves that the guard premise is
    inhabited by a canonical 23-field header. -/
theorem k67GuardOk_decode_header
    (base : Word) (bytes : Bytes) (hdr : Header)
    (hdec : _decode_header bytes = .ok hdr)
    (hguard : k67GuardOk base bytes)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hpin : ChainValidatePostMergeFullSpec.EmptyOmmerHashPinned) :
    ChainValidatePostMergeFullSpec.PostMergeHeaderOk bytes := by
  obtain ⟨items, bs, hfull, hlen, harity, hidx, hfields, hfixed⟩ := decode_header_inv hdec
  have hbytes_len : bytes.length < 2 ^ 64 := by omega
  have hover : base.toNat + bytes.length < 2 ^ 64 := by omega
  have hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q := by
    intro it hit
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hit
    exact ⟨bs.getD i [], by
      have hi' := hidx i hi
      rw [List.getElem?_eq_getElem hi, hget] at hi'
      exact Option.some.inj hi'⟩
  have hidx1 : 1 < items.length := by rcases harity with h | h <;> omega
  have hidx7 : 7 < items.length := by rcases harity with h | h <;> omega
  have hidx14 : 14 < items.length := by rcases harity with h | h <;> omega
  obtain ⟨off1, hsucc1, hcont1, hbound1⟩ :=
      success_content_of_decodeFully_list bytes base items 1 (bs.getD 1 [])
      hfull hbytes (hidx 1 hidx1) hover
  obtain ⟨off7, hsucc7, hcont7, hbound7⟩ :=
      success_content_of_decodeFully_list bytes base items 7 (bs.getD 7 [])
      hfull hbytes (hidx 7 hidx7) hover
  obtain ⟨off14, hsucc14, hcont14, hbound14⟩ :=
      success_content_of_decodeFully_list bytes base items 14 (bs.getD 14 [])
      hfull hbytes (hidx 14 hidx14) hover
  rcases hguard with ⟨startOff, cur14, next14, len14, n1, l1, n7,
    hcleanOuter, hlen14, hzeroNonce, hl1, hommers⟩
  rcases hcleanOuter with ⟨hclean, houter⟩
  rcases hclean with ⟨hprefix15, hitem1, hitem7, hitem14, hdecode14⟩
  rcases hsucc1 with ⟨cursor1, end1, modelNext1, hlist1, modelItem1, hoff1⟩
  rcases hsucc7 with ⟨cursor7, end7, modelNext7, hlist7, modelItem7, hoff7⟩
  rcases hsucc14 with ⟨cursor14, end14, modelNext14, hlist14, modelItem14, hoff14⟩
  have hdetOuter1 := RlpListNthItemSAsm.strictListPayload_deterministic houter hlist1
  have hdetOuter7 := RlpListNthItemSAsm.strictListPayload_deterministic houter hlist7
  have hdetOuter14 := RlpListNthItemSAsm.strictListPayload_deterministic houter hlist14
  rw [← hdetOuter1.1] at modelItem1
  rw [← hdetOuter7.1] at modelItem7
  rw [← hdetOuter14.1] at modelItem14
  rw [← hdetOuter1.2] at modelItem1
  rw [← hdetOuter7.2] at modelItem7
  rw [← hdetOuter14.2] at modelItem14
  have hdet1 := RlpListNthItemSAsm.strictNthItem_deterministic hitem1 modelItem1
  have hdet7 := RlpListNthItemSAsm.strictNthItem_deterministic hitem7 modelItem7
  have hdet14 := RlpListNthItemSAsm.strictNthItem_deterministic hitem14 modelItem14
  have hoff1' : off1 = n1 - l1 - base := by
    rw [hoff1, ← hdet1.1, ← hdet1.2]
  have hoff7' : off7 = n7 - (0 : Word) - base := by
    rw [hoff7, ← hdet7.1, ← hdet7.2]
  have hoff14' : off14 = next14 - len14 - base := by
    rw [hoff14, ← hdet14.1, ← hdet14.2]
  have hlen1 : (bs.getD 1 []).length = 32 :=
    hfixed.2 1 32 (by simp [fixedBytesFieldWidths])
  have hlen14field : (bs.getD 14 []).length = 8 :=
    hfixed.2 14 8 (by simp [fixedBytesFieldWidths])
  have htargetOmLen : k67OmBytes.length = 32 := by
    exact ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes_length
  have hOm : bs.getD 1 [] = k67OmBytes := by
    have hcont1' := hcont1
    have hbound1' := hbound1
    rw [hoff1'] at hcont1' hbound1'
    apply content_eq_target bytes (bs.getD 1 []) k67OmBytes
      (n1 - l1 - base).toNat (bs.getD 1 []).length (0 : BitVec 8)
      hcont1' hbound1' rfl (htargetOmLen.trans hlen1.symm)
    intro k hk
    have hk32 : k < 32 := by rw [← hlen1]; exact hk
    exact hommers k hk32
  have hNonce : bs.getD 14 [] = List.replicate 8 (0 : BitVec 8) := by
    have hcont14' := hcont14
    have hbound14' := hbound14
    rw [hoff14'] at hcont14' hbound14'
    apply content_eq_target bytes (bs.getD 14 []) (List.replicate 8 (0 : BitVec 8))
      (next14 - len14 - base).toNat (bs.getD 14 []).length (0 : BitVec 8)
      hcont14' hbound14' rfl (by rw [List.length_replicate, hlen14field])
    intro k hk
    have hk8 : k < 8 := by rw [← hlen14field]; exact hk
    have hz : (List.replicate 8 (0 : BitVec 8)).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk8)]
      exact List.getElem_replicate (by simpa using hk8)
    exact (hzeroNonce k hk8).trans hz.symm
  have hlen7lt : (bs.getD 7 []).length < 2 ^ 64 := by
    have hle : (bs.getD 7 []).length ≤ bytes.length := by
      have hs := congrArg List.length hcont7
      simp only [List.length_take, List.length_drop] at hs
      omega
    omega
  have hword7 : BitVec.ofNat 64 (bs.getD 7 []).length = (0 : Word) := by
    exact hdet7.2.symm
  have hlen7 : (bs.getD 7 []).length = 0 := by
    have ht := congrArg BitVec.toNat hword7
    have ht' : (bs.getD 7 []).length % 2 ^ 64 = 0 := by
      simp only [BitVec.toNat_ofNat] at ht
      exact ht
    rw [Nat.mod_eq_of_lt hlen7lt] at ht'
    exact ht'
  have hnil7 : bs.getD 7 [] = [] := List.eq_nil_of_length_eq_zero hlen7
  have hDifficulty : hdr.difficulty = 0 := by
    rw [hfields]
    change bytesBEtoNat (bs.getD 7 []) = 0
    rw [hnil7]
    rfl
  have hNonceHeader : hdr.nonce =
      List.replicate 8 (0 : EvmAsm.Stateless.SpecRef.Byte) := by
    rw [hfields]
    simpa [mkHeaderFields] using hNonce
  have hOmHeader : hdr.ommersHash = EMPTY_OMMER_HASH := by
    rw [hfields]
    change bs.getD 1 [] = EMPTY_OMMER_HASH
    exact hOm.trans (by simpa [k67OmBytes] using hpin.symm)
  exact ⟨hdr, hdec, hDifficulty, hNonceHeader, hOmHeader⟩

end EvmAsm.Codegen.HeaderValidatePostMergeCorrespondenceBridge
