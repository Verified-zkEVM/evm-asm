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

private theorem content_getD_of_slice {α : Type} (xs p : List α) (off len : Nat)
    (zero : α)
    (hcontent : (xs.drop off).take len = p)
    (hbound : off + len ≤ xs.length) (hp : p.length = len) :
    ∀ k, k < len → xs.getD (off + k) zero = p.getD k zero := by
  intro k hk
  have hxi : off + k < xs.length := by omega
  have hpi0 := congrArg (fun l => l[k]?) hcontent.symm
  change p[k]? = ((xs.drop off).take len)[k]? at hpi0
  have hkp : k < p.length := by rw [hp]; exact hk
  rw [List.getElem?_eq_getElem hkp] at hpi0
  have hslicei : k < ((xs.drop off).take len).length := by
    rw [List.length_take, List.length_drop]
    omega
  rw [List.getElem?_eq_getElem hslicei, List.getElem_take, List.getElem_drop] at hpi0
  have hpi : p[k] = xs[off + k] := Option.some.inj hpi0
  have hxiD : xs.getD (off + k) zero = xs[off + k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxi]
    rfl
  have hpiD : p.getD k zero = p[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkp]
    rfl
  calc
    xs.getD (off + k) zero = xs[off + k] := hxiD
    _ = p[k] := hpi.symm
    _ = p.getD k zero := hpiD.symm

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

open EvmAsm.Stateless.SpecRef in
/-- **K67 status-1 correspondence (difficulty).**

    The difficulty arm is only meaningful with the authenticated outer-list
    relation retained at the K+604 station.  The decoder inversion supplies
    canonicality for field 7; together with the machine's nonzero length this
    rules out the zero scalar, rather than assuming a width bound that the
    reference does not impose. -/
theorem k67GuardDiff_decode_header
    (base : Word) (bytes : Bytes) (hdr : Header)
    (hdec : _decode_header bytes = .ok hdr)
    (hguard : k67GuardDiff base bytes)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64) :
    hdr.difficulty ≠ 0 := by
  obtain ⟨items, bs, hfull, hlen, harity, hidx, hfields, hfixed⟩ :=
    decode_header_inv hdec
  have hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q := by
    intro it hit
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hit
    exact ⟨bs.getD i [], by
      have hi' := hidx i hi
      rw [List.getElem?_eq_getElem hi, hget] at hi'
      exact Option.some.inj hi'⟩
  have hidx7 : 7 < items.length := by
    rcases harity with h | h <;> omega
  obtain ⟨off7, hsucc7, hcont7, hbound7⟩ :=
    success_content_of_decodeFully_list bytes base items 7 (bs.getD 7 [])
      hfull hbytes (hidx 7 hidx7) (by omega)
  rcases hguard with ⟨startOff, cur, omEnd, omLen, next7, len7, n1, l1,
    houter, hprefix7, hitem7, hlen7ne, hitem1, homEnd, homLen, hcur⟩
  rcases hsucc7 with ⟨cursor7, end7, modelNext7, hlist7, modelItem7, hoff7⟩
  have hdetOuter7 := RlpListNthItemSAsm.strictListPayload_deterministic houter hlist7
  rw [← hdetOuter7.1] at modelItem7
  rw [← hdetOuter7.2] at modelItem7
  have hdet7 := RlpListNthItemSAsm.strictNthItem_deterministic hitem7 modelItem7
  have hlenEq : len7 = BitVec.ofNat 64 (bs.getD 7 []).length := hdet7.2
  have hlenBytes : (bs.getD 7 []).length ≠ 0 := by
    intro hzero
    apply hlen7ne
    rw [hlenEq, hzero]
    rfl
  rw [hfields]
  change bytesBEtoNat (bs.getD 7 []) ≠ 0
  have hcanon := hfixed.1 7 none (by simp [numericFieldWidths])
  cases hp : bs.getD 7 [] with
  | nil =>
      have hlen0 : (bs.getD 7 []).length = 0 := by rw [hp]; rfl
      have hfalse : False := hlenBytes hlen0
      exact hfalse.elim
  | cons b tl =>
      apply Nat.ne_of_gt
      apply EvmAsm.EL.RLP.Nat.fromBytesBE_pos_of_head_ne_zero b tl
      apply hcanon.1 b
      rw [hp]
      rfl

open EvmAsm.Stateless.SpecRef in
/-- **K67 status-2 correspondence (nonce).**  The clean machine walk and its
    field-14 content relation make the decoder's nonce bytes the same bytes
    tested by the guard; the two alternatives in `k67GuardNonce` are therefore
    both incompatible with a canonical zero nonce. -/
theorem k67GuardNonce_decode_header
    (base : Word) (bytes : Bytes) (hdr : Header)
    (hdec : _decode_header bytes = .ok hdr)
    (hguard : k67GuardNonce base bytes)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64) :
    hdr.nonce ≠ List.replicate 8 (0 : EvmAsm.Stateless.SpecRef.Byte) := by
  obtain ⟨items, bs, hfull, hlen, harity, hidx, hfields, hfixed⟩ :=
    decode_header_inv hdec
  have hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q := by
    intro it hit
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hit
    exact ⟨bs.getD i [], by
      have hi' := hidx i hi
      rw [List.getElem?_eq_getElem hi, hget] at hi'
      exact Option.some.inj hi'⟩
  have hidx14 : 14 < items.length := by
    rcases harity with h | h <;> omega
  obtain ⟨off14, hsucc14, hcont14, hbound14⟩ :=
    success_content_of_decodeFully_list bytes base items 14 (bs.getD 14 [])
      hfull hbytes (hidx 14 hidx14) (by omega)
  rcases hguard with ⟨startOff, cur14, next14, len14, n1, l1, n7,
    hcleanOuter, hbad⟩
  rcases hcleanOuter with ⟨hclean, houter⟩
  rcases hclean with ⟨hprefix15, hitem1, hitem7, hitem14, hdecode14⟩
  rcases hsucc14 with ⟨cursor14, end14, modelNext14, hlist14, modelItem14, hoff14⟩
  have hdetOuter14 := RlpListNthItemSAsm.strictListPayload_deterministic houter hlist14
  rw [← hdetOuter14.1] at modelItem14
  rw [← hdetOuter14.2] at modelItem14
  have hdet14 := RlpListNthItemSAsm.strictNthItem_deterministic hitem14 modelItem14
  have hoff14' : off14 = next14 - len14 - base := by
    rw [hoff14, ← hdet14.1, ← hdet14.2]
  have hlen14field : (bs.getD 14 []).length = 8 :=
    hfixed.2 14 8 (by simp [fixedBytesFieldWidths])
  intro hnonce
  have hmodelNonce : bs.getD 14 [] =
      List.replicate 8 (0 : EvmAsm.Stateless.SpecRef.Byte) := by
    rw [hfields] at hnonce
    simpa [mkHeaderFields] using hnonce
  have hcont14' := hcont14
  have hbound14' := hbound14
  rw [hoff14'] at hcont14' hbound14'
  have hgetModel : ∀ k, k < (bs.getD 14 []).length →
      bytes.getD ((next14 - len14 - base).toNat + k) (0 : BitVec 8) =
        (bs.getD 14 []).getD k 0 := by
    intro k hk
    exact content_getD_of_slice bytes (bs.getD 14 [])
      (next14 - len14 - base).toNat (bs.getD 14 []).length (0 : BitVec 8)
      hcont14' hbound14' rfl k hk
  rcases hbad with hlenBad | ⟨k, hk, hneq⟩
  · apply hlenBad
    rw [hdet14.2, hlen14field]
    rfl
  · apply hneq
    have hk' : k < (bs.getD 14 []).length := by
      rw [hlen14field]
      exact hk
    have hget := hgetModel k hk'
    rw [hmodelNonce] at hget
    have hz :
        (List.replicate 8 (0 : EvmAsm.Stateless.SpecRef.Byte)).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk)]
      exact List.getElem_replicate (by simpa using hk)
    exact hget.trans hz

open EvmAsm.Stateless.SpecRef in
/-- **K67 status-3 correspondence (ommers hash).**  The field-1 walk is
    compared against the same pinned bytes used by the machine.  The explicit
    `EmptyOmmerHashPinned` premise is the existing data-section digest bridge;
    it is not folded into the decoder or the walk guard. -/
theorem k67GuardOmmers_decode_header
    (base : Word) (bytes : Bytes) (hdr : Header)
    (hdec : _decode_header bytes = .ok hdr)
    (hguard : k67GuardOmmers base bytes)
    (hover9 : base.toNat + bytes.length + 9 < 2 ^ 64)
    (hpin : ChainValidatePostMergeFullSpec.EmptyOmmerHashPinned) :
    hdr.ommersHash ≠ EMPTY_OMMER_HASH := by
  obtain ⟨items, bs, hfull, hlen, harity, hidx, hfields, hfixed⟩ :=
    decode_header_inv hdec
  have hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q := by
    intro it hit
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hit
    exact ⟨bs.getD i [], by
      have hi' := hidx i hi
      rw [List.getElem?_eq_getElem hi, hget] at hi'
      exact Option.some.inj hi'⟩
  have hidx1 : 1 < items.length := by
    rcases harity with h | h <;> omega
  obtain ⟨off1, hsucc1, hcont1, hbound1⟩ :=
    success_content_of_decodeFully_list bytes base items 1 (bs.getD 1 [])
      hfull hbytes (hidx 1 hidx1) (by omega)
  rcases hguard with ⟨startOff, cur14, next14, len14, n1, l1, n7,
    hcleanOuter, hbad⟩
  rcases hcleanOuter with ⟨hclean, houter⟩
  rcases hclean with ⟨hprefix15, hitem1, hitem7, hitem14, hdecode14⟩
  rcases hsucc1 with ⟨cursor1, end1, modelNext1, hlist1, modelItem1, hoff1⟩
  have hdetOuter1 := RlpListNthItemSAsm.strictListPayload_deterministic houter hlist1
  rw [← hdetOuter1.1] at modelItem1
  rw [← hdetOuter1.2] at modelItem1
  have hdet1 := RlpListNthItemSAsm.strictNthItem_deterministic hitem1 modelItem1
  have hoff1' : off1 = n1 - l1 - base := by
    rw [hoff1, ← hdet1.1, ← hdet1.2]
  have hlen1field : (bs.getD 1 []).length = 32 :=
    hfixed.2 1 32 (by simp [fixedBytesFieldWidths])
  intro hommers
  have hmodelOm : bs.getD 1 [] = EMPTY_OMMER_HASH := by
    rw [hfields] at hommers
    simpa [mkHeaderFields] using hommers
  have hmodelOmBytes : bs.getD 1 [] = k67OmBytes := by
    exact hmodelOm.trans (by
      simpa [ChainValidatePostMergeFullSpec.EmptyOmmerHashPinned, k67OmBytes]
        using hpin)
  have hcont1' := hcont1
  have hbound1' := hbound1
  rw [hoff1'] at hcont1' hbound1'
  have hgetModel : ∀ k, k < (bs.getD 1 []).length →
      bytes.getD ((n1 - l1 - base).toNat + k) (0 : BitVec 8) =
        (bs.getD 1 []).getD k 0 := by
    intro k hk
    exact content_getD_of_slice bytes (bs.getD 1 [])
      (n1 - l1 - base).toNat (bs.getD 1 []).length (0 : BitVec 8)
      hcont1' hbound1' rfl k hk
  rcases hbad with hlenBad | ⟨k, hk, hneq⟩
  · apply hlenBad
    rw [hdet1.2, hlen1field]
    rfl
  · apply hneq
    have hk' : k < (bs.getD 1 []).length := by
      rw [hlen1field]
      exact hk
    have hget := hgetModel k hk'
    rw [hmodelOmBytes] at hget
    exact hget

open EvmAsm.Stateless.SpecRef in
/-- The checks preceding the post-merge fields in `validate_header` have
    succeeded.  This is deliberately an explicit caller-produced premise:
    the K67 field guards select the first failing post-merge check, but do not
    prove the unrelated number/blob/gas/timestamp checks. -/
def validateHeaderPrePostMergeOk (parent header : Header) : Prop :=
  ¬ header.number < 1 ∧
  calculate_excess_blob_gas parent = .ok header.excessBlobGas ∧
  ¬ header.gasUsed > header.gasLimit ∧
  calculate_base_fee_per_gas header.gasLimit parent.gasLimit parent.gasUsed
      parent.baseFeePerGas = .ok header.baseFeePerGas ∧
  ¬ header.timestamp ≤ parent.timestamp ∧
  header.number = parent.number + 1 ∧
  ¬ header.extraData.length > 32

open EvmAsm.Stateless.SpecRef in
/-- K67's difficulty guard is the corresponding SpecRef rejection once the
    preceding `validate_header` checks have been discharged. -/
theorem k67GuardDiff_validate_header_error
    (parent header : Header) (hpre : validateHeaderPrePostMergeOk parent header)
    (hfield : header.difficulty ≠ 0) :
    validate_header parent header =
      .error (.invalidBlock "difficulty nonzero") := by
  rcases hpre with ⟨hnum, hexc, hgas, hbase, htime, hnext, hextra⟩
  unfold validate_header
  simp only [Bind.bind, Except.bind]
  simp only [if_neg hnum]
  rw [hexc]
  simp [hgas, hbase, htime, hnext, hextra, hfield]; rfl

open EvmAsm.Stateless.SpecRef in
/-- K67's nonce guard is the SpecRef nonce rejection after the earlier checks
    and the difficulty arm have been discharged. -/
theorem k67GuardNonce_validate_header_error
    (parent header : Header) (hpre : validateHeaderPrePostMergeOk parent header)
    (hdifficulty : header.difficulty = 0)
    (hfield : header.nonce ≠
      List.replicate 8 (0 : EvmAsm.Stateless.SpecRef.Byte)) :
    validate_header parent header =
      .error (.invalidBlock "nonce nonzero") := by
  rcases hpre with ⟨hnum, hexc, hgas, hbase, htime, hnext, hextra⟩
  have hfield' : ¬ header.nonce =
      [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by
    have hz : List.replicate 8 (0 : EvmAsm.Stateless.SpecRef.Byte) =
        [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by decide
    rw [← hz]
    exact hfield
  unfold validate_header
  simp only [Bind.bind, Except.bind]
  simp only [if_neg hnum]
  rw [hexc]
  simp [hgas, hbase, htime, hnext, hextra, hdifficulty, hfield']; rfl

open EvmAsm.Stateless.SpecRef in
/-- K67's ommers guard is the SpecRef ommers rejection after the earlier
    checks and both preceding post-merge arms have been discharged. -/
theorem k67GuardOmmers_validate_header_error
    (parent header : Header) (hpre : validateHeaderPrePostMergeOk parent header)
    (hdifficulty : header.difficulty = 0)
    (hnonce : header.nonce =
      List.replicate 8 (0 : EvmAsm.Stateless.SpecRef.Byte))
    (hfield : header.ommersHash ≠ EMPTY_OMMER_HASH) :
    validate_header parent header =
      .error (.invalidBlock "ommers hash not empty") := by
  rcases hpre with ⟨hnum, hexc, hgas, hbase, htime, hnext, hextra⟩
  have hnonce' : header.nonce =
      [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by
    simpa [List.replicate] using hnonce
  unfold validate_header
  simp only [Bind.bind, Except.bind]
  simp only [if_neg hnum]
  rw [hexc]
  simp [hgas, hbase, htime, hnext, hextra, hdifficulty, hnonce', hfield]; rfl

end EvmAsm.Codegen.HeaderValidatePostMergeCorrespondenceBridge
