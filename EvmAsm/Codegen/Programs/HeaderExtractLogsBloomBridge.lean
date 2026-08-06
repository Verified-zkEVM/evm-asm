/-
  EvmAsm.Codegen.Programs.HeaderExtractLogsBloomBridge

  Model tie for #11575 row 1: from `rlp_list_nth_item`'s `Success` at field
  index 6, read off the value the model's `_decode_header` assigns to `bloom`.

  The machine side is
  `HeaderExtractLogsBloomSpec.headerExtractLogsBloom_spec_within`; this supplies
  the vocabulary its `helbRetPost` obligation must be read in.

  ## Why this row is UNCONDITIONAL where `header_extract_number` is not

  `helbRetPost` is a three-way disjunction, and its middle arm is
  `a0 = 2 ∧ Success … 6 fo len ∧ len ≠ 256` — the guest rejecting a `bloom`
  field whose content length is not 256.  Before #11615 that arm was *reachable*
  under the model's assumptions, because the port's `getB` was a bare
  `bs.getD i []` with no width check: a successful `_decode_header` said nothing
  about `bloom`'s length, so the bridge would have had to carry
  `hdr.bloom.length = 256` as a caller obligation.

  That hypothesis would have looked like a guest restriction and been graded as
  one.  It was not: `_deserialize_to_bytes` constructs the annotated type and
  `FixedBytes.__new__` enforces `LENGTH`, so `Bloom = Bytes256` **is** width-
  checked by the reference (`ethereum_types` 0.4.1 `bytes.py:29-37`).  The
  leniency was the port's alone.  This is the **second** instance of the
  misattribution pattern #11493 unpicked — a port gap making a correct guest look
  strict — the first being canonicality on `number` (#11617).  #11615 removing it
  is what lets `len = 256` be *derived* here rather than assumed.

  ⚠️ **Do not add the `Uint` width question (#11620) to that list.**  It is the
  opposite case: there the reference imposes *no* bound (`Uint.from_be_bytes` is a
  plain `int.from_bytes`, `numeric.py:523-528`) while the guest bounds at 8, so the
  guest genuinely rejects more than the reference.  Grouping it with the
  misattributions invites reading it as closable, which it is not.

  The general shape, which is the transferable part: **"guest stricter than port"
  resolves differently per ANNOTATION.**  For `FixedBytes` and `FixedUnsigned` the
  reference imposes the same bound the guest does, so the guest is matched and the
  port was the gap.  For arbitrary-precision `Uint` the reference imposes none, so
  the guest is genuinely over-rejecting.  Read the annotation's own conversion
  before deciding which of the two you are looking at.

  So unlike `header_number_of_decode`, this tie needs **no** side condition on
  the field: `decode_header_inv` now yields the width directly.
-/

import EvmAsm.Codegen.Programs.RlpWalkDeterminism
import EvmAsm.Codegen.Programs.HeaderExtractLogsBloomSpec
import EvmAsm.Codegen.Programs.RlpDecodeFullyForward
import EvmAsm.Stateless.SpecRef.Stateless

namespace EvmAsm.Codegen.HeaderExtractLogsBloomSpec

open EvmAsm.Rv64 EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## The model tie

`_decode_header` succeeded ⇒ field 6's reported length is exactly 256 and its
content is exactly the `bloom` the port computes.  Stated one-directionally for
the same reason as row 9: the guest never checks header arity, so on a list of
some other length it still returns a value where `_decode_header` errors. -/

open EvmAsm.Stateless.SpecRef in
/-- **`header_extract_logs_bloom` against `_decode_header`'s `bloom` field.**

    The `len = 256` conclusion is what excludes `helbRetPost`'s `a0 = 2` arm, so
    a caller composing this with the machine triple gets the success arm outright.

    Note there is no width hypothesis: it is a *conclusion* here, because the
    port now performs the `FixedBytes` check the reference performs (#11615). -/
theorem header_logs_bloom_of_decode
    (headerBytes : List (BitVec 8)) (base : Word) (hdr : Header) (fo len : Word)
    (hdec : _decode_header headerBytes = .ok hdr)
    (hsucc : Success headerBytes base headerBytes.length 6 fo len)
    (hover : base.toNat + headerBytes.length < 2 ^ 64) :
    len = BitVec.ofNat 64 256 ∧
      (headerBytes.drop fo.toNat).take 256 = hdr.bloom := by
  obtain ⟨items, bs, hfull, hlenEq, harity, hidx, hval, -, hbwidths⟩ :=
    decode_header_inv hdec
  -- `Bloom = Bytes256`, and the port now checks it, so this is derived not assumed
  have hblen : (bs.getD 6 []).length = 256 := hbwidths 6 256 (Or.inl (by decide))
  have hbloom : hdr.bloom = bs.getD 6 [] := by rw [hval]; rfl
  have h6 : 6 < items.length := by rcases harity with h | h <;> omega
  -- every child is a byte string, which is what the forward stack needs
  have hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q := by
    intro it hit
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hit
    exact ⟨bs.getD i [], by
      have := hidx i hi
      rw [List.getElem?_eq_getElem hi, hget] at this
      exact Option.some.inj this⟩
  obtain ⟨offset, hsucc', hcont, -⟩ :=
    success_content_of_decodeFully_list headerBytes base items 6 (bs.getD 6 [])
      hfull hbytes (hidx 6 h6) hover
  obtain ⟨rfl, rfl⟩ := success_deterministic hsucc' hsucc
  refine ⟨by rw [hblen], ?_⟩
  rw [hbloom, ← hblen]
  exact hcont

end EvmAsm.Codegen.HeaderExtractLogsBloomSpec
