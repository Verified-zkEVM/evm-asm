/-
  EvmAsm.Stateless.SpecRef.HeaderRoundTrip

  **The header RLP round trip** (#12647, second leg of #12223): a header on
  `_decode_header`'s accepting path re-encodes to exactly the bytes it was decoded
  from.

  `BlocksRlp.lean`'s module docstring has asserted this in PROSE — "re-encoding
  reproduces the original bytes exactly … the claim is now unconditional on the
  accepting path" — and `Tests/Correspondence/Header.lean` exercises it as the
  subject's `aux` axis. Neither is a kernel-checked proof, and #10770 / #11183
  lean on it through the block-hash binding. **This module proves it**:
  `encode_headerToRlpItem_of_decode`.

  ## Why a separate module, and why `open private`

  `headerToRlpItem` lives in `BlocksRlp.lean`; the decoder's checks
  (`getNChecked`, `numericFieldsOk`) are `private` to `Stateless.lean`; and
  neither of those modules imports the other. So the statement needs a third
  module that imports both and reaches the private checks — `open private`, from
  Batteries rather than Mathlib so no heavy tower enters the `SpecRef` layer.

  ## The reduction

  `_decode_header` is `decodeFully` → every item is `.bytes` → arity 23/21 →
  `decodeHeaderArm`, and the arm is `.ok (mkHeaderFields isCurrent bs)` once
  `checkNumericFields` passes. The generic half of the round trip is ALREADY
  proved — `EvmAsm.EL.RLP.encode_decodeFully` gives `encode item = bs` from
  `decodeFully bs = some item` — so what remains is header-specific: the decoded
  item IS the re-encoded header.

  Byte fields are stored verbatim by `mkHeaderFields`, so those are definitional.
  The nine numeric fields go through `bytesBEtoNat`, and re-encoding them needs
  `Nat.toBytesBE (bytesBEtoNat b) = b` — true exactly when `b` is canonical,
  which is what the decoder's own `getNChecked` check establishes (#11513). The
  lemmas below are that bridge; the round trip itself is at the end of the file.

  Nothing here is stated under a canonicality hypothesis the CALLER has to
  discharge: `decode_header_inv` already hands the canonicality facts over as its
  sixth conjunct, so accepting is the only hypothesis the final theorem carries.
-/
module

public import EvmAsm.Stateless.SpecRef.Stateless
public import EvmAsm.Stateless.SpecRef.BlocksRlp
public import EvmAsm.EL.RLP.Properties
public import EvmAsm.EL.RLP.EncodeDecode
public import Batteries.Tactic.OpenPrivate
meta import EvmAsm.Stateless.SpecRef.Stateless
meta import EvmAsm.Stateless.SpecRef.BlocksRlp
meta import EvmAsm.EL.RLP.Properties
meta import EvmAsm.EL.RLP.EncodeDecode
meta import Batteries.Tactic.OpenPrivate
-- `open private rlpTestHeader from BlocksRlp` (below) needs BlocksRlp's
-- PRIVATE declarations, which a plain/public import does not carry --
-- they live in the separate `.olean.private`. `import all` is the form
-- that reaches them.
import all EvmAsm.Stateless.SpecRef.BlocksRlp

@[expose] public section

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP
open EvmAsm.Stateless.SpecRef (getNChecked)
open EvmAsm.Stateless.SpecRef (numericFieldsOk)
-- `scalarItem` is no longer `private`: `headerToRlpItem` is an exposed public
-- body that references it, and under the module system a public body may not
-- mention a private declaration. Only `rlpTestHeader` still needs opening.
open private rlpTestHeader from EvmAsm.Stateless.SpecRef.BlocksRlp

/-- **The decoder's scalar check implies canonicality, in re-encoding form.**

    `getNChecked` accepts only canonically-encoded scalars (no leading zero
    byte), which is precisely the hypothesis
    `Nat.toBytesBE_fromBytesBE_of_canonical` wants. `bytesBEtoNat` is an abbrev
    for `Nat.fromBytesBE`, so the conclusion is the re-encoding identity the
    round trip needs at each numeric field. -/
theorem canonical_of_getNChecked {w : Option Nat} {b : Bytes} {n : Nat}
    (h : getNChecked w b = .ok n) :
    EvmAsm.EL.RLP.Nat.toBytesBE (bytesBEtoNat b) = b := by
  unfold getNChecked at h
  split at h
  · rename_i n' hscalar
    have hchk := decodeItemScalar_checks hscalar
    refine EvmAsm.EL.RLP.Nat.toBytesBE_fromBytesBE_of_canonical b ?_
    cases b with
    | nil => simp
    | cons c cs =>
      have := hchk.1 c (by simp)
      simpa using this
  · exact absurd h (by simp)

/-- **Per-field form**: the aggregate check `numericFieldsOk` yields the
    re-encoding identity at every index in `numericFieldWidths` (7, 8, 9, 10, 11,
    15, 17, 18, 22).

    This is the shape the round trip consumes — the aggregate `List.all` is
    awkward to use directly at each of the nine numeric fields. -/
theorem canonical_of_numericFieldsOk {bs : List Bytes}
    (h : numericFieldsOk bs = true) {i : Nat} {w : Option Nat}
    (hmem : (i, w) ∈ numericFieldWidths) :
    EvmAsm.EL.RLP.Nat.toBytesBE (bytesBEtoNat (bs.getD i [])) = bs.getD i [] := by
  unfold numericFieldsOk at h
  have hall := List.all_eq_true.mp h (i, w) hmem
  simp only at hall
  split at hall
  · rename_i n hok
    exact canonical_of_getNChecked hok
  · exact absurd hall (by simp)

/-- Corollary in the form the field list uses: a numeric field's `scalarItem`
    is the decoded bytes unchanged. -/
theorem scalarItem_getD_of_numericFieldsOk {bs : List Bytes}
    (h : numericFieldsOk bs = true) {i : Nat} {w : Option Nat}
    (hmem : (i, w) ∈ numericFieldWidths) :
    scalarItem (bytesBEtoNat (bs.getD i [])) = RLPItem.bytes (bs.getD i []) := by
  unfold scalarItem
  rw [canonical_of_numericFieldsOk h hmem]


/-! ## The round trip

    With the canonicality bridge above, the header-specific half reduces to one
    mechanical identity — the decoded item IS the re-encoded header:

      headerToRlpItem (mkHeaderFields isCurrent bs) = .list (bs.map .bytes)

    ⚠️ How the 23-way split is avoided. `SpecRef` imports no Mathlib (checked:
    zero of its modules do), so `interval_cases` / `fin_cases` are unavailable
    here and the correspondence harness depends on that staying true
    (`scripts/check-correspondence-deps.sh` forbids Subjects rooting in
    Mathlib). Rather than destructure `bs` into 23 cons cells by hand, the
    reconstruction lemma `map_range_getD_bytes` below turns `bs.map .bytes` into
    an index-indexed map, which `List.range`'s own reduction then matches
    against the field literal. Generic, and no case split at all. -/

/-- **Reconstruction**: mapping `.bytes` over a list is the same as reading it
    out by index. Turns the `bs.map .bytes` shape that `decode_header_inv`
    supplies into the per-index shape `headerToRlpItem`'s field literal has, so
    the two meet without destructuring `bs`. -/
private theorem map_range_getD_bytes (l : List Bytes) :
    (List.range l.length).map (fun i => RLPItem.bytes (l.getD i [])) =
      l.map RLPItem.bytes := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    have hn : n < l.length := by simpa using h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

/-- Canonicality in the form `decode_header_inv` supplies it: the inversion
    hands over "no leading zero byte" as a `head?` fact, and
    `Nat.toBytesBE_fromBytesBE_of_canonical` wants a `headD`. -/
private theorem canonical_of_head?_ne_zero {b : Bytes}
    (h : ∀ c, b.head? = some c → c ≠ 0) :
    EvmAsm.EL.RLP.Nat.toBytesBE (bytesBEtoNat b) = b := by
  refine EvmAsm.EL.RLP.Nat.toBytesBE_fromBytesBE_of_canonical b ?_
  cases b with
  | nil => simp
  | cons c cs => simpa using h c (by simp)

/-- ⭐ **The header-specific half of the round trip.** Under the decoder's own
    canonicality facts, re-encoding the field assignment reproduces exactly the
    item that was decoded.

    The byte fields are definitional — `mkHeaderFields` stores them verbatim and
    `headerToRlpItem` re-emits them unchanged. The nine numeric fields are the
    only content here: each went through `bytesBEtoNat` on the way in and
    `Nat.toBytesBE` on the way out, and those compose to the identity exactly on
    canonically-encoded scalars, which is what `hcanon` provides.

    `hcanon` is stated over `numericFieldWidths` membership rather than as nine
    separate hypotheses so that it is literally the sixth conjunct of
    `decode_header_inv` — no repackaging at the call site. -/
theorem headerToRlpItem_mkHeaderFields (isCurrent : Bool) (bs : List Bytes)
    (hlen : bs.length = if isCurrent then 23 else 21)
    (hcanon : ∀ i w, (i, w) ∈ numericFieldWidths →
      ∀ c, (bs.getD i []).head? = some c → c ≠ 0) :
    headerToRlpItem (mkHeaderFields isCurrent bs) =
      RLPItem.list (bs.map RLPItem.bytes) := by
  -- the nine numeric fields, each re-encoding to the bytes it was read from
  have hc : ∀ i w, (i, w) ∈ numericFieldWidths →
      EvmAsm.EL.RLP.Nat.toBytesBE (bytesBEtoNat (bs.getD i [])) = bs.getD i [] :=
    fun i w hmem => canonical_of_head?_ne_zero (hcanon i w hmem)
  have h7 := hc 7 none (by simp [numericFieldWidths])
  have h8 := hc 8 none (by simp [numericFieldWidths])
  have h9 := hc 9 none (by simp [numericFieldWidths])
  have h10 := hc 10 none (by simp [numericFieldWidths])
  have h11 := hc 11 (some 32) (by simp [numericFieldWidths])
  have h15 := hc 15 none (by simp [numericFieldWidths])
  have h17 := hc 17 (some 8) (by simp [numericFieldWidths])
  have h18 := hc 18 (some 8) (by simp [numericFieldWidths])
  have h22 := hc 22 (some 8) (by simp [numericFieldWidths])
  -- read the target out by index instead of destructuring `bs`
  rw [← map_range_getD_bytes bs, hlen]
  cases isCurrent with
  | true =>
      simp only [if_true, headerToRlpItem, mkHeaderFields, scalarItem,
        h7, h8, h9, h10, h11, h15, h17, h18, h22]
      simp [List.range_succ]
  | false =>
      simp only [Bool.false_eq_true, if_false, headerToRlpItem, mkHeaderFields,
        scalarItem, h7, h8, h9, h10, h11, h15, h17, h18]
      simp [List.range_succ]

/-- ⭐⭐ **The header RLP round trip** (#12647, second leg of #12223).

    `_decode_header` accepting `hb` means re-encoding the header it produced
    reproduces `hb` **byte for byte**. Unconditional on the accepting path — no
    canonicality side condition survives, because the decoder's own checks
    established it.

    This is the claim `BlocksRlp.lean`'s module docstring has asserted in PROSE
    ("re-encoding reproduces the original bytes exactly … the claim is now
    unconditional on the accepting path") and that
    `Tests/Correspondence/Header.lean` exercises on a corpus as the subject's
    `aux` axis. Neither is a kernel-checked proof; this is.

    ⭐ Why it matters beyond tidiness: #10770 / #11183 bind a block hash to a
    header through `headerHash h = keccak256 (encode (headerToRlpItem h))`. That
    binding is only as good as the guarantee that the bytes being hashed are the
    bytes that arrived. Without this theorem, a header could in principle decode
    successfully and re-encode to something else, and the hash would be of the
    re-encoding rather than of the input.

    Two halves, and both were already available:
    * the GENERIC half, `encode_decodeFully` — anything `decodeFully` accepts is
      canonical RLP, so `encode item = hb`;
    * the HEADER-SPECIFIC half, `headerToRlpItem_mkHeaderFields` — the item
      accepted is the item the header re-encodes to. -/
theorem encode_headerToRlpItem_of_decode {hb : Bytes} {hdr : Header}
    (h : _decode_header hb = .ok hdr) :
    EvmAsm.EL.RLP.encode (headerToRlpItem hdr) = hb := by
  obtain ⟨items, bs, hfull, hlen, harity, hidx, hval, hnum, -⟩ :=
    decode_header_inv h
  -- the decoded items are exactly the field bytes, tagged
  have hitems : items = bs.map RLPItem.bytes := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < items.length
    · rw [hidx n hn]
      have : n < (bs.map RLPItem.bytes).length := by simp [hlen, hn]
      rw [List.getElem?_eq_getElem this]
      have hbn : n < bs.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbn]
    · have h1 : items[n]? = none := List.getElem?_eq_none (by omega)
      have h2 : (bs.map RLPItem.bytes)[n]? = none := by
        refine List.getElem?_eq_none ?_
        simp only [List.length_map]
        omega
      rw [h1, h2]
  -- and the header re-encodes to exactly that item
  have hmk : headerToRlpItem hdr = RLPItem.list items := by
    rw [hval, hitems]
    refine headerToRlpItem_mkHeaderFields _ bs ?_ ?_
    · rcases harity with h23 | h21
      · simp [h23]
      · simp [h21]
    · intro i w hmem
      exact (hnum i w hmem).1
  rw [hmk]
  exact EvmAsm.EL.RLP.encode_decodeFully hfull

/-! ## Non-vacuity

    Three checks, in the two directions that matter.

    First, that the nine numeric indices really are the ones the header's scalar
    fields sit at, and that byte fields are NOT among them — so
    `canonical_of_numericFieldsOk` is not silently applicable everywhere. -/

#guard (numericFieldWidths.map Prod.fst) == [7, 8, 9, 10, 11, 15, 17, 18, 22]
#guard ¬ ((numericFieldWidths.map Prod.fst).contains 0)
#guard ¬ ((numericFieldWidths.map Prod.fst).contains 12)

/-! ### That `hcanon` is load-bearing

    A theorem whose hypothesis is decoration is worse than no theorem, so the
    two `#guard`s below evaluate `headerToRlpItem_mkHeaderFields`' conclusion on
    a canonical field list and on one that differs in a SINGLE byte, and show it
    holds in the first case and **fails** in the second.

    Both lists have all 23 fields, all empty except field 8 (`number`). Empty is
    canonical (`bytesBEtoNat [] = 0`, `toBytesBE 0 = []`), so every other field
    round-trips by itself and field 8 is the only moving part.

    ⚠️ These are field lists, not encoded headers — `mkHeaderFields` and
    `headerToRlpItem` impose no width checks, which is exactly why `_decode_header`
    runs `bytesFieldsOk` separately. Feeding the bad list to `_decode_header`
    would be REJECTED; the point here is the narrower one that the mechanical
    step alone is false without canonicality, so the hypothesis is carrying the
    proof rather than adorning it. -/

/-- Field 8 = `[0x01]` — the canonical encoding of 1. -/
private def rtCanonFields : List Bytes :=
  (List.range 23).map fun i => if i = 8 then [(1 : EvmAsm.EL.RLP.Byte)] else []

/-- Field 8 = `[0x00, 0x01]` — the same VALUE, one leading zero byte, which is
    precisely what `getNChecked` rejects. -/
private def rtBadFields : List Bytes :=
  (List.range 23).map fun i =>
    if i = 8 then [(0 : EvmAsm.EL.RLP.Byte), (1 : EvmAsm.EL.RLP.Byte)] else []

#guard rtCanonFields.length == 23 && rtBadFields.length == 23
-- the two differ in exactly one field, and it is a numeric one
#guard rtCanonFields.getD 8 [] != rtBadFields.getD 8 []
#guard (List.range 23).all fun i => i = 8 || rtCanonFields.getD i [] == rtBadFields.getD i []
-- holds on the canonical list ...
#guard headerToRlpItem (mkHeaderFields true rtCanonFields)
  == RLPItem.list (rtCanonFields.map RLPItem.bytes)
-- ... and is FALSE one leading zero byte over
#guard ¬ (headerToRlpItem (mkHeaderFields true rtBadFields)
  == RLPItem.list (rtBadFields.map RLPItem.bytes))

/-! ### The whole theorem, on the header whose hash is pinned to Python

    The checks above are about the mechanical step in isolation, on synthetic
    field lists. This one evaluates the FULL conclusion of
    `encode_headerToRlpItem_of_decode` on `BlocksRlp`'s `rlpTestHeader` — the
    23-field header with real field widths whose `headerHash` is pinned to the
    value the Python reference computes,
    `0xaa1274…89e2` (`BlocksRlp.lean`, "Sanity checks").

    ⭐ Why this is the check worth having: it closes the loop against an EXTERNAL
    oracle. The second `#guard` recovers a header by running the decoder, then
    hashes it, and gets the digest Python produced for the header we started
    from. A round-trip theorem stated about the wrong encoder, or true for
    uninteresting reasons, would not survive that. -/

private def rtPinnedBytes : Bytes :=
  EvmAsm.EL.RLP.encode (headerToRlpItem rlpTestHeader)

-- The pinned header's encoding is on `_decode_header`'s accepting path, and
-- re-encoding what comes back reproduces it byte for byte — the theorem's
-- conclusion, evaluated.
#guard match _decode_header rtPinnedBytes with
  | .ok h => EvmAsm.EL.RLP.encode (headerToRlpItem h) == rtPinnedBytes
  | .error _ => false

-- ⭐ And the header the decoder returns hashes to the Python-pinned digest, so
-- the bytes the round trip preserves are the bytes that digest is of. This is
-- the #12223 binding, evaluated at one point.
#guard match _decode_header rtPinnedBytes with
  | .ok h => bytesBEtoNat (headerHash h)
      == 0xaa1274562be0d8f34002861987fa166ee8903056f4df36509220bd9c7b8f89e2
  | .error _ => false

/-! ### And the accepting hypothesis is not "any RLP"

    `0xc0` is the empty RLP list: `decodeFully` accepts it, `_decode_header`
    rejects it on arity. So `_decode_header hb = .ok hdr` is strictly stronger
    than "hb is well-formed RLP", and the theorem is not the generic
    `encode_decodeFully` wearing a header-shaped hat. -/
#guard (EvmAsm.EL.RLP.decodeFully [(0xc0 : EvmAsm.EL.RLP.Byte)]).isSome
#guard match _decode_header [(0xc0 : EvmAsm.EL.RLP.Byte)] with
  | .ok _ => false
  | .error _ => true

end EvmAsm.Stateless.SpecRef
