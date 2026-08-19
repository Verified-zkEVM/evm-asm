/-
  EvmAsm.Stateless.SpecRef.HeaderRoundTrip

  **The header RLP round trip** (#12647, second leg of #12223): a header on
  `_decode_header`'s accepting path re-encodes to exactly the bytes it was decoded
  from.

  `BlocksRlp.lean`'s module docstring has asserted this in PROSE — "re-encoding
  reproduces the original bytes exactly … the claim is now unconditional on the
  accepting path" — and `Tests/Correspondence/Header.lean` exercises it as the
  subject's `aux` axis. Neither is a kernel-checked proof, and #10770 / #11183
  lean on it through the block-hash binding. This module supplies the pieces.

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
  two lemmas below are that bridge.
-/
import EvmAsm.Stateless.SpecRef.Stateless
import EvmAsm.Stateless.SpecRef.BlocksRlp
import EvmAsm.EL.RLP.Properties
import EvmAsm.EL.RLP.EncodeDecode
import Batteries.Tactic.OpenPrivate

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP
open private getNChecked numericFieldsOk from EvmAsm.Stateless.SpecRef.Stateless
open private scalarItem from EvmAsm.Stateless.SpecRef.BlocksRlp

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


/-! ## What remains, and a constraint on how to do it

    With the three lemmas above the round trip reduces to one MECHANICAL step:

      headerToRlpItem (mkHeaderFields isCurrent bs) = .list (bs.map .bytes)

    under `numericFieldsOk bs` and `bs.length = 23` (resp. 21). Byte fields are
    definitional; the nine numeric fields are exactly
    `scalarItem_getD_of_numericFieldsOk`. Then
    `EvmAsm.EL.RLP.encode_decodeFully` closes
    `encode (headerToRlpItem h) = bs`.

    ⚠️ CONSTRAINT worth knowing before starting it: **no `SpecRef` module imports
    Mathlib** (checked: zero of them), so `interval_cases` / `fin_cases` are NOT
    available here and the 23-way case split has to be written with plain
    `rcases`/`match`, or the list destructured up front. I stopped rather than be
    the first module to pull Mathlib into this layer for a tactic convenience —
    the correspondence harness depends on `SpecRef` staying light
    (`scripts/check-correspondence-deps.sh` forbids Subjects rooting in Mathlib). -/

-- Non-vacuity: the nine numeric indices really are the ones the header's
-- scalar fields sit at, and the byte fields are NOT among them (so the
-- corollary above is not silently applicable everywhere).
#guard (numericFieldWidths.map Prod.fst) == [7, 8, 9, 10, 11, 15, 17, 18, 22]
#guard ¬ ((numericFieldWidths.map Prod.fst).contains 0)
#guard ¬ ((numericFieldWidths.map Prod.fst).contains 12)

end EvmAsm.Stateless.SpecRef
