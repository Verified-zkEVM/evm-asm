/-
  EvmAsm.Codegen.Programs.HeaderValidateExtraDataLengthBridge

  Model tie for #11575 row 2: from `rlp_list_nth_item`'s `Success` at field
  index 12, decide the `extra_data` length rule the way `validate_header` does.

  The machine side is
  `HeaderValidateExtraDataLengthSpec.header_validate_extra_data_length_spec_within`;
  this supplies the vocabulary its `hvedPost` obligation must be read in.

  ## ⚠️ The comparison boundary, which is NOT the one the other header rows use

  Every other `header_*` row so far ties a guest routine to a field of
  `_decode_header`.  This one does not, and saying so precisely is required by
  `docs/agents/spec-correspondence.md` §5:

  * `extra_data` is plain `Bytes` in the reference — genuinely **unbounded at
    decode time**, unlike the `FixedBytes` aliases of #11615.  So there is nothing
    to compare against in `_decode_header`.
  * The ≤32 rule is a clause of **`validate_header`** (`SeamShell.lean:248`,
    `if header.extraData.length > 32 then throw`), a different spec function.

  So the boundary is: `_decode_header` supplies the *field*, and the routine
  implements a *`validate_header` clause* over it.  The tie below therefore has
  two conclusions rather than one — the length equation (decode side) and the
  decision equivalence (validation side).  Reading this row as "a `_decode_header`
  field row" would misdescribe what is proved.

  ## Why the decision is an iff, where row 1's was one-directional in the field

  `hvedPost`'s first two arms differ only in the guard — `a0 = 0` with
  `¬ (32 <ᵤ len)` and `a0 = 1` with `32 <ᵤ len` — so on a successful decode the
  guest's accept/reject choice is *total* over the field, and the honest statement
  is an equivalence with the reference's clause.  What stays one-directional is
  the same thing as everywhere else in this family: arity.  The guest never checks
  how many fields the header has.
-/

import EvmAsm.Codegen.Programs.RlpWalkDeterminism
import EvmAsm.Codegen.Programs.HeaderValidateExtraDataLengthSpec
import EvmAsm.Codegen.Programs.RlpDecodeFullyForward
import EvmAsm.Stateless.SpecRef.Stateless

namespace EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec

open EvmAsm.Rv64 EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Stateless.SpecRef in
/-- **`header_validate_extra_data_length` against `validate_header`'s
    `extra_data` clause.**

    The second conjunct is the tie proper: the guest's `a0 = 0`-vs-`a0 = 1` guard
    (`¬ (32 <ᵤ len)`) holds exactly when the reference's
    `header.extraData.length > 32` throw does *not* fire.  The first conjunct is
    what makes that meaningful — it pins the guest's reported `len` to the decoded
    field's length, so the two comparisons are about the same quantity. -/
theorem header_extra_data_length_of_decode
    (headerBytes : List (BitVec 8)) (base : Word) (hdr : Header) (fo len : Word)
    (hdec : _decode_header headerBytes = .ok hdr)
    (hsucc : Success headerBytes base headerBytes.length 12 fo len)
    (hover : base.toNat + headerBytes.length < 2 ^ 64) :
    len = BitVec.ofNat 64 hdr.extraData.length ∧
      (¬ BitVec.ult (32 : Word) len ↔ hdr.extraData.length ≤ 32) := by
  obtain ⟨items, bs, hfull, hlenEq, harity, hidx, hval, -, -⟩ := decode_header_inv hdec
  have hextra : hdr.extraData = bs.getD 12 [] := by rw [hval]; rfl
  -- field 12 exists in BOTH arms (23 and 21), which is why this row represents
  -- the pair with `chain_validate_extra_data_length`
  have h12 : 12 < items.length := by rcases harity with h | h <;> omega
  have hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q := by
    intro it hit
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hit
    exact ⟨bs.getD i [], by
      have := hidx i hi
      rw [List.getElem?_eq_getElem hi, hget] at this
      exact Option.some.inj this⟩
  obtain ⟨offset, hsucc', hcont, hle⟩ :=
    success_content_of_decodeFully_list headerBytes base items 12 (bs.getD 12 [])
      hfull hbytes (hidx 12 h12) hover
  obtain ⟨rfl, rfl⟩ := success_deterministic hsucc' hsucc
  -- the field cannot be wider than the buffer, so no wraparound in the compare
  have hlt : (bs.getD 12 []).length < 2 ^ 64 := by omega
  refine ⟨by rw [hextra], ?_⟩
  rw [hextra]
  have h32 : (32 : Word).toNat = 32 := by decide
  simp only [BitVec.ult_iff_toNat_lt, h32, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.not_lt]

end EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec
