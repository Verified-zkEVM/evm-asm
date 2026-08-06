/-
  EvmAsm.Codegen.Programs.HeaderExtractNumberBridge

  Model tie for #11351: from `rlp_field_to_u64`'s `Result` at field index 8,
  read off the value the model's `_decode_header` assigns to `number`.

  The machine side is `HeaderExtractNumberSpec.header_extract_number_spec_within`;
  this supplies the vocabulary its `Result` obligation must be read in.

  ⚠️ Two of `Result`'s five constructors are *not* reachable under the model's
  assumptions alone, and after #11513 the two have DIFFERENT status. They are not
  a matched pair, and treating them as one was the error that #11493 unpicked:

  * `noncanonical` — the guest rejects a leading zero byte. `_decode_header` now
    rejects it too (`_deserialize_to_uint` does, so the port had been the lenient
    one), which means this constructor is **discharged here** rather than pushed
    onto the caller.
  * `tooLong` — the guest rejects a field wider than eight bytes. The reference
    does **not**: `number` is annotated `Uint`, whose `from_be_bytes` has no
    length check at all, so a nine-byte `number` is accepted by CPython and by
    the (now faithful) port. This is not a port defect; it is evm-asm's
    project-wide assumption that these header fields arrive within the bit-width
    the guest reads them into, which per the ruling on #11620 gives the guest
    freedom to reject outside it. It stays a hypothesis, `hfits`, precisely so
    the assumption is **explicit in the statement** rather than buried in the
    guest's behaviour — an implicit bound would be worse than a recorded false
    reject.

  `hfits` is phrased over `hdr.number` rather than over the encoding, which is
  only possible *because* the port now enforces canonicality: with no leading
  zeros, "at most eight bytes" and "< 2 ^ 64" are the same restriction
  (`Nat.length_le_of_canonical_lt`). Before #11513 it had to be an
  encoding-level side condition the caller could not see.
-/

import EvmAsm.Codegen.Programs.RlpWalkDeterminism
import EvmAsm.Codegen.Programs.HeaderExtractNumberSpec
import EvmAsm.Codegen.Programs.RlpDecodeFullyForward
import EvmAsm.Stateless.SpecRef.Stateless

namespace EvmAsm.Codegen.HeaderExtractNumberSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpFieldToU64SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

/-- A nonempty content slice starts at the selected offset. -/
private theorem head?_of_content {bytes p : List (BitVec 8)} {offset len : Nat}
    (hcontent : (bytes.drop offset).take len = p) (hpos : 0 < len)
    (hne : p ≠ []) :
    p.head? = some (getByteAt bytes offset) := by
  cases hdrop : bytes.drop offset with
  | nil =>
      exfalso
      rw [hdrop] at hcontent
      simp at hcontent
      exact hne hcontent
  | cons x xs =>
      have hx : getByteAt bytes offset = x := by
        have hlt : offset < bytes.length := by
          by_contra hge
          rw [List.drop_eq_nil_of_le (by omega)] at hdrop
          simp at hdrop
        rw [getByteAt, dif_pos hlt]
        have := List.drop_eq_getElem_cons hlt
        rw [this] at hdrop
        exact (List.cons.inj hdrop).1
      rw [hdrop] at hcontent
      cases len with
      | zero => omega
      | succ k =>
          rw [List.take_succ_cons] at hcontent
          rw [← hcontent, hx]
          rfl

/-- **The value tie.**  Under the two strictness restrictions, the guest
    reports success and its output is the big-endian decode of the field
    content — which is exactly what `bytesBEtoNat` computes on the port side. -/
theorem result_value_of_success
    (bytes : List (BitVec 8)) (base : Word) (listLen : Nat)
    (status value offset len : Word) (p : List (BitVec 8))
    (hover : base.toNat + listLen + 9 < 2 ^ 64)
    (hres : Result bytes base listLen 8 status value)
    (hsucc : Success bytes base listLen 8 offset len)
    (hlen : len = BitVec.ofNat 64 p.length)
    (hplen : p.length < 2 ^ 64)
    (hcontent : (bytes.drop offset.toNat).take len.toNat = p)
    (hshort : p.length ≤ 8)
    (hcanon : ∀ c, p.head? = some c → c ≠ 0) :
    status = 0 ∧ value = BitVec.ofNat 64 (Nat.fromBytesBE p) := by
  have hlenNat : len.toNat = p.length := by
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplen]
  cases hres with
  | listFailure hfail => exact absurd hfail (fun hf => success_not_failure hover hsucc hf)
  | tooLong o l hok hgt =>
      obtain ⟨-, rfl⟩ := success_deterministic hok hsucc
      omega
  | noncanonical o l hok hpos hfit hzero =>
      obtain ⟨rfl, rfl⟩ := success_deterministic hok hsucc
      exact absurd (hzero ▸ hcanon _ (head?_of_content hcontent (by omega)
        (by intro hnil; rw [hnil] at hlenNat; simp at hlenNat; omega))) (by simp)
  | empty o l hok hempty =>
      obtain ⟨-, rfl⟩ := success_deterministic hok hsucc
      have hnil : p = [] := by
        have : p.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero this
      exact ⟨rfl, by rw [hnil]; simp [Nat.fromBytesBE]⟩
  | success o l hok hpos hfit hnz =>
      obtain ⟨rfl, rfl⟩ := success_deterministic hok hsucc
      exact ⟨rfl, by rw [hcontent]⟩

/-! ## The model tie

`_decode_header` succeeded ⇒ the guest reports success and writes exactly the
`number` the port computes.  Stated one-directionally: the guest never checks
header arity, so on a list of some other length it still returns a value where
`_decode_header` errors. -/

open EvmAsm.Stateless.SpecRef in
/-- **`header_extract_number` against `_decode_header`'s `number` field.**

    Takes the decode hypothesis directly and inverts it with
    `decode_header_inv`, so the port's own typed checks discharge what used to be
    caller obligations. What remains is `hfits`, the one restriction the
    reference does not share — see the file preamble. -/
theorem header_number_of_decode
    (headerBytes : List (BitVec 8)) (base : Word) (hdr : Header)
    (status value : Word)
    (hdec : _decode_header headerBytes = .ok hdr)
    (hfits : hdr.number < 2 ^ 64)
    (hres : Result headerBytes base headerBytes.length 8 status value)
    (hover : base.toNat + headerBytes.length + 9 < 2 ^ 64) :
    status = 0 ∧ value = BitVec.ofNat 64 hdr.number := by
  obtain ⟨items, bs, hfull, hlenEq, harity, hidx, hval, hchecks⟩ := decode_header_inv hdec
  -- field 8's canonicality is now the PORT's check, not the caller's
  obtain ⟨hcanon, -⟩ := hchecks 8 none (by decide)
  have hnum : hdr.number = bytesBEtoNat (bs.getD 8 []) := by rw [hval]; rfl
  -- canonical ∧ < 2 ^ 64 ⇒ at most eight bytes; this is where `hfits` is spent
  have hcanon1 : (bs.getD 8 []).headD 1 ≠ 0 := by
    cases hb : (bs.getD 8 []) with
    | nil => simp
    | cons x xs => simpa using hcanon x (by rw [hb]; simp)
  have hshort : (bs.getD 8 []).length ≤ 8 := by
    refine Nat.length_le_of_canonical_lt hcanon1 ?_
    calc Nat.fromBytesBE (bs.getD 8 []) = hdr.number := hnum.symm
      _ < 2 ^ 64 := hfits
      _ = 256 ^ 8 := by norm_num
  have h8 : 8 < items.length := by rcases harity with h | h <;> omega
  have hidx8 := hidx 8 h8
  -- every child is a byte string, which is what the forward stack needs
  have hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q := by
    intro it hit
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hit
    exact ⟨bs.getD i [], by
      have := hidx i hi
      rw [List.getElem?_eq_getElem hi, hget] at this
      exact Option.some.inj this⟩
  obtain ⟨offset, hsucc, hcont, -⟩ :=
    success_content_of_decodeFully_list headerBytes base items 8 (bs.getD 8 [])
      hfull hbytes hidx8 (by omega)
  have hlenNat : (BitVec.ofNat 64 (bs.getD 8 []).length).toNat = (bs.getD 8 []).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hst, hval⟩ :=
    result_value_of_success headerBytes base headerBytes.length status value offset
      (BitVec.ofNat 64 (bs.getD 8 []).length) (bs.getD 8 []) hover hres hsucc rfl
      (by omega) (by rw [hlenNat]; exact hcont) hshort hcanon
  exact ⟨hst, by rw [hval, hnum]⟩

end EvmAsm.Codegen.HeaderExtractNumberSpec
