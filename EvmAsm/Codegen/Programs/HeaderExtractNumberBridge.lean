/-
  EvmAsm.Codegen.Programs.HeaderExtractNumberBridge

  Model tie for #11351: from `rlp_field_to_u64`'s `Result` at field index 8,
  read off the value the model's `_decode_header` assigns to `number`.

  The machine side is `HeaderExtractNumberSpec.header_extract_number_spec_within`;
  this supplies the vocabulary its `Result` obligation must be read in.

  ⚠️ Two of `Result`'s five constructors are *not* reachable under the model's
  assumptions alone — they are the guest being STRICTER than the port:

  * `tooLong` — the guest rejects a field wider than eight bytes; the port's
    `getN` is plain `bytesBEtoNat`, which does not care.
  * `noncanonical` — the guest rejects a leading zero byte; `bytesBEtoNat`
    tolerates one.

  Both restrictions are therefore hypotheses here, and both are what make the
  Correspondence row `.domainRestricted` rather than `.agrees`.  The guest's
  extra strictness matches CPython's `rlp.decode_to`, which enforces exactly
  these; it is the *port* that dropped them.
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

    The `items`/`bs` arguments come from `decode_header_inv`; the two content
    restrictions are properties of the ENCODING, not of `hdr.number`, which is
    why they cannot be phrased over the value. -/
theorem header_number_of_decode
    (headerBytes : List (BitVec 8)) (base : Word) (hdr : Header)
    (items : List RLPItem) (bs : List (List (BitVec 8))) (status value : Word)
    (hfull : decodeFully headerBytes = some (.list items))
    (hlenEq : bs.length = items.length)
    (harity : bs.length = 23 ∨ bs.length = 21)
    (hidx : ∀ i, i < items.length → items[i]? = some (.bytes (bs.getD i [])))
    (hnum : hdr.number = bytesBEtoNat (bs.getD 8 []))
    (hshort : (bs.getD 8 []).length ≤ 8)
    (hcanon : ∀ c, (bs.getD 8 []).head? = some c → c ≠ 0)
    (hres : Result headerBytes base headerBytes.length 8 status value)
    (hover : base.toNat + headerBytes.length + 9 < 2 ^ 64) :
    status = 0 ∧ value = BitVec.ofNat 64 hdr.number := by
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
  obtain ⟨offset, hsucc, hcont⟩ :=
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
