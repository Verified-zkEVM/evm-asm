/-
  EvmAsm.Codegen.Programs.RlpListEncodedSizeBridge

  GH #11341 — the **inheritance bridge** for the `rlp_list_encoded_size`
  Correspondence row, the sibling of `RlpBytesEncodedSizeBridge.lean`.

  THE GAP THIS CLOSES. `rlpListEncodedSize_spec` (`RlpListEncodedSizeSAsm.lean:364`)
  is a shade weaker than its `rlp_bytes_encoded_size` counterpart: the size formula
  is not merely local, it is **written inline in the theorem statement** and never
  given a name, so there was nothing a reader could even point at to compare against
  `len(encode_sequence(...))`. The differential over `EvmAsm.EL.RLP` therefore did
  not transfer.

  WHAT IS HERE. `rlesSize` names the formula (definitionally the inline one, so the
  machine proof is reached by `rfl`), `rlesSize_eq_encode_list_length` is the bridge
  to `(encode (.list items)).length`, and `rlpListEncodedSize_encode_spec` is the
  one-rewrite consumer. `RlpListEncodedSizeSAsm.lean` is **untouched** — the bridge
  is the artefact, not a re-proof (`docs/agents/spec-correspondence.md` §4).

  REUSED, NOT REPROVED. The load-bearing fact — that the guest's 9-way
  length-of-length ladder `u64ByteLen` IS `(Nat.toBytesBE ·).length` — was proved
  for the `rlp_bytes_encoded_size` bridge and is imported from there
  (`RlpBytesEncodedSizeSAsm.u64ByteLen_eq_toBytesBE_length`). It lives in that
  namespace because that is where it was first needed; it is not specific to the
  byte-string routine, and this module is the second consumer. The list side then
  reduces to `encode_list_short` / `encode_list_long`
  (`EL/RLP/Properties.lean:2332`/`:2341`), which already existed.

  ⚠️ NOTE ON THE ARGUMENT. The routine takes the **payload length** in `a0` and
  returns the *total* encoded size, so the bridge is stated against a `List RLPItem`
  whose `encodeItems` payload has that length. That is the honest comparison point:
  the guest never sees the items, only their encoded length, and the reference
  `len(encode_sequence(items))` is a function of exactly that. Full domain — both
  arms of the 55/56 split are covered — so the row is `.agrees`, with `hbound` a
  64-bit non-overflow ABI guard as in the sibling module.
-/

import EvmAsm.Codegen.Programs.RlpBytesEncodedSizeBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.EL.RLP

namespace RlpListEncodedSizeSAsm

open RlpBytesEncodedSizeSAsm (u64ByteLen_eq_toBytesBE_length)

/-- The RLP **list** encoded size: a payload below 56 bytes takes a 1-byte
    `0xC0 + len` header, otherwise a `0xF7 + lenOfLen` header followed by the
    big-endian payload length.

    This is the formula `rlpListEncodedSize_spec` states inline
    (`RlpListEncodedSizeSAsm.lean:370-371`); naming it is what lets the bridge
    below be stated at all. Definitionally equal, so the machine proof is reached
    by `rfl`. -/
def rlesSize (v : Word) : Word :=
  if BitVec.ult v (56 : Word) then v + (1 : Word)
  else (v + BitVec.ofNat 64 (u64ByteLen v)) + (1 : Word)

/-- ⭐ **The list encoded-size bridge.** For any item list whose encoded payload is
    `v` bytes long, the guest's computed size is exactly
    `(EL.RLP.encode (.list items)).length` — so `rlp_list_encoded_size` inherits the
    RLP differential rather than resting on an unnamed local formula. -/
theorem rlesSize_eq_encode_list_length (items : List RLPItem) (v : Word)
    (hv : (encode.encodeItems items).length = v.toNat)
    (hbound : (encode.encodeItems items).length + 9 < 2 ^ 64) :
    rlesSize v = BitVec.ofNat 64 (encode (.list items)).length := by
  by_cases hshort : BitVec.ult v (56 : Word)
  · -- payload ≤ 55: one `0xC0 + len` header byte
    have hlt56 : v.toNat < 56 := by simpa [BitVec.ult] using hshort
    have hle : (encode.encodeItems items).length ≤ 55 := by omega
    rw [rlesSize, if_pos hshort, encode_list_short items hle]
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_cons, BitVec.toNat_add, BitVec.toNat_ofNat,
      show ((1 : Word)).toNat = 1 from rfl]
    omega
  · -- payload ≥ 56: `0xF7 + lenOfLen` header plus the big-endian length field
    have hge : 56 ≤ v.toNat := by
      simpa [BitVec.ult, Nat.not_lt] using hshort
    have hgt : 55 < (encode.encodeItems items).length := by omega
    have hL : (Nat.toBytesBE (encode.encodeItems items).length).length = u64ByteLen v := by
      rw [hv, ← u64ByteLen_eq_toBytesBE_length]
    have hLle : u64ByteLen v ≤ 8 := u64ByteLen_le v
    rw [rlesSize, if_neg hshort, encode_list_long items hgt]
    apply BitVec.eq_of_toNat_eq
    simp only [List.length_cons, List.length_append, hL, BitVec.toNat_add,
      BitVec.toNat_ofNat, show ((1 : Word)).toNat = 1 from rfl]
    omega

/-! ## Non-vacuity pins

    Both sides evaluated at the boundaries the formula branches on. `rlesSize` is
    checked against a directly-computed reference size so that a slip in the named
    definition cannot hide behind the `rfl` tie to the machine statement. -/

section Pins

/-- The reference list size, computed straight from `encode`. -/
private def refListSize (items : List RLPItem) : Nat := (encode (.list items)).length

/-- `n` single-byte items, so the payload is exactly `n` bytes. -/
private def ones (n : Nat) : List RLPItem :=
  List.replicate n (RLPItem.bytes [(0x01 : Byte)])

-- empty list, and either side of the 55/56 header split
#guard rlesSize 0 == BitVec.ofNat 64 (refListSize (ones 0))
#guard rlesSize 55 == BitVec.ofNat 64 (refListSize (ones 55))
#guard rlesSize 56 == BitVec.ofNat 64 (refListSize (ones 56))
-- either side of the 1-byte → 2-byte length-of-length step
#guard rlesSize 255 == BitVec.ofNat 64 (refListSize (ones 255))
#guard rlesSize 256 == BitVec.ofNat 64 (refListSize (ones 256))
-- the payload length really is the register argument in these fixtures
#guard (encode.encodeItems (ones 56)).length == 56
#guard (encode.encodeItems (ones 256)).length == 256

end Pins

/-! ## The consumer — the same triple, stated over the shared model -/

variable (v ret : Word)

/-- **`rlp_list_encoded_size` at its linked address, against `EL.RLP`.** Identical
    to `rlpListEncodedSize_spec` except that `a0` is pinned to
    `(encode (.list items)).length` — the shared-model function the differential
    covers — rather than to an inline formula. One rewrite, then the untouched
    machine proof. -/
theorem rlpListEncodedSize_encode_spec (items : List RLPItem)
    (hv : (encode.encodeItems items).length = v.toNat)
    (hbound : (encode.encodeItems items).length + 9 < 2 ^ 64)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 40 (GuestAddrs.rlp_list_encoded_size : Word) ret
      (CodeReq.ofProg (GuestAddrs.rlp_list_encoded_size : Word) rlpListEncodedSize_prog)
      (((.x10 : Reg) ↦ᵣ v) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6)
      (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode (.list items)).length) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6) := by
  rw [← rlesSize_eq_encode_list_length items v hv hbound]
  exact rlpListEncodedSize_spec v ret halignRet

end RlpListEncodedSizeSAsm

end EvmAsm.Codegen
