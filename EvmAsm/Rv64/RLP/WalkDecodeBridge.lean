/-
  EvmAsm.Rv64.RLP.WalkDecodeBridge

  Bridges the machine-level RLP item view used by the verified walk routines
  (`rlp_walk_next` / `rlpItemDecode`: a byte list with a `Nat` offset, prefix-range
  guards, and a content slice) to the pure spec decoder `EvmAsm.EL.RLP.decodeAux`.

  These lemmas are the reusable heart of anchoring walk-based decoders (e.g. the
  verified `withdrawal_decode`) on the pure `decodeFully` / `decodeWithdrawal`.
  This file covers the **byte-string** item classes (single byte, short byte string)
  — the only forms a fixed `uint64` / 20-byte-address field can take.
-/

import EvmAsm.EL.RLP.PrefixDecode
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- A byte present at offset `off` peels off the front of `drop off`. -/
theorem drop_eq_cons_of_getElem? {bytes : List Byte} {off : Nat} {b : Byte}
    (hget : bytes[off]? = some b) :
    bytes.drop off = b :: bytes.drop (off + 1) := by
  have hlt : off < bytes.length := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.1
  have hb : bytes[off] = b := by
    rw [List.getElem?_eq_getElem hlt] at hget; exact Option.some.inj hget
  rw [List.drop_eq_getElem_cons hlt, hb]

/-- **Single-byte bridge.** A byte `b < 0x80` at offset `off` decodes (with any positive
    fuel) to the single-byte item `.bytes [b]`, consuming exactly one byte. -/
theorem decodeAux_singleByte_bridge (bytes : List Byte) (off : Nat) (b : Byte)
    (hget : bytes[off]? = some b) (hsingle : b.toNat < 0x80) (n : Nat) :
    decodeAux (n + 1) (bytes.drop off) = some (.bytes [b], bytes.drop (off + 1)) := by
  rw [drop_eq_cons_of_getElem? hget]
  exact decodeAux_cons_singleByte_of_classifyPrefix n b (bytes.drop (off + 1))
    ((classifyPrefix_singleByte_iff b).mpr hsingle)

set_option maxRecDepth 8000 in
/-- **Short-byte-string bridge.** A prefix `b ∈ [0x80, 0xB7]` at offset `off`, with the
    declared `len = b - 0x80` content bytes available and (for `len = 1`) a canonical
    content byte `≥ 0x80`, decodes (with any positive fuel) to `.bytes content` where
    `content = (drop (off+1)).take len`, consuming `1 + len` bytes total. -/
theorem decodeAux_shortBytes_bridge (bytes : List Byte) (off : Nat) (b : Byte)
    (hget : bytes[off]? = some b) (hlo : 0x80 ≤ b.toNat) (hhi : b.toNat ≤ 0xB7)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length)
    (hcanon : b.toNat - 0x80 = 1 →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80)
    (n : Nat) :
    decodeAux (n + 1) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)),
        bytes.drop (off + 1 + (b.toNat - 0x80))) := by
  rw [drop_eq_cons_of_getElem? hget,
    decodeAux_cons_shortBytes_of_classifyPrefix n b (bytes.drop (off + 1))
      ((classifyPrefix_shortBytes_iff b).mpr ⟨hlo, hhi⟩)]
  -- The payload length encoded in the prefix is `b - 0x80`.
  have hpl : rlpPrefixShortBytesPayloadLen b = b.toNat - 0x80 := rfl
  rw [hpl]
  -- `takeBytes (drop (off+1)) len` succeeds: enough bytes remain.
  have htk : takeBytes (bytes.drop (off + 1)) (b.toNat - 0x80) =
      some ((bytes.drop (off + 1)).take (b.toNat - 0x80),
        bytes.drop (off + 1 + (b.toNat - 0x80))) := by
    have hge : b.toNat - 0x80 ≤ (bytes.drop (off + 1)).length := by
      rw [List.length_drop]; omega
    rw [takeBytes_length_ge hge, List.drop_drop]
  rw [htk]
  -- Generalize the content list to a variable, then case on it: the monadic bind and the
  -- single-byte canonicality `match` reduce concretely per case (no `simp` recursion into
  -- the symbolic `take`/`drop`).
  generalize hC : (bytes.drop (off + 1)).take (b.toNat - 0x80) = C
  rcases C with _ | ⟨b0, _ | ⟨c0, t⟩⟩
  · rfl
  · -- singleton content `[b0]` ⇒ `len = 1` ⇒ canonical content byte `≥ 0x80`.
    have hlen1 : b.toNat - 0x80 = 1 := by
      have hl := congrArg List.length hC
      simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at hl
      omega
    obtain ⟨c, hcget, hcge⟩ := hcanon hlen1
    have hcc : (bytes.drop (off + 1)).take (b.toNat - 0x80) = [c] := by
      rw [hlen1, drop_eq_cons_of_getElem? hcget]; rfl
    rw [hcc] at hC
    have hbc' : b0.toNat = c.toNat := by rw [(by simpa using hC.symm : b0 = c)]
    simp only [Nat.not_lt] at hcge
    simp only [Option.bind_eq_bind, Option.bind_some, if_neg (by omega : ¬ b0.toNat < 0x80)]
  · rfl

/-! ### `decodeItems` composition steps

These chain a byte-string item bridge with the recursive item decoder, so a payload that is a
run of byte-string items (as the verified walk produces them) decodes as the corresponding
`.bytes` item list. Fuel is `n + 2` at the outer level so the inner `decodeAux` runs at `n + 1`
(the bridge's positive-fuel form) and the recursive `decodeItems` continues at `n + 1`. -/

/-- One `decodeItems` step over a single-byte item at offset `off`. -/
theorem decodeItems_cons_singleByte (bytes : List Byte) (off : Nat) (b : Byte)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hget : bytes[off]? = some b) (hsingle : b.toNat < 0x80)
    (hrest : decodeItems (n + 1) (bytes.drop (off + 1)) = some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) = some (.bytes [b] :: items, rest') := by
  have hne : bytes.drop off ≠ [] := by rw [drop_eq_cons_of_getElem? hget]; simp
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne,
    decodeAux_singleByte_bridge bytes off b hget hsingle n]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]

set_option maxRecDepth 8000 in
/-- One `decodeItems` step over a short-byte-string item at offset `off`. -/
theorem decodeItems_cons_shortBytes (bytes : List Byte) (off : Nat) (b : Byte)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hget : bytes[off]? = some b) (hlo : 0x80 ≤ b.toNat) (hhi : b.toNat ≤ 0xB7)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length)
    (hcanon : b.toNat - 0x80 = 1 →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80)
    (hrest : decodeItems (n + 1) (bytes.drop (off + 1 + (b.toNat - 0x80))) = some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)) :: items, rest') := by
  have hne : bytes.drop off ≠ [] := by rw [drop_eq_cons_of_getElem? hget]; simp
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne,
    decodeAux_shortBytes_bridge bytes off b hget hlo hhi hlen hcanon n]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]
