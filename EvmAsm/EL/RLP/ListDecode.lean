/-
  EvmAsm.EL.RLP.ListDecode

  Pure-spec lemmas about `decodeItems` (list payload decode), supporting the
  RV64 list decoder. First slice: a list whose every byte is a single-byte item
  (`< 0x80`) decodes to the corresponding list of one-byte `RLPItem.bytes`.
-/

import EvmAsm.EL.RLP.PrefixDecode
import EvmAsm.EL.RLP.ListDecodeBridge

namespace EvmAsm.EL.RLP

/-- A run of single-byte items (`bs`, every byte `< 0x80`) decodes to one
    one-byte `RLPItem` per byte, consuming the whole run. The depth budget
    `2 * bs.length ≤ nDepth` matches the `decodeItems`/`decodeAux` per-item cost
    (one level each). -/
theorem decodeItems_singleByte_run :
    ∀ (bs : List Byte) (nDepth : Nat),
      (∀ b ∈ bs, b.toNat < 0x80) → 2 * bs.length ≤ nDepth →
      decodeItems nDepth bs = some (bs.map (fun b => RLPItem.bytes [b]), []) := by
  intro bs
  induction bs with
  | nil =>
    intro nDepth _ _
    simp only [decodeItems]; rfl
  | cons b bs ih =>
    intro nDepth hb hd
    simp only [List.length_cons] at hd
    -- nDepth ≥ 2*(bs.length+1) ≥ 2, so nDepth = m+1 with m ≥ 1.
    obtain ⟨m, rfl⟩ : ∃ m, nDepth = m + 1 := ⟨nDepth - 1, by omega⟩
    have hbhd : b.toNat < 0x80 := hb b (by simp)
    have hclass : classifyPrefix b = .singleByte :=
      (classifyPrefix_singleByte_iff b).mpr hbhd
    have haux : decodeAux m (b :: bs) = some (.bytes [b], bs) := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact decodeAux_cons_singleByte_of_classifyPrefix m' b bs hclass
    have hrec : decodeItems m bs = some (bs.map (fun b => RLPItem.bytes [b]), []) :=
      ih m (fun x hx => hb x (by simp [hx])) (by omega)
    simp [decodeItems, haux, hrec]

/-- A **short list** whose payload is a run of single-byte items decodes to the
    structured `RLPItem.list` of one-byte items, consuming exactly the list. -/
theorem decodeAux_shortList_of_singleByte_items
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (hlen : rlpPrefixShortListPayloadLen pfx ≤ rest.length)
    (hsingle : ∀ b ∈ rest.take (rlpPrefixShortListPayloadLen pfx), b.toNat < 0x80)
    (hdepth : 2 * rlpPrefixShortListPayloadLen pfx ≤ nDepth) :
    decodeAux (nDepth + 1) (pfx :: rest)
      = some (.list ((rest.take (rlpPrefixShortListPayloadLen pfx)).map
                (fun b => RLPItem.bytes [b])),
              rest.drop (rlpPrefixShortListPayloadLen pfx)) := by
  have hitems := decodeItems_singleByte_run
    (rest.take (rlpPrefixShortListPayloadLen pfx)) nDepth hsingle
    (by rw [List.length_take, Nat.min_eq_left hlen]; exact hdepth)
  -- Discharge via the merged short-list characterization: the payload slice is
  -- available (`takeBytes`) and decodes exactly (`decodeListPayload`).
  refine (ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff
    nDepth pfx rest h_class _ _).mpr ?_
  refine ⟨rest.take (rlpPrefixShortListPayloadLen pfx), ?_, ?_⟩
  · simp only [takeBytes]; rw [if_pos (by omega)]
  · exact ListDecodeBridge.decodeListPayload_eq_some_of_decodeItems_empty hitems

/-- Cross-check against ground truth: the canonical short list
    `0xC3 [0x01, 0x7F, 0x05]` (prefix `0xC3` = list, 3-byte payload) decodes to its
    three single-byte items with nothing left over. -/
example :
    decodeAux 8 (0xc3 :: [0x01, 0x7f, 0x05])
      = some (.list [.bytes [0x01], .bytes [0x7f], .bytes [0x05]], []) := by
  have h := decodeAux_shortList_of_singleByte_items 7 0xc3 [0x01, 0x7f, 0x05]
    (by decide) (by decide) (by decide) (by decide)
  simpa using h
