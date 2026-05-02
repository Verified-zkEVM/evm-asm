/-
  EvmAsm.EL.RLP.PrefixDecode

  Bridges from the pure RLP prefix classifier to the canonical decoder.
-/

import EvmAsm.EL.RLP.Decode
import EvmAsm.EL.RLP.Prefix

namespace EvmAsm.EL.RLP

/-- A classified single-byte prefix selects the single-byte `decodeAux` branch. -/
theorem decodeAux_cons_singleByte_of_classifyPrefix
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .singleByte) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.bytes [pfx], rest) := by
  have h_lt := (classifyPrefix_singleByte_iff pfx).mp h
  simp [decodeAux, h_lt]

/-- A classified short-byte-string prefix selects the short-string branch. -/
theorem decodeAux_cons_shortBytes_of_classifyPrefix
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .shortBytes) :
    decodeAux (fuel + 1) (pfx :: rest) =
      (do
        let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
        match data with
        | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
        | _ => some (.bytes data, rest')) := by
  have h_range := (classifyPrefix_shortBytes_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  simp [decodeAux, rlpPrefixShortBytesPayloadLen, h_not_lt, h_range.2]
  rfl

/-- A classified long-byte-string prefix selects the long-string branch. -/
theorem decodeAux_cons_longBytes_of_classifyPrefix
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .longBytes) :
    decodeAux (fuel + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (data, rest'') ← takeBytes rest' lenVal
          some (.bytes data, rest'')) := by
  have h_range := (classifyPrefix_longBytes_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_short : ¬ pfx.toNat ≤ 0xB7 := by omega
  simp [decodeAux, rlpPrefixLongBytesLenOfLen,
    h_not_lt, h_not_short, h_range.2]

/-- A classified short-list prefix selects the short-list branch. -/
theorem decodeAux_cons_shortList_of_classifyPrefix
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .shortList) :
    decodeAux (fuel + 1) (pfx :: rest) =
      (do
        let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
        let (items, leftover) ← decodeItems fuel payload
        if List.isEmpty leftover then some (.list items, rest') else none) := by
  have h_range := (classifyPrefix_shortList_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_shortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have h_not_longBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  simp [decodeAux, rlpPrefixShortListPayloadLen,
    h_not_lt, h_not_shortBytes, h_not_longBytes, h_range.2]

/-- A classified long-list prefix selects the long-list branch. -/
theorem decodeAux_cons_longList_of_classifyPrefix
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h : classifyPrefix pfx = .longList) :
    decodeAux (fuel + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (payload, rest'') ← takeBytes rest' lenVal
          let (items, leftover) ← decodeItems fuel payload
          if List.isEmpty leftover then some (.list items, rest'') else none) := by
  have h_range := (classifyPrefix_longList_iff pfx).mp h
  have h_not_lt : ¬ pfx.toNat < 0x80 := by omega
  have h_not_shortBytes : ¬ pfx.toNat ≤ 0xB7 := by omega
  have h_not_longBytes : ¬ pfx.toNat ≤ 0xBF := by omega
  have h_not_shortList : ¬ pfx.toNat ≤ 0xF7 := by omega
  simp [decodeAux, rlpPrefixLongListLenOfLen,
    h_not_lt, h_not_shortBytes, h_not_longBytes, h_not_shortList]

/--
  Classifier-dispatch form of the `decodeAux` prefix branch equations. This
  packages the five class-specific bridge lemmas into one semantic target for
  executable prefix classifiers.
-/
theorem decodeAux_cons_eq_classifyPrefix_match
    (fuel : Nat) (pfx : Byte) (rest : List Byte) :
    decodeAux (fuel + 1) (pfx :: rest) =
      match classifyPrefix pfx with
      | .singleByte => some (.bytes [pfx], rest)
      | .shortBytes =>
          (do
            let (data, rest') ← takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
            match data with
            | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
            | _ => some (.bytes data, rest'))
      | .longBytes =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongBytesLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (data, rest'') ← takeBytes rest' lenVal
              some (.bytes data, rest''))
      | .shortList =>
          (do
            let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
            let (items, leftover) ← decodeItems fuel payload
            if List.isEmpty leftover then some (.list items, rest') else none)
      | .longList =>
          (do
            let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
            if lenVal ≤ 55 then none
            else do
              let (payload, rest'') ← takeBytes rest' lenVal
              let (items, leftover) ← decodeItems fuel payload
              if List.isEmpty leftover then some (.list items, rest'') else none) := by
  cases h : classifyPrefix pfx
  · rw [decodeAux_cons_singleByte_of_classifyPrefix fuel pfx rest h]
  · rw [decodeAux_cons_shortBytes_of_classifyPrefix fuel pfx rest h]
  · rw [decodeAux_cons_longBytes_of_classifyPrefix fuel pfx rest h]
  · rw [decodeAux_cons_shortList_of_classifyPrefix fuel pfx rest h]
  · rw [decodeAux_cons_longList_of_classifyPrefix fuel pfx rest h]

end EvmAsm.EL.RLP
