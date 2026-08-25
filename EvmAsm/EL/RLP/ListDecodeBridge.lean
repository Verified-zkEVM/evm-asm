/-
  EvmAsm.EL.RLP.ListDecodeBridge

  Semantic bridge for Phase 5 list-payload decoding (GH #120).
-/

module

public import EvmAsm.EL.RLP.PrefixDecode

@[expose] public section

namespace EvmAsm.EL.RLP

namespace ListDecodeBridge

/-- Decode an RLP list payload and require that the payload decoder consumes
    the payload exactly. Distinctive token: ListDecodeBridge.decodeListPayload
    #120. -/
def decodeListPayload (nDepth : Nat) (payload : List Byte) : Option (List RLPItem) := do
  let (items, leftover) ← decodeItems nDepth payload
  if List.isEmpty leftover then some items else none

theorem decodeListPayload_eq_some_of_decodeItems_empty
    {nDepth : Nat} {payload : List Byte} {items : List RLPItem}
    (h_decode : decodeItems nDepth payload = some (items, [])) :
    decodeListPayload nDepth payload = some items := by
  simp [decodeListPayload, h_decode]

/--
List-payload decode succeeds exactly when recursive item decoding consumes the
whole payload.

Distinctive token: ListDecodeBridge.decodeListPayload_eq_some_iff #120.
-/
theorem decodeListPayload_eq_some_iff
    (nDepth : Nat) (payload : List Byte) (items : List RLPItem) :
    decodeListPayload nDepth payload = some items ↔
      decodeItems nDepth payload = some (items, []) := by
  unfold decodeListPayload
  cases h_decode : decodeItems nDepth payload with
  | none => simp
  | some decoded =>
      cases decoded with
      | mk decodedItems leftover =>
          cases leftover <;> simp

/--
List-payload decode is non-failing exactly when recursive item decoding
consumes the whole payload for some item list.

Distinctive token:
ListDecodeBridge.decodeListPayload_ne_none_iff_exists_decodeItems_empty #120.
-/
theorem decodeListPayload_ne_none_iff_exists_decodeItems_empty
    (nDepth : Nat) (payload : List Byte) :
    decodeListPayload nDepth payload ≠ none ↔
      ∃ items, decodeItems nDepth payload = some (items, []) := by
  constructor
  · intro h_ne
    cases h_decode : decodeListPayload nDepth payload with
    | none => contradiction
    | some items =>
        exact ⟨items,
          (decodeListPayload_eq_some_iff nDepth payload items).mp h_decode⟩
  · rintro ⟨items, h_decode⟩ h_none
    have h_some :
        decodeListPayload nDepth payload = some items :=
      (decodeListPayload_eq_some_iff nDepth payload items).mpr h_decode
    rw [h_some] at h_none
    contradiction

theorem decodeListPayload_eq_none_of_decodeItems_none
    {nDepth : Nat} {payload : List Byte}
    (h_decode : decodeItems nDepth payload = none) :
    decodeListPayload nDepth payload = none := by
  simp [decodeListPayload, h_decode]

theorem decodeListPayload_eq_none_of_leftover
    {nDepth : Nat} {payload : List Byte} {items : List RLPItem} {leftover : List Byte}
    (h_decode : decodeItems nDepth payload = some (items, leftover))
    (h_leftover : leftover ≠ []) :
    decodeListPayload nDepth payload = none := by
  cases leftover with
  | nil =>
      contradiction
  | cons b bs =>
      simp [decodeListPayload, h_decode]

/--
List-payload decode failure is exactly either recursive decoder failure or
successful payload-prefix decode with trailing bytes left over.

Distinctive token: ListDecodeBridge.decodeListPayload_eq_none_iff #120.
-/
theorem decodeListPayload_eq_none_iff (nDepth : Nat) (payload : List Byte) :
    decodeListPayload nDepth payload = none ↔
      decodeItems nDepth payload = none ∨
        ∃ items leftover,
          decodeItems nDepth payload = some (items, leftover) ∧ leftover ≠ [] := by
  unfold decodeListPayload
  cases h_decode : decodeItems nDepth payload with
  | none => simp
  | some decoded =>
      cases decoded with
      | mk items leftover =>
          cases leftover with
          | nil => simp
          | cons b rest =>
              constructor
              · intro _
                exact Or.inr ⟨items, b :: rest, rfl, by simp⟩
              · intro _
                rfl

theorem decodeAux_cons_shortList_eq_decodeListPayload
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
        let items ← decodeListPayload nDepth payload
        some (.list items, rest')) := by
  rw [decodeAux_cons_shortList_of_classifyPrefix nDepth pfx rest h_class]
  cases h_take : takeBytes rest (rlpPrefixShortListPayloadLen pfx) with
  | none =>
      simp [decodeListPayload]
  | some pair =>
      rcases pair with ⟨payload, rest'⟩
      cases h_decode : decodeItems nDepth payload with
      | none =>
          simp [decodeListPayload, h_decode]
      | some pair' =>
          rcases pair' with ⟨items, leftover⟩
          cases leftover <;> simp [decodeListPayload, h_decode]

/--
Classified short-list decode succeeds exactly when the payload slice is
available and list-payload decoding consumes it exactly.

Distinctive token:
ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff #120.
-/
theorem decodeAux_cons_shortList_eq_some_iff
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (items : List RLPItem) (rest' : List Byte) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.list items, rest') ↔
      ∃ payload,
        takeBytes rest (rlpPrefixShortListPayloadLen pfx) = some (payload, rest') ∧
          decodeListPayload nDepth payload = some items := by
  rw [decodeAux_cons_shortList_eq_decodeListPayload nDepth pfx rest h_class]
  cases h_take : takeBytes rest (rlpPrefixShortListPayloadLen pfx) with
  | none =>
      simp
  | some pair =>
      rcases pair with ⟨payload, slicedRest⟩
      cases h_payload : decodeListPayload nDepth payload with
      | none =>
          simp [h_payload]
      | some decodedItems =>
          constructor
          · intro h_some
            simp [h_payload] at h_some
            exact ⟨payload, by simp [h_some.2],
              by simpa [h_some.1] using h_payload⟩
          · rintro ⟨payload', h_take', h_decode'⟩
            have h_pair : (payload, slicedRest) = (payload', rest') := by
              simpa [h_take] using h_take'
            have h_payload_eq : payload = payload' := congrArg Prod.fst h_pair
            have h_rest_eq : slicedRest = rest' := congrArg Prod.snd h_pair
            have h_decode_payload :
                decodeListPayload nDepth payload = some items := by
              simpa [h_payload_eq] using h_decode'
            have h_items : decodedItems = items :=
              Option.some.inj (h_payload.symm.trans h_decode_payload)
            simp [h_payload, h_items, h_rest_eq]

theorem decodeAux_cons_longList_eq_decodeListPayload
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (payload, rest'') ← takeBytes rest' lenVal
          let items ← decodeListPayload nDepth payload
          some (.list items, rest'')) := by
  rw [decodeAux_cons_longList_of_classifyPrefix nDepth pfx rest h_class]
  cases h_read : readLength rest (rlpPrefixLongListLenOfLen pfx) with
  | none =>
      simp [decodeListPayload]
  | some pair =>
      rcases pair with ⟨lenVal, rest'⟩
      by_cases h_short : lenVal ≤ 55
      · simp [decodeListPayload, h_short]
      · cases h_take : takeBytes rest' lenVal with
        | none =>
            simp [decodeListPayload, h_short, h_take]
        | some pair' =>
            rcases pair' with ⟨payload, rest''⟩
            cases h_decode : decodeItems nDepth payload with
            | none =>
                simp [decodeListPayload, h_short, h_take, h_decode]
            | some pair'' =>
                rcases pair'' with ⟨items, leftover⟩
                cases leftover <;> simp [decodeListPayload, h_short, h_take, h_decode]

/--
Classified long-list decode succeeds exactly when the long-form length field is
canonical, the payload slice is available, and list-payload decoding consumes
that payload exactly.

Distinctive token:
ListDecodeBridge.decodeAux_cons_longList_eq_some_iff #120.
-/
theorem decodeAux_cons_longList_eq_some_iff
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longList)
    (items : List RLPItem) (outRest : List Byte) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.list items, outRest) ↔
      ∃ lenVal rest' payload,
        readLength rest (rlpPrefixLongListLenOfLen pfx) = some (lenVal, rest') ∧
          55 < lenVal ∧
            takeBytes rest' lenVal = some (payload, outRest) ∧
              decodeListPayload nDepth payload = some items := by
  rw [decodeAux_cons_longList_eq_decodeListPayload nDepth pfx rest h_class]
  cases h_read : readLength rest (rlpPrefixLongListLenOfLen pfx) with
  | none =>
      simp
  | some pair =>
      rcases pair with ⟨lenVal, rest'⟩
      by_cases h_short : lenVal ≤ 55
      · constructor
        · intro h_some
          simp [h_short] at h_some
        · rintro ⟨lenVal', rest'', payload', h_read', h_long', h_take',
            h_decode'⟩
          have h_read_pair : (lenVal, rest') = (lenVal', rest'') := by
            simpa [h_read] using h_read'
          have h_len_eq : lenVal = lenVal' := congrArg Prod.fst h_read_pair
          omega
      · cases h_take : takeBytes rest' lenVal with
        | none =>
            simp [h_short, h_take, Option.bind]
        | some pair' =>
            rcases pair' with ⟨payload, slicedRest⟩
            cases h_payload : decodeListPayload nDepth payload with
            | none =>
                simp [h_short, h_take, h_payload, Option.bind]
            | some decodedItems =>
                constructor
                · intro h_some
                  simp [h_short, h_take, h_payload, Option.bind] at h_some
                  have h_long : 55 < lenVal := by omega
                  have h_take_out :
                      takeBytes rest' lenVal = some (payload, outRest) := by
                    rw [← h_some.2]
                    exact h_take
                  have h_decode_items :
                      decodeListPayload nDepth payload = some items := by
                    rw [← h_some.1]
                    exact h_payload
                  refine Exists.intro lenVal ?_
                  refine Exists.intro rest' ?_
                  refine Exists.intro payload ?_
                  constructor
                  · rfl
                  constructor
                  · exact h_long
                  constructor
                  · exact h_take_out
                  · exact h_decode_items
                · rintro ⟨lenVal', rest'', payload', h_read', _h_long',
                    h_take', h_decode'⟩
                  have h_read_pair : (lenVal, rest') = (lenVal', rest'') := by
                    simpa [h_read] using h_read'
                  have h_len_eq : lenVal = lenVal' := congrArg Prod.fst h_read_pair
                  have h_rest_eq : rest' = rest'' := congrArg Prod.snd h_read_pair
                  have h_take_payload :
                      takeBytes rest' lenVal = some (payload', outRest) := by
                    simpa [h_len_eq, h_rest_eq] using h_take'
                  have h_take_pair : (payload, slicedRest) = (payload', outRest) := by
                    simpa [h_take] using h_take_payload
                  have h_payload_eq : payload = payload' := congrArg Prod.fst h_take_pair
                  have h_sliced_eq : slicedRest = outRest := congrArg Prod.snd h_take_pair
                  have h_decode_payload :
                      decodeListPayload nDepth payload = some items := by
                    simpa [h_payload_eq] using h_decode'
                  have h_items : decodedItems = items :=
                    Option.some.inj (h_payload.symm.trans h_decode_payload)
                  simp [h_short, h_take, h_payload, h_items, h_sliced_eq,
                    Option.bind]

end ListDecodeBridge

end EvmAsm.EL.RLP
