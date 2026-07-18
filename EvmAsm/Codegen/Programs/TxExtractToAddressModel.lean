/-
  Pure model for `tx_extract_to_address` success domain.

  Status codes match the guest routine:
    0 : success (to is 0 or 20 bytes)
    1 : tx_type_dispatch failed
    2 : `to` field extraction failed
-/

import EvmAsm.EL.RLP.Decode
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressModel

open EvmAsm.EL.RLP
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Rv64

/-- Field index of `to` by EIP-2718 type. -/
def toFieldIndex (ty : Nat) : Nat :=
  if ty = 0 then 3 else if ty = 1 then 4 else 5

/-- Decode outer/inner list payload items (canonical EL decode). -/
def decodeListItems (bs : List (BitVec 8)) : Option (List RLPItem) :=
  match decode bs with
  | some (.list items, rest) =>
    if rest.isEmpty then some items else none
  | _ => none

/-- Pure extract-to-address: (status, toBytes20-or-empty, isCreation).
    On non-success, toBytes is [] and isCreation is 0. -/
def teerExtractToAddress (txBytes : List (BitVec 8)) :
    Word × List (BitVec 8) × Word :=
  let st := (teerTxTypeDispatch txBytes).1
  let ty := (teerTxTypeDispatch txBytes).2.1
  let innerOff := (teerTxTypeDispatch txBytes).2.2
  if st ≠ (0 : Word) then
    ((1 : Word), [], (0 : Word))
  else
    let inner := txBytes.drop innerOff.toNat
    match decodeListItems inner with
    | none => ((2 : Word), [], (0 : Word))
    | some items =>
      match items[toFieldIndex ty.toNat]? with
      | some (.bytes content) =>
        if content.length = 0 then
          ((0 : Word), [], (1 : Word))
        else if content.length = 20 then
          ((0 : Word), content, (0 : Word))
        else
          ((2 : Word), [], (0 : Word))
      | _ => ((2 : Word), [], (0 : Word))

/-- Success-domain guard for ExtractAssumed packaging. -/
def extractSuccess (txBytes : List (BitVec 8)) : Prop :=
  (teerExtractToAddress txBytes).1 = (0 : Word)

theorem extractSuccess_status
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    (teerExtractToAddress txBytes).1 = (0 : Word) := h

/-- Success implies type_dispatch success (status 0). -/
theorem extractSuccess_type_ok
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    (teerTxTypeDispatch txBytes).1 = (0 : Word) := by
  by_cases hty : (teerTxTypeDispatch txBytes).1 = (0 : Word)
  · exact hty
  · have hfail : teerExtractToAddress txBytes = ((1 : Word), [], (0 : Word)) := by
      unfold teerExtractToAddress
      rw [if_pos hty]
    unfold extractSuccess at h
    rw [hfail] at h
    exact absurd h (by decide)

/-- Success outcome: status 0 with creation (empty to) or 20-byte to. -/
theorem extractSuccess_outcome
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    (teerTxTypeDispatch txBytes).1 = (0 : Word) ∧
      ∃ content isCre,
        teerExtractToAddress txBytes = ((0 : Word), content, isCre) ∧
        ((content = [] ∧ isCre = (1 : Word)) ∨
          (content.length = 20 ∧ isCre = (0 : Word))) := by
  have hty := extractSuccess_type_ok txBytes h
  refine ⟨hty, ?_⟩
  revert h
  unfold extractSuccess teerExtractToAddress
  intro h
  simp only [hty, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢
  cases hdec : decodeListItems
      (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) with
  | none =>
    simp only [hdec] at h
    exact absurd h (by decide)
  | some items =>
    simp only [hdec] at h ⊢
    cases hitem : items[toFieldIndex (teerTxTypeDispatch txBytes).2.1.toNat]? with
    | none =>
      simp only [hitem] at h
      exact absurd h (by decide)
    | some item =>
      cases item with
      | list _ =>
        simp only [hitem] at h
        exact absurd h (by decide)
      | bytes content =>
        simp only [hitem] at h ⊢
        by_cases h0 : content.length = 0
        · have hcre : content = [] := List.eq_nil_of_length_eq_zero h0
          subst hcre
          simp only [List.length_nil, ↓reduceIte] at h ⊢
          exact ⟨[], (1 : Word), rfl, Or.inl ⟨rfl, rfl⟩⟩
        · by_cases h20 : content.length = 20
          · rw [if_neg h0, if_pos h20] at h ⊢
            exact ⟨content, (0 : Word), rfl, Or.inr ⟨h20, rfl⟩⟩
          · rw [if_neg h0, if_neg h20] at h
            -- h : False (status 2 ≠ success 0)
            exact False.elim ((by decide : ¬((2 : Word) = 0)) h)

/-- Success + empty to-bytes ⇒ creation flag. -/
theorem extractSuccess_creation
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes)
    (hempty : (teerExtractToAddress txBytes).2.1 = []) :
    (teerExtractToAddress txBytes).2.2 = (1 : Word) := by
  obtain ⟨_, content, isCre, heq, hcases⟩ := extractSuccess_outcome txBytes h
  have hc : (teerExtractToAddress txBytes).2.1 = content := by
    rw [heq]
  have hi : (teerExtractToAddress txBytes).2.2 = isCre := by
    rw [heq]
  rw [hi]
  rw [hc] at hempty
  cases hcases with
  | inl hcre => exact hcre.2
  | inr hcopy =>
    have : content.length = 0 := by simp [hempty]
    omega

/-- Success + 20-byte to ⇒ non-creation. -/
theorem extractSuccess_copy
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes)
    (hlen : (teerExtractToAddress txBytes).2.1.length = 20) :
    (teerExtractToAddress txBytes).2.2 = (0 : Word) := by
  obtain ⟨_, content, isCre, heq, hcases⟩ := extractSuccess_outcome txBytes h
  have hc : (teerExtractToAddress txBytes).2.1 = content := by
    rw [heq]
  have hi : (teerExtractToAddress txBytes).2.2 = isCre := by
    rw [heq]
  rw [hi]
  rw [hc] at hlen
  cases hcases with
  | inl hcre =>
    have : content.length = 0 := by simp [hcre.1]
    omega
  | inr hcopy => exact hcopy.2

/-- Success ⇒ inner list at type-dispatch offset decodes. -/
theorem extractSuccess_decode
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    ∃ items, decodeListItems
        (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) = some items := by
  have hty := extractSuccess_type_ok txBytes h
  have hstat : (teerExtractToAddress txBytes).1 = (0 : Word) := h
  unfold teerExtractToAddress at hstat
  simp only [hty, ne_eq, not_true_eq_false, ↓reduceIte] at hstat
  cases hdec : decodeListItems
      (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) with
  | none =>
    simp only [hdec] at hstat
    exact absurd hstat (by decide)
  | some items =>
    -- `cases hdec` rewrites the goal LHS to `some items`
    exact ⟨items, rfl⟩

/-- Success ⇒ `to` field is a bytes item at the type-dependent index. -/
theorem extractSuccess_to_field
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    ∃ items content,
      decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
        some items ∧
      items[toFieldIndex (teerTxTypeDispatch txBytes).2.1.toNat]? =
        some (.bytes content) ∧
      ((content = [] ∧ (teerExtractToAddress txBytes).2.2 = (1 : Word)) ∨
        (content.length = 20 ∧ (teerExtractToAddress txBytes).2.2 = (0 : Word))) := by
  have hty := extractSuccess_type_ok txBytes h
  have hstat : (teerExtractToAddress txBytes).1 = (0 : Word) := h
  unfold teerExtractToAddress at hstat
  simp only [hty, ne_eq, not_true_eq_false, ↓reduceIte] at hstat
  cases hdec : decodeListItems
      (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) with
  | none =>
    simp only [hdec] at hstat
    exact absurd hstat (by decide)
  | some items =>
    simp only [hdec] at hstat
    cases hitem : items[toFieldIndex (teerTxTypeDispatch txBytes).2.1.toNat]? with
    | none =>
      simp only [hitem] at hstat
      exact absurd hstat (by decide)
    | some item =>
      cases item with
      | list _ =>
        simp only [hitem] at hstat
        exact absurd hstat (by decide)
      | bytes content =>
        simp only [hitem] at hstat
        by_cases h0 : content.length = 0
        · have hcre : content = [] := List.eq_nil_of_length_eq_zero h0
          subst hcre
          simp only [List.length_nil, ↓reduceIte] at hstat
          have hisCre : (teerExtractToAddress txBytes).2.2 = (1 : Word) := by
            unfold teerExtractToAddress
            simp only [hty, ne_eq, not_true_eq_false, ↓reduceIte, hdec, hitem,
              List.length_nil, ↓reduceIte]
          exact ⟨items, [], rfl, hitem, Or.inl ⟨rfl, hisCre⟩⟩
        · by_cases h20 : content.length = 20
          · simp only [if_neg h0, if_pos h20] at hstat
            have hisCre : (teerExtractToAddress txBytes).2.2 = (0 : Word) := by
              unfold teerExtractToAddress
              simp only [hty, ne_eq, not_true_eq_false, ↓reduceIte, hdec, hitem,
                if_neg h0, if_pos h20]
            exact ⟨items, content, rfl, hitem, Or.inr ⟨h20, hisCre⟩⟩
          · simp only [if_neg h0, if_neg h20] at hstat
            exact False.elim ((by decide : ¬((2 : Word) = 0)) hstat)

/-- Type-dispatch success type is one of 0..4 (legacy / 1..4). -/
theorem teer_success_type_le4 (txBytes : List (BitVec 8))
    (h : (teerTxTypeDispatch txBytes).1 = (0 : Word)) :
    (teerTxTypeDispatch txBytes).2.1.toNat ≤ 4 := by
  match txBytes with
  | [] =>
    simp only [teerTxTypeDispatch] at h
    exact absurd h (by decide)
  | b :: rest =>
    simp only [teerTxTypeDispatch] at h ⊢
    by_cases hleg : 192 ≤ b.toNat
    · simp only [hleg, ↓reduceIte] at h ⊢
      decide
    · simp only [hleg, ↓reduceIte] at h ⊢
      by_cases h1 : b = (1 : BitVec 8)
      · simp only [h1, ↓reduceIte] at h ⊢; decide
      · simp only [h1, ↓reduceIte] at h ⊢
        by_cases h2 : b = (2 : BitVec 8)
        · simp only [h2, ↓reduceIte] at h ⊢; decide
        · simp only [h2, ↓reduceIte] at h ⊢
          by_cases h3 : b = (3 : BitVec 8)
          · simp only [h3, ↓reduceIte] at h ⊢; decide
          · simp only [h3, ↓reduceIte] at h ⊢
            by_cases h4 : b = (4 : BitVec 8)
            · simp only [h4, ↓reduceIte] at h ⊢; decide
            · simp only [h4, ↓reduceIte] at h
              exact absurd h (by decide)

/-- Success ⇒ type word ≤ 4. -/
theorem extractSuccess_type_le4 (txBytes : List (BitVec 8))
    (h : extractSuccess txBytes) :
    (teerTxTypeDispatch txBytes).2.1.toNat ≤ 4 :=
  teer_success_type_le4 txBytes (extractSuccess_type_ok txBytes h)

/-- Creation path pure: empty to-bytes ⇒ length 0 (for hcre residual). -/
theorem extractSuccess_creation_len
    (txBytes : List (BitVec 8))
    (hempty : (teerExtractToAddress txBytes).2.1 = []) :
    (teerExtractToAddress txBytes).2.1.length = 0 := by
  simp only [hempty, List.length_nil]

/-- `to` field index by type. -/
theorem toFieldIndex_legacy : toFieldIndex 0 = 3 := rfl
theorem toFieldIndex_t1 : toFieldIndex 1 = 4 := rfl
theorem toFieldIndex_type234 (ty : Nat) (h2 : 2 ≤ ty) (_h4 : ty ≤ 4) :
    toFieldIndex ty = 5 := by
  unfold toFieldIndex
  have hne0 : ty ≠ 0 := by omega
  have hne1 : ty ≠ 1 := by omega
  simp only [hne0, ↓reduceIte, hne1, ↓reduceIte]

/-- Success ⇒ type is 0..4 with matching `to` field index. -/
theorem extractSuccess_toFieldIndex
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    toFieldIndex (teerTxTypeDispatch txBytes).2.1.toNat =
      (if (teerTxTypeDispatch txBytes).2.1.toNat = 0 then 3
       else if (teerTxTypeDispatch txBytes).2.1.toNat = 1 then 4
       else 5) := by
  have _hle := extractSuccess_type_le4 txBytes h
  rfl

/-- Successful list decode implies nonempty buffer. -/
theorem decodeListItems_some_ne_nil {bs : List Byte} {items : List RLPItem}
    (h : decodeListItems bs = some items) : bs ≠ [] := by
  intro hnil
  subst hnil
  -- decodeListItems [] unfolds to match decode [] = none
  simp only [decodeListItems, decode, decodeAux] at h
  exact (nomatch h : False)

/-- `drop n ≠ []` ⇒ `n < length`. -/
private theorem drop_ne_nil_lt_length {α : Type _} (l : List α) (n : Nat)
    (hne : l.drop n ≠ []) : n < l.length := by
  by_contra hge
  have hle : l.length ≤ n := Nat.le_of_not_gt hge
  have hnil : l.drop n = [] := List.drop_eq_nil_of_le hle
  exact hne hnil

/-- Success ⇒ type-dispatch inner offset is in bounds (walk_init `hoff`). -/
theorem extractSuccess_inner_lt
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length := by
  obtain ⟨items, hdec⟩ := extractSuccess_decode txBytes h
  have hne := decodeListItems_some_ne_nil hdec
  exact drop_ne_nil_lt_length txBytes _ hne

/-- Success ⇒ type234 path uses field index 5 (six walk_nexts: skip 0..4, read 5). -/
theorem extractSuccess_type234_toFieldIndex
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes)
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat) :
    toFieldIndex (teerTxTypeDispatch txBytes).2.1.toNat = 5 := by
  have hle := extractSuccess_type_le4 txBytes h
  exact toFieldIndex_type234 _ hge hle

/-- Creation under success: `to` content is empty (hcre pure half). -/
theorem extractSuccess_creation_to_empty
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes)
    (hcre : (teerExtractToAddress txBytes).2.2 = (1 : Word)) :
    (teerExtractToAddress txBytes).2.1 = [] := by
  obtain ⟨_, content, isCre, heq, hcases⟩ := extractSuccess_outcome txBytes h
  have hc : (teerExtractToAddress txBytes).2.1 = content := by rw [heq]
  have hi : (teerExtractToAddress txBytes).2.2 = isCre := by rw [heq]
  rw [hi] at hcre
  cases hcases with
  | inl h0 =>
    rw [hc, h0.1]
  | inr h20 =>
    have : isCre = (0 : Word) := h20.2
    rw [this] at hcre
    exact absurd hcre (by decide)

/-- Copy under success: `to` content length is 20 (hlen20 pure half). -/
theorem extractSuccess_copy_to_len20
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes)
    (hcopy : (teerExtractToAddress txBytes).2.2 = (0 : Word)) :
    (teerExtractToAddress txBytes).2.1.length = 20 := by
  obtain ⟨_, content, isCre, heq, hcases⟩ := extractSuccess_outcome txBytes h
  have hc : (teerExtractToAddress txBytes).2.1 = content := by rw [heq]
  have hi : (teerExtractToAddress txBytes).2.2 = isCre := by rw [heq]
  rw [hi] at hcopy
  cases hcases with
  | inl h0 =>
    have : isCre = (1 : Word) := h0.2
    rw [this] at hcopy
    exact absurd hcopy (by decide)
  | inr h20 =>
    rw [hc, h20.1]

#print axioms extractSuccess_type_ok
#print axioms extractSuccess_outcome
#print axioms extractSuccess_creation
#print axioms extractSuccess_copy
#print axioms extractSuccess_decode
#print axioms extractSuccess_to_field
#print axioms extractSuccess_type_le4
#print axioms teer_success_type_le4
#print axioms extractSuccess_creation_len
#print axioms extractSuccess_inner_lt
#print axioms extractSuccess_type234_toFieldIndex
#print axioms extractSuccess_creation_to_empty
#print axioms extractSuccess_copy_to_len20

end EvmAsm.Codegen.TxExtractToAddressModel
