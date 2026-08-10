/-
  EvmAsm.EL.RLP.LongSpan

  **Encoded-span lemmas for the RLP long forms** (GH #10780 item 3, read side).

  `Codegen/Programs/RlpSpliceHelperSpec.lean` proves `decode_span_singleByte`,
  `decode_span_shortBytes` and `decode_span_shortList` — "on a successful decode, the
  item's full encoded length is *this* function of the head byte" — and its `SpanForm`
  predicate then **excludes** the long forms:

      def SpanForm (b : BitVec 8) : Prop :=
        b.toNat < 0xb8 ∨ (0xc0 ≤ b.toNat ∧ b.toNat < 0xf8)

  i.e. `0xB8..0xBF` (long strings) and `0xF8..0xFF` (long lists) are out of domain, and
  that exclusion is what makes `rlp_item_size_spec_within` `.conditional`.

  This module supplies the two missing span facts, in the pure model.

  ## Why the long forms are genuinely provable here (unlike `rlp_encode_uint_be`)

  Worth stating because the sibling issue's other arm is the opposite case. The emitted
  `rlp_item_size` **does** implement the long forms (`RlpRead.lean:724`): idx12–14 set
  `x7 := head - 0xB7` and idx20–21 set `x7 := head - 0xF7`, both falling into a shared
  tail (idx22–34) that reads `x7` bytes big-endian into `x28` and returns
  `1 + x7 + x28`. So there is real behaviour to verify, not a missing code path — and
  `rlpPrefixLongBytesLenOfLen`/`rlpPrefixLongListLenOfLen` are literally
  `pfx.toNat - 0xB7` and `pfx.toNat - 0xF7`, the same two constants.

  ## Shape of the statements, and why `lenVal` is a hypothesis rather than a projection

  The span is `1 + lenOfLen + lenVal`, where `lenVal` is the payload length the decoder
  read from the length-of-length bytes. Rather than writing it as a projection out of
  `readLength` (which would force every consumer to case on an `Option`), `lenVal` and
  its `readLength` equation are hypotheses. That is the form the machine proof wants:
  the guest's loop *computes* `lenVal` in `x28`, so the triple will have exactly this
  equation in hand and can pass it straight in.

  `readLength_takeBytes` is the companion the loop proof needs on the value side: it
  exposes `lenVal = Nat.fromBytesBE lenBytes` over the `lenOfLen` bytes actually
  consumed — the big-endian accumulation `x28 := (x28 <<< 8) ||| byte` performs.

  ## ⚠️ Scope: pure model only

  This module does **not** widen `SpanForm` or re-grade `rlp_item_size`. Doing so needs
  the machine half — a loop invariant over idx25–31 with a *variable* trip count
  (`lenOfLen` ranges over 1..8), which cannot be unrolled the way a fixed-width arm can.
  These lemmas are its specification side, landed first in the same order the short
  forms were built (pure `decode_span_*` lemmas, then the triple that consumes them).
-/

import EvmAsm.EL.RLP.PrefixDecode
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.EL.RLP

/-! ## `readLength` inversion

    The existing `ReadLength.lean` lemmas all build a `readLength` result from a
    `takeBytes` fact. Both directions are needed here, so these are the inversions. -/

/-- **`readLength` consumes exactly `n` bytes.** The length side, which is all the span
    computation needs. -/
theorem readLength_length {bs rest : List Byte} {n lenVal : Nat}
    (h : readLength bs n = some (lenVal, rest)) : bs.length = n + rest.length := by
  unfold readLength at h
  cases htk : takeBytes bs n with
  | none => rw [htk] at h; simp at h
  | some pair =>
    obtain ⟨lenBytes, rest0⟩ := pair
    obtain ⟨hsp, hlen⟩ := takeBytes_eq_some_imp htk
    rw [htk] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    -- `split` handles both the `match` on the length bytes and the leading-zero `ite`.
    have hrest : rest = rest0 := by
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm
      · split at h
        · exact absurd h (by simp)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm
    subst hrest
    have hl := congrArg List.length hsp
    rw [List.length_append, hlen] at hl
    omega

/-- **`readLength`'s value is the big-endian number of the bytes it consumed.** This is
    the fact the guest's accumulator loop (`x28 := (x28 <<< 8) ||| byte`) has to match. -/
theorem readLength_takeBytes {bs rest : List Byte} {n lenVal : Nat}
    (h : readLength bs n = some (lenVal, rest)) :
    ∃ lenBytes, takeBytes bs n = some (lenBytes, rest) ∧ lenBytes.length = n
      ∧ lenVal = Nat.fromBytesBE lenBytes := by
  unfold readLength at h
  cases htk : takeBytes bs n with
  | none => rw [htk] at h; simp at h
  | some pair =>
    obtain ⟨lenBytes, rest0⟩ := pair
    obtain ⟨hsp, hlen⟩ := takeBytes_eq_some_imp htk
    rw [htk] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    -- ⚠️ `cases htk : takeBytes bs n` rewrote the GOAL too, so the `takeBytes`
    -- component is already `rfl` rather than `htk`.
    -- Case on the length bytes so the empty branch knows its own shape (which is what
    -- `Nat.fromBytesBE_nil` needs); `split` alone leaves that as an unnamed binder.
    cases lenBytes with
    | nil =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨[], ?_, hlen, ?_⟩
      · rw [h.2]
      · rw [← h.1, Nat.fromBytesBE_nil]
    | cons b t =>
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨b :: t, ?_, hlen, ?_⟩
        · rw [h.2]
        · exact h.1.symm

/-! ## The long-form spans -/

private theorem fuel_succ (n : Nat) : 2 * n + 2 = (2 * n + 1) + 1 := rfl

/-- ⭐ **Long-string form** (`0xB8..0xBF`): the item's full encoded length is
    `1 + lenOfLen + lenVal` — one header byte, the length-of-length bytes, and the
    payload.

    Mirrors `decode_span_shortBytes`, and the `1 +` is the header byte the short forms
    fold into their arithmetic. -/
theorem decode_span_longBytes {pfx : Byte} {rest0 : List Byte} {item : RLPItem}
    {rest : List Byte} {lenVal : Nat} {lenRest : List Byte}
    (h : decode (pfx :: rest0) = some (item, rest))
    (hlo : 0xB8 ≤ pfx.toNat) (hhi : pfx.toNat ≤ 0xBF)
    (hread : readLength rest0 (rlpPrefixLongBytesLenOfLen pfx) = some (lenVal, lenRest)) :
    (encode item).length = 1 + rlpPrefixLongBytesLenOfLen pfx + lenVal := by
  have henc := decode_eq_some_imp_encode _ _ _ h
  have hcl : classifyPrefix pfx = .longBytes :=
    (classifyPrefix_longBytes_iff pfx).mpr ⟨hlo, hhi⟩
  rw [decode_cons_eq_decodeAux_fuel, fuel_succ,
      decodeAux_cons_longBytes_of_classifyPrefix _ _ _ hcl, hread] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  by_cases hshort : lenVal ≤ 55
  · rw [if_pos hshort] at h; exact absurd h (by simp)
  · rw [if_neg hshort] at h
    cases htk : takeBytes lenRest lenVal with
    | none => rw [htk] at h; simp at h
    | some pair =>
      obtain ⟨data, rest''⟩ := pair
      obtain ⟨hspd, hpld⟩ := takeBytes_eq_some_imp htk
      rw [htk] at h
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hr⟩ := h
      subst hr
      have hlr := readLength_length hread
      have hlenc := congrArg List.length henc
      have hlspd := congrArg List.length hspd
      rw [List.length_cons, List.length_append] at hlenc
      rw [List.length_append, hpld] at hlspd
      omega

/-- ⭐ **Long-list form** (`0xF8..0xFF`): the same shape with `0xF7` as the base. -/
theorem decode_span_longList {pfx : Byte} {rest0 : List Byte} {item : RLPItem}
    {rest : List Byte} {lenVal : Nat} {lenRest : List Byte}
    (h : decode (pfx :: rest0) = some (item, rest))
    (hlo : 0xF8 ≤ pfx.toNat)
    (hread : readLength rest0 (rlpPrefixLongListLenOfLen pfx) = some (lenVal, lenRest)) :
    (encode item).length = 1 + rlpPrefixLongListLenOfLen pfx + lenVal := by
  have henc := decode_eq_some_imp_encode _ _ _ h
  have hcl : classifyPrefix pfx = .longList :=
    (classifyPrefix_longList_iff pfx).mpr hlo
  rw [decode_cons_eq_decodeAux_fuel, fuel_succ,
      decodeAux_cons_longList_of_classifyPrefix _ _ _ hcl, hread] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  by_cases hshort : lenVal ≤ 55
  · rw [if_pos hshort] at h; exact absurd h (by simp)
  · rw [if_neg hshort] at h
    cases htk : takeBytes lenRest lenVal with
    | none => rw [htk] at h; simp at h
    | some pair =>
      obtain ⟨payload, rest''⟩ := pair
      obtain ⟨hspd, hpld⟩ := takeBytes_eq_some_imp htk
      rw [htk] at h
      simp only [Option.bind_some] at h
      cases hdi : decodeItems (2 * rest0.length + 1) payload with
      | none => rw [hdi] at h; simp at h
      | some pair2 =>
        obtain ⟨items, leftover⟩ := pair2
        rw [hdi] at h
        simp only [Option.bind_some] at h
        cases leftover with
        | cons x xs => simp at h
        | nil =>
          replace h : some (RLPItem.list items, rest'') = some (item, rest) := by
            simpa using h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          have hr : rest = rest'' := h.2.symm
          subst hr
          have hlr := readLength_length hread
          have hlenc := congrArg List.length henc
          have hlspd := congrArg List.length hspd
          rw [List.length_cons, List.length_append] at hlenc
          rw [List.length_append, hpld] at hlspd
          omega

/-! ## Non-vacuity

    Both hypotheses are satisfiable — a long form that actually decodes. The witness is
    a 56-byte string, the smallest payload that requires the long form at all (55 is the
    short-form ceiling, which is exactly the boundary #10780 asks to pin). -/

section NonVacuity

/-- `0xB8, 56, <56 bytes>` — the minimal long string. -/
private def sampleLongBytes : List Byte :=
  (0xB8 : Byte) :: (56 : Byte) :: List.replicate 56 (7 : Byte)

/-- It decodes, and consumes the whole buffer. -/
example : decode sampleLongBytes = some (.bytes (List.replicate 56 (7 : Byte)), []) := by
  decide

/-- `readLength` on the tail yields the payload length 56 after one length byte — so the
    hypothesis shape of `decode_span_longBytes` is inhabited. -/
example : readLength ((56 : Byte) :: List.replicate 56 (7 : Byte))
    (rlpPrefixLongBytesLenOfLen (0xB8 : Byte)) = some (56, List.replicate 56 (7 : Byte)) := by
  decide

/-- ⭐ And the span comes out as `1 + 1 + 56 = 58`, matching the buffer length — the
    arithmetic the guest's `1 + x7 + x28` has to reproduce.

    Derived by *applying* `decode_span_longBytes` to the witness rather than by
    evaluating `encode`, which is the stronger check: it shows the theorem fires on a
    real input, and `encode` on a 56-byte payload does not reduce under `decide`. -/
example : (encode (RLPItem.bytes (List.replicate 56 (7 : Byte)))).length = 58 := by
  have hlen : rlpPrefixLongBytesLenOfLen (0xB8 : Byte) = 1 := by decide
  have h := decode_span_longBytes (pfx := (0xB8 : Byte))
    (rest0 := (56 : Byte) :: List.replicate 56 (7 : Byte))
    (item := .bytes (List.replicate 56 (7 : Byte))) (rest := [])
    (lenVal := 56) (lenRest := List.replicate 56 (7 : Byte))
    (by decide) (by decide) (by decide) (by decide)
  rw [hlen] at h
  simpa using h

end NonVacuity

end EvmAsm.EL.RLP
