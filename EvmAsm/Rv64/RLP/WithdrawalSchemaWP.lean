/-
  EvmAsm.Rv64.RLP.WithdrawalSchemaWP

  Withdrawal-specific adapters for the generic schema WP calculus.  The static
  ABI schema in `WithdrawalDecode` remains result-free; this file packages the
  success-path field byte witnesses into generic `FieldSpec`s and proves the
  validity/canonicality facts that generated WP proofs can reuse.
-/

import EvmAsm.Rv64.RLP.WithdrawalDecode
import EvmAsm.Rv64.RLP.SchemaWP
import EvmAsm.Rv64.RLP.SchemaFoldConcat
import EvmAsm.Rv64.RLP.SchemaListEncode
import EvmAsm.Rv64.Tactics.DropPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace WithdrawalDecode

/-- Success-path field witnesses for `[index, validator_index, address, amount]`.
    This is not the static schema: the byte lists are postcondition witnesses,
    while the offsets and field kinds match the result-free ABI layout. -/
def successFieldSpecs (d0 d1 d2 d3 : List Byte) : List FieldSpec :=
  [ { isScalar := true, data := d0, di := 0, imm := (0 : BitVec 12) }
  , { isScalar := true, data := d1, di := 8, imm := (8 : BitVec 12) }
  , { isScalar := false, data := d2, di := 16, imm := (16 : BitVec 12) }
  , { isScalar := true, data := d3, di := 40, imm := (40 : BitVec 12) }
  ]

private theorem headD_ne_zero_schema_guard (d : List Byte) (h : d.headD 1 ≠ 0) :
    d = [] ∨ ¬ d.head?.getD (BitVec.ofNat 8 1) = BitVec.ofNat 8 0 := by
  right
  cases hd : d with
  | nil => simp
  | cons b _ =>
      have hb : b ≠ (0 : Byte) := by simpa [hd] using h
      simpa [hd] using hb

/-- Canonicality side conditions for the three scalar witnesses. -/
theorem successFieldSpecs_schemaCanonical
    (d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hc1 : d1.headD 1 ≠ 0) (hc3 : d3.headD 1 ≠ 0) :
    SchemaWP.SchemaCanonical (successFieldSpecs d0 d1 d2 d3) := by
  simp [SchemaWP.SchemaCanonical, successFieldSpecs]
  exact ⟨headD_ne_zero_schema_guard d0 hc0,
    headD_ne_zero_schema_guard d1 hc1, headD_ne_zero_schema_guard d3 hc3⟩

private theorem encode_bytes_length_lt_256_pow_8_of_length_eq_20 (d : List Byte)
    (h : d.length = 20) :
    (encode (.bytes d)).length < 256 ^ 8 := by
  cases d with
  | nil => simp at h
  | cons b tail =>
      cases tail with
      | nil => simp at h
      | cons c tail =>
          simp at h
          unfold encode encodeBytes
          have htail : tail.length ≤ 53 := by omega
          simp [htail]
          omega

/-- Core validity for the fixed withdrawal success witness list. -/
theorem successFieldSpecs_coreValid
    (d0 d1 d2 d3 : List Byte)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8) :
    ∀ f, f ∈ successFieldSpecs d0 d1 d2 d3 → fieldCoreValid outputSize f := by
  intro f hf
  simp [successFieldSpecs] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · simp [fieldCoreValid, outputSize, fieldWriteLen, hl0]
    decide
  · simp [fieldCoreValid, outputSize, fieldWriteLen, hl1]
    decide
  · have henc := encode_bytes_length_lt_256_pow_8_of_length_eq_20 d2 haddr
    simp [fieldCoreValid, outputSize, fieldWriteLen, haddr]
    exact ⟨henc, by decide⟩
  · simp [fieldCoreValid, outputSize, fieldWriteLen, hl3]
    decide

/-- Build the generic `SchemaValid` evidence for a successful withdrawal witness
    from one concatenation fact over the list payload. -/
theorem successFieldSpecs_schemaValid_of_concat
    (bs tail d0 d1 d2 d3 : List Byte) (O : Nat)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail) :
    SchemaValid bs outputSize O (successFieldSpecs d0 d1 d2 d3) :=
  schemaValid_of_concat bs outputSize tail (successFieldSpecs d0 d1 d2 d3) O
    (successFieldSpecs_coreValid d0 d1 d2 d3 hl0 hl1 haddr hl3) hconcat

/-- One-shot pure decode automation for the four success-path withdrawal fields. -/
theorem successFieldSpecs_decodes_of_concat
    (bs tail d0 d1 d2 d3 : List Byte) (O : Nat)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail) :
    schemaDecodes bs O (successFieldSpecs d0 d1 d2 d3) :=
  SchemaWP.schemaDecodes_of_valid_canonical bs (successFieldSpecs d0 d1 d2 d3) O outputSize
    (successFieldSpecs_schemaValid_of_concat bs tail d0 d1 d2 d3 O hl0 hl1 haddr hl3 hconcat)
    (successFieldSpecs_schemaCanonical d0 d1 d2 d3 hc0 hc1 hc3)

private theorem encode_bytes_length_le_9_of_length_le_8 (d : List Byte) (h : d.length ≤ 8) :
    (encode (.bytes d)).length ≤ 9 := by
  unfold encode encodeBytes
  cases d with
  | nil => simp
  | cons b tail =>
      cases tail with
      | nil =>
          by_cases hb : b.toNat < 0x80 <;> simp [hb]
      | cons c tail =>
          have htail : tail.length ≤ 6 := by simpa using h
          have hshort : tail.length + 1 + 1 ≤ 55 := by omega
          simp [hshort]
          omega

private theorem encode_bytes_length_le_21_of_length_eq_20 (d : List Byte) (h : d.length = 20) :
    (encode (.bytes d)).length ≤ 21 := by
  cases d with
  | nil => simp at h
  | cons b tail =>
      cases tail with
      | nil => simp at h
      | cons c tail =>
          simp at h
          unfold encode encodeBytes
          have htail : tail.length ≤ 53 := by omega
          simp [htail]
          omega

theorem schemaEncBytes_successFieldSpecs_length_le_48
    (d0 d1 d2 d3 : List Byte)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8) :
    (schemaEncBytes (successFieldSpecs d0 d1 d2 d3)).length ≤ 48 := by
  have h0 := encode_bytes_length_le_9_of_length_le_8 d0 hl0
  have h1 := encode_bytes_length_le_9_of_length_le_8 d1 hl1
  have h2 := encode_bytes_length_le_21_of_length_eq_20 d2 haddr
  have h3 := encode_bytes_length_le_9_of_length_le_8 d3 hl3
  simp [schemaEncBytes, successFieldSpecs]
  omega

private theorem encode_successFieldSpecs_length_lt_256_pow_8
    (d0 d1 d2 d3 : List Byte)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8) :
    (encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))).length < 256 ^ 8 := by
  have hpayload := schemaEncBytes_successFieldSpecs_length_le_48 d0 d1 d2 d3 hl0 hl1 haddr hl3
  have hshort : (schemaEncBytes (successFieldSpecs d0 d1 d2 d3)).length ≤ 55 := by omega
  rw [encode_list_schemaItems_short (successFieldSpecs d0 d1 d2 d3) hshort]
  simp
  omega

/-- A complete encoded withdrawal success witness exposes the schema payload at
    offset `1`.  This is the pure input-slicing automation used by the WP
    wrappers below, so callers do not need to hand-write a concat premise. -/
theorem successFieldSpecs_concat_of_input
    (bs d0 d1 d2 d3 : List Byte)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) :
    bs.drop 1 = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ ([] : List Byte) := by
  have hpayload := schemaEncBytes_successFieldSpecs_length_le_48 d0 d1 d2 d3 hl0 hl1 haddr hl3
  have hshort : (schemaEncBytes (successFieldSpecs d0 d1 d2 d3)).length ≤ 55 := by omega
  exact schemaConcat_of_encoded_list_short bs (successFieldSpecs d0 d1 d2 d3) hshort hinput

/-- The success witness list characterizes the pure withdrawal decoder.  This is
    the semantic bridge used by the ABI postcondition; the static schema still
    contains no decoded result. -/
theorem decodeWithdrawal_encode_successFieldSpecs
    (d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal (encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) =
      some (fromFieldBytes d0 d1 d2 d3) := by
  have hfull : decodeFully (encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) =
      some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]) := by
    have hsize := encode_successFieldSpecs_length_lt_256_pow_8 d0 d1 d2 d3 hl0 hl1 haddr hl3
    simpa [schemaItems, successFieldSpecs] using
      (decodeFully_encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))) hsize)
  exact decodeWithdrawal_eq_some_of_decodeFully_fields hfull hc0 hl0 hc1 hl1 haddr hc3 hl3

/-- Same bridge as `decodeWithdrawal_encode_successFieldSpecs`, but for callers
    that carry the encoded-list equality as a hypothesis. -/
theorem decodeWithdrawal_eq_some_of_successFieldSpecs_input
    (input d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) :
    decodeWithdrawal input = some (fromFieldBytes d0 d1 d2 d3) := by
  rw [hinput]
  exact decodeWithdrawal_encode_successFieldSpecs d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3

/-- Result-free predicate saying that `input` is the canonical encoded withdrawal
    success schema for some four field byte strings.  It intentionally carries no
    decoded `Withdrawal` value. -/
def successFieldSpecsInput (input : List Byte) : Prop :=
  ∃ d0 d1 d2 d3 : List Byte,
    input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))
      ∧ d0.headD 1 ≠ 0 ∧ d0.length ≤ 8
      ∧ d1.headD 1 ≠ 0 ∧ d1.length ≤ 8
      ∧ d2.length = 20
      ∧ d3.headD 1 ≠ 0 ∧ d3.length ≤ 8

/-- Any successful pure withdrawal decode exposes exactly the result-free success
    schema encoding for its four byte fields.  This is the reverse bridge needed
    by WP callers that case-split on `decodeWithdrawal input`, without putting
    the decoded value into the static schema. -/
theorem successFieldSpecs_input_of_decodeWithdrawal_eq_some
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w) :
    ∃ d0 d1 d2 d3 : List Byte,
      input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))
        ∧ d0.headD 1 ≠ 0 ∧ d0.length ≤ 8
        ∧ d1.headD 1 ≠ 0 ∧ d1.length ≤ 8
        ∧ d2.length = 20
        ∧ d3.headD 1 ≠ 0 ∧ d3.length ≤ 8
        ∧ w = fromFieldBytes d0 d1 d2 d3 := by
  rcases (decodeWithdrawal_eq_some_iff input w).mp hdec with
    ⟨d0, d1, d2, d3, hfull, hc0, hl0, hc1, hl1, haddr, hc3, hl3, hi, hv, ha, hamt⟩
  have hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))) := by
    have hbound := encode_successFieldSpecs_length_lt_256_pow_8 d0 d1 d2 d3 hl0 hl1 haddr hl3
    exact (decodeFully_eq_encode input (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))
      hbound).mp (by simpa [schemaItems, successFieldSpecs] using hfull)
  have hw : w = fromFieldBytes d0 d1 d2 d3 := by
    cases w
    simp [fromFieldBytes] at hi hv ha hamt ⊢
    exact ⟨hi, hv, ha, hamt⟩
  exact ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3, hw⟩

/-- Success of the pure decoder is equivalent to the existence of canonical
    field-byte witnesses whose result-free schema encoding is the input and
    whose bytes compute the returned value. -/
theorem decodeWithdrawal_eq_some_iff_successFieldSpecs_input
    (input : List Byte) (w : Withdrawal) :
    decodeWithdrawal input = some w ↔
      ∃ d0 d1 d2 d3 : List Byte,
        input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))
          ∧ d0.headD 1 ≠ 0 ∧ d0.length ≤ 8
          ∧ d1.headD 1 ≠ 0 ∧ d1.length ≤ 8
          ∧ d2.length = 20
          ∧ d3.headD 1 ≠ 0 ∧ d3.length ≤ 8
          ∧ w = fromFieldBytes d0 d1 d2 d3 := by
  constructor
  · exact successFieldSpecs_input_of_decodeWithdrawal_eq_some input w
  · rintro ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3, hw⟩
    rw [hw]
    exact decodeWithdrawal_eq_some_of_successFieldSpecs_input input d0 d1 d2 d3
      hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput

/-- Failure is reason-erased: the pure decoder fails exactly when the input is not
    any canonical success-schema encoding. -/
theorem decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput
    (input : List Byte) :
    decodeWithdrawal input = none ↔ ¬ successFieldSpecsInput input := by
  constructor
  · intro hnone hsucc
    rcases hsucc with
      ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3⟩
    have hsome := decodeWithdrawal_eq_some_of_successFieldSpecs_input input d0 d1 d2 d3
      hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput
    rw [hnone] at hsome
    contradiction
  · intro hnot
    cases hdec : decodeWithdrawal input with
    | none => rfl
    | some w =>
        exfalso
        rcases successFieldSpecs_input_of_decodeWithdrawal_eq_some input w hdec with
          ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3, _hw⟩
        exact hnot ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3⟩

private theorem exists_eq_list_of_length_eq_20 (d : List Byte) (h : d.length = 20) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 : Byte,
      d = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
        b10, b11, b12, b13, b14, b15, b16, b17, b18, b19] := by
  rcases d with _ | ⟨b0, d⟩; · simp at h
  rcases d with _ | ⟨b1, d⟩; · simp at h
  rcases d with _ | ⟨b2, d⟩; · simp at h
  rcases d with _ | ⟨b3, d⟩; · simp at h
  rcases d with _ | ⟨b4, d⟩; · simp at h
  rcases d with _ | ⟨b5, d⟩; · simp at h
  rcases d with _ | ⟨b6, d⟩; · simp at h
  rcases d with _ | ⟨b7, d⟩; · simp at h
  rcases d with _ | ⟨b8, d⟩; · simp at h
  rcases d with _ | ⟨b9, d⟩; · simp at h
  rcases d with _ | ⟨b10, d⟩; · simp at h
  rcases d with _ | ⟨b11, d⟩; · simp at h
  rcases d with _ | ⟨b12, d⟩; · simp at h
  rcases d with _ | ⟨b13, d⟩; · simp at h
  rcases d with _ | ⟨b14, d⟩; · simp at h
  rcases d with _ | ⟨b15, d⟩; · simp at h
  rcases d with _ | ⟨b16, d⟩; · simp at h
  rcases d with _ | ⟨b17, d⟩; · simp at h
  rcases d with _ | ⟨b18, d⟩; · simp at h
  rcases d with _ | ⟨b19, d⟩; · simp at h
  rcases d with _ | ⟨_b20, _d⟩
  · exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
      b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, rfl⟩
  · simp at h

local macro "withdrawal_schema_output_norm" : tactic =>
  `(tactic| (simp [schemaOut, fieldUpdate, successFieldSpecs, outputSize, successBytes,
      fromFieldBytes, u64LEBytes, spillRange, copyRangeGen, getByteAt, addressBEBytes,
      Nat.fromBytesBE] <;> bv_omega))

/-- The successful schema field walk writes exactly the ABI success bytes when
    started from a zeroed output struct.  This hides the field-update fold from
    callers: generated WP proofs can target the semantic postcondition directly. -/
theorem successFieldSpecs_schemaOut_zeroed_eq_successBytes
    (d0 d1 d2 d3 : List Byte) (haddr : d2.length = 20) :
    schemaOut (List.replicate outputSize (0 : Byte)) (successFieldSpecs d0 d1 d2 d3) =
      successBytes (fromFieldBytes d0 d1 d2 d3) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, rfl⟩ :=
    exists_eq_list_of_length_eq_20 d2 haddr
  withdrawal_schema_output_norm

/-- WP certificate for the successful withdrawal field walk, built from the four
    field byte witnesses plus one payload concatenation fact.  This is the
    withdrawal-specialized entry point to the generic schema WP fold. -/
def successFieldSpecsStepCertOfConcat
    (base regionBase outBase : Word) (rOut : Reg)
    (bs tail outBytes d0 d1 d2 d3 : List Byte) (O : Nat)
    (hout : outBytes.length = outputSize)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3)))
      (schemaCR base rOut (successFieldSpecs d0 d1 d2 d3))
      (schemaINV regionBase outBase rOut bs (O + schemaEnc (successFieldSpecs d0 d1 d2 d3))
        (schemaOut outBytes (successFieldSpecs d0 d1 d2 d3))) := by
  have hvalid : SchemaValid bs outBytes.length O (successFieldSpecs d0 d1 d2 d3) := by
    rw [hout]
    exact successFieldSpecs_schemaValid_of_concat bs tail d0 d1 d2 d3 O hl0 hl1 haddr hl3 hconcat
  have hcanon := successFieldSpecs_schemaCanonical d0 d1 d2 d3 hc0 hc1 hc3
  exact SchemaWP.schemaStepCert base regionBase outBase rOut bs O outBytes
    (successFieldSpecs d0 d1 d2 d3) hvalid hcanon halign hdalign hover hwin hdov hdval hcode

/-- The wrapper above computes exactly the initial schema invariant as its WP precondition. -/
theorem successFieldSpecsStepCertOfConcat_pre
    (base regionBase outBase : Word) (rOut : Reg)
    (bs tail outBytes d0 d1 d2 d3 : List Byte) (O : Nat)
    (hout : outBytes.length = outputSize)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    (successFieldSpecsStepCertOfConcat base regionBase outBase rOut bs tail outBytes d0 d1 d2 d3 O
      hout hc0 hl0 hc1 hl1 haddr hc3 hl3 hconcat halign hdalign hover hwin hdov hdval hcode).pre =
      schemaINV regionBase outBase rOut bs O outBytes := by
  rfl

/-- Success-path schema WP certificate for a complete short-list encoded
    withdrawal input.  This uses the generic `SchemaWP` encoded-list constructor
    and fixes the payload offset to `1`. -/
def successFieldSpecsStepCertOfInput
    (base regionBase outBase : Word) (rOut : Reg)
    (bs outBytes d0 d1 d2 d3 : List Byte)
    (hout : outBytes.length = outputSize)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3)))
      (schemaCR base rOut (successFieldSpecs d0 d1 d2 d3))
      (schemaINV regionBase outBase rOut bs (1 + schemaEnc (successFieldSpecs d0 d1 d2 d3))
        (schemaOut outBytes (successFieldSpecs d0 d1 d2 d3))) := by
  have hcore : ∀ f, f ∈ successFieldSpecs d0 d1 d2 d3 → fieldCoreValid outBytes.length f := by
    rw [hout]
    exact successFieldSpecs_coreValid d0 d1 d2 d3 hl0 hl1 haddr hl3
  have hcanon := successFieldSpecs_schemaCanonical d0 d1 d2 d3 hc0 hc1 hc3
  have hpayload := schemaEncBytes_successFieldSpecs_length_le_48 d0 d1 d2 d3 hl0 hl1 haddr hl3
  have hshort : (schemaEncBytes (successFieldSpecs d0 d1 d2 d3)).length ≤ 55 := by omega
  exact SchemaWP.schemaStepCertOfEncodedListShort base regionBase outBase rOut bs outBytes
    (successFieldSpecs d0 d1 d2 d3) hcore hcanon hshort hinput halign hdalign hover hwin
    hdov hdval hcode

/-- The encoded-input schema wrapper computes the initial schema invariant at payload offset `1`. -/
theorem successFieldSpecsStepCertOfInput_pre
    (base regionBase outBase : Word) (rOut : Reg)
    (bs outBytes d0 d1 d2 d3 : List Byte)
    (hout : outBytes.length = outputSize)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    (successFieldSpecsStepCertOfInput base regionBase outBase rOut bs outBytes d0 d1 d2 d3
      hout hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov hdval hcode).pre =
      schemaINV regionBase outBase rOut bs 1 outBytes := by
  unfold successFieldSpecsStepCertOfInput
  rfl

/-- Success-path schema WP certificate whose postcondition is already the
    semantic ABI byte layout.  The only output-side precondition is the static
    zeroed 48-byte output struct; the raw `schemaOut` fold is discharged by
    `successFieldSpecs_schemaOut_zeroed_eq_successBytes`. -/
def successFieldSpecsStepSuccessBytesCertOfConcat
    (base regionBase outBase : Word) (rOut : Reg)
    (bs tail d0 d1 d2 d3 : List Byte) (O : Nat)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3)))
      (schemaCR base rOut (successFieldSpecs d0 d1 d2 d3))
      (schemaINV regionBase outBase rOut bs (O + schemaEnc (successFieldSpecs d0 d1 d2 d3))
        (successBytes (fromFieldBytes d0 d1 d2 d3))) := by
  let outBytes := List.replicate outputSize (0 : Byte)
  have hout : outBytes.length = outputSize := by
    simp [outBytes]
  have hdov' : outBase.toNat + outBytes.length < 2 ^ 64 := by
    simpa [outBytes, outputSize] using hdov
  have hdval' : ∀ i, i < outBytes.length →
      isValidByteAccess (outBase + BitVec.ofNat 64 i) = true := by
    intro i hi
    exact hdval i (by simpa [outBytes, outputSize] using hi)
  have cert := successFieldSpecsStepCertOfConcat base regionBase outBase rOut bs tail outBytes
    d0 d1 d2 d3 O hout hc0 hl0 hc1 hl1 haddr hc3 hl3 hconcat halign hdalign hover hwin
    hdov' hdval' hcode
  exact cert.weakenPost (by
    intro h hp
    rw [← successFieldSpecs_schemaOut_zeroed_eq_successBytes d0 d1 d2 d3 haddr]
    simpa [outBytes] using hp)

/-- The success-bytes wrapper computes the zeroed-output schema invariant as its WP precondition. -/
theorem successFieldSpecsStepSuccessBytesCertOfConcat_pre
    (base regionBase outBase : Word) (rOut : Reg)
    (bs tail d0 d1 d2 d3 : List Byte) (O : Nat)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    (successFieldSpecsStepSuccessBytesCertOfConcat base regionBase outBase rOut bs tail d0 d1 d2
      d3 O hc0 hl0 hc1 hl1 haddr hc3 hl3 hconcat halign hdalign hover hwin hdov hdval hcode).pre =
      schemaINV regionBase outBase rOut bs O (List.replicate outputSize (0 : Byte)) := by
  rfl

/-- Encoded-input version of the success-bytes schema WP certificate. -/
def successFieldSpecsStepSuccessBytesCertOfInput
    (base regionBase outBase : Word) (rOut : Reg)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    WP.CFG.Cert base (base + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3)))
      (schemaCR base rOut (successFieldSpecs d0 d1 d2 d3))
      (schemaINV regionBase outBase rOut bs (1 + schemaEnc (successFieldSpecs d0 d1 d2 d3))
        (successBytes (fromFieldBytes d0 d1 d2 d3))) := by
  let outBytes := List.replicate outputSize (0 : Byte)
  have hout : outBytes.length = outputSize := by
    simp [outBytes]
  have hdov' : outBase.toNat + outBytes.length < 2 ^ 64 := by
    simpa [outBytes, outputSize] using hdov
  have hdval' : ∀ i, i < outBytes.length →
      isValidByteAccess (outBase + BitVec.ofNat 64 i) = true := by
    intro i hi
    exact hdval i (by simpa [outBytes, outputSize] using hi)
  have cert := successFieldSpecsStepCertOfInput base regionBase outBase rOut bs outBytes
    d0 d1 d2 d3 hout hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin
    hdov' hdval' hcode
  exact cert.weakenPost (by
    intro h hp
    rw [← successFieldSpecs_schemaOut_zeroed_eq_successBytes d0 d1 d2 d3 haddr]
    simpa [outBytes] using hp)

/-- The encoded-input success-bytes wrapper computes the zeroed-output schema invariant. -/
theorem successFieldSpecsStepSuccessBytesCertOfInput_pre
    (base regionBase outBase : Word) (rOut : Reg)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) < 2 ^ 64) :
    (successFieldSpecsStepSuccessBytesCertOfInput base regionBase outBase rOut bs d0 d1 d2
      d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov hdval hcode).pre =
      schemaINV regionBase outBase rOut bs 1 (List.replicate outputSize (0 : Byte)) := by
  rfl

/-- A status-return block rooted at `base` has no code requirements below `base`. -/
theorem statusReturnCode_none_below (base status a : Word)
    (hcode : base.toNat + 8 < 2 ^ 64) (hlt : a.toNat < base.toNat) :
    statusReturnCode base status a = none := by
  have hne_base : a ≠ base := by
    intro h
    have := congrArg BitVec.toNat h
    omega
  have hbase_false : (a == base) = false := by
    rw [Bool.eq_false_iff]
    intro h
    rw [beq_iff_eq] at h
    exact hne_base h
  have hnext_false : (a == base + 4#64) = false := by
    rw [Bool.eq_false_iff]
    intro h
    rw [beq_iff_eq] at h
    bv_omega
  simp [statusReturnCode, CodeReq.union, CodeReq.singleton, hbase_false, hnext_false]

/-- The schema walk code range is disjoint from a status-return block placed
    immediately after it. -/
theorem schemaCR_disjoint_statusReturnCode (rOut : Reg) (specs : List FieldSpec)
    (base status : Word)
    (hcode : base.toNat + schemaSize specs + 8 < 2 ^ 64) :
    (schemaCR base rOut specs).Disjoint
      (statusReturnCode (base + BitVec.ofNat 64 (schemaSize specs)) status) := by
  have hbase : (base + BitVec.ofNat 64 (schemaSize specs)).toNat =
      base.toNat + schemaSize specs := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + schemaSize specs) ?_ ?_
  · intro a ha
    exact schemaCR_none_above rOut specs base a (by omega) ha
  · intro a ha
    exact statusReturnCode_none_below (base + BitVec.ofNat 64 (schemaSize specs)) status a
      (by rw [hbase]; omega) (by rw [hbase]; exact ha)

/-- Success endpoint precondition with the incoming status register abstracted as
    `regOwn`. Generated schema-walk callers should not need to provide the old
    status value because the endpoint overwrites it. -/
def successStatusReturnAbiRegOwnPre
    (inputBase outBase raVal : Word) (input : List Byte) (w : Withdrawal) : Assertion :=
  (((.x1 ↦ᵣ raVal) ** successStatusReturnAbiFrame inputBase outBase input w) ** regOwn .x10)

/-- ABI-facing success endpoint that consumes `regOwn .x10` instead of a
    concrete old status value. -/
def successStatusReturnAbiRegOwnCert
    (base inputBase outBase raVal : Word) (input : List Byte) (w : Withdrawal) :
    WP.CFG.Cert base (successStatusReturnExit raVal) (successStatusReturnCode base)
      (abiPost inputBase outBase raVal input) := by
  exact WP.CFG.block (WP.Entails.refl _)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
      (P := (.x1 ↦ᵣ raVal) ** successStatusReturnAbiFrame inputBase outBase input w)
      (by
        intro statusOld
        have hs := successStatusReturn_abiPost_spec_within base inputBase outBase raVal statusOld
          input w
        exact cpsTripleWithin_weaken (fun h hp => by
          unfold successStatusReturnAbiPre successStatusReturnPre statusReturnPre
          xperm_hyp hp) (fun _ hp => hp) hs))

/-- The reg-own success endpoint computes the value-independent ABI precondition. -/
theorem successStatusReturnAbiRegOwnCert_pre
    (base inputBase outBase raVal : Word) (input : List Byte) (w : Withdrawal) :
    (successStatusReturnAbiRegOwnCert base inputBase outBase raVal input w).pre =
      successStatusReturnAbiRegOwnPre inputBase outBase raVal input w := by
  rfl

/-- Scratch resources left after the successful schema walk and framed through
    the status-return endpoint. The output pointer is held in `s0` (`x8`), as
    established by the withdrawal decoder prologue. -/
def successSchemaReturnFrame (regionBase outBase : Word) (O : Nat) : Assertion :=
  ((regOwn .x5) ** (regOwn .x11) ** (regOwn .x12) **
    (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
    (regOwn .x15) ** (.x8 ↦ᵣ outBase))

theorem successSchemaReturnFrame_pcFree
    (regionBase outBase : Word) (O : Nat) :
    (successSchemaReturnFrame regionBase outBase O).pcFree := by
  unfold successSchemaReturnFrame
  pcFree

/-- One-instruction bridge from a list value pointer in `x10` to the schema
    cursor convention (`x13 = inputBase + O + 1`). -/
def schemaCursorInitCode (base : Word) : CodeReq :=
  CodeReq.singleton base (.ADDI .x13 .x10 (1 : BitVec 12))

def schemaCursorInitRestNoX13
    (regionBase outBase raVal : Word) (bs outBytes : List Byte) : Assertion :=
  (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x11) **
    (regOwn .x12) ** (regOwn .x14) ** (regOwn .x15) ** bytesRegion regionBase bs) **
   ((.x8 ↦ᵣ outBase) ** bytesRegion outBase outBytes) ** (.x1 ↦ᵣ raVal))

/-- Precondition for `schemaCursorInitCode`: `x10` points at the RLP list value
    start, `x13` is arbitrary, and the remaining schema resources are owned. -/
def schemaCursorInitPre
    (regionBase outBase raVal : Word) (bs : List Byte) (O : Nat)
    (outBytes : List Byte) : Assertion :=
  ((.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
    schemaCursorInitRestNoX13 regionBase outBase raVal bs outBytes) ** regOwn .x13

def schemaCursorInitPostRest
    (regionBase outBase raVal : Word) (bs : List Byte) (O : Nat)
    (outBytes : List Byte) : Assertion :=
  (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x11) **
    (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + 1))) **
    (regOwn .x14) ** (regOwn .x15) ** bytesRegion regionBase bs) **
   ((.x8 ↦ᵣ outBase) ** bytesRegion outBase outBytes) ** (.x1 ↦ᵣ raVal))

theorem schemaCursorInitPostRest_entails_schemaINV
    (regionBase outBase raVal : Word) (bs : List Byte) (O : Nat)
    (outBytes : List Byte) :
    WP.Entails
      ((.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        schemaCursorInitPostRest regionBase outBase raVal bs O outBytes)
      (schemaINV regionBase outBase .x8 bs (O + 1) outBytes ** (.x1 ↦ᵣ raVal)) := by
  intro h hp
  have hpOwn : (regOwn .x10 **
      schemaCursorInitPostRest regionBase outBase raVal bs O outBytes) h :=
    sepConj_mono_left (regIs_to_regOwn .x10 (regionBase + BitVec.ofNat 64 O)) h hp
  unfold schemaCursorInitPostRest at hpOwn
  unfold schemaINV
  xperm_hyp hpOwn

/-- WP bridge from `x10 = inputBase + O` to the schema cursor precondition at
    payload offset `O + 1`.  This is the handoff from the outer-list classifier
    to generated schema field code. -/
def schemaCursorInitCert
    (base regionBase outBase raVal : Word) (bs : List Byte) (O : Nat)
    (outBytes : List Byte) :
    WP.CFG.Cert base (base + 4) (schemaCursorInitCode base)
      (schemaINV regionBase outBase .x8 bs (O + 1) outBytes ** (.x1 ↦ᵣ raVal)) := by
  have hspec : cpsTripleWithin 1 base (base + 4) (schemaCursorInitCode base)
      (schemaCursorInitPre regionBase outBase raVal bs O outBytes)
      ((.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        schemaCursorInitPostRest regionBase outBase raVal bs O outBytes) := by
    unfold schemaCursorInitPre schemaCursorInitCode
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x13)
      (P := (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        schemaCursorInitRestNoX13 regionBase outBase raVal bs outBytes) ?_
    intro oldX13
    have hadd := addi_spec_gen_within .x13 .x10 oldX13
      (regionBase + BitVec.ofNat 64 O) (1 : BitVec 12) base (by decide)
    have hframed := cpsTripleWithin_frameR
      (schemaCursorInitRestNoX13 regionBase outBase raVal bs outBytes)
      (by unfold schemaCursorInitRestNoX13; pcFree) hadd
    refine cpsTripleWithin_weaken ?_ ?_ hframed
    · intro h hp
      unfold schemaCursorInitRestNoX13 at hp ⊢
      xperm_hyp hp
    · intro h hp
      unfold schemaCursorInitRestNoX13 at hp
      unfold schemaCursorInitPostRest
      rw [show (regionBase + BitVec.ofNat 64 O) + signExtend12 (1 : BitVec 12) =
          regionBase + BitVec.ofNat 64 (O + 1) by
            rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
            bv_omega] at hp
      xperm_hyp hp
  exact WP.CFG.block
    (schemaCursorInitPostRest_entails_schemaINV regionBase outBase raVal bs O outBytes) hspec

theorem schemaCursorInitCert_pre
    (base regionBase outBase raVal : Word) (bs : List Byte) (O : Nat)
    (outBytes : List Byte) :
    (schemaCursorInitCert base regionBase outBase raVal bs O outBytes).pre =
      schemaCursorInitPre regionBase outBase raVal bs O outBytes := by
  rfl

theorem schemaCursorInitCode_none_above (base a : Word)
    (h : base.toNat + 4 ≤ a.toNat) :
    schemaCursorInitCode base a = none := by
  unfold schemaCursorInitCode
  exact CodeReq.singleton_miss (by
    intro h_eq
    have := congrArg BitVec.toNat h_eq
    omega)

theorem schemaCursorInitCode_none_below (base a : Word)
    (h : a.toNat < base.toNat) :
    schemaCursorInitCode base a = none := by
  unfold schemaCursorInitCode
  exact CodeReq.singleton_miss (by
    intro h_eq
    have := congrArg BitVec.toNat h_eq
    omega)

theorem schemaCursorInitCode_disjoint_schemaCR
    (base : Word) (rOut : Reg) (specs : List FieldSpec)
    (hcode : base.toNat + 4 + schemaSize specs < 2 ^ 64) :
    (schemaCursorInitCode base).Disjoint (schemaCR (base + 4) rOut specs) := by
  have hbase4 : (base + 4).toNat = base.toNat + 4 := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + 4) ?_ ?_
  · intro a ha
    exact schemaCursorInitCode_none_above base a ha
  · intro a ha
    exact schemaCR_none_below rOut specs (base + 4) a (by rw [hbase4]; omega)
      (by rw [hbase4]; exact ha)

theorem schemaCursorInitCode_disjoint_successStatusReturnCode
    (base statusBase : Word) :
    base.toNat + 4 ≤ statusBase.toNat →
    statusBase.toNat + 8 < 2 ^ 64 →
    (schemaCursorInitCode base).Disjoint (successStatusReturnCode statusBase) := by
  intro hle hcode
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + 4) ?_ ?_
  · intro a ha
    exact schemaCursorInitCode_none_above base a ha
  · intro a ha
    unfold successStatusReturnCode
    exact statusReturnCode_none_below statusBase (0 : Word) a hcode (by omega)

theorem schemaCursorInitCode_disjoint_successReturnTail
    (base : Word) (rOut : Reg) (specs : List FieldSpec)
    (hcode : base.toNat + 4 + schemaSize specs + 8 < 2 ^ 64) :
    (schemaCursorInitCode base).Disjoint
      ((schemaCR (base + 4) rOut specs).union
        (successStatusReturnCode
          ((base + 4) + BitVec.ofNat 64 (schemaSize specs)))) := by
  have hbase4 : (base + 4).toNat = base.toNat + 4 := by
    bv_omega
  have hret : ((base + 4) + BitVec.ofNat 64 (schemaSize specs)).toNat =
      base.toNat + 4 + schemaSize specs := by
    bv_omega
  refine CodeReq.Disjoint.union_right ?h_schema ?h_return
  · exact schemaCursorInitCode_disjoint_schemaCR base rOut specs (by omega)
  · exact schemaCursorInitCode_disjoint_successStatusReturnCode base
      ((base + 4) + BitVec.ofNat 64 (schemaSize specs)) (by rw [hret]; omega)
      (by rw [hret]; omega)

theorem schemaCursorInitSuccessReturnTail_none_below
    (base : Word) (rOut : Reg) (specs : List FieldSpec) (a : Word)
    (hcode : base.toNat + 4 + schemaSize specs + 8 < 2 ^ 64)
    (hlt : a.toNat < base.toNat) :
    ((schemaCursorInitCode base).union
      ((schemaCR (base + 4) rOut specs).union
        (successStatusReturnCode
          ((base + 4) + BitVec.ofNat 64 (schemaSize specs))))) a = none := by
  have hbase4 : (base + 4).toNat = base.toNat + 4 := by
    bv_omega
  have hret : ((base + 4) + BitVec.ofNat 64 (schemaSize specs)).toNat =
      base.toNat + 4 + schemaSize specs := by
    bv_omega
  have h0 : schemaCursorInitCode base a = none :=
    schemaCursorInitCode_none_below base a hlt
  have hschema : schemaCR (base + 4) rOut specs a = none :=
    schemaCR_none_below rOut specs (base + 4) a (by rw [hbase4]; omega)
      (by rw [hbase4]; omega)
  have hstatus : successStatusReturnCode ((base + 4) + BitVec.ofNat 64 (schemaSize specs)) a = none := by
    unfold successStatusReturnCode
    exact statusReturnCode_none_below ((base + 4) + BitVec.ofNat 64 (schemaSize specs))
      (0 : Word) a (by rw [hret]; omega) (by rw [hret]; omega)
  simp only [CodeReq.union, h0]
  rw [hschema]
  exact hstatus

/-- Free landing-pad jump used to move the walk-init short-list success exit out
    of the classifier code range before running generated schema code. -/
def walkInitShortSuccessJumpCode (base : Word) : CodeReq :=
  CodeReq.singleton (base + 124) (.JAL .x0 (48 : BitVec 21))

theorem walkInitShortSuccessJumpCode_disjoint_successReturnTail
    (base : Word) (rOut : Reg) (specs : List FieldSpec)
    (hcode : base.toNat + 172 + 4 + schemaSize specs + 8 < 2 ^ 64) :
    (walkInitShortSuccessJumpCode base).Disjoint
      ((schemaCursorInitCode (base + 172)).union
        ((schemaCR (base + 172 + 4) rOut specs).union
          (successStatusReturnCode
            ((base + 172 + 4) + BitVec.ofNat 64 (schemaSize specs))))) := by
  have hbase172 : (base + 172).toNat = base.toNat + 172 := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + 172) ?_ ?_
  · intro a ha
    unfold walkInitShortSuccessJumpCode
    exact CodeReq.singleton_miss (by
      intro h_eq
      have := congrArg BitVec.toNat h_eq
      bv_omega)
  · intro a ha
    exact schemaCursorInitSuccessReturnTail_none_below (base + 172) rOut specs a
      (by rw [hbase172]; omega) (by rw [hbase172]; exact ha)

/-- Extra resources a walk-init success candidate must carry in order to hand off
    to the generated schema WP code.  The output buffer is intentionally fixed
    to zeros because the current schema certificate proves updates from a zeroed
    ABI result struct. -/
def schemaWalkInitFrame (outBase : Word) : Assertion :=
  ((.x8 ↦ᵣ outBase) ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    regOwn .x15 ** bytesRegion outBase (List.replicate outputSize (0 : Byte)))

theorem schemaWalkInitFrame_pcFree (outBase : Word) :
    (schemaWalkInitFrame outBase).pcFree := by
  unfold schemaWalkInitFrame
  pcFree

/-- Automated success-path WP certificate: a generated field-schema walk followed
    by the success return shim. The schema remains result-free; the decoded
    withdrawal appears only through the success witnesses and the ABI post. -/
def successFieldSpecsReturnAbiCertOfConcat
    (base regionBase outBase raVal : Word)
    (bs tail d0 d1 d2 d3 : List Byte) (O : Nat)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      ((schemaCR base .x8 (successFieldSpecs d0 d1 d2 d3)).union
        (successStatusReturnCode
          (base + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3)))))
      (abiPost regionBase outBase raVal bs **
        successSchemaReturnFrame regionBase outBase
          (O + schemaEnc (successFieldSpecs d0 d1 d2 d3))) := by
  let specs := successFieldSpecs d0 d1 d2 d3
  let w := fromFieldBytes d0 d1 d2 d3
  have hdec : decodeWithdrawal bs = some w := by
    exact decodeWithdrawal_eq_some_of_successFieldSpecs_input bs d0 d1 d2 d3
      hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput
  have hschemaCode : base.toNat + schemaSize specs < 2 ^ 64 := by
    dsimp [specs] at hcode ⊢
    omega
  have schemaCert := successFieldSpecsStepSuccessBytesCertOfConcat base regionBase outBase .x8
    bs tail d0 d1 d2 d3 O hc0 hl0 hc1 hl1 haddr hc3 hl3 hconcat halign hdalign hover
    hwin hdov hdval hschemaCode
  let schemaWithRa := WP.CFG.frameR schemaCert (.x1 ↦ᵣ raVal) (by pcFree)
  have schemaStrong :
      WP.CFG.Cert base (base + BitVec.ofNat 64 (schemaSize specs)) (schemaCR base .x8 specs)
        (successStatusReturnAbiRegOwnPre regionBase outBase raVal bs w **
          successSchemaReturnFrame regionBase outBase (O + schemaEnc specs)) := by
    exact schemaWithRa.weakenPost (by
      intro h hp
      unfold schemaINV at hp
      unfold successStatusReturnAbiRegOwnPre successStatusReturnAbiFrame successSchemaReturnFrame
      rw [show (⌜decodeWithdrawal bs = some w⌝ : Assertion) = empAssertion by
        funext h
        unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
        apply propext
        constructor
        · intro h_p
          exact h_p.1
        · intro h_empty
          exact ⟨h_empty, hdec⟩]
      simp only [sepConj_emp_right']
      xperm_hyp hp)
  let retBase := base + BitVec.ofNat 64 (schemaSize specs)
  let tailCert := (successStatusReturnAbiRegOwnCert retBase regionBase outBase raVal bs w).frameR
    (successSchemaReturnFrame regionBase outBase (O + schemaEnc specs))
    (successSchemaReturnFrame_pcFree regionBase outBase (O + schemaEnc specs))
  have hd : (schemaCR base .x8 specs).Disjoint (successStatusReturnCode retBase) := by
    dsimp [retBase, specs]
    exact schemaCR_disjoint_statusReturnCode .x8 (successFieldSpecs d0 d1 d2 d3) base (0 : Word)
      (by simpa [successStatusReturnCode] using hcode)
  exact WP.CFG.seqDisjoint hd schemaStrong.sound tailCert (WP.Entails.refl _)

/-- The composed success-path certificate reduces to the initial schema invariant
    plus the preserved return address; no decoded result appears in the precondition. -/
theorem successFieldSpecsReturnAbiCertOfConcat_pre
    (base regionBase outBase raVal : Word)
    (bs tail d0 d1 d2 d3 : List Byte) (O : Nat)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hconcat : bs.drop O = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (successFieldSpecsReturnAbiCertOfConcat base regionBase outBase raVal bs tail d0 d1 d2 d3 O
      hc0 hl0 hc1 hl1 haddr hc3 hl3 hconcat hinput halign hdalign hover hwin hdov hdval
      hcode).pre =
      (schemaINV regionBase outBase .x8 bs O (List.replicate outputSize (0 : Byte)) **
        (.x1 ↦ᵣ raVal)) := by
  unfold successFieldSpecsReturnAbiCertOfConcat
  rfl

/-- Caller-facing success-path WP certificate for a full short-list-encoded
    withdrawal.  The schema payload slice is derived from `hinput` internally,
    leaving only static memory/code facts and the success witnesses as inputs. -/
def successFieldSpecsReturnAbiCertOfInput
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      ((schemaCR base .x8 (successFieldSpecs d0 d1 d2 d3)).union
        (successStatusReturnCode
          (base + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3)))))
      (abiPost regionBase outBase raVal bs **
        successSchemaReturnFrame regionBase outBase
          (1 + schemaEnc (successFieldSpecs d0 d1 d2 d3))) :=
  successFieldSpecsReturnAbiCertOfConcat base regionBase outBase raVal bs ([] : List Byte)
    d0 d1 d2 d3 1 hc0 hl0 hc1 hl1 haddr hc3 hl3
    (successFieldSpecs_concat_of_input bs d0 d1 d2 d3 hl0 hl1 haddr hl3 hinput)
    hinput halign hdalign hover hwin hdov hdval hcode

/-- The encoded-input success wrapper computes the expected initial precondition:
    schema invariant at payload offset `1`, plus the preserved return address. -/
theorem successFieldSpecsReturnAbiCertOfInput_pre
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (successFieldSpecsReturnAbiCertOfInput base regionBase outBase raVal bs d0 d1 d2 d3
      hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov hdval hcode).pre =
      (schemaINV regionBase outBase .x8 bs 1 (List.replicate outputSize (0 : Byte)) **
        (.x1 ↦ᵣ raVal)) := by
  unfold successFieldSpecsReturnAbiCertOfInput
  rw [successFieldSpecsReturnAbiCertOfConcat_pre]

/-- Caller-facing success-path certificate for a walk-init success candidate:
    `x10` points to the list value start, so the first instruction initializes
    the schema cursor (`x13`) and then the generic generated schema/return
    certificate takes over. -/
def successFieldSpecsReturnAbiCertOfInputFromListStart
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      ((schemaCursorInitCode base).union
        ((schemaCR (base + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
          (successStatusReturnCode
            ((base + 4) + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3))))))
      (abiPost regionBase outBase raVal bs **
        successSchemaReturnFrame regionBase outBase
          (1 + schemaEnc (successFieldSpecs d0 d1 d2 d3))) := by
  let specs := successFieldSpecs d0 d1 d2 d3
  have htailCode : (base + 4).toNat + schemaSize specs + 8 < 2 ^ 64 := by
    have hbase4 : (base + 4).toNat = base.toNat + 4 := by
      bv_omega
    rw [hbase4]
    dsimp [specs] at hcode ⊢
    omega
  let head := schemaCursorInitCert base regionBase outBase raVal bs 0
    (List.replicate outputSize (0 : Byte))
  let tail := successFieldSpecsReturnAbiCertOfInput (base + 4) regionBase outBase raVal
    bs d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov
    hdval htailCode
  have hd : (schemaCursorInitCode base).Disjoint
      ((schemaCR (base + 4) .x8 specs).union
        (successStatusReturnCode
          ((base + 4) + BitVec.ofNat 64 (schemaSize specs)))) := by
    exact schemaCursorInitCode_disjoint_successReturnTail base .x8 specs (by
      dsimp [specs] at hcode ⊢
      exact hcode)
  exact WP.CFG.seqDisjoint hd head.sound tail (by
    rw [successFieldSpecsReturnAbiCertOfInput_pre]
    exact WP.Entails.refl _)

theorem successFieldSpecsReturnAbiCertOfInputFromListStart_pre
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (successFieldSpecsReturnAbiCertOfInputFromListStart base regionBase outBase raVal bs
      d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov
      hdval hcode).pre =
      schemaCursorInitPre regionBase outBase raVal bs 0
        (List.replicate outputSize (0 : Byte)) := by
  unfold successFieldSpecsReturnAbiCertOfInputFromListStart
  rfl

/-- The same list-start success cert, preserving the `x6 = 0xf8` scratch value
    produced by the short-list classifier. This is the exact tail shape needed
    when composing from `walkInitShortListCandidatePost`. -/
def successFieldSpecsReturnAbiCertOfInputFromListStartF8
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      ((schemaCursorInitCode base).union
        ((schemaCR (base + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
          (successStatusReturnCode
            ((base + 4) + BitVec.ofNat 64 (schemaSize (successFieldSpecs d0 d1 d2 d3))))))
      ((abiPost regionBase outBase raVal bs **
        successSchemaReturnFrame regionBase outBase
          (1 + schemaEnc (successFieldSpecs d0 d1 d2 d3))) **
        (.x6 ↦ᵣ (0xf8 : Word))) :=
  (successFieldSpecsReturnAbiCertOfInputFromListStart base regionBase outBase raVal bs
    d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov
    hdval hcode).frameR (.x6 ↦ᵣ (0xf8 : Word)) (by pcFree)

theorem successFieldSpecsReturnAbiCertOfInputFromListStartF8_pre
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (successFieldSpecsReturnAbiCertOfInputFromListStartF8 base regionBase outBase raVal bs
      d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov
      hdval hcode).pre =
      (schemaCursorInitPre regionBase outBase raVal bs 0
        (List.replicate outputSize (0 : Byte)) ** (.x6 ↦ᵣ (0xf8 : Word))) := by
  unfold successFieldSpecsReturnAbiCertOfInputFromListStartF8
  change ((successFieldSpecsReturnAbiCertOfInputFromListStart base regionBase outBase raVal bs
      d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov
      hdval hcode).pre ** (.x6 ↦ᵣ (0xf8 : Word))) =
    (schemaCursorInitPre regionBase outBase raVal bs 0
      (List.replicate outputSize (0 : Byte)) ** (.x6 ↦ᵣ (0xf8 : Word)))
  rw [successFieldSpecsReturnAbiCertOfInputFromListStart_pre]

/-- Short-list success continuation from the walk-init success label.  The label
    at `base + 124` contains only a jump island; generated schema code starts at
    `base + 172`, after the classifier/failure-return code range. -/
def successFieldSpecsReturnAbiCertOfInputFromWalkShortExit
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.CFG.Cert (base + 124) (successStatusReturnExit raVal)
      ((walkInitShortSuccessJumpCode base).union
        ((schemaCursorInitCode (base + 172)).union
          ((schemaCR (base + 172 + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
            (successStatusReturnCode
              ((base + 172 + 4) + BitVec.ofNat 64
                (schemaSize (successFieldSpecs d0 d1 d2 d3)))))))
      ((abiPost regionBase outBase raVal bs **
        successSchemaReturnFrame regionBase outBase
          (1 + schemaEnc (successFieldSpecs d0 d1 d2 d3))) **
        (.x6 ↦ᵣ (0xf8 : Word))) := by
  let specs := successFieldSpecs d0 d1 d2 d3
  let tailBase : Word := base + 172
  let tailPre : Assertion :=
    schemaCursorInitPre regionBase outBase raVal bs 0
      (List.replicate outputSize (0 : Byte)) ** (.x6 ↦ᵣ (0xf8 : Word))
  have htailCode : tailBase.toNat + 4 + schemaSize specs + 8 < 2 ^ 64 := by
    have hbase172 : tailBase.toNat = base.toNat + 172 := by
      dsimp [tailBase]
      bv_omega
    rw [hbase172]
    dsimp [specs] at hcode ⊢
    omega
  let tail := successFieldSpecsReturnAbiCertOfInputFromListStartF8 tailBase regionBase outBase
    raVal bs d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin
    hdov hdval htailCode
  have hjal := jal_x0_spec_gen_within (48 : BitVec 21) (base + 124)
  have htarget : (base + 124) + signExtend21 (48 : BitVec 21) = tailBase := by
    dsimp [tailBase]
    simp [signExtend21]
    bv_omega
  rw [htarget] at hjal
  let jump := (WP.CFG.block (WP.Entails.refl _) hjal).frameR tailPre (by
    dsimp [tailPre]
    unfold schemaCursorInitPre schemaCursorInitRestNoX13
    pcFree)
  have hd : (walkInitShortSuccessJumpCode base).Disjoint
      ((schemaCursorInitCode tailBase).union
        ((schemaCR (tailBase + 4) .x8 specs).union
          (successStatusReturnCode
            ((tailBase + 4) + BitVec.ofNat 64 (schemaSize specs))))) := by
    dsimp [tailBase, specs]
    exact walkInitShortSuccessJumpCode_disjoint_successReturnTail base .x8
      (successFieldSpecs d0 d1 d2 d3) (by simpa [Nat.add_assoc] using hcode)
  exact WP.CFG.seqDisjoint hd jump.sound tail (by
    intro h hp
    dsimp [tailPre] at hp
    rw [successFieldSpecsReturnAbiCertOfInputFromListStartF8_pre]
    simpa [sepConj_emp_left'] using hp)

theorem successFieldSpecsReturnAbiCertOfInputFromWalkShortExit_pre
    (base regionBase outBase raVal : Word)
    (bs d0 d1 d2 d3 : List Byte)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : bs = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (successFieldSpecsReturnAbiCertOfInputFromWalkShortExit base regionBase outBase raVal bs
      d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov
      hdval hcode).pre =
      (empAssertion **
        (schemaCursorInitPre regionBase outBase raVal bs 0
          (List.replicate outputSize (0 : Byte)) ** (.x6 ↦ᵣ (0xf8 : Word)))) := by
  unfold successFieldSpecsReturnAbiCertOfInputFromWalkShortExit
  rfl

/-- Link proof from the raw short-list classifier post, framed with the schema
    handoff resources, to the F8-framed generated success tail precondition. -/
theorem walkInitShortListCandidatePost_schemaWalkInitFrame_entails_tailPre
    (inputBase listLen raVal outBase : Word) (input : List Byte)
    (hoff : 0 < input.length) :
    WP.Entails
      (walkInitShortListCandidatePost inputBase listLen raVal input 0 hoff **
        schemaWalkInitFrame outBase)
      (schemaCursorInitPre inputBase outBase raVal input 0
        (List.replicate outputSize (0 : Byte)) ** (.x6 ↦ᵣ (0xf8 : Word))) := by
  intro h hp
  unfold walkInitShortListCandidatePost walkInitPrefixF8Post schemaWalkInitFrame at hp
  unfold schemaCursorInitPre schemaCursorInitRestNoX13
  drop_pure hp
  let pfx : Word := walkInitPrefixWord input 0 hoff
  let endPtr : Word := (inputBase + BitVec.ofNat 64 0) + listLen
  change
    (((((.x10 ↦ᵣ (inputBase + BitVec.ofNat 64 0)) **
        (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x11) **
          (regOwn .x12) ** (regOwn .x14) ** (regOwn .x15) ** bytesRegion inputBase input) **
         ((.x8 ↦ᵣ outBase) ** bytesRegion outBase (List.replicate outputSize (0 : Byte))) **
         (.x1 ↦ᵣ raVal))) ** regOwn .x13) ** (.x6 ↦ᵣ (0xf8 : Word))) h)
  have w1 := sepConj_mono_left (regIs_to_regOwn .x11 endPtr) h hp
  have w2 := sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 pfx))) h w1
  xperm_hyp w2

/-- The same link, targeting the computed precondition of the jump-island short
    success continuation. -/
theorem walkInitShortListCandidatePost_schemaWalkInitFrame_entails_walkShortExitPre
    (base inputBase listLen raVal outBase : Word) (input d0 d1 d2 d3 : List Byte)
    (hoff : 0 < input.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (halign : inputBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.Entails
      (walkInitShortListCandidatePost inputBase listLen raVal input 0 hoff **
        schemaWalkInitFrame outBase)
      (successFieldSpecsReturnAbiCertOfInputFromWalkShortExit base inputBase outBase raVal input
        d0 d1 d2 d3 hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput halign hdalign hover hwin hdov
        hdval hcode).pre := by
  intro h hp
  rw [successFieldSpecsReturnAbiCertOfInputFromWalkShortExit_pre]
  have htail := walkInitShortListCandidatePost_schemaWalkInitFrame_entails_tailPre
    inputBase listLen raVal outBase input hoff h hp
  exact (sepConj_emp_left h).mpr htail

attribute [rv64_wp_entails]
  walkInitShortListCandidatePost_schemaWalkInitFrame_entails_walkShortExitPre

end WithdrawalDecode

end EvmAsm.Rv64.RLP
