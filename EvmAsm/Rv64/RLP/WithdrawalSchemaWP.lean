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

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP

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

private theorem schemaEncBytes_successFieldSpecs_length_le_48
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

end WithdrawalDecode

end EvmAsm.Rv64.RLP
