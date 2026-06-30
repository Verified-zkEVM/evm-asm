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

end WithdrawalDecode

end EvmAsm.Rv64.RLP
