/-
  EvmAsm.Rv64.RLP.WithdrawalDecodeAutoWP

  Caller-facing WP automation for the withdrawal decoder success path.  The
  generated schema code still depends on the field byte witnesses, but callers
  only provide the pure `decodeWithdrawal` result; this module extracts the
  witnesses and packages the resulting WP certificate.
-/

import EvmAsm.Rv64.RLP.WithdrawalDecodeSemanticWP

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace WithdrawalDecode

theorem schemaSize_successFieldSpecs_le_1392
    (d0 d1 d2 d3 : List Byte) (haddr : d2.length = 20) :
    schemaSize (successFieldSpecs d0 d1 d2 d3) <= 1392 := by
  simp [schemaSize, successFieldSpecs, fieldSize, haddr]
  split <;> split <;> split <;> omega

theorem successFieldSpecs_input_length_pos
    (input d0 d1 d2 d3 : List Byte)
    (hl0 : d0.length <= 8) (hl1 : d1.length <= 8)
    (haddr : d2.length = 20) (hl3 : d3.length <= 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) :
    0 < input.length := by
  have hpayload :=
    schemaEncBytes_successFieldSpecs_length_le_48 d0 d1 d2 d3 hl0 hl1 haddr hl3
  have hshort : (schemaEncBytes (successFieldSpecs d0 d1 d2 d3)).length <= 55 := by
    omega
  subst input
  rw [encode_list_schemaItems_short (successFieldSpecs d0 d1 d2 d3) hshort]
  simp

/-- WP package produced from a pure successful withdrawal decode.  The schema
    remains result-free: the decoded value is related to the postcondition only
    through `hw`, while the generated code/cert fields are indexed by the byte
    witnesses extracted from `decodeWithdrawal`. -/
structure WalkInitShortSuccessDecodedWP
    (base sp0 raVal s0Old s1Old s2Old outBase : Word)
    (m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal) where
  d0 : List Byte
  d1 : List Byte
  d2 : List Byte
  d3 : List Byte
  hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))
  hc0 : Not (d0.headD 1 = 0)
  hl0 : d0.length <= 8
  hc1 : Not (d1.headD 1 = 0)
  hl1 : d1.length <= 8
  haddr : d2.length = 20
  hc3 : Not (d3.headD 1 = 0)
  hl3 : d3.length <= 8
  hw : w = fromFieldBytes d0 d1 d2 d3
  hoff : 0 < input.length
  h_schema_size : schemaSize (successFieldSpecs d0 d1 d2 d3) <= 1392
  cert : WP.CFG.Cert base (successStatusReturnExit raVal)
    ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) (successFieldSpecs d0 d1 d2 d3)))
    (walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3 **
      walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old)
  hpre : cert.pre =
    (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
      walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input)

/-- Decode-driven automation for the prologue-to-success WP slice.  It consumes
    the pure decoder result and a uniform static code-size bound, then proves that
    the same generated WP package as the witness-heavy constructor is available. -/
theorem walkInitShortSuccessDecodedWP_nonempty
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    Nonempty (WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w) := by
  rcases successFieldSpecs_input_of_decodeWithdrawal_eq_some input w hdec with
    ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3, hw⟩
  have hoff := successFieldSpecs_input_length_pos input d0 d1 d2 d3 hl0 hl1 haddr hl3 hinput
  have h_schema_size := schemaSize_successFieldSpecs_le_1392 d0 d1 d2 d3 haddr
  have hcode : (base + 24).toNat + 172 + 4 +
      schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64 := by
    omega
  exact ⟨
    { d0 := d0
      d1 := d1
      d2 := d2
      d3 := d3
      hinput := hinput
      hc0 := hc0
      hl0 := hl0
      hc1 := hc1
      hl1 := hl1
      haddr := haddr
      hc3 := hc3
      hl3 := hl3
      hw := hw
      hoff := hoff
      h_schema_size := h_schema_size
      cert := walkInitShortSuccessFromPrologueCert base sp0 raVal s0Old s1Old s2Old outBase
        m0 m1 m2 m3 inputBase listLen t0Old t1Old input d0 d1 d2 d3 hsalign hoff hover
        hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput h_len h_prologue_code
        hcode
      hpre := by
        rw [walkInitShortSuccessFromPrologueCert_pre] }⟩


/-- Direct constructor for the decoded-success WP package.  This is the entry
    point generated callers should use: bind the package once, then continue
    with `pkg.cert` and `pkg.hpre` rather than manually destructing the pure
    decoder characterization. -/
noncomputable def walkInitShortSuccessDecodedWP
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w :=
  Classical.choice (walkInitShortSuccessDecodedWP_nonempty base sp0 raVal s0Old s1Old s2Old
    outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin
    hdalign hdov hdval h_len h_prologue_code h_code_max)

/-- The decoded-success package exposes the same static prologue precondition as
    the witness-heavy certificate. -/
theorem walkInitShortSuccessDecodedWP_cert_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
      h_len h_prologue_code h_code_max).cert.pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) :=
  (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
    inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval h_len
    h_prologue_code h_code_max).hpre

attribute [rv64_wp]
  walkInitShortSuccessDecodedWP_cert_pre

attribute [rv64_wp_cert]
  walkInitShortSuccessFromPrologueCert

-- Regression: `wp_rv64_cert` derives the exact generated-code bound from a
-- uniform static schema-size cap and local arithmetic facts.
example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0)
    (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_schema_size : schemaSize (successFieldSpecs d0 d1 d2 d3) <= 1392)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      ((prologueCode base).union
        (walkInitShortSuccessResolvedCode (base + 24) (successFieldSpecs d0 d1 d2 d3)))
      (walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3 **
        walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old) := by
  wp_rv64_cert

/-- Result-free success schemas are exactly the inputs for which the Lean
    withdrawal decoder returns some value. This keeps the schema predicate free
    of the decoded result while still characterizing `decodeWithdrawal`. -/
theorem successFieldSpecsInput_iff_exists_decodeWithdrawal_eq_some
    (input : List Byte) :
    successFieldSpecsInput input ↔ ∃ w : Withdrawal, decodeWithdrawal input = some w := by
  constructor
  · rintro ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3⟩
    exact ⟨fromFieldBytes d0 d1 d2 d3,
      decodeWithdrawal_eq_some_of_successFieldSpecs_input input d0 d1 d2 d3
        hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput⟩
  · rintro ⟨w, hdec⟩
    rcases successFieldSpecs_input_of_decodeWithdrawal_eq_some input w hdec with
      ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3, _hw⟩
    exact ⟨d0, d1, d2, d3, hinput, hc0, hl0, hc1, hl1, haddr, hc3, hl3⟩

/-- Solve a withdrawal WP certificate goal by first trying the certificate
    database directly, then splitting on the pure decoder result and exposing
    the corresponding result-free schema/failure facts to the same database. -/
macro "wp_withdrawal_decode_cert " input:term : tactic =>
  `(tactic| first
    | wp_rv64_cert
    | cases hdec : decodeWithdrawal $input with
      | none =>
          have h_failure : ¬ successFieldSpecsInput $input :=
            (decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput $input).1 hdec
          wp_rv64_cert
      | some w =>
          have h_success : successFieldSpecsInput $input :=
            (successFieldSpecsInput_iff_exists_decodeWithdrawal_eq_some $input).2 ⟨w, hdec⟩
          wp_rv64_cert)

/-- A result-free success-schema input is enough to produce a decoded-success WP
    package for some Lean withdrawal result. -/
theorem walkInitShortSuccessDecodedWP_exists_of_successFieldSpecsInput
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    ∃ w : Withdrawal,
      Nonempty (WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase
        m0 m1 m2 m3 inputBase listLen t0Old t1Old input w) := by
  rcases (successFieldSpecsInput_iff_exists_decodeWithdrawal_eq_some input).mp h_success with
    ⟨w, hdec⟩
  exact ⟨w, walkInitShortSuccessDecodedWP_nonempty base sp0 raVal s0Old s1Old s2Old outBase
    m0 m1 m2 m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign
    hdov hdval h_len h_prologue_code h_code_max⟩

/-- Direct package constructor from the result-free success-schema predicate.
    The returned Sigma carries the Lean decoded value, but the caller does not
    put that value into the schema or precondition. -/
noncomputable def walkInitShortSuccessSchemaInputWP
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    Sigma (fun w : Withdrawal => WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old
      s2Old outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old input w) :=
  let h_pkg := walkInitShortSuccessDecodedWP_exists_of_successFieldSpecsInput base sp0 raVal
    s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old input h_success
    hsalign hover hwin hdalign hdov hdval h_len h_prologue_code h_code_max
  Classical.choice (by
    rcases h_pkg with ⟨w, hpkg⟩
    exact ⟨⟨w, Classical.choice hpkg⟩⟩)

/-- The result-free success-schema package has the same static prologue
    precondition as the decoded-result package. -/
theorem walkInitShortSuccessSchemaInputWP_cert_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessSchemaInputWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
      h_len h_prologue_code h_code_max).2.cert.pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) :=
  (walkInitShortSuccessSchemaInputWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
    inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval h_len
    h_prologue_code h_code_max).2.hpre

attribute [rv64_wp]
  walkInitShortSuccessSchemaInputWP_cert_pre

/-- Nonempty inputs select the reason-erased classifier exits in the zero/nonzero
    facade. This hides the empty-input singleton branch once a caller has any
    static nonempty witness. -/
theorem walkInitZeroNonzeroAbiFailureFromPrologueExits_of_pos
    (base sp0 raVal s0Old s1Old s2Old outBase : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (hoff : 0 < input.length) :
    walkInitZeroNonzeroAbiFailureFromPrologueExits base sp0 raVal s0Old s1Old s2Old outBase
      inputBase listLen t0Old t1Old input =
      walkInitAbiFailureReasonErasedFromPrologueExits base sp0 raVal s0Old s1Old s2Old outBase
        inputBase listLen t0Old t1Old input hoff := by
  cases input with
  | nil => simp at hoff
  | cons _ _ => rfl

namespace WalkInitShortSuccessDecodedWP

/-- Result-free schema witnesses extracted by a decoded-success WP package. -/
def specs
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w) : List FieldSpec :=
  successFieldSpecs pkg.d0 pkg.d1 pkg.d2 pkg.d3

/-- The decoded package's generated success schema fits under the public max-code
    bound used by `walkInitShortSuccessDecodedWP`. -/
theorem code_bound_of_max
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (base + 24).toNat + 172 + 4 + schemaSize pkg.specs + 8 < 2 ^ 64 := by
  have h_schema_size := pkg.h_schema_size
  unfold specs
  omega


/-- Code covered by the prologue-to-success certificate carried by a decoded WP
    package.  Naming it lets generated proofs talk about the package, not the
    extracted field witnesses. -/
def successCode
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w) : CodeReq :=
  (prologueCode base).union (walkInitShortSuccessResolvedCode (base + 24) pkg.specs)

/-- Postcondition of the package-carried success certificate. -/
def successPost
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w) : Assertion :=
  walkInitShortSuccessAbiPost inputBase outBase raVal input pkg.d0 pkg.d1 pkg.d2 pkg.d3 **
    walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old

/-- Package projection as a WP certificate.  This is registered as a certificate
    hint so `wp_rv64_cert` can close package-shaped success goals directly. -/
def successCert
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w) :
    WP.CFG.Cert base (successStatusReturnExit raVal) pkg.successCode pkg.successPost := by
  dsimp [successCode, successPost, specs]
  exact pkg.cert

/-- The package-shaped success certificate reduces to the static caller
    precondition. -/
theorem successCert_pre
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w) :
    pkg.successCert.pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  dsimp [successCert]
  exact pkg.hpre

attribute [rv64_wp] successCert_pre
attribute [rv64_wp_cert] successCert

example
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w) :
    WP.CFG.Cert base (successStatusReturnExit raVal) pkg.successCode pkg.successPost := by
  wp_rv64_cert

/-- Zero/nonzero classifier facade over the same generated code requirement as a
    decoded-success package.  This removes the last need to reconstruct the
    witness-specific `successFieldSpecs` when composing branch-level automation. -/
def failureNBranch
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) pkg.specs)) :=
  walkInitZeroNonzeroAbiFailureFromPrologueResolvedCodeSuccessFrameNBranch base sp0 raVal
    s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old input pkg.specs
    hsalign hover hwin h_len h_prologue_code (pkg.code_bound_of_max h_code_max)

/-- The package-indexed zero/nonzero facade has the same static precondition as
    the decoded success certificate. -/
theorem failureNBranch_pre
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (pkg.failureNBranch hsalign hover hwin h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  unfold failureNBranch
  rw [walkInitZeroNonzeroAbiFailureFromPrologueResolvedCodeSuccessFrameNBranch_pre]

/-- Package-indexed classifier exits normalized to the nonempty, reason-erased
    shape. The low-level empty/nonempty `match` is discharged by `pkg.hoff`. -/
theorem failureNBranch_exits
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (pkg.failureNBranch hsalign hover hwin h_len h_prologue_code h_code_max).exits =
      (walkInitAbiFailureReasonErasedFromPrologueExits base sp0 raVal s0Old s1Old s2Old
        outBase inputBase listLen t0Old t1Old input pkg.hoff).map
        (fun ex => (ex.1, ex.2 ** walkInitSchemaScratchFrame)) := by
  unfold failureNBranch
  rw [walkInitZeroNonzeroAbiFailureFromPrologueResolvedCodeSuccessFrameNBranch_exits]
  unfold walkInitZeroNonzeroAbiFailureFromPrologueResolvedCodeSuccessFrameExits
  rw [walkInitZeroNonzeroAbiFailureFromPrologueExits_of_pos base sp0 raVal s0Old s1Old
    s2Old outBase inputBase listLen t0Old t1Old input pkg.hoff]

attribute [rv64_wp]
  failureNBranch_pre

attribute [rv64_wp_cert]
  failureNBranch

/-- Package-indexed failure branch with the long-list exit already continued
    through the reason-erased failure return block. -/
def failureLongNBranch
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base (pkg.successCode.union (failStatusReturnCode ((base + 24) + 28))) := by
  dsimp [successCode]
  exact walkInitAbiFailureReasonErasedFromPrologueResolvedCodeLongFailureSuccessFrameNBranch
    base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old
    input pkg.specs hsalign pkg.hoff (by omega) (hwin 0 pkg.hoff) h_len (by omega)
    h_prologue_code (pkg.code_bound_of_max h_code_max)

/-- The long-failure package branch keeps the same static success-shaped
    precondition as the success certificate. -/
theorem failureLongNBranch_pre
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (pkg.failureLongNBranch hsalign hover hwin h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  simpa [failureLongNBranch] using
    (walkInitAbiFailureReasonErasedFromPrologueResolvedCodeLongFailureSuccessFrameNBranch_pre
      base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old
      input pkg.specs hsalign pkg.hoff (by omega) (hwin 0 pkg.hoff) h_len (by omega)
      h_prologue_code (pkg.code_bound_of_max h_code_max))

attribute [rv64_wp]
  failureLongNBranch_pre

attribute [rv64_wp_cert]
  failureLongNBranch

example
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base (pkg.successCode.union (failStatusReturnCode ((base + 24) + 28))) := by
  wp_rv64_cert

example
    {base sp0 raVal s0Old s1Old s2Old outBase : Word}
    {m0 m1 m2 m3 inputBase listLen t0Old t1Old : Word}
    {input : List Byte} {w : Withdrawal}
    (pkg : WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) pkg.specs)) := by
  wp_rv64_cert



end WalkInitShortSuccessDecodedWP

/-- Success certificate projected directly from a pure successful decode result.
    Generated callers can provide `decodeWithdrawal input = some w` and static
    memory/code facts; the field-byte witness package stays internal. -/
noncomputable def walkInitShortSuccessDecodedCert
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
        inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
        h_len h_prologue_code h_code_max).successCode
      (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
        inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
        h_len h_prologue_code h_code_max).successPost :=
  (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
    inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).successCert

/-- The decoded-result success cert has the static prologue precondition. -/
theorem walkInitShortSuccessDecodedCert_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessDecodedCert base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
      m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
      h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  exact (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).successCert_pre

/-- Failure classifier branch over the same resolved code as the decoded-success
    package, without exposing the package to generated callers. -/
noncomputable def walkInitShortSuccessDecodedFailureNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24)
        (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
          m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov
          hdval h_len h_prologue_code h_code_max).specs)) :=
  (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
    inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureNBranch hsalign hover hwin h_len h_prologue_code
    h_code_max

/-- The decoded-result failure branch has the same static prologue precondition
    as the decoded success cert. -/
theorem walkInitShortSuccessDecodedFailureNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessDecodedFailureNBranch base sp0 raVal s0Old s1Old s2Old outBase
      m0 m1 m2 m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign
      hdov hdval h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  exact (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureNBranch_pre hsalign hover hwin h_len h_prologue_code
    h_code_max

/-- Decoded-result failure exits normalized to the nonempty, reason-erased shape. -/
theorem walkInitShortSuccessDecodedFailureNBranch_exits
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessDecodedFailureNBranch base sp0 raVal s0Old s1Old s2Old outBase
      m0 m1 m2 m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign
      hdov hdval h_len h_prologue_code h_code_max).exits =
      (walkInitAbiFailureReasonErasedFromPrologueExits base sp0 raVal s0Old s1Old s2Old
        outBase inputBase listLen t0Old t1Old input
        (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
          m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov
          hdval h_len h_prologue_code h_code_max).hoff).map
        (fun ex => (ex.1, ex.2 ** walkInitSchemaScratchFrame)) := by
  exact (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureNBranch_exits hsalign hover hwin h_len h_prologue_code
    h_code_max

/-- Decoded-result failure branch with the long-list exit already continued
    through the reason-erased ABI failure return. -/
noncomputable def walkInitShortSuccessDecodedLongFailureNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode.union
        (failStatusReturnCode ((base + 24) + 28))) :=
  (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
    inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureLongNBranch hsalign hover hwin h_len
    h_prologue_code h_code_max

/-- The decoded-result long-failure branch has the same static prologue
    precondition as the success certificate. -/
theorem walkInitShortSuccessDecodedLongFailureNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessDecodedLongFailureNBranch base sp0 raVal s0Old s1Old s2Old outBase
      m0 m1 m2 m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign
      hdov hdval h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  exact (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureLongNBranch_pre hsalign hover hwin h_len
    h_prologue_code h_code_max

attribute [rv64_wp]
  walkInitShortSuccessDecodedCert_pre
  walkInitShortSuccessDecodedFailureNBranch_pre
  walkInitShortSuccessDecodedLongFailureNBranch_pre

attribute [rv64_wp_cert]
  walkInitShortSuccessDecodedCert
  walkInitShortSuccessDecodedFailureNBranch
  walkInitShortSuccessDecodedLongFailureNBranch

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
        inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
        h_len h_prologue_code h_code_max).successCode
      (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
        inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov hdval
        h_len h_prologue_code h_code_max).successPost := by
  wp_rv64_cert

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24)
        (walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
          m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov
          hdval h_len h_prologue_code h_code_max).specs)) := by
  wp_rv64_cert

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode.union
        (failStatusReturnCode ((base + 24) + 28))) := by
  wp_rv64_cert

/-- Result-free package projection from a successful schema-input predicate.
    Generated callers can keep the schema predicate free of decoded results and
    still obtain the concrete decoded-success WP package when they need to name
    its code or postcondition. -/
noncomputable def walkInitShortSuccessSchemaInputPkg
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old input
      (walkInitShortSuccessSchemaInputWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).1 :=
  (walkInitShortSuccessSchemaInputWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).2

/-- Success certificate projected directly from the result-free schema predicate. -/
noncomputable def walkInitShortSuccessSchemaInputCert
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode
      (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successPost :=
  (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).successCert

/-- The result-free schema-input success cert has the static prologue
    precondition. -/
theorem walkInitShortSuccessSchemaInputCert_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessSchemaInputCert base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
      m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
      h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  exact (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
    m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).successCert_pre

/-- Failure classifier branch over the same resolved code as the result-free
    schema-input success package.  This is useful when a generated proof keeps a
    zero/nonzero disjunction in the CFG before selecting the success exit. -/
noncomputable def walkInitShortSuccessSchemaInputFailureNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24)
        (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
          m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
          hdval h_len h_prologue_code h_code_max).specs)) :=
  (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureNBranch hsalign hover hwin h_len h_prologue_code
    h_code_max

/-- The result-free schema-input failure branch has the same static prologue
    precondition as the success cert. -/
theorem walkInitShortSuccessSchemaInputFailureNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessSchemaInputFailureNBranch base sp0 raVal s0Old s1Old s2Old outBase
      m0 m1 m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign
      hdov hdval h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  exact (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
    m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureNBranch_pre hsalign hover hwin h_len h_prologue_code
    h_code_max

/-- Result-free schema-input failure exits normalized to the nonempty,
    reason-erased classifier shape. -/
theorem walkInitShortSuccessSchemaInputFailureNBranch_exits
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessSchemaInputFailureNBranch base sp0 raVal s0Old s1Old s2Old outBase
      m0 m1 m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign
      hdov hdval h_len h_prologue_code h_code_max).exits =
      (walkInitAbiFailureReasonErasedFromPrologueExits base sp0 raVal s0Old s1Old s2Old
        outBase inputBase listLen t0Old t1Old input
        (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
          m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
          hdval h_len h_prologue_code h_code_max).hoff).map
        (fun ex => (ex.1, ex.2 ** walkInitSchemaScratchFrame)) := by
  exact (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
    m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureNBranch_exits hsalign hover hwin h_len h_prologue_code
    h_code_max

/-- Result-free schema-input failure branch with the long-list exit already
    continued through the reason-erased ABI failure return. -/
noncomputable def walkInitShortSuccessSchemaInputLongFailureNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
        m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode.union
        (failStatusReturnCode ((base + 24) + 28))) :=
  (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
    m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureLongNBranch hsalign hover hwin h_len
    h_prologue_code h_code_max

/-- The result-free schema-input long-failure branch has the same static
    prologue precondition as the success certificate. -/
theorem walkInitShortSuccessSchemaInputLongFailureNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (walkInitShortSuccessSchemaInputLongFailureNBranch base sp0 raVal s0Old s1Old s2Old
      outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover
      hwin hdalign hdov hdval h_len h_prologue_code h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  exact (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
    m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov hdval
    h_len h_prologue_code h_code_max).failureLongNBranch_pre hsalign hover hwin h_len
    h_prologue_code h_code_max


attribute [rv64_wp]
  walkInitShortSuccessSchemaInputCert_pre
  walkInitShortSuccessSchemaInputFailureNBranch_pre
  walkInitShortSuccessSchemaInputLongFailureNBranch_pre

attribute [rv64_wp_cert]
  walkInitShortSuccessSchemaInputCert
  walkInitShortSuccessSchemaInputFailureNBranch
  walkInitShortSuccessSchemaInputLongFailureNBranch

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode
      (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successPost := by
  wp_rv64_cert

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24)
        (walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
          m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
          hdval h_len h_prologue_code h_code_max).specs)) := by
  wp_rv64_cert

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
        m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode.union
        (failStatusReturnCode ((base + 24) + 28))) := by
  wp_rv64_cert


-- Register the generic reason-erased zero/nonzero classifier after the more
-- specific decoded/schema-success facades. Generated proofs can then fall
-- back to the coarse ABI failure branch when they only know a static schema
-- size bound, without reconstructing the precise success witnesses.
attribute [rv64_wp_cert]
  walkInitZeroNonzeroAbiFailureReasonErasedFromPrologueResolvedCodeSuccessFrameNBranch
  walkInitZeroNonzeroAbiFailureReasonErasedFromPrologueResolvedCodeLongFailureSuccessFrameNBranch

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (specs : List FieldSpec)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_schema_size : schemaSize specs <= 1392)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) specs)) := by
  wp_rv64_cert

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (specs : List FieldSpec)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_schema_size : schemaSize specs <= 1392)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base (((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) specs)).union
      (failStatusReturnCode ((base + 24) + 28))) := by
  wp_rv64_cert

theorem successFieldSpecsInput_or_decodeWithdrawal_eq_none
    (input : List Byte) :
    successFieldSpecsInput input ∨ decodeWithdrawal input = none := by
  cases hdec : decodeWithdrawal input with
  | none =>
      exact Or.inr rfl
  | some w =>
      exact Or.inl
        ((successFieldSpecsInput_iff_exists_decodeWithdrawal_eq_some input).2 ⟨w, hdec⟩)

/-- Result-free schema-success bridge for generated validating field walks.  The
    decoded result is used only as an existential witness for the semantic
    characterization of `successFieldSpecsInput`; the schema predicate itself
    remains result-free. -/
theorem successFieldSpecsInput_of_shortList_four_decode_chain
    {pfx : Byte} {payload r1 r2 r3 r4 d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, r1))
    (h1 : ∀ m, decodeAux (m + 1) r1 = some (.bytes d1, r2))
    (h2 : ∀ m, decodeAux (m + 1) r2 = some (.bytes d2, r3))
    (h3 : ∀ m, decodeAux (m + 1) r3 = some (.bytes d3, r4))
    (hend : r4 = [])
    (h_min : 2 ≤ payload.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    successFieldSpecsInput (pfx :: payload) :=
  (successFieldSpecsInput_iff_exists_decodeWithdrawal_eq_some (pfx :: payload)).2
    ⟨fromFieldBytes d0 d1 d2 d3,
      decodeWithdrawal_shortList_four_of_decodeAux_chain_auto h_class h_len h0 h1 h2 h3 hend
        h_min hc0 hl0 hc1 hl1 haddr hc3 hl3⟩

/-- Convert a validating field-post `decode` fact into the fuel-polymorphic
    `decodeAux` continuation consumed by the short-list WP bridge. -/
macro "wp_rlp_field_decode_aux " hDecode:term : tactic =>
  `(tactic| exact decodeAux_bytes_all_fuel_of_decode _ _ _ _ $hDecode)

/-- Exact-arity success automation for WP-generated validating field walks.  It
    derives the four `decodeAux` continuations from field-post `decode` facts and
    applies the withdrawal success bridge. -/
macro "withdrawal_decode_success_chain " hclass:term ", " hlen:term ", " hdec0:term ", "
    hdec1:term ", " hdec2:term ", " hdec3:term ", " hend:term ", " hmin:term ", "
    hc0:term ", " hl0:term ", " hc1:term ", " hl1:term ", " haddr:term ", "
    hc3:term ", " hl3:term : tactic =>
  `(tactic| exact decodeWithdrawal_shortList_four_of_decodeAux_chain_auto
    $hclass $hlen
    (by wp_rlp_field_decode_aux $hdec0)
    (by wp_rlp_field_decode_aux $hdec1)
    (by wp_rlp_field_decode_aux $hdec2)
    (by wp_rlp_field_decode_aux $hdec3)
    $hend $hmin $hc0 $hl0 $hc1 $hl1 $haddr $hc3 $hl3)

/-- Result-free schema-success automation for WP-generated validating field walks. -/
macro "withdrawal_schema_success_chain " hclass:term ", " hlen:term ", " hdec0:term ", "
    hdec1:term ", " hdec2:term ", " hdec3:term ", " hend:term ", " hmin:term ", "
    hc0:term ", " hl0:term ", " hc1:term ", " hl1:term ", " haddr:term ", "
    hc3:term ", " hl3:term : tactic =>
  `(tactic| exact successFieldSpecsInput_of_shortList_four_decode_chain
    $hclass $hlen
    (by wp_rlp_field_decode_aux $hdec0)
    (by wp_rlp_field_decode_aux $hdec1)
    (by wp_rlp_field_decode_aux $hdec2)
    (by wp_rlp_field_decode_aux $hdec3)
    $hend $hmin $hc0 $hl0 $hc1 $hl1 $haddr $hc3 $hl3)

/-- Exact-arity leftover failure automation for WP-generated validating field
    walks.  It derives all four `decodeAux` continuations from local field-post
    `decode` facts, then applies the chain-shaped withdrawal failure bridge. -/
macro "withdrawal_decode_failure_chain " hclass:term ", " hlen:term ", " hdec0:term ", "
    hdec1:term ", " hdec2:term ", " hdec3:term ", " hleftover:term ", " hmin:term : tactic =>
  `(tactic| exact decodeWithdrawal_none_of_shortList_four_leftover_chain_auto
    $hclass $hlen
    (by wp_rlp_field_decode_aux $hdec0)
    (by wp_rlp_field_decode_aux $hdec1)
    (by wp_rlp_field_decode_aux $hdec2)
    (by wp_rlp_field_decode_aux $hdec3)
    $hleftover $hmin)

/-- Pure failure automation for the semantic side of withdrawal WP joins. It
    consumes the common facts produced by validating RLP blocks: failed complete
    decode, raw decode failure, raw decode with trailing bytes, non-list complete
    decode, wrong list arity, bad canonical field guards, or a result-free schema
    negation. -/
macro "withdrawal_decode_failure" : tactic =>
  `(tactic| first
    | assumption
    | exact decodeWithdrawal_none_of_decodeFully_none (by assumption)
    | exact decodeWithdrawal_none_of_decode_none (by assumption)
    | exact decodeWithdrawal_none_of_decode_leftover (by assumption) (by assumption)
    | exact decodeWithdrawal_none_of_decodeFully_bytes (by assumption)
    | exact decodeWithdrawal_none_of_decodeFully_list_length_ne_four (by assumption) (by assumption)
    | exact decodeWithdrawal_none_of_decodeFully_fields_not_canonical (by assumption) (by assumption)
    | exact decodeWithdrawal_none_of_walkInitPrefixWord_not_lt_f8 _ (by assumption) (by assumption)
    | exact (decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput _).2 (by assumption))

/-- Exact-arity leftover failure automation for validated short-list paths.
    Generated proofs pass the static branch facts produced by the WP walk. -/
macro "withdrawal_decode_failure " hclass:term ", " hlen:term ", " h0:term ", " h1:term ", "
    h2:term ", " h3:term ", " hleftover:term ", " hmin:term : tactic =>
  `(tactic| exact decodeWithdrawal_none_of_shortList_four_leftover_auto
    $hclass $hlen $h0 $h1 $h2 $h3 $hleftover $hmin)

/-- Schema-concat leftover failure automation for generated WP schema walks.
    The caller supplies only static field bounds, the schema payload split, and a
    nonempty leftover; the intermediate `decodeAux` facts are derived internally. -/
macro "withdrawal_decode_failure " hclass:term ", " hlen:term ", " hl0:term ", " hl1:term ", "
    haddr:term ", " hl3:term ", " hPayload:term ", " hTail:term ", " hmin:term : tactic =>
  `(tactic| exact decodeWithdrawal_none_of_shortList_successFieldSpecs_leftover_auto
    $hclass $hlen $hl0 $hl1 $haddr $hl3 $hPayload $hTail $hmin)

/-- Same automation, but returning the result-free schema failure predicate used
    by caller-facing WP wrappers. -/
macro "withdrawal_schema_failure" : tactic =>
  `(tactic| exact (decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput _).1
    (by withdrawal_decode_failure))

/-- Schema-concat leftover failure automation for result-free schema predicates. -/
macro "withdrawal_schema_failure " hclass:term ", " hlen:term ", " hl0:term ", " hl1:term ", "
    haddr:term ", " hl3:term ", " hPayload:term ", " hTail:term ", " hmin:term : tactic =>
  `(tactic| exact (decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput _).1
    (by withdrawal_decode_failure $hclass, $hlen, $hl0, $hl1, $haddr, $hl3, $hPayload,
      $hTail, $hmin))

/-- Withdrawal-domain WP automation.  This is the tactic generated proofs should
    use at control-flow joins: it solves pure withdrawal failure/schema facts
    first, then asks the WP certificate, entailment, and dead-exit databases. -/
macro "wp_withdrawal_decode_auto" : tactic =>
  `(tactic| first
    | withdrawal_decode_failure
    | withdrawal_schema_failure
    | assumption
    | omega
    | bv_omega
    | wp_rv64_cert
    | wp_rv64_link
    | wp_rv64_dead)

/-- Outcome-splitting withdrawal WP automation.  When the goal is a WP
    certificate, this first splits on the pure decoder result and exposes the
    corresponding result-free schema fact before falling back to the generic
    withdrawal WP driver. -/
macro "wp_withdrawal_decode_auto " input:term : tactic =>
  `(tactic| first
    | wp_withdrawal_decode_cert $input
    | wp_withdrawal_decode_auto)

/-- Chain-shaped exact-arity success overload for generated validating field walks.
    It can close either the semantic `decodeWithdrawal = some ...` goal or the
    result-free `successFieldSpecsInput` goal. -/
macro "wp_withdrawal_decode_chain_auto " hclass:term ", " hlen:term ", " hdec0:term ", "
    hdec1:term ", " hdec2:term ", " hdec3:term ", " hend:term ", " hmin:term ", "
    hc0:term ", " hl0:term ", " hc1:term ", " hl1:term ", " haddr:term ", "
    hc3:term ", " hl3:term : tactic =>
  `(tactic| first
    | withdrawal_schema_success_chain $hclass, $hlen, $hdec0, $hdec1, $hdec2, $hdec3,
        $hend, $hmin, $hc0, $hl0, $hc1, $hl1, $haddr, $hc3, $hl3
    | withdrawal_decode_success_chain $hclass, $hlen, $hdec0, $hdec1, $hdec2, $hdec3,
        $hend, $hmin, $hc0, $hl0, $hc1, $hl1, $haddr, $hc3, $hl3
    | wp_withdrawal_decode_auto)

/-- Chain-shaped exact-arity leftover overload for generated validating field walks.
    The four field `decodeAux` continuations are built automatically from the
    WP field-post `decode` facts. -/
macro "wp_withdrawal_decode_chain_auto " hclass:term ", " hlen:term ", " hdec0:term ", "
    hdec1:term ", " hdec2:term ", " hdec3:term ", " hleftover:term ", " hmin:term : tactic =>
  `(tactic| first
    | withdrawal_decode_failure_chain $hclass, $hlen, $hdec0, $hdec1, $hdec2, $hdec3,
        $hleftover, $hmin
    | wp_withdrawal_decode_auto)

/-- Exact-arity leftover overload for generated short-list field walks. -/
macro "wp_withdrawal_decode_auto " hclass:term ", " hlen:term ", " h0:term ", " h1:term ", "
    h2:term ", " h3:term ", " hleftover:term ", " hmin:term : tactic =>
  `(tactic| first
    | withdrawal_decode_failure $hclass, $hlen, $h0, $h1, $h2, $h3, $hleftover, $hmin
    | wp_withdrawal_decode_auto)

/-- Schema-concat exact-arity leftover overload for generated withdrawal schema
    walks.  This keeps the schema result-free while deriving the semantic
    failure fact needed by ABI postconditions. -/
macro "wp_withdrawal_decode_auto " hclass:term ", " hlen:term ", " hl0:term ", " hl1:term ", "
    haddr:term ", " hl3:term ", " hPayload:term ", " hTail:term ", " hmin:term : tactic =>
  `(tactic| first
    | withdrawal_schema_failure $hclass, $hlen, $hl0, $hl1, $haddr, $hl3, $hPayload,
        $hTail, $hmin
    | withdrawal_decode_failure $hclass, $hlen, $hl0, $hl1, $haddr, $hl3, $hPayload,
        $hTail, $hmin
    | wp_withdrawal_decode_auto)

example
    (input : List Byte) (hfull : decodeFully input = none) :
    decodeWithdrawal input = none := by
  withdrawal_decode_failure

example
    (input : List Byte) (hfull : decodeFully input = none) :
    decodeWithdrawal input = none := by
  wp_withdrawal_decode_auto

example
    (input : List Byte) (hoff : 0 < input.length)
    (hnot : ¬ BitVec.ult (walkInitPrefixWord input 0 hoff) (0xf8 : Word)) :
    decodeWithdrawal input = none := by
  wp_withdrawal_decode_auto

example (P : Assertion) :
    WP.Entails P P := by
  wp_withdrawal_decode_auto

example
    (input : List Byte) (item : RLPItem) (leftover : List Byte)
    (hdecode : decode input = some (item, leftover))
    (hleftover : leftover ≠ []) :
    decodeWithdrawal input = none := by
  withdrawal_decode_failure

example
    (input : List Byte) (items : List RLPItem)
    (hfull : decodeFully input = some (.list items))
    (hlen : items.length ≠ 4) :
    decodeWithdrawal input = none := by
  withdrawal_decode_failure

example
    (input d0 d1 d2 d3 : List Byte)
    (hfull : decodeFully input = some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]))
    (hbad : ¬
      (d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧
        d1.headD 1 ≠ 0 ∧ d1.length ≤ 8 ∧
        d2.length = 20 ∧
        d3.headD 1 ≠ 0 ∧ d3.length ≤ 8)) :
    decodeWithdrawal input = none := by
  withdrawal_decode_failure

example
    (p0 : Byte) (r0 d0 r1 : List Byte)
    (hdec0 : decode (p0 :: r0) = some (.bytes d0, r1)) :
    ∀ m, decodeAux (m + 1) (p0 :: r0) = some (.bytes d0, r1) := by
  wp_rlp_field_decode_aux hdec0

example
    (pfx p0 p1 p2 p3 : Byte) (r0 r1 r2 r3 r4 d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = (p0 :: r0).length)
    (hdec0 : decode (p0 :: r0) = some (.bytes d0, p1 :: r1))
    (hdec1 : decode (p1 :: r1) = some (.bytes d1, p2 :: r2))
    (hdec2 : decode (p2 :: r2) = some (.bytes d2, p3 :: r3))
    (hdec3 : decode (p3 :: r3) = some (.bytes d3, r4))
    (h_leftover : r4 ≠ [])
    (h_min : 2 ≤ (p0 :: r0).length) :
    decodeWithdrawal (pfx :: p0 :: r0) = none := by
  wp_withdrawal_decode_chain_auto h_class, h_len, hdec0, hdec1, hdec2, hdec3, h_leftover, h_min

example
    (pfx p0 p1 p2 p3 : Byte) (r0 r1 r2 r3 d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = (p0 :: r0).length)
    (hdec0 : decode (p0 :: r0) = some (.bytes d0, p1 :: r1))
    (hdec1 : decode (p1 :: r1) = some (.bytes d1, p2 :: r2))
    (hdec2 : decode (p2 :: r2) = some (.bytes d2, p3 :: r3))
    (hdec3 : decode (p3 :: r3) = some (.bytes d3, []))
    (h_end : ([] : List Byte) = [])
    (h_min : 2 ≤ (p0 :: r0).length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    decodeWithdrawal (pfx :: p0 :: r0) = some (fromFieldBytes d0 d1 d2 d3) := by
  wp_withdrawal_decode_chain_auto h_class, h_len, hdec0, hdec1, hdec2, hdec3, h_end, h_min,
    hc0, hl0, hc1, hl1, haddr, hc3, hl3

example
    (pfx p0 p1 p2 p3 : Byte) (r0 r1 r2 r3 d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = (p0 :: r0).length)
    (hdec0 : decode (p0 :: r0) = some (.bytes d0, p1 :: r1))
    (hdec1 : decode (p1 :: r1) = some (.bytes d1, p2 :: r2))
    (hdec2 : decode (p2 :: r2) = some (.bytes d2, p3 :: r3))
    (hdec3 : decode (p3 :: r3) = some (.bytes d3, []))
    (h_end : ([] : List Byte) = [])
    (h_min : 2 ≤ (p0 :: r0).length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    successFieldSpecsInput (pfx :: p0 :: r0) := by
  wp_withdrawal_decode_chain_auto h_class, h_len, hdec0, hdec1, hdec2, hdec3, h_end, h_min,
    hc0, hl0, hc1, hl1, haddr, hc3, hl3

example
    (pfx : Byte) (payload d0 d1 d2 d3 : List Byte)
    (off1 off2 off3 off4 : Nat)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (.bytes d0, payload.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (payload.drop off1) =
      some (.bytes d1, payload.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (payload.drop off2) =
      some (.bytes d2, payload.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (payload.drop off3) =
      some (.bytes d3, payload.drop off4))
    (h_leftover : payload.drop off4 ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none := by
  withdrawal_decode_failure h_class, h_len, h0, h1, h2, h3, h_leftover, h_min

example
    (pfx : Byte) (payload tail d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (h_payload : payload = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (h_tail : tail ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none := by
  withdrawal_decode_failure h_class, h_len, hl0, hl1, haddr, hl3, h_payload, h_tail, h_min

example
    (input : List Byte) (hfull : decodeFully input = none) :
    ¬ successFieldSpecsInput input := by
  withdrawal_schema_failure

example
    (input : List Byte) (items : List RLPItem)
    (hfull : decodeFully input = some (.list items))
    (hlen : items.length ≠ 4) :
    ¬ successFieldSpecsInput input := by
  withdrawal_schema_failure

example
    (pfx : Byte) (payload tail d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (h_payload : payload = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (h_tail : tail ≠ [])
    (h_min : 2 ≤ payload.length) :
    ¬ successFieldSpecsInput (pfx :: payload) := by
  withdrawal_schema_failure h_class, h_len, hl0, hl1, haddr, hl3, h_payload, h_tail, h_min

example
    (pfx : Byte) (payload tail d0 d1 d2 d3 : List Byte)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (h_payload : payload = schemaEncBytes (successFieldSpecs d0 d1 d2 d3) ++ tail)
    (h_tail : tail ≠ [])
    (h_min : 2 ≤ payload.length) :
    ¬ successFieldSpecsInput (pfx :: payload) := by
  wp_withdrawal_decode_auto h_class, h_len, hl0, hl1, haddr, hl3, h_payload, h_tail, h_min

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (specs : List FieldSpec)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_schema_size : schemaSize specs <= 1392)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base ((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) specs)) := by
  wp_withdrawal_decode_auto input

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (specs : List FieldSpec)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_schema_size : schemaSize specs <= 1392)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base (((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) specs)).union
      (failStatusReturnCode ((base + 24) + 28))) := by
  wp_withdrawal_decode_auto input


noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (specs : List FieldSpec)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_bound : input.length < 2 ^ 64)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code : (base + 24).toNat + 172 + 4 + schemaSize specs + 8 < 2 ^ 64) :
    WP.NBranch base (((prologueCode base).union
      (walkInitShortSuccessResolvedCode (base + 24) specs)).union
      (failStatusReturnCode ((base + 24) + 28))) := by
  wp_withdrawal_decode_auto

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte) (w : Withdrawal)
    (hdec : decodeWithdrawal input = some w)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
        m3 inputBase listLen t0Old t1Old input w hdec hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode.union
        (failStatusReturnCode ((base + 24) + 28))) := by
  wp_withdrawal_decode_auto input

noncomputable example
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (h_success : successFieldSpecsInput input)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : forall i, i < input.length -> isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : forall i, i < outputSize -> isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len : listLen = BitVec.ofNat 64 input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitShortSuccessSchemaInputPkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1
        m2 m3 inputBase listLen t0Old t1Old input h_success hsalign hover hwin hdalign hdov
        hdval h_len h_prologue_code h_code_max).successCode.union
        (failStatusReturnCode ((base + 24) + 28))) := by
  wp_withdrawal_decode_auto input

end WithdrawalDecode


end EvmAsm.Rv64.RLP
