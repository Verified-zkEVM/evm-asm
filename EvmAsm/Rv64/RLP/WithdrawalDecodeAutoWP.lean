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

attribute [rv64_wp]
  walkInitShortSuccessDecodedCert_pre
  walkInitShortSuccessDecodedFailureNBranch_pre

attribute [rv64_wp_cert]
  walkInitShortSuccessDecodedCert
  walkInitShortSuccessDecodedFailureNBranch

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


attribute [rv64_wp]
  walkInitShortSuccessSchemaInputCert_pre
  walkInitShortSuccessSchemaInputFailureNBranch_pre

attribute [rv64_wp_cert]
  walkInitShortSuccessSchemaInputCert
  walkInitShortSuccessSchemaInputFailureNBranch

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

end WithdrawalDecode


end EvmAsm.Rv64.RLP
