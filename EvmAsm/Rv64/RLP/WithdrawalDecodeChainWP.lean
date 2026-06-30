/-
  EvmAsm.Rv64.RLP.WithdrawalDecodeChainWP

  Chain-shaped automation facade for generated withdrawal decode WP proofs.
  The field walker exposes a sequence of pure `decode` facts over successive
  payload remainders; this module bundles those facts once and projects the
  existing result-free schema-input WP packages from that bundle.
-/

import EvmAsm.Rv64.RLP.WithdrawalDecodeAutoWP

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace WithdrawalDecode

/-- Successful four-field short-list decode chain produced by a validating field
    walk.  The decoded field bytes are postcondition witnesses; the schema input
    predicate derived from this structure remains result-free. -/
structure SuccessDecodeChain (pfx : Byte) (payload : List Byte) where
  r1 : List Byte
  r2 : List Byte
  r3 : List Byte
  r4 : List Byte
  d0 : List Byte
  d1 : List Byte
  d2 : List Byte
  d3 : List Byte
  h_class : classifyPrefix pfx = .shortList
  h_len : rlpPrefixShortListPayloadLen pfx = payload.length
  hdec0 : decode payload = some (.bytes d0, r1)
  hdec1 : decode r1 = some (.bytes d1, r2)
  hdec2 : decode r2 = some (.bytes d2, r3)
  hdec3 : decode r3 = some (.bytes d3, r4)
  hend : r4 = []
  h_min : 2 ≤ payload.length
  hc0 : d0.headD 1 ≠ 0
  hl0 : d0.length ≤ 8
  hc1 : d1.headD 1 ≠ 0
  hl1 : d1.length ≤ 8
  haddr : d2.length = 20
  hc3 : d3.headD 1 ≠ 0
  hl3 : d3.length ≤ 8

namespace SuccessDecodeChain

/-- Build a success chain from the facts emitted by a generated field walk. -/
def ofLocalFacts {pfx : Byte} {payload r1 r2 r3 r4 d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hdec0 : decode payload = some (.bytes d0, r1))
    (hdec1 : decode r1 = some (.bytes d1, r2))
    (hdec2 : decode r2 = some (.bytes d2, r3))
    (hdec3 : decode r3 = some (.bytes d3, r4))
    (hend : r4 = [])
    (h_min : 2 ≤ payload.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    SuccessDecodeChain pfx payload where
  r1 := r1
  r2 := r2
  r3 := r3
  r4 := r4
  d0 := d0
  d1 := d1
  d2 := d2
  d3 := d3
  h_class := h_class
  h_len := h_len
  hdec0 := hdec0
  hdec1 := hdec1
  hdec2 := hdec2
  hdec3 := hdec3
  hend := hend
  h_min := h_min
  hc0 := hc0
  hl0 := hl0
  hc1 := hc1
  hl1 := hl1
  haddr := haddr
  hc3 := hc3
  hl3 := hl3

/-- Full RLP input represented by a short-list success chain. -/
def input {pfx : Byte} {payload : List Byte} (_chain : SuccessDecodeChain pfx payload) :
    List Byte :=
  pfx :: payload

/-- Withdrawal value characterized by the field bytes in a success chain. -/
def value {pfx : Byte} {payload : List Byte} (chain : SuccessDecodeChain pfx payload) :
    Withdrawal :=
  fromFieldBytes chain.d0 chain.d1 chain.d2 chain.d3

/-- First field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux0 {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) payload = some (.bytes chain.d0, chain.r1) :=
  decodeAux_bytes_all_fuel_of_decode_list payload chain.d0 chain.r1 chain.hdec0

/-- Second field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux1 {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) chain.r1 = some (.bytes chain.d1, chain.r2) :=
  decodeAux_bytes_all_fuel_of_decode_list chain.r1 chain.d1 chain.r2 chain.hdec1

/-- Third field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux2 {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) chain.r2 = some (.bytes chain.d2, chain.r3) :=
  decodeAux_bytes_all_fuel_of_decode_list chain.r2 chain.d2 chain.r3 chain.hdec2

/-- Fourth field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux3 {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) chain.r3 = some (.bytes chain.d3, chain.r4) :=
  decodeAux_bytes_all_fuel_of_decode_list chain.r3 chain.d3 chain.r4 chain.hdec3

/-- Result-free schema-success predicate derived from the decode chain. -/
theorem successFieldSpecsInput {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    successFieldSpecsInput chain.input :=
  successFieldSpecsInput_of_shortList_four_decode_chain chain.h_class chain.h_len
    chain.decodeAux0 chain.decodeAux1 chain.decodeAux2 chain.decodeAux3 chain.hend chain.h_min
    chain.hc0 chain.hl0 chain.hc1 chain.hl1 chain.haddr chain.hc3 chain.hl3

/-- Semantic success characterized by the chain's field bytes. -/
theorem decodeWithdrawal_eq_some {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    decodeWithdrawal chain.input = some chain.value :=
  decodeWithdrawal_shortList_four_of_decodeAux_chain_auto chain.h_class chain.h_len
    chain.decodeAux0 chain.decodeAux1 chain.decodeAux2 chain.decodeAux3 chain.hend chain.h_min
    chain.hc0 chain.hl0 chain.hc1 chain.hl1 chain.haddr chain.hc3 chain.hl3

/-- Result-free WP package projected from a success decode chain. -/
noncomputable def wpPackage {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    Sigma (fun w : Withdrawal => WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old
      s2Old outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old chain.input w) :=
  walkInitShortSuccessSchemaInputWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
    inputBase listLen t0Old t1Old chain.input chain.successFieldSpecsInput hsalign hover hwin
    hdalign hdov hdval h_len_word h_prologue_code h_code_max

/-- Decoded-success package carried by a success decode chain. -/
noncomputable def pkg {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WalkInitShortSuccessDecodedWP base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
      inputBase listLen t0Old t1Old chain.input
      (chain.wpPackage base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase
        listLen t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
        h_code_max).1 :=
  (chain.wpPackage base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
    t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
    h_code_max).2

/-- Success certificate projected from a success decode chain package. -/
noncomputable def successCert {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
        t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
        h_code_max).successCode
      (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
        t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
        h_code_max).successPost :=
  (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
    t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
    h_code_max).successCert

/-- Chain success certificate reduces to the static prologue precondition. -/
theorem successCert_pre {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (chain.successCert base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
      t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
      h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase
          chain.input) := by
  exact (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
    t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
    h_code_max).successCert_pre

/-- Reason-erased failure branch over the same generated code as the chain
    success certificate. -/
noncomputable def failureLongNBranch {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
        t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
        h_code_max).successCode.union (failStatusReturnCode ((base + 24) + 28))) :=
  (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
    t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
    h_code_max).failureLongNBranch hsalign hover hwin h_len_word h_prologue_code h_code_max

/-- Chain failure branch reduces to the same static prologue precondition as the
    success certificate. -/
theorem failureLongNBranch_pre {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    (chain.failureLongNBranch base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase
      listLen t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
      h_code_max).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase
          chain.input) := by
  exact (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
    t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
    h_code_max).failureLongNBranch_pre hsalign hover hwin h_len_word h_prologue_code h_code_max

attribute [rv64_wp]
  successCert_pre
  failureLongNBranch_pre

attribute [rv64_wp_cert]
  successCert
  failureLongNBranch

end SuccessDecodeChain

/-- Exact-arity failure chain produced by a validating field walk after four
    successful byte-field decodes but with a nonempty payload remainder. -/
structure LeftoverDecodeChain (pfx : Byte) (payload : List Byte) where
  r1 : List Byte
  r2 : List Byte
  r3 : List Byte
  r4 : List Byte
  d0 : List Byte
  d1 : List Byte
  d2 : List Byte
  d3 : List Byte
  h_class : classifyPrefix pfx = .shortList
  h_len : rlpPrefixShortListPayloadLen pfx = payload.length
  hdec0 : decode payload = some (.bytes d0, r1)
  hdec1 : decode r1 = some (.bytes d1, r2)
  hdec2 : decode r2 = some (.bytes d2, r3)
  hdec3 : decode r3 = some (.bytes d3, r4)
  h_leftover : r4 ≠ []
  h_min : 2 ≤ payload.length

namespace LeftoverDecodeChain

/-- Build an exact-arity leftover chain from the facts emitted by a generated
    field walk. -/
def ofLocalFacts {pfx : Byte} {payload r1 r2 r3 r4 d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hdec0 : decode payload = some (.bytes d0, r1))
    (hdec1 : decode r1 = some (.bytes d1, r2))
    (hdec2 : decode r2 = some (.bytes d2, r3))
    (hdec3 : decode r3 = some (.bytes d3, r4))
    (h_leftover : r4 ≠ [])
    (h_min : 2 ≤ payload.length) :
    LeftoverDecodeChain pfx payload where
  r1 := r1
  r2 := r2
  r3 := r3
  r4 := r4
  d0 := d0
  d1 := d1
  d2 := d2
  d3 := d3
  h_class := h_class
  h_len := h_len
  hdec0 := hdec0
  hdec1 := hdec1
  hdec2 := hdec2
  hdec3 := hdec3
  h_leftover := h_leftover
  h_min := h_min

/-- Full RLP input represented by an exact-arity failure chain. -/
def input {pfx : Byte} {payload : List Byte} (_chain : LeftoverDecodeChain pfx payload) :
    List Byte :=
  pfx :: payload

/-- First field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux0 {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) payload = some (.bytes chain.d0, chain.r1) :=
  decodeAux_bytes_all_fuel_of_decode_list payload chain.d0 chain.r1 chain.hdec0

/-- Second field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux1 {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) chain.r1 = some (.bytes chain.d1, chain.r2) :=
  decodeAux_bytes_all_fuel_of_decode_list chain.r1 chain.d1 chain.r2 chain.hdec1

/-- Third field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux2 {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) chain.r2 = some (.bytes chain.d2, chain.r3) :=
  decodeAux_bytes_all_fuel_of_decode_list chain.r2 chain.d2 chain.r3 chain.hdec2

/-- Fourth field decode as a fuel-polymorphic `decodeAux` continuation. -/
theorem decodeAux3 {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    ∀ m, decodeAux (m + 1) chain.r3 = some (.bytes chain.d3, chain.r4) :=
  decodeAux_bytes_all_fuel_of_decode_list chain.r3 chain.d3 chain.r4 chain.hdec3

/-- Exact-arity leftover chains are reason-erased withdrawal failures. -/
theorem decodeWithdrawal_eq_none {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    decodeWithdrawal chain.input = none :=
  decodeWithdrawal_none_of_shortList_four_leftover_chain_auto chain.h_class chain.h_len
    chain.decodeAux0 chain.decodeAux1 chain.decodeAux2 chain.decodeAux3 chain.h_leftover
    chain.h_min

/-- Exact-arity leftover chains cannot satisfy the result-free success schema. -/
theorem not_successFieldSpecsInput {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    ¬ successFieldSpecsInput chain.input :=
  (decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput chain.input).1
    chain.decodeWithdrawal_eq_none

end LeftoverDecodeChain

/-- Synthesize a successful withdrawal decode chain from the generated local
    `decode`, classifier, length, and field-guard facts. -/
macro "withdrawal_success_decode_chain" : tactic => do
  let hClass := Lean.mkIdent `h_class
  let hLen := Lean.mkIdent `h_len
  let hDec0 := Lean.mkIdent `hdec0
  let hDec1 := Lean.mkIdent `hdec1
  let hDec2 := Lean.mkIdent `hdec2
  let hDec3 := Lean.mkIdent `hdec3
  let hEnd := Lean.mkIdent `hend
  let hMin := Lean.mkIdent `h_min
  let hC0 := Lean.mkIdent `hc0
  let hL0 := Lean.mkIdent `hl0
  let hC1 := Lean.mkIdent `hc1
  let hL1 := Lean.mkIdent `hl1
  let hAddr := Lean.mkIdent `haddr
  let hC3 := Lean.mkIdent `hc3
  let hL3 := Lean.mkIdent `hl3
  `(tactic| exact SuccessDecodeChain.ofLocalFacts $hClass:ident $hLen:ident $hDec0:ident
    $hDec1:ident $hDec2:ident $hDec3:ident $hEnd:ident $hMin:ident $hC0:ident
    $hL0:ident $hC1:ident $hL1:ident $hAddr:ident $hC3:ident $hL3:ident)

/-- Synthesize an exact-arity leftover failure chain from generated local
    `decode`, classifier, length, and leftover facts. -/
macro "withdrawal_leftover_decode_chain" : tactic => do
  let hClass := Lean.mkIdent `h_class
  let hLen := Lean.mkIdent `h_len
  let hDec0 := Lean.mkIdent `hdec0
  let hDec1 := Lean.mkIdent `hdec1
  let hDec2 := Lean.mkIdent `hdec2
  let hDec3 := Lean.mkIdent `hdec3
  let hLeftover := Lean.mkIdent `h_leftover
  let hMin := Lean.mkIdent `h_min
  `(tactic| exact LeftoverDecodeChain.ofLocalFacts $hClass:ident $hLen:ident $hDec0:ident
    $hDec1:ident $hDec2:ident $hDec3:ident $hLeftover:ident $hMin:ident)

/-- Context-driven WP automation for generated successful field-walk proofs.
    It derives semantic success or the result-free schema fact from the standard
    local names, then falls through to the WP certificate/link/dead-exit
    databases. Use the argument-taking `wp_withdrawal_decode_chain_auto` when a
    generated proof uses nonstandard names. -/
macro "wp_withdrawal_decode_success_chain" : tactic => do
  let hClass := Lean.mkIdent `h_class
  let hLen := Lean.mkIdent `h_len
  let hDec0 := Lean.mkIdent `hdec0
  let hDec1 := Lean.mkIdent `hdec1
  let hDec2 := Lean.mkIdent `hdec2
  let hDec3 := Lean.mkIdent `hdec3
  let hEnd := Lean.mkIdent `hend
  let hMin := Lean.mkIdent `h_min
  let hC0 := Lean.mkIdent `hc0
  let hL0 := Lean.mkIdent `hl0
  let hC1 := Lean.mkIdent `hc1
  let hL1 := Lean.mkIdent `hl1
  let hAddr := Lean.mkIdent `haddr
  let hC3 := Lean.mkIdent `hc3
  let hL3 := Lean.mkIdent `hl3
  `(tactic| first
    | exact (SuccessDecodeChain.ofLocalFacts $hClass:ident $hLen:ident $hDec0:ident
        $hDec1:ident $hDec2:ident $hDec3:ident $hEnd:ident $hMin:ident $hC0:ident
        $hL0:ident $hC1:ident $hL1:ident $hAddr:ident $hC3:ident
        $hL3:ident).successFieldSpecsInput
    | exact (SuccessDecodeChain.ofLocalFacts $hClass:ident $hLen:ident $hDec0:ident
        $hDec1:ident $hDec2:ident $hDec3:ident $hEnd:ident $hMin:ident $hC0:ident
        $hL0:ident $hC1:ident $hL1:ident $hAddr:ident $hC3:ident
        $hL3:ident).decodeWithdrawal_eq_some
    | wp_rv64_cert
    | wp_withdrawal_decode_auto)

/-- Context-driven WP automation for generated exact-arity leftover field-walk
    proofs. It derives the reason-erased semantic/schema failure facts from the
    standard local names, then falls through to the WP databases. -/
macro "wp_withdrawal_decode_leftover_chain" : tactic => do
  let hClass := Lean.mkIdent `h_class
  let hLen := Lean.mkIdent `h_len
  let hDec0 := Lean.mkIdent `hdec0
  let hDec1 := Lean.mkIdent `hdec1
  let hDec2 := Lean.mkIdent `hdec2
  let hDec3 := Lean.mkIdent `hdec3
  let hLeftover := Lean.mkIdent `h_leftover
  let hMin := Lean.mkIdent `h_min
  `(tactic| first
    | exact (LeftoverDecodeChain.ofLocalFacts $hClass:ident $hLen:ident $hDec0:ident
        $hDec1:ident $hDec2:ident $hDec3:ident $hLeftover:ident
        $hMin:ident).not_successFieldSpecsInput
    | exact (LeftoverDecodeChain.ofLocalFacts $hClass:ident $hLen:ident $hDec0:ident
        $hDec1:ident $hDec2:ident $hDec3:ident $hLeftover:ident
        $hMin:ident).decodeWithdrawal_eq_none
    | wp_rv64_cert
    | wp_withdrawal_decode_auto)

example
    {pfx : Byte} {payload r1 r2 r3 r4 d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hdec0 : decode payload = some (.bytes d0, r1))
    (hdec1 : decode r1 = some (.bytes d1, r2))
    (hdec2 : decode r2 = some (.bytes d2, r3))
    (hdec3 : decode r3 = some (.bytes d3, r4))
    (hend : r4 = [])
    (h_min : 2 ≤ payload.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    successFieldSpecsInput (pfx :: payload) := by
  wp_withdrawal_decode_success_chain

example
    {pfx : Byte} {payload r1 r2 r3 r4 d0 d1 d2 d3 : List Byte}
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (hdec0 : decode payload = some (.bytes d0, r1))
    (hdec1 : decode r1 = some (.bytes d1, r2))
    (hdec2 : decode r2 = some (.bytes d2, r3))
    (hdec3 : decode r3 = some (.bytes d3, r4))
    (h_leftover : r4 ≠ [])
    (h_min : 2 ≤ payload.length) :
    decodeWithdrawal (pfx :: payload) = none := by
  wp_withdrawal_decode_leftover_chain

noncomputable example
    {pfx : Byte} {payload : List Byte} (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
        t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
        h_code_max).successCode
      (chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
        t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
        h_code_max).successPost := by
  wp_rv64_cert

noncomputable example
    {pfx : Byte} {payload : List Byte} (chain : SuccessDecodeChain pfx payload)
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + chain.input.length < 2 ^ 64)
    (hwin : ∀ i, i < chain.input.length →
      isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (h_len_word : listLen = BitVec.ofNat 64 chain.input.length)
    (h_prologue_code : base.toNat + 24 < 2 ^ 64)
    (h_code_max : (base + 24).toNat + 172 + 4 + 1392 + 8 < 2 ^ 64) :
    WP.NBranch base
      ((chain.pkg base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase listLen
        t0Old t1Old hsalign hover hwin hdalign hdov hdval h_len_word h_prologue_code
        h_code_max).successCode.union (failStatusReturnCode ((base + 24) + 28))) := by
  wp_rv64_cert

end WithdrawalDecode

end EvmAsm.Rv64.RLP
