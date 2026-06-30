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

/-- Success chains choose the success side of a result-free schema split. -/
theorem successFieldSpecsInput_or_not {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    WithdrawalDecode.successFieldSpecsInput chain.input ∨
      ¬ WithdrawalDecode.successFieldSpecsInput chain.input :=
  Or.inl chain.successFieldSpecsInput

/-- Success chains choose the decoded-success side of a reason-erased decode split. -/
theorem decodeWithdrawal_some_or_none {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    (∃ w : Withdrawal, decodeWithdrawal chain.input = some w) ∨
      decodeWithdrawal chain.input = none :=
  Or.inl ⟨chain.value, chain.decodeWithdrawal_eq_some⟩

/-- Success chains can also feed joins that only distinguish schema success from
    semantic failure. -/
theorem successFieldSpecsInput_or_decodeWithdrawal_none {pfx : Byte} {payload : List Byte}
    (chain : SuccessDecodeChain pfx payload) :
    WithdrawalDecode.successFieldSpecsInput chain.input ∨ decodeWithdrawal chain.input = none :=
  Or.inl chain.successFieldSpecsInput

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

/-- Exact-arity leftover chains choose the failure side of a result-free schema split. -/
theorem successFieldSpecsInput_or_not {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    successFieldSpecsInput chain.input ∨ ¬ successFieldSpecsInput chain.input :=
  Or.inr chain.not_successFieldSpecsInput

/-- Exact-arity leftover chains choose the reason-erased failure side of a decode split. -/
theorem decodeWithdrawal_some_or_none {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    (∃ w : Withdrawal, decodeWithdrawal chain.input = some w) ∨
      decodeWithdrawal chain.input = none :=
  Or.inr chain.decodeWithdrawal_eq_none

/-- Exact-arity leftover chains can feed joins that only distinguish schema
    success from semantic failure. -/
theorem successFieldSpecsInput_or_decodeWithdrawal_none {pfx : Byte} {payload : List Byte}
    (chain : LeftoverDecodeChain pfx payload) :
    successFieldSpecsInput chain.input ∨ decodeWithdrawal chain.input = none :=
  Or.inr chain.decodeWithdrawal_eq_none

end LeftoverDecodeChain

/-- Branch-join outcome for generated exact-arity withdrawal walks.  The failure
    case deliberately carries no precise failure reason: downstream WP code only
    needs to distinguish schema success from reason-erased semantic failure. -/
inductive DecodeChainOutcome (pfx : Byte) (payload : List Byte) where
  | success (chain : SuccessDecodeChain pfx payload)
  | leftover (chain : LeftoverDecodeChain pfx payload)

namespace DecodeChainOutcome

/-- Full RLP input represented by a chain outcome. -/
def input {pfx : Byte} {payload : List Byte} (_outcome : DecodeChainOutcome pfx payload) :
    List Byte :=
  pfx :: payload

/-- Project the result-free schema split needed by control-flow joins. -/
theorem successFieldSpecsInput_or_not {pfx : Byte} {payload : List Byte}
    (outcome : DecodeChainOutcome pfx payload) :
    successFieldSpecsInput outcome.input ∨ ¬ successFieldSpecsInput outcome.input := by
  cases outcome with
  | success chain =>
      simpa [input, SuccessDecodeChain.input] using chain.successFieldSpecsInput_or_not
  | leftover chain =>
      simpa [input, LeftoverDecodeChain.input] using chain.successFieldSpecsInput_or_not

/-- Project the reason-erased semantic decode split needed by ABI-level joins. -/
theorem decodeWithdrawal_some_or_none {pfx : Byte} {payload : List Byte}
    (outcome : DecodeChainOutcome pfx payload) :
    (∃ w : Withdrawal, decodeWithdrawal outcome.input = some w) ∨
      decodeWithdrawal outcome.input = none := by
  cases outcome with
  | success chain =>
      simpa [input, SuccessDecodeChain.input] using chain.decodeWithdrawal_some_or_none
  | leftover chain =>
      simpa [input, LeftoverDecodeChain.input] using chain.decodeWithdrawal_some_or_none

/-- Project the join fact that keeps schema success result-free while erasing
    the precise failure reason. -/
theorem successFieldSpecsInput_or_decodeWithdrawal_none {pfx : Byte} {payload : List Byte}
    (outcome : DecodeChainOutcome pfx payload) :
    successFieldSpecsInput outcome.input ∨ decodeWithdrawal outcome.input = none := by
  cases outcome with
  | success chain =>
      simpa [input, SuccessDecodeChain.input] using
        chain.successFieldSpecsInput_or_decodeWithdrawal_none
  | leftover chain =>
      simpa [input, LeftoverDecodeChain.input] using
        chain.successFieldSpecsInput_or_decodeWithdrawal_none

end DecodeChainOutcome

/-- Synthesize a successful withdrawal decode chain from the generated local
    `decode`, classifier, length, and field-guard facts. -/
macro "withdrawal_success_decode_chain" : tactic => do
  let h_class_stx := Lean.mkIdent `h_class
  let h_len_stx := Lean.mkIdent `h_len
  let h_dec0_stx := Lean.mkIdent `hdec0
  let h_dec1_stx := Lean.mkIdent `hdec1
  let h_dec2_stx := Lean.mkIdent `hdec2
  let h_dec3_stx := Lean.mkIdent `hdec3
  let h_end_stx := Lean.mkIdent `hend
  let h_min_stx := Lean.mkIdent `h_min
  let h_c0_stx := Lean.mkIdent `hc0
  let h_l0_stx := Lean.mkIdent `hl0
  let h_c1_stx := Lean.mkIdent `hc1
  let h_l1_stx := Lean.mkIdent `hl1
  let h_addr_stx := Lean.mkIdent `haddr
  let h_c3_stx := Lean.mkIdent `hc3
  let h_l3_stx := Lean.mkIdent `hl3
  `(tactic| exact SuccessDecodeChain.ofLocalFacts $h_class_stx:ident $h_len_stx:ident $h_dec0_stx:ident
    $h_dec1_stx:ident $h_dec2_stx:ident $h_dec3_stx:ident $h_end_stx:ident $h_min_stx:ident $h_c0_stx:ident
    $h_l0_stx:ident $h_c1_stx:ident $h_l1_stx:ident $h_addr_stx:ident $h_c3_stx:ident $h_l3_stx:ident)

/-- Synthesize an exact-arity leftover failure chain from generated local
    `decode`, classifier, length, and leftover facts. -/
macro "withdrawal_leftover_decode_chain" : tactic => do
  let h_class_stx := Lean.mkIdent `h_class
  let h_len_stx := Lean.mkIdent `h_len
  let h_dec0_stx := Lean.mkIdent `hdec0
  let h_dec1_stx := Lean.mkIdent `hdec1
  let h_dec2_stx := Lean.mkIdent `hdec2
  let h_dec3_stx := Lean.mkIdent `hdec3
  let h_leftover_stx := Lean.mkIdent `h_leftover
  let h_min_stx := Lean.mkIdent `h_min
  `(tactic| exact LeftoverDecodeChain.ofLocalFacts $h_class_stx:ident $h_len_stx:ident $h_dec0_stx:ident
    $h_dec1_stx:ident $h_dec2_stx:ident $h_dec3_stx:ident $h_leftover_stx:ident $h_min_stx:ident)

/-- Synthesize a success outcome from the generated local names. -/
macro "withdrawal_success_decode_outcome" : tactic =>
  `(tactic| exact DecodeChainOutcome.success (by withdrawal_success_decode_chain))

/-- Synthesize an exact-arity leftover outcome from the generated local names. -/
macro "withdrawal_leftover_decode_outcome" : tactic =>
  `(tactic| exact DecodeChainOutcome.leftover (by withdrawal_leftover_decode_chain))

/-- Synthesize whichever exact-arity withdrawal outcome is available in the
    current generated branch context. -/
macro "withdrawal_decode_outcome" : tactic =>
  `(tactic| first
    | withdrawal_success_decode_outcome
    | withdrawal_leftover_decode_outcome)

/-- Explicit success-outcome constructor for generated proofs with nonstandard
    local names. -/
macro "withdrawal_success_decode_outcome " hclass:term ", " hlen:term ", " hdec0:term ", "
    hdec1:term ", " hdec2:term ", " hdec3:term ", " hend:term ", " hmin:term ", "
    hc0:term ", " hl0:term ", " hc1:term ", " hl1:term ", " haddr:term ", "
    hc3:term ", " hl3:term : tactic =>
  `(tactic| exact DecodeChainOutcome.success (SuccessDecodeChain.ofLocalFacts
    $hclass $hlen $hdec0 $hdec1 $hdec2 $hdec3 $hend $hmin $hc0 $hl0 $hc1 $hl1
    $haddr $hc3 $hl3))

/-- Explicit leftover-outcome constructor for generated proofs with nonstandard
    local names. -/
macro "withdrawal_leftover_decode_outcome " hclass:term ", " hlen:term ", " hdec0:term ", "
    hdec1:term ", " hdec2:term ", " hdec3:term ", " hleftover:term ", "
    hmin:term : tactic =>
  `(tactic| exact DecodeChainOutcome.leftover (LeftoverDecodeChain.ofLocalFacts
    $hclass $hlen $hdec0 $hdec1 $hdec2 $hdec3 $hleftover $hmin))

/-- Context-driven WP automation for generated successful field-walk proofs.
    It derives semantic success or the result-free schema fact from the standard
    local names, then falls through to the WP certificate/link/dead-exit
    databases. Use the argument-taking `wp_withdrawal_decode_chain_auto` when a
    generated proof uses nonstandard names. -/
macro "wp_withdrawal_decode_success_chain" : tactic => do
  let h_class_stx := Lean.mkIdent `h_class
  let h_len_stx := Lean.mkIdent `h_len
  let h_dec0_stx := Lean.mkIdent `hdec0
  let h_dec1_stx := Lean.mkIdent `hdec1
  let h_dec2_stx := Lean.mkIdent `hdec2
  let h_dec3_stx := Lean.mkIdent `hdec3
  let h_end_stx := Lean.mkIdent `hend
  let h_min_stx := Lean.mkIdent `h_min
  let h_c0_stx := Lean.mkIdent `hc0
  let h_l0_stx := Lean.mkIdent `hl0
  let h_c1_stx := Lean.mkIdent `hc1
  let h_l1_stx := Lean.mkIdent `hl1
  let h_addr_stx := Lean.mkIdent `haddr
  let h_c3_stx := Lean.mkIdent `hc3
  let h_l3_stx := Lean.mkIdent `hl3
  `(tactic| first
    | exact (SuccessDecodeChain.ofLocalFacts $h_class_stx:ident $h_len_stx:ident $h_dec0_stx:ident
        $h_dec1_stx:ident $h_dec2_stx:ident $h_dec3_stx:ident $h_end_stx:ident $h_min_stx:ident $h_c0_stx:ident
        $h_l0_stx:ident $h_c1_stx:ident $h_l1_stx:ident $h_addr_stx:ident $h_c3_stx:ident
        $h_l3_stx:ident).successFieldSpecsInput
    | exact (SuccessDecodeChain.ofLocalFacts $h_class_stx:ident $h_len_stx:ident $h_dec0_stx:ident
        $h_dec1_stx:ident $h_dec2_stx:ident $h_dec3_stx:ident $h_end_stx:ident $h_min_stx:ident $h_c0_stx:ident
        $h_l0_stx:ident $h_c1_stx:ident $h_l1_stx:ident $h_addr_stx:ident $h_c3_stx:ident
        $h_l3_stx:ident).decodeWithdrawal_eq_some
    | wp_rv64_cert
    | wp_withdrawal_decode_auto)

/-- Context-driven WP automation for generated exact-arity leftover field-walk
    proofs. It derives the reason-erased semantic/schema failure facts from the
    standard local names, then falls through to the WP databases. -/
macro "wp_withdrawal_decode_leftover_chain" : tactic => do
  let h_class_stx := Lean.mkIdent `h_class
  let h_len_stx := Lean.mkIdent `h_len
  let h_dec0_stx := Lean.mkIdent `hdec0
  let h_dec1_stx := Lean.mkIdent `hdec1
  let h_dec2_stx := Lean.mkIdent `hdec2
  let h_dec3_stx := Lean.mkIdent `hdec3
  let h_leftover_stx := Lean.mkIdent `h_leftover
  let h_min_stx := Lean.mkIdent `h_min
  `(tactic| first
    | exact (LeftoverDecodeChain.ofLocalFacts $h_class_stx:ident $h_len_stx:ident $h_dec0_stx:ident
        $h_dec1_stx:ident $h_dec2_stx:ident $h_dec3_stx:ident $h_leftover_stx:ident
        $h_min_stx:ident).not_successFieldSpecsInput
    | exact (LeftoverDecodeChain.ofLocalFacts $h_class_stx:ident $h_len_stx:ident $h_dec0_stx:ident
        $h_dec1_stx:ident $h_dec2_stx:ident $h_dec3_stx:ident $h_leftover_stx:ident
        $h_min_stx:ident).decodeWithdrawal_eq_none
    | wp_rv64_cert
    | wp_withdrawal_decode_auto)

/-- Chain-object WP automation.  Generated proofs that already bundled the field
    walk into a `SuccessDecodeChain` or `LeftoverDecodeChain` can pass the bundle
    once; the tactic projects the semantic/schema fact or delegates to the WP
    certificate database. -/
macro "wp_withdrawal_decode_chain " chain:term : tactic =>
  `(tactic| first
    | exact ($chain).successFieldSpecsInput
    | exact ($chain).decodeWithdrawal_eq_some
    | exact ($chain).not_successFieldSpecsInput
    | exact ($chain).decodeWithdrawal_eq_none
    | exact ($chain).successFieldSpecsInput_or_not
    | exact ($chain).decodeWithdrawal_some_or_none
    | exact ($chain).successFieldSpecsInput_or_decodeWithdrawal_none
    | left; exact ($chain).successFieldSpecsInput
    | left; exact ⟨($chain).value, ($chain).decodeWithdrawal_eq_some⟩
    | right; exact ($chain).not_successFieldSpecsInput
    | right; exact ($chain).decodeWithdrawal_eq_none
    | wp_rv64_cert
    | wp_withdrawal_decode_auto)

open Lean Meta Elab Tactic

private def getNatLitVal? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
      if e.isAppOfArity ``OfNat.ofNat 3 then
        match e.getAppArgs[1]! with
        | .lit (.natVal n) => some n
        | _ => none
      else
        none

private def sameExpr (a b : Expr) : TacticM Bool :=
  withoutModifyingState (isDefEq a b)

private def eqSides? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Eq 3 then
    let args := e.getAppArgs
    some (args[1]!, args[2]!)
  else
    none

private def isConst (e : Expr) (name : Name) : Bool :=
  match e.getAppFn with
  | .const n _ => n == name
  | _ => false

private def listLengthArg? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``List.length 2 then
    some e.getAppArgs[1]!
  else
    none

private def listNil? (e : Expr) : Bool :=
  e.isAppOfArity ``List.nil 1

private structure NamedClassFact where
  name : Name
  pfx : Expr

private structure NamedLenFact where
  name : Name
  pfx : Expr
  payload : Expr

private structure NamedDecodeFact where
  name : Name
  input : Expr
  data : Expr
  rest : Expr

private structure NamedEndFact where
  name : Name
  rest : Expr

private structure NamedMinFact where
  name : Name
  payload : Expr

private structure NamedHeadNeZeroFact where
  name : Name
  data : Expr

private structure NamedLenLeFact where
  name : Name
  data : Expr
  bound : Nat

private structure NamedLenEqFact where
  name : Name
  data : Expr
  value : Nat

private structure WalkFactDb where
  classes : Array NamedClassFact := #[]
  lens : Array NamedLenFact := #[]
  decodes : Array NamedDecodeFact := #[]
  ends : Array NamedEndFact := #[]
  leftovers : Array NamedEndFact := #[]
  mins : Array NamedMinFact := #[]
  headNeZeros : Array NamedHeadNeZeroFact := #[]
  lenLes : Array NamedLenLeFact := #[]
  lenEqs : Array NamedLenEqFact := #[]

private def parseClassFact? (name : Name) (type : Expr) : Option NamedClassFact := do
  let (lhs, rhs) ← eqSides? type
  guard (lhs.isAppOfArity ``EvmAsm.EL.RLP.classifyPrefix 1)
  guard (isConst rhs ``EvmAsm.EL.RLP.PrefixClass.shortList)
  some { name := name, pfx := lhs.getAppArgs[0]! }

private def parseLenFact? (name : Name) (type : Expr) : Option NamedLenFact := do
  let (lhs, rhs) ← eqSides? type
  guard (lhs.isAppOfArity ``EvmAsm.EL.RLP.rlpPrefixShortListPayloadLen 1)
  let payload ← listLengthArg? rhs
  some { name := name, pfx := lhs.getAppArgs[0]!, payload := payload }

private def parseDecodeFact? (name : Name) (type : Expr) : Option NamedDecodeFact := do
  let (lhs, rhs) ← eqSides? type
  guard (lhs.isAppOfArity ``EvmAsm.EL.RLP.decode 1)
  guard (rhs.isAppOfArity ``Option.some 2)
  let pair := rhs.getAppArgs[1]!
  guard (pair.isAppOfArity ``Prod.mk 4)
  let item := pair.getAppArgs[2]!
  guard (item.isAppOfArity ``EvmAsm.EL.RLP.RLPItem.bytes 1)
  some {
    name := name
    input := lhs.getAppArgs[0]!
    data := item.getAppArgs[0]!
    rest := pair.getAppArgs[3]!
  }

private def parseEndFact? (name : Name) (type : Expr) : Option NamedEndFact := do
  let (lhs, rhs) ← eqSides? type
  guard (listNil? rhs)
  some { name := name, rest := lhs }

private def parseLeftoverFact? (name : Name) (type : Expr) : Option NamedEndFact := do
  guard (type.isAppOfArity ``Ne 3)
  let args := type.getAppArgs
  guard (listNil? args[2]!)
  some { name := name, rest := args[1]! }

private def parseMinFact? (name : Name) (type : Expr) : Option NamedMinFact := do
  guard (type.isAppOfArity ``LE.le 4)
  let args := type.getAppArgs
  guard (getNatLitVal? args[2]! == some 2)
  let payload ← listLengthArg? args[3]!
  some { name := name, payload := payload }

private def parseHeadNeZeroFact? (name : Name) (type : Expr) : Option NamedHeadNeZeroFact := do
  guard (type.isAppOfArity ``Ne 3)
  let args := type.getAppArgs
  guard (args[1]!.isAppOfArity ``List.headD 3)
  guard (getNatLitVal? args[1]!.getAppArgs[2]! == some 1)
  guard (getNatLitVal? args[2]! == some 0)
  some { name := name, data := args[1]!.getAppArgs[1]! }

private def parseLenLeFact? (name : Name) (type : Expr) : Option NamedLenLeFact := do
  guard (type.isAppOfArity ``LE.le 4)
  let args := type.getAppArgs
  let data ← listLengthArg? args[2]!
  let bound ← getNatLitVal? args[3]!
  some { name := name, data := data, bound := bound }

private def parseLenEqFact? (name : Name) (type : Expr) : Option NamedLenEqFact := do
  let (lhs, rhs) ← eqSides? type
  let data ← listLengthArg? lhs
  let value ← getNatLitVal? rhs
  some { name := name, data := data, value := value }

private def collectWalkFactDb : TacticM WalkFactDb := do
  let mut db : WalkFactDb := {}
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail then
      continue
    let type ← instantiateMVars localDecl.type
    let name := localDecl.userName
    if let some fact := parseClassFact? name type then
      db := { db with classes := db.classes.push fact }
    if let some fact := parseLenFact? name type then
      db := { db with lens := db.lens.push fact }
    if let some fact := parseDecodeFact? name type then
      db := { db with decodes := db.decodes.push fact }
    if let some fact := parseEndFact? name type then
      db := { db with ends := db.ends.push fact }
    if let some fact := parseLeftoverFact? name type then
      db := { db with leftovers := db.leftovers.push fact }
    if let some fact := parseMinFact? name type then
      db := { db with mins := db.mins.push fact }
    if let some fact := parseHeadNeZeroFact? name type then
      db := { db with headNeZeros := db.headNeZeros.push fact }
    if let some fact := parseLenLeFact? name type then
      db := { db with lenLes := db.lenLes.push fact }
    if let some fact := parseLenEqFact? name type then
      db := { db with lenEqs := db.lenEqs.push fact }
  return db

private def findClassFact? (db : WalkFactDb) (pfx : Expr) : TacticM (Option Name) := do
  for fact in db.classes do
    if ← sameExpr fact.pfx pfx then
      return some fact.name
  return none

private def findDecodeFrom? (db : WalkFactDb) (input : Expr) :
    TacticM (Array NamedDecodeFact) := do
  let mut out := #[]
  for fact in db.decodes do
    if ← sameExpr fact.input input then
      out := out.push fact
  return out

private def findEndFact? (facts : Array NamedEndFact) (rest : Expr) :
    TacticM (Option Name) := do
  for fact in facts do
    if ← sameExpr fact.rest rest then
      return some fact.name
  return none

private def findMinFact? (db : WalkFactDb) (payload : Expr) : TacticM (Option Name) := do
  for fact in db.mins do
    if ← sameExpr fact.payload payload then
      return some fact.name
  return none

private def findHeadNeZeroFact? (db : WalkFactDb) (data : Expr) :
    TacticM (Option Name) := do
  for fact in db.headNeZeros do
    if ← sameExpr fact.data data then
      return some fact.name
  return none

private def findLenLeFact? (db : WalkFactDb) (data : Expr) (bound : Nat) :
    TacticM (Option Name) := do
  for fact in db.lenLes do
    if fact.bound == bound then
      if ← sameExpr fact.data data then
        return some fact.name
  return none

private def findLenEqFact? (db : WalkFactDb) (data : Expr) (value : Nat) :
    TacticM (Option Name) := do
  for fact in db.lenEqs do
    if fact.value == value then
      if ← sameExpr fact.data data then
        return some fact.name
  return none

private def factIdent (name : Name) : TSyntax `term :=
  ⟨mkIdent name⟩

private def tryCloseWithSuccessWalk (className lenName dec0Name dec1Name dec2Name dec3Name endName minName
    canon0Name len0Name canon1Name len1Name addrName canon3Name len3Name : Name) : TacticM Unit := do
  let className := factIdent className
  let lenName := factIdent lenName
  let dec0Name := factIdent dec0Name
  let dec1Name := factIdent dec1Name
  let dec2Name := factIdent dec2Name
  let dec3Name := factIdent dec3Name
  let endName := factIdent endName
  let minName := factIdent minName
  let canon0Name := factIdent canon0Name
  let len0Name := factIdent len0Name
  let canon1Name := factIdent canon1Name
  let len1Name := factIdent len1Name
  let addrName := factIdent addrName
  let canon3Name := factIdent canon3Name
  let len3Name := factIdent len3Name
  evalTactic (← `(tactic|
    wp_withdrawal_decode_chain (SuccessDecodeChain.ofLocalFacts
      $className $lenName $dec0Name $dec1Name $dec2Name $dec3Name $endName $minName $canon0Name $len0Name $canon1Name
      $len1Name $addrName $canon3Name $len3Name); done))

private def tryCloseWithLeftoverWalk (className lenName dec0Name dec1Name dec2Name dec3Name leftoverName
    minName : Name) : TacticM Unit := do
  let className := factIdent className
  let lenName := factIdent lenName
  let dec0Name := factIdent dec0Name
  let dec1Name := factIdent dec1Name
  let dec2Name := factIdent dec2Name
  let dec3Name := factIdent dec3Name
  let leftoverName := factIdent leftoverName
  let minName := factIdent minName
  evalTactic (← `(tactic|
    wp_withdrawal_decode_chain (LeftoverDecodeChain.ofLocalFacts
      $className $lenName $dec0Name $dec1Name $dec2Name $dec3Name $leftoverName $minName); done))

/-- Type-directed WP automation for generated four-field withdrawal walks.
    It finds the local classifier, short-list length, field `decode` chain, and
    either the success guards or leftover fact, then delegates to the existing
    chain-object WP driver.  This avoids threading a manual `DecodeChainOutcome`
    through branch joins. -/
elab "wp_withdrawal_decode_walk" : tactic => withMainContext do
  let db ← collectWalkFactDb
  for lenFact in db.lens do
    let some className ← findClassFact? db lenFact.pfx | continue
    let dec0s ← findDecodeFrom? db lenFact.payload
    for dec0 in dec0s do
      let dec1s ← findDecodeFrom? db dec0.rest
      for dec1 in dec1s do
        let dec2s ← findDecodeFrom? db dec1.rest
        for dec2 in dec2s do
          let dec3s ← findDecodeFrom? db dec2.rest
          for dec3 in dec3s do
            let some minName ← findMinFact? db lenFact.payload | continue
            let saved ← saveState
            try
              let some endName ← findEndFact? db.ends dec3.rest | throwError "no end fact"
              let some canon0Name ← findHeadNeZeroFact? db dec0.data | throwError "no field 0 canonicality fact"
              let some len0Name ← findLenLeFact? db dec0.data 8 | throwError "no field 0 length fact"
              let some canon1Name ← findHeadNeZeroFact? db dec1.data | throwError "no field 1 canonicality fact"
              let some len1Name ← findLenLeFact? db dec1.data 8 | throwError "no field 1 length fact"
              let some addrName ← findLenEqFact? db dec2.data 20 | throwError "no address length fact"
              let some canon3Name ← findHeadNeZeroFact? db dec3.data | throwError "no field 3 canonicality fact"
              let some len3Name ← findLenLeFact? db dec3.data 8 | throwError "no field 3 length fact"
              tryCloseWithSuccessWalk className lenFact.name dec0.name dec1.name dec2.name dec3.name
                endName minName canon0Name len0Name canon1Name len1Name addrName canon3Name len3Name
              return
            catch _ =>
              restoreState saved
            let saved ← saveState
            try
              let some leftoverName ← findEndFact? db.leftovers dec3.rest | throwError "no leftover fact"
              tryCloseWithLeftoverWalk className lenFact.name dec0.name dec1.name dec2.name dec3.name
                leftoverName minName
              return
            catch _ =>
              restoreState saved
  throwError "wp_withdrawal_decode_walk: no four-field withdrawal decode walk closed the goal"


private def successFieldSpecsInputArg? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``EvmAsm.Rv64.RLP.WithdrawalDecode.successFieldSpecsInput 1 then
    some e.getAppArgs[0]!
  else
    none

private def decodeWithdrawalNoneArg? (e : Expr) : Option Expr := do
  let (lhs, rhs) ← eqSides? e
  guard (lhs.isAppOfArity ``EvmAsm.EL.decodeWithdrawal 1)
  guard (rhs.isAppOfArity ``Option.none 1)
  some lhs.getAppArgs[0]!

private def isResultFreeDecodeSplitLocalType (e : Expr) : TacticM Bool := do
  unless e.isAppOfArity ``Or 2 do
    return false
  let args := e.getAppArgs
  let some successInput := successFieldSpecsInputArg? args[0]! | return false
  let some failureInput := decodeWithdrawalNoneArg? args[1]! | return false
  sameExpr successInput failureInput

/-- Consume a result-free branch join of the form
    `successFieldSpecsInput input ∨ decodeWithdrawal input = none`.  The success
    branch exposes the schema predicate, while the failure branch exposes only
    the reason-erased semantic failure fact. -/
elab "wp_withdrawal_decode_split" : tactic => withMainContext do
  let lctx ← getLCtx
  for localDecl in lctx do
    if localDecl.isImplementationDetail then
      continue
    let localType ← whnfR (← instantiateMVars localDecl.type)
    unless ← isResultFreeDecodeSplitLocalType localType do
      continue
    let id := Lean.mkIdent localDecl.userName
    try
      evalTactic (← `(tactic|
        cases $id:ident with
        | inl h_success =>
            first
            | exact h_success
            | exact (successFieldSpecsInput_iff_exists_decodeWithdrawal_eq_some _).mp h_success
            | left; exact h_success
            | left; exact (successFieldSpecsInput_iff_exists_decodeWithdrawal_eq_some _).mp h_success
            | wp_withdrawal_decode_auto
        | inr h_failure =>
            first
            | exact h_failure
            | exact (decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput _).1 h_failure
            | right; exact h_failure
            | right; exact (decodeWithdrawal_eq_none_iff_not_successFieldSpecsInput _).1 h_failure
            | wp_withdrawal_decode_auto
        done))
      return
    catch _ =>
      (Pure.pure PUnit.unit : TacticM PUnit)
  throwError "wp_withdrawal_decode_split: no result-free schema/failure split closed the goal"

private def isDecodeChainLocalType (e : Expr) : Bool :=
  e.isAppOfArity ``SuccessDecodeChain 2 ||
    e.isAppOfArity ``LeftoverDecodeChain 2 ||
    e.isAppOfArity ``DecodeChainOutcome 2

/-- Context-driven chain WP automation.  It scans local hypotheses for already
    bundled success/leftover chain objects, projects the needed pure fact, and
    then falls back to the generic withdrawal WP driver. -/
elab "wp_withdrawal_decode_chain" : tactic => withMainContext do
  let lctx ← getLCtx
  for localDecl in lctx do
    if localDecl.isImplementationDetail then
      continue
    let localType ← whnfR (← instantiateMVars localDecl.type)
    unless isDecodeChainLocalType localType do
      continue
    let id := Lean.mkIdent localDecl.userName
    try
      evalTactic (← `(tactic| wp_withdrawal_decode_chain $id:ident; done))
      return
    catch _ =>
      (Pure.pure PUnit.unit : TacticM PUnit)
  try
    evalTactic (← `(tactic| wp_withdrawal_decode_split; done))
    return
  catch _ =>
    (Pure.pure PUnit.unit : TacticM PUnit)
  try
    evalTactic (← `(tactic| wp_withdrawal_decode_walk; done))
    return
  catch _ =>
    (Pure.pure PUnit.unit : TacticM PUnit)
  try
    evalTactic (← `(tactic| wp_withdrawal_decode_auto; done))
  catch _ =>
    throwError "wp_withdrawal_decode_chain: no local decode chain or withdrawal WP hint closed the goal"

/-- Outcome-driven WP automation for a bundled `DecodeChainOutcome` or a `Sum`
    of success/leftover chains.  The tactic splits the outcome once and delegates
    each branch to the chain-object WP driver. -/
macro "wp_withdrawal_decode_outcome " outcome:term : tactic =>
  `(tactic| first
    | exact ($outcome).successFieldSpecsInput_or_not
    | exact ($outcome).decodeWithdrawal_some_or_none
    | exact ($outcome).successFieldSpecsInput_or_decodeWithdrawal_none
    | have h_outcome := $outcome
      cases h_outcome with
      | success chain => wp_withdrawal_decode_chain chain
      | leftover chain => wp_withdrawal_decode_chain chain
    | have h_outcome := $outcome
      cases h_outcome with
      | inl chain => wp_withdrawal_decode_chain chain
      | inr chain => wp_withdrawal_decode_chain chain
    | wp_withdrawal_decode_auto)

private def isDecodeChainOutcomeLocalType (e : Expr) : Bool :=
  e.isAppOfArity ``DecodeChainOutcome 2 ||
    (e.isAppOfArity ``Sum 2 &&
      e.getAppArgs[0]!.isAppOfArity ``SuccessDecodeChain 2 &&
      e.getAppArgs[1]!.isAppOfArity ``LeftoverDecodeChain 2)

/-- Context-driven outcome WP automation.  Generated proofs that already bundled
    a branch join as a `DecodeChainOutcome` or `Sum` can leave the term implicit;
    the tactic finds the local outcome and delegates to `wp_withdrawal_decode_outcome outcome`. -/
elab "wp_withdrawal_decode_outcome" : tactic => withMainContext do
  let lctx ← getLCtx
  for localDecl in lctx do
    if localDecl.isImplementationDetail then
      continue
    let localType ← whnfR (← instantiateMVars localDecl.type)
    unless isDecodeChainOutcomeLocalType localType do
      continue
    let id := Lean.mkIdent localDecl.userName
    try
      evalTactic (← `(tactic| wp_withdrawal_decode_outcome $id:ident; done))
      return
    catch _ =>
      (Pure.pure PUnit.unit : TacticM PUnit)
  try
    evalTactic (← `(tactic| wp_withdrawal_decode_split; done))
    return
  catch _ =>
    (Pure.pure PUnit.unit : TacticM PUnit)
  try
    evalTactic (← `(tactic| wp_withdrawal_decode_walk; done))
  catch _ =>
    throwError "wp_withdrawal_decode_outcome: no local decode-chain outcome closed the goal"

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
    (hend : r4 = [])
    (h_min : 2 ≤ payload.length)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8) :
    DecodeChainOutcome pfx payload := by
  withdrawal_decode_outcome

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
    DecodeChainOutcome pfx payload := by
  withdrawal_decode_outcome


example
    {pfx : Byte} {payload rem1 rem2 rem3 rem4 field0 field1 field2 field3 : List Byte}
    (class_fact : classifyPrefix pfx = .shortList)
    (len_fact : rlpPrefixShortListPayloadLen pfx = payload.length)
    (decode0_fact : decode payload = some (.bytes field0, rem1))
    (decode1_fact : decode rem1 = some (.bytes field1, rem2))
    (decode2_fact : decode rem2 = some (.bytes field2, rem3))
    (decode3_fact : decode rem3 = some (.bytes field3, rem4))
    (end_fact : rem4 = [])
    (min_fact : 2 ≤ payload.length)
    (canon0_fact : field0.headD 1 ≠ 0) (len0_fact : field0.length ≤ 8)
    (canon1_fact : field1.headD 1 ≠ 0) (len1_fact : field1.length ≤ 8)
    (addr_fact : field2.length = 20)
    (canon3_fact : field3.headD 1 ≠ 0) (len3_fact : field3.length ≤ 8) :
    successFieldSpecsInput (pfx :: payload) ∨ decodeWithdrawal (pfx :: payload) = none := by
  wp_withdrawal_decode_walk

example
    {pfx : Byte} {payload rem1 rem2 rem3 rem4 field0 field1 field2 field3 : List Byte}
    (class_fact : classifyPrefix pfx = .shortList)
    (len_fact : rlpPrefixShortListPayloadLen pfx = payload.length)
    (decode0_fact : decode payload = some (.bytes field0, rem1))
    (decode1_fact : decode rem1 = some (.bytes field1, rem2))
    (decode2_fact : decode rem2 = some (.bytes field2, rem3))
    (decode3_fact : decode rem3 = some (.bytes field3, rem4))
    (leftover_fact : rem4 ≠ [])
    (min_fact : 2 ≤ payload.length) :
    (∃ w : Withdrawal, decodeWithdrawal (pfx :: payload) = some w) ∨
      decodeWithdrawal (pfx :: payload) = none := by
  wp_withdrawal_decode_outcome


example (input : List Byte)
    (h_split : successFieldSpecsInput input ∨ decodeWithdrawal input = none) :
    (∃ w : Withdrawal, decodeWithdrawal input = some w) ∨ decodeWithdrawal input = none := by
  wp_withdrawal_decode_split

example (input : List Byte)
    (h_split : successFieldSpecsInput input ∨ decodeWithdrawal input = none) :
    successFieldSpecsInput input ∨ decodeWithdrawal input = none := by
  wp_withdrawal_decode_outcome

example
    {pfx : Byte} {payload : List Byte} (chain : SuccessDecodeChain pfx payload) :
    successFieldSpecsInput chain.input := by
  wp_withdrawal_decode_chain chain

example
    {pfx : Byte} {payload : List Byte} (chain : SuccessDecodeChain pfx payload) :
    successFieldSpecsInput chain.input := by
  wp_withdrawal_decode_chain

example
    {pfx : Byte} {payload : List Byte} (chain : LeftoverDecodeChain pfx payload) :
    decodeWithdrawal chain.input = none := by
  wp_withdrawal_decode_chain chain

example
    {pfx : Byte} {payload : List Byte} (chain : LeftoverDecodeChain pfx payload) :
    successFieldSpecsInput chain.input ∨ ¬ successFieldSpecsInput chain.input := by
  wp_withdrawal_decode_chain

example
    {pfx : Byte} {payload : List Byte} (outcome : DecodeChainOutcome pfx payload) :
    successFieldSpecsInput outcome.input ∨ decodeWithdrawal outcome.input = none := by
  wp_withdrawal_decode_outcome outcome

example
    {pfx : Byte} {payload : List Byte} (outcome : DecodeChainOutcome pfx payload) :
    successFieldSpecsInput outcome.input ∨ decodeWithdrawal outcome.input = none := by
  wp_withdrawal_decode_chain

example
    {pfx : Byte} {payload : List Byte} (outcome : DecodeChainOutcome pfx payload) :
    successFieldSpecsInput outcome.input ∨ decodeWithdrawal outcome.input = none := by
  wp_withdrawal_decode_outcome

example
    {pfx : Byte} {payload : List Byte}
    (outcome : Sum (SuccessDecodeChain pfx payload) (LeftoverDecodeChain pfx payload)) :
    (∃ w : Withdrawal, decodeWithdrawal (pfx :: payload) = some w) ∨
      decodeWithdrawal (pfx :: payload) = none := by
  wp_withdrawal_decode_outcome outcome

example
    {pfx : Byte} {payload : List Byte}
    (outcome : Sum (SuccessDecodeChain pfx payload) (LeftoverDecodeChain pfx payload)) :
    (∃ w : Withdrawal, decodeWithdrawal (pfx :: payload) = some w) ∨
      decodeWithdrawal (pfx :: payload) = none := by
  wp_withdrawal_decode_outcome

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
