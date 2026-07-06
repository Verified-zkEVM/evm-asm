/-
  EvmAsm.EL.Conformance.RLP

  Compact Lean-side conformance vectors for the executable RLP decoder
  (GH #125 / GH #120).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.RLP.Decode

namespace EvmAsm.EL
namespace Conformance
namespace RLP

abbrev Byte := EvmAsm.EL.RLP.Byte
abbrev RLPItem := EvmAsm.EL.RLP.RLPItem

/-- Input shape for an RLP decode executable-helper conformance vector. -/
structure DecodeInput where
  bytes : List Byte
  deriving Repr

/-- Decode exactly one RLP item and reject leftover bytes. -/
def runDecodeFully (input : DecodeInput) : Option RLPItem :=
  match EvmAsm.EL.RLP.decode input.bytes with
  | some (item, []) => some item
  | _ => none

/-- Nested list decode vector, covering recursive item decoding.
    Distinctive token: rlpNestedListDecodeVector. -/
def rlpNestedListDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-nested-list-decode"
    input := { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    expected := .value (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) }

/-- Non-canonical singleton byte string must be rejected; `0x01` should be
    encoded directly as the single byte `0x01`, not as `0x81 0x01`. -/
def rlpNoncanonicalSingletonVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-noncanonical-singleton"
    input := { bytes := [(0x81 : Byte), 0x01] }
    expected := .error "noncanonical-singleton" }

/-- Empty-list decoding covers the canonical `0xc0` list prefix.
    Distinctive token: RLP.rlpEmptyListDecodeVector #120 #125. -/
def rlpEmptyListDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-empty-list-decode"
    input := { bytes := [(0xc0 : Byte)] }
    expected := .value (.list []) }

/-- Long-form byte string at the first canonical long-byte boundary.
    Distinctive token: RLP.rlpLongBytesDecodeVector #120 #125. -/
def rlpLongBytesDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-long-bytes-decode"
    input := { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) }
    expected := .value (.bytes (List.replicate 56 (0x7f : Byte))) }

theorem runDecodeFully_nestedList :
    runDecodeFully { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] } =
      some (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) := rfl

theorem runDecodeFully_reject_noncanonical_singleton :
    runDecodeFully { bytes := [(0x81 : Byte), 0x01] } = none := rfl

theorem runDecodeFully_emptyList :
    runDecodeFully { bytes := [(0xc0 : Byte)] } = some (.list []) := rfl

theorem runDecodeFully_longBytes :
    runDecodeFully
      { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) } =
      some (.bytes (List.replicate 56 (0x7f : Byte))) := by
  rfl

theorem rlpNestedListDecodeVector_passed :
    checkVector? runDecodeFully rlpNestedListDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-nested-list-decode"
    { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]])
    runDecodeFully_nestedList

theorem rlpNoncanonicalSingletonVector_errored :
    checkVector? runDecodeFully rlpNoncanonicalSingletonVector =
      .errored "rlp-noncanonical-singleton" "noncanonical-singleton" :=
  checkVector?_none_error runDecodeFully
    "rlp-noncanonical-singleton"
    "noncanonical-singleton"
    { bytes := [(0x81 : Byte), 0x01] }
    runDecodeFully_reject_noncanonical_singleton

theorem rlpEmptyListDecodeVector_passed :
    checkVector? runDecodeFully rlpEmptyListDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-empty-list-decode"
    { bytes := [(0xc0 : Byte)] }
    (.list [])
    runDecodeFully_emptyList

theorem rlpLongBytesDecodeVector_passed :
    checkVector? runDecodeFully rlpLongBytesDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-long-bytes-decode"
    { bytes := (0xb8 : Byte) :: 0x38 :: List.replicate 56 (0x7f : Byte) }
    (.bytes (List.replicate 56 (0x7f : Byte)))
    runDecodeFully_longBytes

/-- Vector IDs for RLP executable-decoding conformance coverage.
    Distinctive token: rlpConformanceVectorIds #125 #120. -/
def rlpConformanceVectorIds : List String :=
  [ rlpNestedListDecodeVector.id
  , rlpNoncanonicalSingletonVector.id
  , rlpEmptyListDecodeVector.id
  , rlpLongBytesDecodeVector.id
  ]

theorem rlpConformanceVectorIds_eq :
    rlpConformanceVectorIds =
      [ "rlp-nested-list-decode"
      , "rlp-noncanonical-singleton"
      , "rlp-empty-list-decode"
      , "rlp-long-bytes-decode"
      ] := rfl

theorem rlpConformanceVectorIds_length :
    rlpConformanceVectorIds.length = 4 := rfl

theorem rlpConformanceVectorIds_nodup :
    rlpConformanceVectorIds.Nodup := by
  decide

/-- Compact checked-vector batch for RLP executable decoding.
    Distinctive token: RLP.rlpConformanceVectors #125 #120. -/
def rlpConformanceVectors : List CheckResult :=
  [ checkVector? runDecodeFully rlpNestedListDecodeVector
  , checkVector? runDecodeFully rlpNoncanonicalSingletonVector
  , checkVector? runDecodeFully rlpEmptyListDecodeVector
  , checkVector? runDecodeFully rlpLongBytesDecodeVector
  ]

theorem rlpConformanceVectors_passed :
    rlpConformanceVectors =
      [ .passed
      , .errored "rlp-noncanonical-singleton" "noncanonical-singleton"
      , .passed
      , .passed
      ] := by
  simp [rlpConformanceVectors, rlpNestedListDecodeVector_passed,
    rlpNoncanonicalSingletonVector_errored, rlpEmptyListDecodeVector_passed,
    rlpLongBytesDecodeVector_passed]

end RLP
end Conformance
end EvmAsm.EL
