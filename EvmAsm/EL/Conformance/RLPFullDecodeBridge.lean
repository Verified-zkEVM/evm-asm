/-
  EvmAsm.EL.Conformance.RLPFullDecodeBridge

  Bridge the RLP conformance runner to the reusable top-level RLP full-decode
  wrapper (GH #125 / GH #120).
-/

module

public import EvmAsm.EL.Conformance.RLP
public import EvmAsm.EL.RLP.FullDecode

public section

namespace EvmAsm.EL
namespace Conformance
namespace RLPConformanceFullDecodeBridge

/--
The RLP conformance runner is exactly the reusable full-input decode wrapper
applied to the input bytes.

Distinctive token: RLPConformanceFullDecodeBridge.runDecodeFully_eq_decodeFully #125 #120.
-/
theorem runDecodeFully_eq_decodeFully (input : RLP.DecodeInput) :
    RLP.runDecodeFully input = EvmAsm.EL.RLP.decodeFully input.bytes := by
  unfold RLP.runDecodeFully EvmAsm.EL.RLP.decodeFully
  rfl

theorem runDecodeFully_eq_some_iff
    (input : RLP.DecodeInput) (item : RLP.RLPItem) :
    RLP.runDecodeFully input = some item ↔
      EvmAsm.EL.RLP.decode input.bytes = some (item, []) := by
  rw [runDecodeFully_eq_decodeFully]
  exact EvmAsm.EL.RLP.decodeFully_eq_some_iff input.bytes item

theorem checkVector?_runDecodeFully_eq_decodeFully
    (vector : TestVector RLP.DecodeInput RLP.RLPItem) :
    checkVector? RLP.runDecodeFully vector =
      checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes) vector := by
  cases vector with
  | mk id input expected =>
      cases expected <;> simp [checkVector?, runDecodeFully_eq_decodeFully]

theorem rlpNestedListDecodeVector_passed_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpNestedListDecodeVector = .passed := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpNestedListDecodeVector_passed

theorem rlpNoncanonicalSingletonVector_errored_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpNoncanonicalSingletonVector =
      .errored "rlp-noncanonical-singleton" "noncanonical-singleton" := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpNoncanonicalSingletonVector_errored

theorem rlpLongBytesDecodeVector_passed_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpLongBytesDecodeVector = .passed := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpLongBytesDecodeVector_passed

/--
Bridge the empty-list RLP decode conformance vector through the reusable
top-level full-decode wrapper, mirroring the nested-list and
noncanonical-singleton bridges above.

Distinctive token: rlpEmptyListDecodeVector_passed_via_decodeFully #120 #125.
-/
theorem rlpEmptyListDecodeVector_passed_via_decodeFully :
    checkVector? (fun input => EvmAsm.EL.RLP.decodeFully input.bytes)
        RLP.rlpEmptyListDecodeVector = .passed := by
  rw [← checkVector?_runDecodeFully_eq_decodeFully]
  exact RLP.rlpEmptyListDecodeVector_passed

end RLPConformanceFullDecodeBridge
end Conformance
end EvmAsm.EL
