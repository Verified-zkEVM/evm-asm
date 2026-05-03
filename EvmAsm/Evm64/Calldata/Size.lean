/-
  EvmAsm.Evm64.Calldata.Size

  Pure CALLDATASIZE semantics for issue #104.
-/

import EvmAsm.Evm64.Calldata.Basic

namespace EvmAsm.Evm64
namespace Calldata

/-- CALLDATASIZE pushes the calldata byte length as a 256-bit EVM word. -/
def callDataSizeWord (sizeBytes : Nat) : EvmWord :=
  BitVec.ofNat 256 sizeBytes

/-- CALLDATASIZE semantics for a concrete calldata byte list. -/
def callDataSizeOf (data : List (BitVec 8)) : EvmWord :=
  callDataSizeWord data.length

@[simp] theorem callDataSizeWord_zero :
    callDataSizeWord 0 = 0 := rfl

@[simp] theorem callDataSizeOf_nil :
    callDataSizeOf [] = 0 := rfl

theorem callDataSizeOf_eq_length (data : List (BitVec 8)) :
    callDataSizeOf data = BitVec.ofNat 256 data.length := rfl

theorem callDataSizeOf_cons (b : BitVec 8) (data : List (BitVec 8)) :
    callDataSizeOf (b :: data) = callDataSizeWord (data.length + 1) := by
  simp [callDataSizeOf, callDataSizeWord, Nat.add_comm]

theorem callDataSizeOf_append (xs ys : List (BitVec 8)) :
    callDataSizeOf (xs ++ ys) = callDataSizeWord (xs.length + ys.length) := by
  simp [callDataSizeOf, callDataSizeWord, List.length_append]

theorem callDataSizeOf_append_nil (xs : List (BitVec 8)) :
    callDataSizeOf (xs ++ []) = callDataSizeOf xs := by
  simp [callDataSizeOf]

end Calldata
end EvmAsm.Evm64
