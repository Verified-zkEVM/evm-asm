/-
  EvmAsm.EL.CallOutputMemory

  Destination-address bridge for CALL-family returned bytes (GH #114).
-/

import Mathlib.Data.List.GetD
import EvmAsm.EL.CallOutputBridge

namespace EvmAsm.EL

namespace CallOutputMemory

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev Byte := EvmAsm.EL.Byte

/-- First caller-memory byte written by a CALL-family output copy. -/
def outputStart (range : MemoryRange) : Nat :=
  range.offset.toNat

/-- One-past-the-end caller-memory byte for a CALL-family output copy. -/
def outputEnd (range : MemoryRange) : Nat :=
  outputStart range + range.size.toNat

/-- Destination-relative index for a concrete caller-memory byte address. -/
def outputWriteIndex (range : MemoryRange) (addr : Nat) : Nat :=
  addr - outputStart range

/-- Prop-valued range predicate for addresses written by CALL-family output
    copying. -/
def writesOutputAddress (range : MemoryRange) (addr : Nat) : Prop :=
  outputStart range ≤ addr ∧ addr < outputEnd range

instance (range : MemoryRange) (addr : Nat) :
    Decidable (writesOutputAddress range addr) := by
  unfold writesOutputAddress
  infer_instance

theorem outputStart_eq (range : MemoryRange) :
    outputStart range = range.offset.toNat := rfl

theorem outputEnd_eq (range : MemoryRange) :
    outputEnd range = range.offset.toNat + range.size.toNat := rfl

theorem outputWriteIndex_eq (range : MemoryRange) (addr : Nat) :
    outputWriteIndex range addr = addr - range.offset.toNat := rfl

theorem writesOutputAddress_iff (range : MemoryRange) (addr : Nat) :
    writesOutputAddress range addr ↔
      range.offset.toNat ≤ addr ∧ addr < range.offset.toNat + range.size.toNat := by
  rfl

theorem outputWriteIndex_at_output_add (range : MemoryRange) (i : Nat) :
    outputWriteIndex range (outputStart range + i) = i := by
  unfold outputWriteIndex
  omega

end CallOutputMemory

end EvmAsm.EL
