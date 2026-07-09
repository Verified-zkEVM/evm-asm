/-
  EvmAsm.EL.TerminatingDataMemory

  Bridge from RETURN/REVERT stack arguments to returned memory bytes (GH #113).
-/

import EvmAsm.EL.TerminatingArgsBridge

namespace EvmAsm.EL

namespace TerminatingDataMemory

abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs
abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev MemoryReader := Nat → Byte

/-- First memory byte consumed as RETURN/REVERT output data. -/
def dataStart (args : TerminatingArgs) : Nat :=
  (TerminatingArgsBridge.dataRange args).offset.toNat

/-- Number of memory bytes consumed as RETURN/REVERT output data. -/
def dataSize (args : TerminatingArgs) : Nat :=
  (TerminatingArgsBridge.dataRange args).size.toNat

/-- RETURN/REVERT data bytes loaded from a pure memory-reader function. -/
def terminatingDataFromMemory
    (readByte : MemoryReader) (args : TerminatingArgs) : List Byte :=
  (List.range (dataSize args)).map (fun i => readByte (dataStart args + i))

theorem dataStart_eq (args : TerminatingArgs) :
    dataStart args = (TerminatingArgsBridge.dataRange args).offset.toNat := rfl

theorem dataSize_eq (args : TerminatingArgs) :
    dataSize args = (TerminatingArgsBridge.dataRange args).size.toNat := rfl

@[simp] theorem terminatingDataFromMemory_length
    (readByte : MemoryReader) (args : TerminatingArgs) :
    (terminatingDataFromMemory readByte args).length = dataSize args := by
  simp [terminatingDataFromMemory]

theorem terminatingDataFromMemory_get
    {readByte : MemoryReader} {args : TerminatingArgs} {i : Nat}
    (h : i < dataSize args) :
    (terminatingDataFromMemory readByte args)[i]'(by
      simpa [terminatingDataFromMemory_length] using h) =
      readByte (dataStart args + i) := by
  simp [terminatingDataFromMemory, List.getElem_map, List.getElem_range]

@[simp] theorem terminatingDataFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    terminatingDataFromMemory readByte
        (EvmAsm.Evm64.TerminatingArgs.returnArgs rangeOffset 0) = [] := rfl

@[simp] theorem terminatingDataFromMemory_revert_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    terminatingDataFromMemory readByte
        (EvmAsm.Evm64.TerminatingArgs.revertArgs rangeOffset 0) = [] := rfl

end TerminatingDataMemory

end EvmAsm.EL
