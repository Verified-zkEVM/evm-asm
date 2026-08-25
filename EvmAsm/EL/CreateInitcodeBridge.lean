/-
  EvmAsm.EL.CreateInitcodeBridge

  Bridge from CREATE/CREATE2 initcode stack ranges to memory bytes (GH #115).
-/

module

public import EvmAsm.EL.CreateArgsBridge

@[expose] public section

namespace EvmAsm.EL

namespace CreateInitcodeBridge

abbrev InitcodeRange := EvmAsm.Evm64.CreateArgs.InitcodeRange
abbrev CreateArgs := EvmAsm.Evm64.CreateArgs.Create
abbrev Create2Args := EvmAsm.Evm64.CreateArgs.Create2
abbrev MemoryReader := Nat → Byte

/-- First memory byte consumed as CREATE/CREATE2 initcode. -/
def initcodeStart (range : InitcodeRange) : Nat :=
  range.offset.toNat

/-- Number of memory bytes consumed as CREATE/CREATE2 initcode. -/
def initcodeSize (range : InitcodeRange) : Nat :=
  range.size.toNat

/-- CREATE/CREATE2 initcode bytes loaded from a pure memory-reader function.
    Distinctive token: CreateInitcodeBridge.initcodeFromMemory #115. -/
def initcodeFromMemory (readByte : MemoryReader) (range : InitcodeRange) : List Byte :=
  (List.range (initcodeSize range)).map (fun i => readByte (initcodeStart range + i))

def createInitcodeFromMemory (readByte : MemoryReader) (args : CreateArgs) : List Byte :=
  initcodeFromMemory readByte (CreateArgsBridge.createInitcodeRange args)

def create2InitcodeFromMemory (readByte : MemoryReader) (args : Create2Args) : List Byte :=
  initcodeFromMemory readByte (CreateArgsBridge.create2InitcodeRange args)

/-- Build the EL CREATE request directly from stack args and a pure memory reader. -/
def createRequestFromMemory
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) : CreateRequest :=
  CreateArgsBridge.createRequest creator (createInitcodeFromMemory readByte args) gas args

/-- Build the EL CREATE2 request directly from stack args and a pure memory reader. -/
def create2RequestFromMemory
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) : CreateRequest :=
  CreateArgsBridge.create2Request creator (create2InitcodeFromMemory readByte args) gas args

theorem initcodeStart_eq (range : InitcodeRange) :
    initcodeStart range = range.offset.toNat := rfl

theorem initcodeSize_eq (range : InitcodeRange) :
    initcodeSize range = range.size.toNat := rfl

@[simp] theorem initcodeFromMemory_length (readByte : MemoryReader) (range : InitcodeRange) :
    (initcodeFromMemory readByte range).length = initcodeSize range := by
  simp [initcodeFromMemory]

theorem initcodeFromMemory_get
    {readByte : MemoryReader} {range : InitcodeRange} {i : Nat}
    (h : i < initcodeSize range) :
    (initcodeFromMemory readByte range)[i]'(by
      simpa [initcodeFromMemory_length] using h) =
      readByte (initcodeStart range + i) := by
  simp [initcodeFromMemory, List.getElem_map, List.getElem_range]

@[simp] theorem initcodeFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    initcodeFromMemory readByte { offset := rangeOffset, size := 0 } = [] := rfl

theorem createInitcodeFromMemory_eq
    (readByte : MemoryReader) (args : CreateArgs) :
    createInitcodeFromMemory readByte args =
      initcodeFromMemory readByte args.initcode := rfl

theorem create2InitcodeFromMemory_eq
    (readByte : MemoryReader) (args : Create2Args) :
    create2InitcodeFromMemory readByte args =
      initcodeFromMemory readByte args.initcode := rfl

theorem createRequestFromMemory_eq
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    createRequestFromMemory creator readByte gas args =
      CreateArgsBridge.createRequest creator (createInitcodeFromMemory readByte args) gas args :=
  rfl

theorem create2RequestFromMemory_eq
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    create2RequestFromMemory creator readByte gas args =
      CreateArgsBridge.create2Request creator (create2InitcodeFromMemory readByte args) gas args :=
  rfl

theorem createRequestFromMemoryInitcode
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequestFromMemory creator readByte gas args).initcode =
      createInitcodeFromMemory readByte args := rfl

theorem create2RequestFromMemoryInitcode
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2RequestFromMemory creator readByte gas args).initcode =
      create2InitcodeFromMemory readByte args := rfl

theorem createRequestFromMemoryKind
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequestFromMemory creator readByte gas args).kind = .create := rfl

theorem create2RequestFromMemoryKind
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2RequestFromMemory creator readByte gas args).kind = .create2 := rfl

theorem createRequestFromMemoryValue
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : CreateArgs) :
    (createRequestFromMemory creator readByte gas args).value = args.value := rfl

theorem create2RequestFromMemorySalt?
    (creator : Address) (readByte : MemoryReader) (gas : EvmAsm.Evm64.EvmWord)
    (args : Create2Args) :
    (create2RequestFromMemory creator readByte gas args).salt? = some args.salt := rfl

end CreateInitcodeBridge

end EvmAsm.EL
