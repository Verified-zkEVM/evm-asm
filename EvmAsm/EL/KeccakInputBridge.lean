/-
  EvmAsm.EL.KeccakInputBridge

  Bridge from EVM KECCAK256 stack arguments to the executable memory input
  consumed by the zkVM accelerator (GH #111).
-/

module

public import EvmAsm.EL.WorldState
public import EvmAsm.Evm64.KeccakArgs

@[expose] public section

namespace EvmAsm.EL

namespace KeccakInputBridge

abbrev KeccakArgs := EvmAsm.Evm64.KeccakArgs.Args

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := Nat → Byte

/-- Input payload passed to the `zkvm_keccak256(data, len, output)` accelerator. -/
structure AcceleratorInput where
  bytes : List Byte
  deriving Repr

/--
Executable-spec `memory_read_bytes(memory, start, size)` shape: read exactly
`size` bytes starting at `start`.
-/
def memoryReadBytes (memory : MemoryReader) (start size : Nat) : List Byte :=
  (List.range size).map (fun i => memory (start + i))

/-- Distinctive token: KeccakInputBridge.keccakInputBytesFromMemory #111. -/
def keccakInputBytesFromMemory (memory : MemoryReader) (args : KeccakArgs) : List Byte :=
  memoryReadBytes memory
    (EvmAsm.Evm64.KeccakArgs.inputOffsetNat args)
    (EvmAsm.Evm64.KeccakArgs.inputSizeNat args)

/-- Accelerator-call input assembled from KECCAK stack arguments and memory. -/
def acceleratorInputFromArgs (memory : MemoryReader) (args : KeccakArgs) : AcceleratorInput :=
  { bytes := keccakInputBytesFromMemory memory args }

theorem memoryReadBytes_length (memory : MemoryReader) (start size : Nat) :
    (memoryReadBytes memory start size).length = size := by
  simp [memoryReadBytes]

theorem memoryReadBytes_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (memoryReadBytes memory start size)[i]? = some (memory (start + i)) := by
  simp [memoryReadBytes, h_i]

@[simp] theorem memoryReadBytes_zero (memory : MemoryReader) (start : Nat) :
    memoryReadBytes memory start 0 = [] := rfl

theorem keccakInputBytesFromMemory_length (memory : MemoryReader) (args : KeccakArgs) :
    (keccakInputBytesFromMemory memory args).length =
      EvmAsm.Evm64.KeccakArgs.inputSizeNat args := by
  simp [keccakInputBytesFromMemory, memoryReadBytes_length]

theorem keccakInputBytesFromMemory_get?
    (memory : MemoryReader) (args : KeccakArgs) (i : Nat)
    (h_i : i < EvmAsm.Evm64.KeccakArgs.inputSizeNat args) :
    (keccakInputBytesFromMemory memory args)[i]? =
      some (memory (EvmAsm.Evm64.KeccakArgs.inputOffsetNat args + i)) := by
  simp [keccakInputBytesFromMemory, memoryReadBytes_get?, h_i]

@[simp] theorem keccakInputBytesFromMemory_zero_size
    (memory : MemoryReader) (offset : EvmAsm.Evm64.EvmWord) :
    keccakInputBytesFromMemory memory (EvmAsm.Evm64.KeccakArgs.keccakArgs offset 0) = [] := by
  rfl

theorem acceleratorInputFromArgs_bytes (memory : MemoryReader) (args : KeccakArgs) :
    (acceleratorInputFromArgs memory args).bytes =
      keccakInputBytesFromMemory memory args := rfl

theorem acceleratorInputFromArgs_length (memory : MemoryReader) (args : KeccakArgs) :
    (acceleratorInputFromArgs memory args).bytes.length =
      EvmAsm.Evm64.KeccakArgs.inputSizeNat args := by
  simp [acceleratorInputFromArgs, keccakInputBytesFromMemory_length]

end KeccakInputBridge

end EvmAsm.EL
