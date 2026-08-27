/-
  EvmAsm.EL.ModexpInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_modexp` accelerator (precompile 0x05).

  The C interface is

      zkvm_status zkvm_modexp(const uint8_t* base, size_t base_len,
                              const uint8_t* exp, size_t exp_len,
                              const uint8_t* modulus, size_t mod_len,
                              uint8_t* output);

  so the input payload is three independent variable-width byte buffers,
  each read from a contiguous range of executable memory.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace ModexpInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- Input payload passed to `zkvm_modexp(base, base_len, exp, exp_len,
modulus, mod_len, output)`. The output buffer is part of the result
bridge; the request only carries the three input buffers. -/
structure AcceleratorInput where
  base    : List Byte
  exp     : List Byte
  modulus : List Byte
  deriving Repr

/-- Executable-spec `memory_read_bytes(memory, start, size)` shape: read
exactly `size` bytes starting at `start`. -/
def memoryReadBytes (memory : MemoryReader) (start size : Nat) : List Byte :=
  KeccakInputBridge.memoryReadBytes memory start size

/-- Distinctive token: ModexpInputBridge.modexpInputBytesFromMemory. -/
def modexpInputBytesFromMemory
    (memory : MemoryReader) (start size : Nat) : List Byte :=
  memoryReadBytes memory start size

/-- Accelerator-call input assembled from three independent byte buffers
read from executable memory. -/
def acceleratorInputFromMemory
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    AcceleratorInput :=
  { base    := modexpInputBytesFromMemory memory baseStart baseLen
    exp     := modexpInputBytesFromMemory memory expStart  expLen
    modulus := modexpInputBytesFromMemory memory modStart  modLen }

theorem memoryReadBytes_length (memory : MemoryReader) (start size : Nat) :
    (memoryReadBytes memory start size).length = size := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_length]

theorem memoryReadBytes_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (memoryReadBytes memory start size)[i]? = some (memory (start + i)) := by
  simp [memoryReadBytes, KeccakInputBridge.memoryReadBytes_get?, h_i]

@[simp] theorem memoryReadBytes_zero (memory : MemoryReader) (start : Nat) :
    memoryReadBytes memory start 0 = [] := rfl

theorem modexpInputBytesFromMemory_length
    (memory : MemoryReader) (start size : Nat) :
    (modexpInputBytesFromMemory memory start size).length = size := by
  simp [modexpInputBytesFromMemory, memoryReadBytes_length]

theorem modexpInputBytesFromMemory_get?
    (memory : MemoryReader) (start size i : Nat) (h_i : i < size) :
    (modexpInputBytesFromMemory memory start size)[i]? =
      some (memory (start + i)) := by
  simp [modexpInputBytesFromMemory, memoryReadBytes_get?, h_i]

@[simp] theorem modexpInputBytesFromMemory_zero_size
    (memory : MemoryReader) (start : Nat) :
    modexpInputBytesFromMemory memory start 0 = [] := rfl

theorem acceleratorInputFromMemory_base
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).base =
      modexpInputBytesFromMemory memory baseStart baseLen := rfl

theorem acceleratorInputFromMemory_exp
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).exp =
      modexpInputBytesFromMemory memory expStart expLen := rfl

theorem acceleratorInputFromMemory_modulus
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).modulus =
      modexpInputBytesFromMemory memory modStart modLen := rfl

theorem acceleratorInputFromMemory_base_length
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).base.length =
      baseLen := by
  simp [acceleratorInputFromMemory, modexpInputBytesFromMemory_length]

theorem acceleratorInputFromMemory_exp_length
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).exp.length =
      expLen := by
  simp [acceleratorInputFromMemory, modexpInputBytesFromMemory_length]

theorem acceleratorInputFromMemory_modulus_length
    (memory : MemoryReader)
    (baseStart baseLen expStart expLen modStart modLen : Nat) :
    (acceleratorInputFromMemory memory
        baseStart baseLen expStart expLen modStart modLen).modulus.length =
      modLen := by
  simp [acceleratorInputFromMemory, modexpInputBytesFromMemory_length]

end ModexpInputBridge

end EvmAsm.EL
