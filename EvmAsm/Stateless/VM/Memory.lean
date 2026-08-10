/-
  EvmAsm.Stateless.VM.Memory

  Per-frame EVM memory model. Per the Yellow Paper:

  - Memory is byte-addressable, expandable in 32-byte words.
  - Reads/writes outside the current memory frontier trigger
    gas-cost-aware expansion.

  The opcode-level MLOAD / MSTORE / MSTORE8 semantics are
  already implemented as verified Programs at:

      EvmAsm/Evm64/MLoad/Program.lean
      EvmAsm/Evm64/MStore/Program.lean
      EvmAsm/Evm64/MStore8/Program.lean

  This file is the per-frame book-keeping shim:

  - `memory_base` pointer in the frame.
  - `memory_size` (current frontier in bytes).
  - `expand_by_words(n_words)` helper that charges gas per the
    quadratic memory schedule:
        gas = 3*n + n^2 / 512   (where n = total memory words)
    and zero-fills any newly-expanded region.

  ## Working RAM

  Per-frame memory in the emitted guest is `evm_memory` /
  `evm_memory_pool` / `call_frame_arena` in `.bss` (GH #11186). The
  former aspirational `0xa0b70000` 16 MiB slab is reclaimed — not a
  `MemoryLayout` anchor.

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.VM.Memory

-- TODO(stateless-vm): expose `expand_memory(frame, offset, size)
-- -> gas_charged` and the per-frame book-keeping helpers.

end EvmAsm.Stateless.VM.Memory
