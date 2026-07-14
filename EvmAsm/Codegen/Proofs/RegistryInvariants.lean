/-
  EvmAsm.Codegen.Proofs.RegistryInvariants

  Structural invariants of `tinyInterpRegistry` and the 256-entry jump
  table emitted from it. These theorems form Phase 1 of the codegen-
  proofs roadmap: they guard the registry's well-formedness at compile
  time (`lake build` fails if a future PR adds a duplicate opcode
  byte, a duplicate handler label, or an out-of-range opcode byte) and
  characterize what `jumpTargetLabel` returns for every byte 0..255.

  No new semantics — pure data-level reasoning over
  `List OpcodeHandlerSpec`. Phase 2 (codegen↔AST round-trip), Phase 3
  (dispatch-loop spec), and Phase 4 (handler ABI lifting) build on top
  of this foundation; see the roadmap in CODEGEN.md.

  Lives under `EvmAsm/Codegen/Proofs/` so future correctness theorems
  about the codegen layer can be grouped here, separate from the
  emitter / driver / registry `def`s.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.FileSizeGuard
import EvmAsm.Codegen.Programs.Registry

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Codegen

-- ============================================================================
-- 1. Opcode-byte uniqueness
-- ============================================================================
--
-- Concatenating each handler's `opcodes` list yields the multiset of all
-- opcode bytes the registry claims. Proving `Nodup` ensures the 256-entry
-- jump table built by `jumpTargetLabel` is well-defined: every byte is
-- claimed by at most one handler. `find?` returns the first match, so a
-- duplicate would silently route to whichever handler appears first in
-- the registry — exactly the kind of footgun this lemma rules out.

/-- The multiset of all opcode bytes claimed by handlers in
    `tinyInterpRegistry` has no duplicates. Catches "two handlers
    fighting for the same byte" at build time. -/
theorem tinyInterpRegistry_opcodes_Nodup :
    (tinyInterpRegistry.flatMap (·.opcodes)).Nodup := by
  set_option maxRecDepth 2048 in decide

-- ============================================================================
-- 2. Handler-label uniqueness
-- ============================================================================
--
-- Each handler's `label` is rendered verbatim as an asm label in the
-- emitted dispatcher epilogue (see `OpcodeHandlerSpec.emitSubroutine`).
-- Duplicate labels would make `riscv64-elf-as` reject the assembly with
-- "symbol redefinition" — this lemma promotes that drift detection to
-- `lake build` (kernel-checked).

/-- All handler labels in `tinyInterpRegistry` are distinct. Catches
    accidental label collisions before they reach the assembler. -/
theorem tinyInterpRegistry_labels_Nodup :
    (tinyInterpRegistry.map (·.label)).Nodup := by
  set_option maxRecDepth 2048 in decide

-- ============================================================================
-- 3. Opcode bytes fit in a u8
-- ============================================================================
--
-- The dispatch loop fetches a single byte (`lbu x5, 0(x10)`) and indexes
-- a 256-entry jump table. An opcode value ≥ 256 in the registry would
-- never match a `lbu`-extracted byte, so the handler would be
-- unreachable in practice — also a bug worth catching at compile time.

/-- Every opcode byte claimed by `tinyInterpRegistry` is `< 256`. -/
theorem tinyInterpRegistry_opcodes_lt_256 :
    ∀ b ∈ tinyInterpRegistry.flatMap (·.opcodes), b < 256 := by
  set_option maxRecDepth 2048 in decide

-- ============================================================================
-- 4. Jump-table targets are well-formed
-- ============================================================================
--
-- For every possible opcode byte (0..255), `jumpTargetLabel` returns
-- either a label that appears in the registry or the fallback
-- `"h_invalid"`. Combined with `tinyInterpRegistry_labels_Nodup`, this
-- guarantees the emitted jump table targets are all defined symbols in
-- the assembled ELF — no dangling references.

/-- For every byte `b < 256`, `jumpTargetLabel tinyInterpRegistry b`
    is either `"h_invalid"` or a label registered in
    `tinyInterpRegistry`. -/
theorem jumpTargetLabel_well_formed :
    ∀ b, b < 256 →
      jumpTargetLabel tinyInterpRegistry b = "h_invalid" ∨
      jumpTargetLabel tinyInterpRegistry b ∈ tinyInterpRegistry.map (·.label) := by
  set_option maxRecDepth 2048 in decide

-- ============================================================================
-- 5. Wired-opcode count
-- ============================================================================
--
-- A concrete count of how many of the 256 possible opcode bytes route
-- to a real handler (i.e. NOT to "h_invalid"). Updating this number
-- when wiring new opcodes is a deliberate-by-design step — drift here
-- means PROGRESS.md's coverage table is also stale.

/-- Exactly 154 opcode bytes are claimed by `tinyInterpRegistry` today.
    Update this number when wiring new opcodes (EXP, etc.). -/
theorem tinyInterpRegistry_wired_opcode_count :
    (tinyInterpRegistry.flatMap (·.opcodes)).length = 154 := by
  set_option maxRecDepth 2048 in decide

/-- Exactly 154 bytes in `[0, 255]` route to a registered handler;
    the remaining 102 fall through to `h_invalid`. -/
theorem jumpTable_non_invalid_count :
    ((List.range 256).filter
      (fun b => jumpTargetLabel tinyInterpRegistry b ≠ "h_invalid")).length = 154 := by
  set_option maxRecDepth 2048 in decide

end EvmAsm.Codegen.Proofs
