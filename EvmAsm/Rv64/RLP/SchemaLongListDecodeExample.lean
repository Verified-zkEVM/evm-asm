/-
  EvmAsm.Rv64.RLP.SchemaLongListDecodeExample

  EL.3 / Phase 5 — concrete end-to-end cross-check of the LONG-list decoder (the real tx/header
  form). Decodes a long RLP list of two 32-byte arrays (e.g. two hashes) — encoding
  `0xf8 0x42 ‖ (0xa0 ‖ 32×0x01) ‖ (0xa0 ‖ 32×0x01)`, 68 bytes — at region `0x2000` into a 64-byte
  output struct at `0x3000` via `x18`, placing the two payloads at output offsets 0 and 32. The
  whole pipeline runs: long-list-header descend (prefix `0xf8`, one length byte) ⨾ N-field fold,
  with `SchemaValid` from the single concatenation fact (`schemaValid_of_concat`) and the list
  window/pointer discharged by `long_list_schema_walk`. Complements the short-list example by
  exercising the long-form header path.
-/

import EvmAsm.Rv64.RLP.SchemaListWalkLong
import EvmAsm.Rv64.RLP.SchemaFoldConcat

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- A 32-byte payload (e.g. a hash), all `0x01`. -/
abbrev egHash : List Byte := List.replicate 32 (0x01 : Byte)

/-- The 68-byte buffer: a long RLP list (`0xf8`, length byte `0x42` = 66) whose payload is two
    32-byte arrays, each RLP-encoded as `0xa0 ‖ 32 bytes`. -/
abbrev egLongBs : List Byte :=
  [(0xf8 : Byte), 0x42] ++ ((0xa0 : Byte) :: egHash) ++ ((0xa0 : Byte) :: egHash)

/-- Two 32-byte-array fields at output offsets 0 and 32. -/
abbrev egLongSpecs : List FieldSpec :=
  [⟨false, egHash, 0, 0⟩, ⟨false, egHash, 32, 32⟩]

end EvmAsm.Rv64.RLP
