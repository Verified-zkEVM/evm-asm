/-
  EvmAsm.Codegen.Programs.Chain

  Chain-level header aggregators carved out of
  `EvmAsm.Codegen.Programs.Header` per the file-size hard cap.

  Hosts two converted kernels, each pinned by a kernel-checked `_eq_prog`
  drift guard (emitted `String` == rendered `Program`) and a `.s` fixture:

    K239  chain_extract_timestamp_range
    K247  chain_extract_basefee_first_last

  Both operate on an N-element header chain and `jal` the
  `rlp_field_to_u64_strict` RLP helper at runtime.

  (The module's other aggregators — total/min/max gas & blob-gas, basefee /
  extra-data ranges — were unreferenced dead code: no `BuildUnit` consumer,
  no `.s` fixture, no `MANIFEST.tsv` entry. Removed; recoverable in git
  history.)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_extract_timestamp_range -- PR-K239

    Extract `(first_timestamp, last_timestamp)` from an N-element
    header chain. With K229 increasing-timestamps validated, the
    pair is monotonically non-decreasing; callers can use the
    range as a chain-segment duration or epoch identifier. The
    timestamp counterpart to K197 chain_extract_number_range.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_timestamp)
      a4 (input)  : u64 out (last_timestamp)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's timestamp field exceeds 8 bytes BE -/
def chainExtractTimestampRange_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x8 .x0 (brOff 2147483792 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (11 : Word),
    .MV .x13 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483716),
    .BNE .x10 .x0 (brOff 2147483800 2147483720),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .LI .x12 (11 : Word),
    .MV .x13 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483776),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractTimestampRange_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractTimestampRange_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_field_to_u64_strict"),
    (32, .jal .x1 "rlp_field_to_u64_strict") ]

def chainExtractTimestampRangeFunction : String :=
  "chain_extract_timestamp_range:\n" ++ emitProgramR chainExtractTimestampRange_prog chainExtractTimestampRange_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractTimestampRange_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractTimestampRangeFunction_eq_prog :
    chainExtractTimestampRangeFunction = "chain_extract_timestamp_range:\n" ++ emitProgramR chainExtractTimestampRange_prog chainExtractTimestampRange_relocs := rfl

#guard chainExtractTimestampRangeFunction.startsWith "chain_extract_timestamp_range:\n"
#guard chainExtractTimestampRange_prog.length = 47

/-! ## chain_extract_basefee_first_last -- PR-K247

    Extract `(first_basefee, last_basefee)` from an N-element
    header chain. Basefee counterpart to K197
    `chain_extract_number_range` and K239
    `chain_extract_timestamp_range`. Useful for measuring
    basefee drift across a chain segment (e.g., EIP-1559
    market-pressure analytics).

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_basefee)
      a4 (input)  : u64 out (last_basefee)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's basefee field exceeds 8 bytes BE -/
def chainExtractBasefeeFirstLast_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x8 .x0 (brOff 2147483792 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (15 : Word),
    .MV .x13 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483716),
    .BNE .x10 .x0 (brOff 2147483800 2147483720),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .LI .x12 (15 : Word),
    .MV .x13 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483776),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractBasefeeFirstLast_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractBasefeeFirstLast_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_field_to_u64_strict"),
    (32, .jal .x1 "rlp_field_to_u64_strict") ]

def chainExtractBasefeeFirstLastFunction : String :=
  "chain_extract_basefee_first_last:\n" ++ emitProgramR chainExtractBasefeeFirstLast_prog chainExtractBasefeeFirstLast_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractBasefeeFirstLast_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractBasefeeFirstLastFunction_eq_prog :
    chainExtractBasefeeFirstLastFunction = "chain_extract_basefee_first_last:\n" ++ emitProgramR chainExtractBasefeeFirstLast_prog chainExtractBasefeeFirstLast_relocs := rfl

#guard chainExtractBasefeeFirstLastFunction.startsWith "chain_extract_basefee_first_last:\n"
#guard chainExtractBasefeeFirstLast_prog.length = 47

end EvmAsm.Codegen
