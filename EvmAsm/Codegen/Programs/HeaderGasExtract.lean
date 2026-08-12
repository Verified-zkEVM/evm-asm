/-
  EvmAsm.Codegen.Programs.HeaderGasExtract

  Header gas-field extractors split out of `BlockHashPredicates.lean`.

  Hosts:
    K210  header_extract_gas_used
    K211  header_extract_gas_limit

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## header_extract_gas_used / header_extract_gas_limit -- PR-K210 / K211

    Two more u64 header-field extractors, completing the
    `header_extract_*` u64 family alongside K198
    (base_fee_per_gas):

      K210  header_extract_gas_used   (field 10)
      K211  header_extract_gas_limit  (field 9)

    Each thin-wraps `rlp_field_to_u64_strict` for the specific field
    index. Useful for chain monitoring / fee-market analysis.

    Calling convention (both):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field missing
        2 : field exceeds 8 bytes BE -/
def headerExtractGasUsed_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x13 .x12,
    .LI .x12 (10 : Word),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483664),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractGasUsed_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractGasUsed_relocs : RelocTable :=
  [ (4, .jal .x1 "rlp_field_to_u64_strict") ]

def headerExtractGasUsedFunction : String :=
  "header_extract_gas_used:\n" ++ emitProgramR headerExtractGasUsed_prog headerExtractGasUsed_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractGasUsed_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractGasUsedFunction_eq_prog :
    headerExtractGasUsedFunction = "header_extract_gas_used:\n" ++ emitProgramR headerExtractGasUsed_prog headerExtractGasUsed_relocs := rfl

#guard headerExtractGasUsedFunction.startsWith "header_extract_gas_used:\n"
#guard headerExtractGasUsed_prog.length = 8
def ziskHeaderExtractGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_gas_used\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhegu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  headerExtractGasUsedFunction ++ "\n" ++
  ".Lhegu_pdone:"

def ziskHeaderExtractGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractGasUsedPrologue
  dataAsm     := ziskHeaderExtractGasUsedDataSection
}

def headerExtractGasLimit_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x13 .x12,
    .LI .x12 (9 : Word),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483664),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractGasLimit_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractGasLimit_relocs : RelocTable :=
  [ (4, .jal .x1 "rlp_field_to_u64_strict") ]

def headerExtractGasLimitFunction : String :=
  "header_extract_gas_limit:\n" ++ emitProgramR headerExtractGasLimit_prog headerExtractGasLimit_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractGasLimit_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractGasLimitFunction_eq_prog :
    headerExtractGasLimitFunction = "header_extract_gas_limit:\n" ++ emitProgramR headerExtractGasLimit_prog headerExtractGasLimit_relocs := rfl

#guard headerExtractGasLimitFunction.startsWith "header_extract_gas_limit:\n"
#guard headerExtractGasLimit_prog.length = 8
def ziskHeaderExtractGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_gas_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhegl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  headerExtractGasLimitFunction ++ "\n" ++
  ".Lhegl_pdone:"

def ziskHeaderExtractGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractGasLimitPrologue
  dataAsm     := ziskHeaderExtractGasLimitDataSection
}

end EvmAsm.Codegen
