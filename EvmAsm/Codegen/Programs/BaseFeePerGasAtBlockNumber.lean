/-
  EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockNumber

  Number-keyed `header.base_fee_per_gas` extractor (RLP
  field 15). Introduces a new local helper
  `header_extract_base_fee_u64` (the existing
  `header_validate_base_fee` takes a pointer to the field,
  not an extractor). The helper reuses
  `rlp_field_to_u64_strict`, which rejects non-canonical
  scalars and fails if the field is > 8 bytes -- mainnet
  base fees have stayed sub-u64 since EIP-1559.

  Completes the EIP-1559 fee-market triple at block_number
  alongside gas_used (PR 7541) and gas_limit (PR 7551).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_extract_base_fee_u64

    Local helper: extract `header.base_fee_per_gas` (RLP
    field 15) into a u64. Fails if the field exceeds 8
    bytes BE (unreachable for mainnet historicals).
    Mirrors the shape of header_extract_gas_used /
    header_extract_gas_limit / etc.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : field 15 exceeds 8 bytes BE
-/
def headerExtractBaseFeeU64_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x13 .x12,
    .LI .x12 (15 : Word),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (16)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractBaseFeeU64_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractBaseFeeU64_relocs : RelocTable :=
  [ (4, .jal .x1 "rlp_field_to_u64_strict") ]

def headerExtractBaseFeeU64Function : String :=
  "header_extract_base_fee_u64:\n" ++ emitProgramR headerExtractBaseFeeU64_prog headerExtractBaseFeeU64_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractBaseFeeU64_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractBaseFeeU64Function_eq_prog :
    headerExtractBaseFeeU64Function = "header_extract_base_fee_u64:\n" ++ emitProgramR headerExtractBaseFeeU64_prog headerExtractBaseFeeU64_relocs := rfl

#guard headerExtractBaseFeeU64Function.startsWith "header_extract_base_fee_u64:\n"
#guard headerExtractBaseFeeU64_prog.length = 8
/-! ## base_fee_per_gas_at_block_number

    Number-keyed extractor for
    `header.block.base_fee_per_gas` (RLP field 15, u64 BE
    in practice; Uint in spec).

    Pipeline (composes K233 scan + the new
    header_extract_base_fee_u64; no other helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_base_fee_u64 -> u64

    Use cases:
      * EIP-1559 base-fee oracle: surface the per-block
        base_fee. Paired with gas_used (PR 7541) and
        gas_limit (PR 7551), callers can independently
        verify next_base_fee derivations.
      * Fee-market analysis: chain N calls with successive
        block_numbers to study base-fee trajectory.
      * Tx-replay validation: a callers' EXECUTION trace
        records (block_number, base_fee); verify the trace
        agrees with the on-chain header.

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 base_fee_per_gas out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (base_fee written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header base_fee extraction failed
            (RLP malformed / field 15 > 8 bytes / pre-1559
            header)
-/
def baseFeePerGasAtBlockNumberFunction : String :=
  "base_fee_per_gas_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # base_fee u64 out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lbfbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lbfbn_loop:\n" ++
  "  beq s5, s4, .Lbfbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lbfbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lbfbn_have_end\n" ++
  ".Lbfbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lbfbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, bfbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lbfbn_parse_fail\n" ++
  "  la t0, bfbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lbfbn_hit\n" ++
  "  j .Lbfbn_step\n" ++
  ".Lbfbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Lbfbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lbfbn_loop\n" ++
  ".Lbfbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_base_fee_u64\n" ++
  "  beqz a0, .Lbfbn_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lbfbn_ret\n" ++
  ".Lbfbn_finish:\n" ++
  "  bnez s8, .Lbfbn_parse_status\n" ++
  ".Lbfbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbfbn_ret\n" ++
  ".Lbfbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lbfbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_base_fee_per_gas_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : base_fee_per_gas (u64; 0 on failure) -/
def ziskBaseFeePerGasAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 base_fee out\n" ++
  "  jal ra, base_fee_per_gas_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbfbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractBaseFeeU64Function ++ "\n" ++
  baseFeePerGasAtBlockNumberFunction ++ "\n" ++
  ".Lbfbn_pdone:"

def ziskBaseFeePerGasAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "bfbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
