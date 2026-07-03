/-
  EvmAsm.Codegen.Programs.BlockRlpSize

  RISC-V helpers for EIP-7934 block RLP size enforcement. The main helper
  computes the exact canonical `len(rlp.encode(Block(...)))` from the SSZ
  ExecutionPayload shape consumed by the stateless guest, plus the caller's
  already rebuilt header RLP length. This assumes the stateless input represents
  the same block that execution-specs validates; see
  `docs/execution-specs-feedback.md` for the EIP-7934 fixture-equivalence note.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Withdrawal

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_rlp_rebuilt_size -- compute len(rlp.encode(Block(...))) from SSZ.
    Mirrors execution-specs' EIP-7934 check without trusting fixture sidecars:
    the caller supplies the already rebuilt header RLP length, and this routine
    derives the transaction and withdrawal list RLP lengths from the SSZ
    ExecutionPayload. It returns status in a0 and rebuilt block RLP length in a1.

    a0 = SSZ ExecutionPayload ptr   a1 = rebuilt header RLP length
    a2 = SSZ_BASE                   a0 = 0 ok / 1 malformed input, a1 = length -/
def rlpBytesEncodedSize_prog : Program :=
  [ .LI .x5 (1 : Word),
    .BNE .x11 .x5 (16 : BitVec 13),
    .LBU .x6 .x10 (0 : BitVec 12),
    .LI .x7 (128 : Word),
    .BLTU .x6 .x7 (20 : BitVec 13),
    .LI .x5 (56 : Word),
    .BGEU .x11 .x5 (20 : BitVec 13),
    .ADDI .x10 .x11 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x5 .x11,
    .LI .x6 (0 : Word),
    .BEQ .x5 .x0 (16 : BitVec 13),
    .SRLI .x5 .x5 (8 : BitVec 6),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .ADD .x10 .x11 .x6,
    .ADDI .x10 .x10 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpBytesEncodedSizeFunction : String :=
  "rlp_bytes_encoded_size:\n" ++ emitProgram rlpBytesEncodedSize_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpBytesEncodedSize_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpBytesEncodedSizeFunction_eq_prog :
    rlpBytesEncodedSizeFunction = "rlp_bytes_encoded_size:\n" ++ emitProgram rlpBytesEncodedSize_prog := rfl

#guard rlpBytesEncodedSizeFunction.startsWith "rlp_bytes_encoded_size:\n"
#guard rlpBytesEncodedSize_prog.length = 20
def rlpListEncodedSize_prog : Program :=
  [ .LI .x5 (56 : Word),
    .BGEU .x10 .x5 (12 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x5 .x10,
    .LI .x6 (0 : Word),
    .BEQ .x5 .x0 (16 : BitVec 13),
    .SRLI .x5 .x5 (8 : BitVec 6),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .ADD .x10 .x10 .x6,
    .ADDI .x10 .x10 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpListEncodedSizeFunction : String :=
  "rlp_list_encoded_size:\n" ++ emitProgram rlpListEncodedSize_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpListEncodedSize_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpListEncodedSizeFunction_eq_prog :
    rlpListEncodedSizeFunction = "rlp_list_encoded_size:\n" ++ emitProgram rlpListEncodedSize_prog := rfl

#guard rlpListEncodedSizeFunction.startsWith "rlp_list_encoded_size:\n"
#guard rlpListEncodedSize_prog.length = 13
def blockRlpRebuiltSizeFunction : String :=
  "block_rlp_rebuilt_size:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # payload\n" ++
  "  mv s1, a1                   # header RLP length\n" ++
  "  mv s2, a2                   # SSZ_BASE (reserved for future schema checks)\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le; mv s3, a0    # tx_off\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le; mv s4, a0    # withdrawals_off\n" ++
  "  bltu s4, s3, .Lbrl_fail\n" ++
  "  addi a0, s0, 528; jal ra, bgv_u32le; mv s5, a0    # block_access_list_off\n" ++
  "  bltu s5, s4, .Lbrl_fail\n" ++
  "  add s6, s0, s3              # tx section ptr\n" ++
  "  sub s7, s4, s3              # tx section len\n" ++
  "  li s8, 0                    # tx list payload length\n" ++
  "  beqz s7, .Lbrl_tx_list_size\n" ++
  "  mv a0, s6; jal ra, bgv_u32le; mv s9, a0           # first SSZ offset = 4*N\n" ++
  "  li t0, 4; remu t1, s9, t0; bnez t1, .Lbrl_fail\n" ++
  "  bltu s7, s9, .Lbrl_fail\n" ++
  "  divu s10, s9, t0            # tx count\n" ++
  "  li s2, 0                    # i\n" ++
  ".Lbrl_tx_loop:\n" ++
  "  bgeu s2, s10, .Lbrl_tx_list_size\n" ++
  "  slli t3, s2, 2; add a0, s6, t3; jal ra, bgv_u32le; la t0, brl_item_start; sd a0, 0(t0)\n" ++
  "  addi t5, s2, 1; bgeu t5, s10, .Lbrl_tx_last\n" ++
  "  slli t6, t5, 2; add a0, s6, t6; jal ra, bgv_u32le; la t0, brl_item_end; sd a0, 0(t0); j .Lbrl_tx_have_end\n" ++
  ".Lbrl_tx_last:\n" ++
  "  la t0, brl_item_end; sd s7, 0(t0)\n" ++
  ".Lbrl_tx_have_end:\n" ++
  "  la t0, brl_item_start; ld t4, 0(t0); la t0, brl_item_end; ld t5, 0(t0)\n" ++
  "  bltu t4, s9, .Lbrl_fail\n" ++
  "  bltu t5, t4, .Lbrl_fail\n" ++
  "  bltu s7, t5, .Lbrl_fail\n" ++
  "  add t6, s6, t4; sub a1, t5, t4\n" ++
  "  beqz a1, .Lbrl_tx_as_bytes\n" ++
  "  lbu t0, 0(t6); li t1, 0xc0; bgeu t0, t1, .Lbrl_tx_as_legacy\n" ++
  ".Lbrl_tx_as_bytes:\n" ++
  "  mv a0, t6; jal ra, rlp_bytes_encoded_size\n" ++
  "  add s8, s8, a0; j .Lbrl_tx_next\n" ++
  ".Lbrl_tx_as_legacy:\n" ++
  "  add s8, s8, a1\n" ++
  ".Lbrl_tx_next:\n" ++
  "  addi s2, s2, 1; j .Lbrl_tx_loop\n" ++
  ".Lbrl_tx_list_size:\n" ++
  "  mv a0, s8; jal ra, rlp_list_encoded_size; mv s8, a0\n" ++
  "  add s6, s0, s4              # withdrawals section ptr\n" ++
  "  sub s7, s5, s4              # withdrawals section len\n" ++
  "  li t0, 44; remu t1, s7, t0; bnez t1, .Lbrl_fail\n" ++
  "  divu s9, s7, t0             # withdrawal count\n" ++
  "  li s10, 0                   # withdrawal list payload length\n" ++
  "  li s2, 0\n" ++
  ".Lbrl_wd_loop:\n" ++
  "  bgeu s2, s9, .Lbrl_wd_list_size\n" ++
  "  li t0, 44; mul t1, s2, t0; add a0, s6, t1\n" ++
  "  la a1, brl_wd_buf; la a2, brl_wd_len; jal ra, ssz_withdrawal_to_rlp\n" ++
  "  bnez a0, .Lbrl_fail\n" ++
  "  la t0, brl_wd_len; ld t1, 0(t0); add s10, s10, t1\n" ++
  "  addi s2, s2, 1; j .Lbrl_wd_loop\n" ++
  ".Lbrl_wd_list_size:\n" ++
  "  mv a0, s10; jal ra, rlp_list_encoded_size; mv s10, a0\n" ++
  "  add t0, s1, s8              # header + txs\n" ++
  "  addi t0, t0, 1              # empty ommers list = 0xc0\n" ++
  "  add t0, t0, s10             # + withdrawals\n" ++
  "  mv a0, t0; jal ra, rlp_list_encoded_size\n" ++
  "  mv a1, a0; li a0, 0; j .Lbrl_ret\n" ++
  ".Lbrl_fail:\n" ++
  "  li a0, 1; li a1, 0\n" ++
  ".Lbrl_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

end EvmAsm.Codegen
