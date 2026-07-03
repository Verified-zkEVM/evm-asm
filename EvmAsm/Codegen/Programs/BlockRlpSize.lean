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
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def blockRlpRebuiltSize_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .ADDI .x10 .x8 (504 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_rlp_rebuilt_size + 68)),
    .MV .x19 .x10,
    .ADDI .x10 .x8 (508 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_rlp_rebuilt_size + 80)),
    .MV .x20 .x10,
    .BLTU .x20 .x19 (388 : BitVec 13),
    .ADDI .x10 .x8 (528 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_rlp_rebuilt_size + 96)),
    .MV .x21 .x10,
    .BLTU .x21 .x20 (372 : BitVec 13),
    .ADD .x22 .x8 .x19,
    .SUB .x23 .x20 .x19,
    .LI .x24 (0 : Word),
    .BEQ .x23 .x0 (204 : BitVec 13),
    .MV .x10 .x22,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_rlp_rebuilt_size + 128)),
    .MV .x25 .x10,
    .LI .x5 (4 : Word),
    .REMU .x6 .x25 .x5,
    .BNE .x6 .x0 (332 : BitVec 13),
    .BLTU .x23 .x25 (328 : BitVec 13),
    .DIVU .x26 .x25 .x5,
    .LI .x18 (0 : Word),
    .BGEU .x18 .x26 (164 : BitVec 13),
    .SLLI .x28 .x18 (2 : BitVec 6),
    .ADD .x10 .x22 .x28,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_rlp_rebuilt_size + 172)),
    .AUIPC .x5 (laHi GuestAddrs.brl_item_start (GuestAddrs.block_rlp_rebuilt_size + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.brl_item_start (GuestAddrs.block_rlp_rebuilt_size + 176)),
    .SD .x5 .x10 (0 : BitVec 12),
    .ADDI .x30 .x18 (1 : BitVec 12),
    .BGEU .x30 .x26 (32 : BitVec 13),
    .SLLI .x31 .x30 (2 : BitVec 6),
    .ADD .x10 .x22 .x31,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_rlp_rebuilt_size + 204)),
    .AUIPC .x5 (laHi GuestAddrs.brl_item_end (GuestAddrs.block_rlp_rebuilt_size + 208)),
    .ADDI .x5 .x5 (laLo GuestAddrs.brl_item_end (GuestAddrs.block_rlp_rebuilt_size + 208)),
    .SD .x5 .x10 (0 : BitVec 12),
    .JAL .x0 (16 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.brl_item_end (GuestAddrs.block_rlp_rebuilt_size + 224)),
    .ADDI .x5 .x5 (laLo GuestAddrs.brl_item_end (GuestAddrs.block_rlp_rebuilt_size + 224)),
    .SD .x5 .x23 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.brl_item_start (GuestAddrs.block_rlp_rebuilt_size + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.brl_item_start (GuestAddrs.block_rlp_rebuilt_size + 236)),
    .LD .x29 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.brl_item_end (GuestAddrs.block_rlp_rebuilt_size + 248)),
    .ADDI .x5 .x5 (laLo GuestAddrs.brl_item_end (GuestAddrs.block_rlp_rebuilt_size + 248)),
    .LD .x30 .x5 (0 : BitVec 12),
    .BLTU .x29 .x25 (216 : BitVec 13),
    .BLTU .x30 .x29 (212 : BitVec 13),
    .BLTU .x23 .x30 (208 : BitVec 13),
    .ADD .x31 .x22 .x29,
    .SUB .x11 .x30 .x29,
    .BEQ .x11 .x0 (16 : BitVec 13),
    .LBU .x5 .x31 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BGEU .x5 .x6 (20 : BitVec 13),
    .MV .x10 .x31,
    .JAL .x1 (jalOff GuestAddrs.rlp_bytes_encoded_size (GuestAddrs.block_rlp_rebuilt_size + 300)),
    .ADD .x24 .x24 .x10,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x24 .x24 .x11,
    .ADDI .x18 .x18 (1 : BitVec 12),
    .JAL .x0 (-160 : BitVec 21),
    .MV .x10 .x24,
    .JAL .x1 (jalOff GuestAddrs.rlp_list_encoded_size (GuestAddrs.block_rlp_rebuilt_size + 328)),
    .MV .x24 .x10,
    .ADD .x22 .x8 .x20,
    .SUB .x23 .x21 .x20,
    .LI .x5 (44 : Word),
    .REMU .x6 .x23 .x5,
    .BNE .x6 .x0 (124 : BitVec 13),
    .DIVU .x25 .x23 .x5,
    .LI .x26 (0 : Word),
    .LI .x18 (0 : Word),
    .BGEU .x18 .x25 (64 : BitVec 13),
    .LI .x5 (44 : Word),
    .MUL .x6 .x18 .x5,
    .ADD .x10 .x22 .x6,
    .AUIPC .x11 (laHi GuestAddrs.brl_wd_buf (GuestAddrs.block_rlp_rebuilt_size + 384)),
    .ADDI .x11 .x11 (laLo GuestAddrs.brl_wd_buf (GuestAddrs.block_rlp_rebuilt_size + 384)),
    .AUIPC .x12 (laHi GuestAddrs.brl_wd_len (GuestAddrs.block_rlp_rebuilt_size + 392)),
    .ADDI .x12 .x12 (laLo GuestAddrs.brl_wd_len (GuestAddrs.block_rlp_rebuilt_size + 392)),
    .JAL .x1 (jalOff GuestAddrs.ssz_withdrawal_to_rlp (GuestAddrs.block_rlp_rebuilt_size + 400)),
    .BNE .x10 .x0 (72 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.brl_wd_len (GuestAddrs.block_rlp_rebuilt_size + 408)),
    .ADDI .x5 .x5 (laLo GuestAddrs.brl_wd_len (GuestAddrs.block_rlp_rebuilt_size + 408)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x26 .x26 .x6,
    .ADDI .x18 .x18 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .MV .x10 .x26,
    .JAL .x1 (jalOff GuestAddrs.rlp_list_encoded_size (GuestAddrs.block_rlp_rebuilt_size + 436)),
    .MV .x26 .x10,
    .ADD .x5 .x9 .x24,
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADD .x5 .x5 .x26,
    .MV .x10 .x5,
    .JAL .x1 (jalOff GuestAddrs.rlp_list_encoded_size (GuestAddrs.block_rlp_rebuilt_size + 460)),
    .MV .x11 .x10,
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (1 : Word),
    .LI .x11 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def blockRlpRebuiltSizeFunction : String :=
  "block_rlp_rebuilt_size:\n" ++ emitProgram blockRlpRebuiltSize_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blockRlpRebuiltSize_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem blockRlpRebuiltSizeFunction_eq_prog :
    blockRlpRebuiltSizeFunction = "block_rlp_rebuilt_size:\n" ++ emitProgram blockRlpRebuiltSize_prog := rfl

#guard blockRlpRebuiltSizeFunction.startsWith "block_rlp_rebuilt_size:\n"
#guard blockRlpRebuiltSize_prog.length = 135
end EvmAsm.Codegen
