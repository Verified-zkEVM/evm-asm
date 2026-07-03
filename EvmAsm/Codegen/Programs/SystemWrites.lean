/-
  EvmAsm.Codegen.Programs.SystemWrites

  system_write_descriptors (bead evm-asm-fhsxz.2.4.2.5, steps a/b): derive the
  per-block SYSTEM-contract storage writes from the ExecutionPayload — the two
  modeled startup effects of the two unchecked system calls every Amsterdam
  block runs at block start (before withdrawals):

    * EIP-2935 (history contract 0x0000…2935):
        slot  = (block_number - 1) % 8191
        value = parent block hash (= payload.parent_hash)
    * EIP-4788 (beacon-roots contract 0x000f3df6…beac02):
        slot  = timestamp % 8191        value = timestamp
        slot' = (timestamp % 8191)+8191 value' = parent_beacon_block_root
        (a zero root is a storage deletion; absent slots remain no-ops.)

  Reads (byte-wise, no-misaligned): exec_payload = SSZ_BASE + 60; parent_hash @
  payload+0 (32 B); block_number @ payload+404 (u64 LE); timestamp @ payload+428
  (u64 LE); parent_beacon_block_root @ NPR+8 = SSZ_BASE+24 (32 B).

  The slot index is the 32-byte big-endian storage key; the stored value is the
  MINIMAL big-endian word (leading zeros stripped) — what the storage trie leaf's
  rlp(value) wants. The EIP-2935 storage slot is reduced modulo the 8191-entry
  history serve window (HISTORY_SERVE_WINDOW, matching the deployed history
  contract's 0x1fff modulus) before encoding the 32-byte big-endian storage key.

  Outputs feed account_apply_storage_slot (one per system contract) in the
  verdict's state recompute.  Shared Amsterdam system-transaction gas and
  reservoir constants live in AmsterdamSystemTx.lean; this helper is the current
  direct-descriptor shortcut for the EIP-4788/EIP-2935 startup calls.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.AmsterdamSystemTx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## swd_read_u64le -- read a little-endian u64 byte-wise (a0=ptr -> a0). Leaf. -/
def swdReadU64le_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LBU .x6 .x10 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (2 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (3 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (4 : BitVec 12),
    .SLLI .x6 .x6 (32 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (5 : BitVec 12),
    .SLLI .x6 .x6 (40 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (6 : BitVec 12),
    .SLLI .x6 .x6 (48 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (7 : BitVec 12),
    .SLLI .x6 .x6 (56 : BitVec 6),
    .OR .x5 .x5 .x6,
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def swdReadU64leFunction : String :=
  "swd_read_u64le:\n" ++ emitProgram swdReadU64le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `swdReadU64le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem swdReadU64leFunction_eq_prog :
    swdReadU64leFunction = "swd_read_u64le:\n" ++ emitProgram swdReadU64le_prog := rfl

#guard swdReadU64leFunction.startsWith "swd_read_u64le:\n"
#guard swdReadU64le_prog.length = 24
/-! ## swd_write_be32_u64 -- write a0 (u64) big-endian into the LOW 8 bytes of a
    zeroed 32-byte buffer at a1 (the 32-byte storage slot key). Leaf. -/
def swdWriteBe32U64_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (32 : Word),
    .BEQ .x5 .x6 (20 : BitVec 13),
    .ADD .x7 .x11 .x5,
    .SB .x7 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x5 (0 : Word),
    .LI .x6 (8 : Word),
    .BEQ .x5 .x6 (44 : BitVec 13),
    .LI .x7 (56 : Word),
    .SLLI .x28 .x5 (3 : BitVec 6),
    .SUB .x7 .x7 .x28,
    .SRL .x29 .x10 .x7,
    .ANDI .x29 .x29 (255 : BitVec 12),
    .ADDI .x30 .x11 (24 : BitVec 12),
    .ADD .x30 .x30 .x5,
    .SB .x30 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def swdWriteBe32U64Function : String :=
  "swd_write_be32_u64:\n" ++ emitProgram swdWriteBe32U64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `swdWriteBe32U64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem swdWriteBe32U64Function_eq_prog :
    swdWriteBe32U64Function = "swd_write_be32_u64:\n" ++ emitProgram swdWriteBe32U64_prog := rfl

#guard swdWriteBe32U64Function.startsWith "swd_write_be32_u64:\n"
#guard swdWriteBe32U64_prog.length = 21
/-! ## swd_write_be8 -- write a0 (u64) big-endian into 8 bytes at a1. Leaf. -/
def swdWriteBe8_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (8 : Word),
    .BEQ .x5 .x6 (40 : BitVec 13),
    .LI .x7 (56 : Word),
    .SLLI .x28 .x5 (3 : BitVec 6),
    .SUB .x7 .x7 .x28,
    .SRL .x29 .x10 .x7,
    .ANDI .x29 .x29 (255 : BitVec 12),
    .ADD .x30 .x11 .x5,
    .SB .x30 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def swdWriteBe8Function : String :=
  "swd_write_be8:\n" ++ emitProgram swdWriteBe8_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `swdWriteBe8_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem swdWriteBe8Function_eq_prog :
    swdWriteBe8Function = "swd_write_be8:\n" ++ emitProgram swdWriteBe8_prog := rfl

#guard swdWriteBe8Function.startsWith "swd_write_be8:\n"
#guard swdWriteBe8_prog.length = 13
/-! ## swd_minimal_copy -- copy src[a0..a0+a1) stripping leading zero bytes into
    a2; write the resulting length to a3. Leaf. -/
def swdMinimalCopy_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .BEQ .x6 .x0 (24 : BitVec 13),
    .LBU .x7 .x5 (0 : BitVec 12),
    .BNE .x7 .x0 (16 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .SD .x13 .x6 (0 : BitVec 12),
    .MV .x28 .x12,
    .LI .x29 (0 : Word),
    .BEQ .x29 .x6 (28 : BitVec 13),
    .ADD .x30 .x5 .x29,
    .LBU .x31 .x30 (0 : BitVec 12),
    .ADD .x7 .x28 .x29,
    .SB .x7 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def swdMinimalCopyFunction : String :=
  "swd_minimal_copy:\n" ++ emitProgram swdMinimalCopy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `swdMinimalCopy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem swdMinimalCopyFunction_eq_prog :
    swdMinimalCopyFunction = "swd_minimal_copy:\n" ++ emitProgram swdMinimalCopy_prog := rfl

#guard swdMinimalCopyFunction.startsWith "swd_minimal_copy:\n"
#guard swdMinimalCopy_prog.length = 19
/-! ## system_write_descriptors
    a0 = SSZ_BASE.  Fills (slot_key 32 B, value, value_len) for EIP-2935 and
    EIP-4788 into swd_* buffers.  a0 (output) = 0. -/
def systemWriteDescriptorsFunction : String :=
  "system_write_descriptors:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  addi s1, s0, 60             # exec_payload\n" ++
  "  # ---- EIP-2935: slot = (number-1) % 8191, value = parent_hash ----\n" ++
  "  addi a0, s1, 404; jal ra, swd_read_u64le\n" ++
  "  addi a0, a0, -1             # number - 1\n" ++
  "  li t0, 8191; remu a0, a0, t0\n" ++
  "  la a1, swd_2935_slot; jal ra, swd_write_be32_u64\n" ++
  "  mv a0, s1; li a1, 32; la a2, swd_2935_val; la a3, swd_2935_vlen\n" ++
  "  jal ra, swd_minimal_copy\n" ++
  "  # ---- EIP-4788: slot = timestamp % 8191, value = timestamp ----\n" ++
  "  addi a0, s1, 428; jal ra, swd_read_u64le\n" ++
  "  mv s2, a0                   # timestamp\n" ++
  "  li t0, 8191; remu a0, a0, t0\n" ++
  "  la a1, swd_4788_slot; jal ra, swd_write_be32_u64\n" ++
  "  mv a0, s2; la a1, swd_ts_be8; jal ra, swd_write_be8\n" ++
  "  la a0, swd_ts_be8; li a1, 8; la a2, swd_4788_val; la a3, swd_4788_vlen\n" ++
  "  jal ra, swd_minimal_copy\n" ++
  "  # ---- EIP-4788: slot = timestamp + 8191, value = parent_beacon_block_root ----\n" ++
  "  mv a0, s2; li t0, 8191; remu a0, a0, t0; add a0, a0, t0\n" ++
  "  la a1, swd_4788_root_slot; jal ra, swd_write_be32_u64\n" ++
  "  addi a0, s0, 24; li a1, 32; la a2, swd_4788_root_val; la a3, swd_4788_root_vlen\n" ++
  "  jal ra, swd_minimal_copy\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ### zisk_system_write_descriptors probe. Fed a real fixture SSZ input.
    Output: +0 swd_2935_slot(32) +32 2935_vlen +40 2935_val(32)
            +72 swd_4788_slot(32) +104 4788_vlen +112 4788_val(32)
            +144 swd_4788_root_slot(32) +176 root_vlen +184 root_val(32). -/
def ziskSystemWriteDescriptorsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000000; addi a0, a0, 18    # SSZ_BASE\n" ++
  "  jal ra, system_write_descriptors\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, swd_2935_slot; li t2, 0; \n" ++
  ".Lswp_c1:\n" ++
  "  li t3, 32; beq t2, t3, .Lswp_c1d\n" ++
  "  add t4, t1, t2; lbu t5, 0(t4); add t6, t0, t2; sb t5, 0(t6); addi t2, t2, 1; j .Lswp_c1\n" ++
  ".Lswp_c1d:\n" ++
  "  la t1, swd_2935_vlen; ld t5, 0(t1); sd t5, 32(t0)\n" ++
  "  la t1, swd_2935_val; li t2, 0\n" ++
  ".Lswp_c2:\n" ++
  "  li t3, 32; beq t2, t3, .Lswp_c2d\n" ++
  "  add t4, t1, t2; lbu t5, 0(t4); addi t6, t0, 40; add t6, t6, t2; sb t5, 0(t6); addi t2, t2, 1; j .Lswp_c2\n" ++
  ".Lswp_c2d:\n" ++
  "  la t1, swd_4788_slot; li t2, 0\n" ++
  ".Lswp_c3:\n" ++
  "  li t3, 32; beq t2, t3, .Lswp_c3d\n" ++
  "  add t4, t1, t2; lbu t5, 0(t4); addi t6, t0, 72; add t6, t6, t2; sb t5, 0(t6); addi t2, t2, 1; j .Lswp_c3\n" ++
  ".Lswp_c3d:\n" ++
  "  la t1, swd_4788_vlen; ld t5, 0(t1); sd t5, 104(t0)\n" ++
  "  la t1, swd_4788_val; li t2, 0\n" ++
  ".Lswp_c4:\n" ++
  "  li t3, 32; beq t2, t3, .Lswp_c4d\n" ++
  "  add t4, t1, t2; lbu t5, 0(t4); addi t6, t0, 112; add t6, t6, t2; sb t5, 0(t6); addi t2, t2, 1; j .Lswp_c4\n" ++
  ".Lswp_c4d:\n" ++
  "  la t1, swd_4788_root_slot; li t2, 0\n" ++
  ".Lswp_c5:\n" ++
  "  li t3, 32; beq t2, t3, .Lswp_c5d\n" ++
  "  add t4, t1, t2; lbu t5, 0(t4); addi t6, t0, 144; add t6, t6, t2; sb t5, 0(t6); addi t2, t2, 1; j .Lswp_c5\n" ++
  ".Lswp_c5d:\n" ++
  "  la t1, swd_4788_root_vlen; ld t5, 0(t1); sd t5, 176(t0)\n" ++
  "  la t1, swd_4788_root_val; li t2, 0\n" ++
  ".Lswp_c6:\n" ++
  "  li t3, 32; beq t2, t3, .Lswp_c6d\n" ++
  "  add t4, t1, t2; lbu t5, 0(t4); addi t6, t0, 184; add t6, t6, t2; sb t5, 0(t6); addi t2, t2, 1; j .Lswp_c6\n" ++
  ".Lswp_c6d:\n" ++
  "  j .Lswd_pdone\n" ++
  swdReadU64leFunction ++ "\n" ++
  swdWriteBe32U64Function ++ "\n" ++
  swdWriteBe8Function ++ "\n" ++
  swdMinimalCopyFunction ++ "\n" ++
  systemWriteDescriptorsFunction ++ "\n" ++
  ".Lswd_pdone:"

def ziskSystemWriteDescriptorsDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "swd_2935_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_2935_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_val:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "swd_2935_vlen:\n  .zero 8\n" ++
  "swd_4788_vlen:\n  .zero 8\n" ++
  "swd_4788_root_vlen:\n  .zero 8\n" ++
  "swd_ts_be8:\n  .zero 8"

def ziskSystemWriteDescriptorsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSystemWriteDescriptorsPrologue
  dataAsm     := ziskSystemWriteDescriptorsDataSection
}

end EvmAsm.Codegen
