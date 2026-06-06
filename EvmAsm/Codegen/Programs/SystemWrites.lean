/-
  EvmAsm.Codegen.Programs.SystemWrites

  system_write_descriptors (bead evm-asm-fhsxz.2.4.2.5, steps a/b): derive the
  per-block SYSTEM-contract storage writes from the ExecutionPayload — the two
  system calls every Amsterdam block runs at block start (before withdrawals):

    * EIP-2935 (history contract 0x0000…2935):
        slot  = (block_number - 1) % 8192
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
  rlp(value) wants. The EIP-2935 storage slot is reduced modulo the 8192-entry
  history buffer before encoding the 32-byte big-endian storage key.

  Outputs feed account_apply_storage_slot (one per system contract) in the
  verdict's state recompute.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## swd_read_u64le -- read a little-endian u64 byte-wise (a0=ptr -> a0). Leaf. -/
def swdReadU64leFunction : String :=
  "swd_read_u64le:\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  lbu t1, 1(a0); slli t1, t1, 8;  or t0, t0, t1\n" ++
  "  lbu t1, 2(a0); slli t1, t1, 16; or t0, t0, t1\n" ++
  "  lbu t1, 3(a0); slli t1, t1, 24; or t0, t0, t1\n" ++
  "  lbu t1, 4(a0); slli t1, t1, 32; or t0, t0, t1\n" ++
  "  lbu t1, 5(a0); slli t1, t1, 40; or t0, t0, t1\n" ++
  "  lbu t1, 6(a0); slli t1, t1, 48; or t0, t0, t1\n" ++
  "  lbu t1, 7(a0); slli t1, t1, 56; or t0, t0, t1\n" ++
  "  mv a0, t0\n" ++
  "  ret"

/-! ## swd_write_be32_u64 -- write a0 (u64) big-endian into the LOW 8 bytes of a
    zeroed 32-byte buffer at a1 (the 32-byte storage slot key). Leaf. -/
def swdWriteBe32U64Function : String :=
  "swd_write_be32_u64:\n" ++
  "  li t0, 0\n" ++
  ".Lswd_z:\n" ++
  "  li t1, 32; beq t0, t1, .Lswd_zd\n" ++
  "  add t2, a1, t0; sb x0, 0(t2); addi t0, t0, 1; j .Lswd_z\n" ++
  ".Lswd_zd:\n" ++
  "  # write the 8 BE bytes into offsets 24..31\n" ++
  "  li t0, 0\n" ++
  ".Lswd_b:\n" ++
  "  li t1, 8; beq t0, t1, .Lswd_bd\n" ++
  "  li t2, 56; slli t3, t0, 3; sub t2, t2, t3   # shift = 56 - 8*t0\n" ++
  "  srl t4, a0, t2; andi t4, t4, 0xff\n" ++
  "  addi t5, a1, 24; add t5, t5, t0; sb t4, 0(t5)\n" ++
  "  addi t0, t0, 1; j .Lswd_b\n" ++
  ".Lswd_bd:\n" ++
  "  ret"

/-! ## swd_write_be8 -- write a0 (u64) big-endian into 8 bytes at a1. Leaf. -/
def swdWriteBe8Function : String :=
  "swd_write_be8:\n" ++
  "  li t0, 0\n" ++
  ".Lswd8:\n" ++
  "  li t1, 8; beq t0, t1, .Lswd8d\n" ++
  "  li t2, 56; slli t3, t0, 3; sub t2, t2, t3\n" ++
  "  srl t4, a0, t2; andi t4, t4, 0xff\n" ++
  "  add t5, a1, t0; sb t4, 0(t5)\n" ++
  "  addi t0, t0, 1; j .Lswd8\n" ++
  ".Lswd8d:\n" ++
  "  ret"

/-! ## swd_minimal_copy -- copy src[a0..a0+a1) stripping leading zero bytes into
    a2; write the resulting length to a3. Leaf. -/
def swdMinimalCopyFunction : String :=
  "swd_minimal_copy:\n" ++
  "  mv t0, a0                   # src cursor\n" ++
  "  mv t1, a1                   # remaining\n" ++
  ".Lswd_skip:\n" ++
  "  beqz t1, .Lswd_emit         # all zero -> length 0\n" ++
  "  lbu t2, 0(t0); bnez t2, .Lswd_emit\n" ++
  "  addi t0, t0, 1; addi t1, t1, -1; j .Lswd_skip\n" ++
  ".Lswd_emit:\n" ++
  "  sd t1, 0(a3)                # out length = remaining\n" ++
  "  mv t3, a2; li t4, 0\n" ++
  ".Lswd_cp:\n" ++
  "  beq t4, t1, .Lswd_cpd\n" ++
  "  add t5, t0, t4; lbu t6, 0(t5); add t2, t3, t4; sb t6, 0(t2)\n" ++
  "  addi t4, t4, 1; j .Lswd_cp\n" ++
  ".Lswd_cpd:\n" ++
  "  ret"

/-! ## system_write_descriptors
    a0 = SSZ_BASE.  Fills (slot_key 32 B, value, value_len) for EIP-2935 and
    EIP-4788 into swd_* buffers.  a0 (output) = 0. -/
def systemWriteDescriptorsFunction : String :=
  "system_write_descriptors:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  addi s1, s0, 60             # exec_payload\n" ++
  "  # ---- EIP-2935: slot = (number-1) % 8192, value = parent_hash ----\n" ++
  "  addi a0, s1, 404; jal ra, swd_read_u64le\n" ++
  "  addi a0, a0, -1             # number - 1\n" ++
  "  li t0, 8192; remu a0, a0, t0\n" ++
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
