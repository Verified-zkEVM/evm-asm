/-
  EvmAsm.Codegen.Programs.EIP7708Logs

  Synthetic Amsterdam EIP-7708 Transfer/Burn event-log descriptor helpers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

private def copyWordAsm (src : String) (dstOff : Nat) : String :=
  "  ld t3, 0(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString dstOff ++ "(t2)\n" ++
  "  ld t3, 8(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString (dstOff + 8) ++ "(t2)\n" ++
  "  ld t3, 16(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString (dstOff + 16) ++ "(t2)\n" ++
  "  ld t3, 24(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString (dstOff + 24) ++ "(t2)\n"

/-! ## EIP-7708 synthetic event-log descriptors

    `eip7708_append_synthetic_log` appends one descriptor in the same bounded
    256-byte shape used by the runtime LOG0..LOG4 capture path:

      +0   topic count (2 for Burn, 3 for Transfer)
      +8   memory offset low u64 (0 for synthetic logs)
      +16  memory size low u64 (32)
      +24  copied data length (32)
      +32  topic0 hash
      +64  topic1 account/sender word
      +96  topic2 recipient word for Transfer
      +160 32-byte amount data, canonical big-endian
      +192 SYSTEM_ADDRESS context word

    Calling convention:

      x20        : env ptr whose +472 cell is the event-log descriptor count
      a0         : topic count, 2 or 3
      a1         : topic0 ptr, descriptor word order
      a2         : topic1 ptr, descriptor word order
      a3         : topic2 ptr, descriptor word order; ignored for topic count 2
      a4         : amount EVM-word ptr, descriptor word order
      a0 output  : 0 success/no-op, 1 descriptor buffer overflow,
                   2 invalid topic count

    Amount zero is a successful no-op, matching execution-specs'
    `emit_transfer_log` / `emit_burn_log` early return. -/
def eip7708SyntheticLogFunctions : String :=
  "eip7708_append_synthetic_log:\n" ++
  "  ld t0, 0(a4)\n" ++
  "  ld t1, 8(a4)\n" ++
  "  or t0, t0, t1\n" ++
  "  ld t1, 16(a4)\n" ++
  "  or t0, t0, t1\n" ++
  "  ld t1, 24(a4)\n" ++
  "  or t0, t0, t1\n" ++
  "  beqz t0, .Leip7708_success\n" ++
  "  li t0, 2\n" ++
  "  bltu a0, t0, .Leip7708_bad_topic_count\n" ++
  "  li t0, 3\n" ++
  "  bgtu a0, t0, .Leip7708_bad_topic_count\n" ++
  "  ld t0, 472(x20)\n" ++
  "  li t1, 16\n" ++
  "  bgeu t0, t1, .Leip7708_overflow\n" ++
  "  la t2, evm_event_logs\n" ++
  "  slli t1, t0, 8\n" ++
  "  add t2, t2, t1\n" ++
  "  mv t0, t2\n" ++
  "  li t1, 32\n" ++
  ".Leip7708_zero_loop:\n" ++
  "  sd x0, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Leip7708_zero_loop\n" ++
  "  sd a0, 0(t2)\n" ++
  "  li t0, 32\n" ++
  "  sd t0, 16(t2)\n" ++
  "  sd t0, 24(t2)\n" ++
  copyWordAsm "a1" 32 ++
  copyWordAsm "a2" 64 ++
  "  li t0, 3\n" ++
  "  bne a0, t0, .Leip7708_amount_data\n" ++
  copyWordAsm "a3" 96 ++
  ".Leip7708_amount_data:\n" ++
  "  addi t0, a4, 31\n" ++
  "  addi t1, t2, 160\n" ++
  "  li t3, 32\n" ++
  ".Leip7708_amount_rev:\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  sb t4, 0(t1)\n" ++
  "  addi t0, t0, -1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  bnez t3, .Leip7708_amount_rev\n" ++
  "  li t0, -2\n" ++
  "  sd t0, 192(t2)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 200(t2)\n" ++
  "  li t0, 0xffffffff\n" ++
  "  sd t0, 208(t2)\n" ++
  "  sd x0, 216(t2)\n" ++
  "  sd x0, 224(t2)\n" ++
  "  sd x0, 232(t2)\n" ++
  "  sd x0, 240(t2)\n" ++
  "  sd x0, 248(t2)\n" ++
  "  ld t0, 472(x20)\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 472(x20)\n" ++
  ".Leip7708_success:\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Leip7708_overflow:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Leip7708_bad_topic_count:\n" ++
  "  li a0, 2\n" ++
  "  ret\n" ++
  "\n" ++
  "eip7708_append_transfer_log:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  li a0, 3\n" ++
  "  la a1, eip7708_transfer_topic\n" ++
  "  mv a2, s0\n" ++
  "  mv a3, s1\n" ++
  "  mv a4, s2\n" ++
  "  jal ra, eip7708_append_synthetic_log\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n" ++
  "\n" ++
  "eip7708_append_burn_log:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  li a0, 2\n" ++
  "  la a1, eip7708_burn_topic\n" ++
  "  mv a2, s0\n" ++
  "  mv a3, x0\n" ++
  "  mv a4, s1\n" ++
  "  jal ra, eip7708_append_synthetic_log\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret\n"

def eip7708SyntheticLogTopicData : String :=
  ".balign 8\n" ++
  "eip7708_transfer_topic:\n" ++
  "  .quad 0x28f55a4df523b3ef, 0x952ba7f163c4a116\n" ++
  "  .quad 0x69c2b068fc378daa, 0xddf252ad1be2c89b\n" ++
  "eip7708_burn_topic:\n" ++
  "  .quad 0x71a0fdb75d397ca5, 0x6cffcc184412cf7a\n" ++
  "  .quad 0x815c1ee09dbd0673, 0xcc16f5dbb4873280\n"

def eip7708SyntheticLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 624\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 4096\n" ++
  eip7708SyntheticLogTopicData ++
  "eip7708_probe_sender:\n" ++
  "  .quad 0x1111111111111111, 0x1111111111111111, 0x0000000011111111, 0\n" ++
  "eip7708_probe_recipient:\n" ++
  "  .quad 0x2222222222222222, 0x2222222222222222, 0x0000000022222222, 0\n" ++
  "eip7708_probe_account:\n" ++
  "  .quad 0x3333333333333333, 0x3333333333333333, 0x0000000033333333, 0\n" ++
  "eip7708_probe_amount_transfer:\n" ++
  "  .quad 0x8877665544332211, 0xffeeddccbbaa9900, 0x0123456789abcdef, 0xfedcba9876543210\n" ++
  "eip7708_probe_amount_burn:\n" ++
  "  .quad 0x0000000000000005, 0, 0, 0\n" ++
  "eip7708_probe_amount_zero:\n" ++
  "  .zero 32\n"

/-- `zisk_eip7708_synthetic_logs`: probe BuildUnit.

    The first input byte at `INPUT_ADDR + 16` selects mode:
      0/default : append one Transfer log and output its 256-byte descriptor
      1         : append one Burn log and output its 256-byte descriptor
      2         : call the zero-amount Transfer helper and output
                  `{status:u64, descriptor_count:u64}`.

    The split modes keep each check within ziskemu's fixed 256-byte public
    output while still validating the full descriptor shape. -/
def ziskEip7708SyntheticLogsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, evm_env\n" ++
  "  li t0, 0x40000010\n" ++
  "  lbu t1, 0(t0)\n" ++
  "  li t2, 1\n" ++
  "  beq t1, t2, .Leip7708_probe_burn\n" ++
  "  li t2, 2\n" ++
  "  beq t1, t2, .Leip7708_probe_zero\n" ++
  "  la a0, eip7708_probe_sender\n" ++
  "  la a1, eip7708_probe_recipient\n" ++
  "  la a2, eip7708_probe_amount_transfer\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  j .Leip7708_probe_copy_desc\n" ++
  ".Leip7708_probe_burn:\n" ++
  "  la a0, eip7708_probe_account\n" ++
  "  la a1, eip7708_probe_amount_burn\n" ++
  "  jal ra, eip7708_append_burn_log\n" ++
  "  j .Leip7708_probe_copy_desc\n" ++
  ".Leip7708_probe_zero:\n" ++
  "  la a0, eip7708_probe_sender\n" ++
  "  la a1, eip7708_probe_recipient\n" ++
  "  la a2, eip7708_probe_amount_zero\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  ld t1, 472(x20)\n" ++
  "  sd t1, 8(t0)\n" ++
  "  j .Leip7708_probe_done\n" ++
  ".Leip7708_probe_copy_desc:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, evm_event_logs\n" ++
  "  li t2, 32\n" ++
  ".Leip7708_probe_copy:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Leip7708_probe_copy\n" ++
  "  j .Leip7708_probe_done\n" ++
  eip7708SyntheticLogFunctions ++
  ".Leip7708_probe_done:"

def ziskEip7708SyntheticLogsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7708SyntheticLogsPrologue
  dataAsm     := eip7708SyntheticLogDataSection
}

end EvmAsm.Codegen
