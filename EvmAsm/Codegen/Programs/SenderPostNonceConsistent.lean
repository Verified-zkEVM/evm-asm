/-
  EvmAsm.Codegen.Programs.SenderPostNonceConsistent

  `sender_post_nonce_consistent` (bead bmvmx.1.6.3, nonce slice) — verify a tx
  sender's BAL-declared post nonce against execution: a single transaction from a
  sender increments its nonce by exactly one, so

      BAL sender post_nonce == sender pre_nonce + 1.

  This is the SENDER analog of the recipient nonce/code emptiness check (#8567),
  and it is NON-redundant with the state-root check: the guest validates the
  prover-supplied BAL against the prover-supplied header.state_root (consistency),
  so an execution-derived equality like nonce == pre + 1 catches a BAL that
  misreports the sender's post nonce. The EOA simple-transfer path already checks
  this (tx_gas_bal_post_verify status 30..32); the contract-recipient path did NOT
  (it only checked the sender balance, #8594), so this closes that gap.

  Input is the `tx_gas_sender_bal_lookup` output record (the runtime balance
  kernel's tgbpvr_lookup), whose relevant fields are:
    +80  pre nonce, u64
    +128 post nonce byte length (UINT64_MAX when the BAL omits it)
    +136 post nonce bytes, big-endian, capacity 32

  Conservative: an absent or >8-byte post nonce returns "skip" (2) rather than
  rejecting (the reverse "BAL must declare the sender nonce change" direction is a
  separate, stricter slice).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## sender_post_nonce_consistent
    a0 = tx_gas_sender_bal_lookup output record ptr
    a0 (output) = 0 consistent (post == pre+1) / 1 mismatch / 2 skip (absent or >u64).
    Leaf; clobbers t0-t5. -/
def senderPostNonceConsistent_prog : Program :=
  [ .LD .x5 .x10 (128 : BitVec 12),
    .LI .x6 (-1 : Word),
    .BEQ .x5 .x6 (80 : BitVec 13),
    .LI .x6 (8 : Word),
    .BLTU .x6 .x5 (72 : BitVec 13),
    .ADDI .x7 .x10 (136 : BitVec 12),
    .LI .x28 (0 : Word),
    .MV .x29 .x5,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x30 .x7 (0 : BitVec 12),
    .OR .x28 .x28 .x30,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LD .x29 .x10 (80 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .BEQ .x28 .x29 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def senderPostNonceConsistentFunction : String :=
  "sender_post_nonce_consistent:\n" ++ emitProgram senderPostNonceConsistent_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `senderPostNonceConsistent_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem senderPostNonceConsistentFunction_eq_prog :
    senderPostNonceConsistentFunction = "sender_post_nonce_consistent:\n" ++ emitProgram senderPostNonceConsistent_prog := rfl

#guard senderPostNonceConsistentFunction.startsWith "sender_post_nonce_consistent:\n"
/-- `zisk_sender_post_nonce_consistent`: known-answer probe over a lookup-shaped
    buffer (pre nonce @+80, post-nonce len @+128, post-nonce bytes @+136). Cases
    surfaced to OUTPUT (0xa0010000):
      +0  pre=7, post={08} (len 1)        -> 0 match (7+1==8)
      +8  pre=7, post={09} (len 1)        -> 1 mismatch
      +16 pre=7, post absent (len -1)     -> 2 skip
      +24 pre=255, post={01,00} (len 2)   -> 0 match (255+1==256, BE multi-byte) -/
def ziskSenderPostNonceConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Case A: pre=7, post len=1 bytes={8} -> match.
  "  la t0, spnc_buf\n" ++
  "  li t1, 7;  sd t1, 80(t0)\n" ++
  "  li t1, 1;  sd t1, 128(t0)\n" ++
  "  li t1, 8;  sb t1, 136(t0)\n" ++
  "  mv a0, t0; jal ra, sender_post_nonce_consistent; sd a0, 0(s0)\n" ++
  -- Case B: post bytes={9} -> mismatch.
  "  la t0, spnc_buf; li t1, 9; sb t1, 136(t0)\n" ++
  "  mv a0, t0; jal ra, sender_post_nonce_consistent; sd a0, 8(s0)\n" ++
  -- Case C: post absent (len -1) -> skip.
  "  la t0, spnc_buf; li t1, -1; sd t1, 128(t0)\n" ++
  "  mv a0, t0; jal ra, sender_post_nonce_consistent; sd a0, 16(s0)\n" ++
  -- Case D: pre=255, post len=2 bytes={0x01,0x00} (BE 256) -> match.
  "  la t0, spnc_buf\n" ++
  "  li t1, 255; sd t1, 80(t0)\n" ++
  "  li t1, 2;   sd t1, 128(t0)\n" ++
  "  li t1, 0x01; sb t1, 136(t0); li t1, 0x00; sb t1, 137(t0)\n" ++
  "  mv a0, t0; jal ra, sender_post_nonce_consistent; sd a0, 24(s0)\n" ++
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lspnc_done\n" ++
  senderPostNonceConsistentFunction ++ "\n" ++
  ".Lspnc_done:"

def ziskSenderPostNonceConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "spnc_buf:\n  .zero 176\n"


end EvmAsm.Codegen
