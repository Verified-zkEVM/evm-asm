/-
  EvmAsm.Codegen.Programs.MultiTxSenderDebit

  Focused helper for the bmvmx.5.5.2.2 B2 cumulative-balance chain.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## multi_tx_running_sender_balance_step

    One update step for the B2.2 per-sender running-balance table. Entries are
    64 bytes: sender address lane at +0, running u256 BE balance at +32.
    Return status: 0 updated, 1 underflow, 2 table full.
-/
def multiTxRunningSenderBalanceStep_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .LD .x5 .x9 (0 : BitVec 12),
    .LI .x6 (0 : Word),
    .BGEU .x6 .x5 (brOff (GuestAddrs.multi_tx_running_sender_balance_step + 152) (GuestAddrs.multi_tx_running_sender_balance_step + 64)),
    .SLLI .x7 .x6 (6 : BitVec 6),
    .ADD .x7 .x8 .x7,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (40 : BitVec 13),
    .ADD .x30 .x7 .x28,
    .LBU .x30 .x30 (0 : BitVec 12),
    .ADD .x31 .x19 .x28,
    .LBU .x31 .x31 (0 : BitVec 12),
    .BNE .x30 .x31 (12 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-56 : BitVec 21),
    .ADDI .x10 .x7 (32 : BitVec 12),
    .MV .x11 .x21,
    .ADDI .x12 .x7 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.multi_tx_running_sender_balance_step + 136)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.multi_tx_running_sender_balance_step + 264) (GuestAddrs.multi_tx_running_sender_balance_step + 140)),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.multi_tx_running_sender_balance_step + 276) (GuestAddrs.multi_tx_running_sender_balance_step + 148)),
    .BGEU .x5 .x18 (brOff (GuestAddrs.multi_tx_running_sender_balance_step + 272) (GuestAddrs.multi_tx_running_sender_balance_step + 152)),
    .SLLI .x7 .x5 (6 : BitVec 6),
    .ADD .x7 .x8 .x7,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (28 : BitVec 13),
    .ADD .x30 .x19 .x28,
    .LBU .x30 .x30 (0 : BitVec 12),
    .ADD .x31 .x7 .x28,
    .SB .x31 .x30 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x29 (32 : Word),
    .BEQ .x28 .x29 (20 : BitVec 13),
    .ADD .x31 .x7 .x28,
    .SB .x31 .x0 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .ADDI .x12 .x7 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.multi_tx_running_sender_balance_step + 236)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (28 : BitVec 21),
    .LD .x5 .x9 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `multiTxRunningSenderBalanceStep_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def multiTxRunningSenderBalanceStep_relocs : RelocTable :=
  [ (34, .jal .x1 "u256_sub_be"),
    (59, .jal .x1 "u256_sub_be") ]

def multiTxRunningSenderBalanceStepFunction : String :=
  "multi_tx_running_sender_balance_step:\n" ++ emitProgramR multiTxRunningSenderBalanceStep_prog multiTxRunningSenderBalanceStep_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `multiTxRunningSenderBalanceStep_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem multiTxRunningSenderBalanceStepFunction_eq_prog :
    multiTxRunningSenderBalanceStepFunction = "multi_tx_running_sender_balance_step:\n" ++ emitProgramR multiTxRunningSenderBalanceStep_prog multiTxRunningSenderBalanceStep_relocs := rfl

#guard multiTxRunningSenderBalanceStepFunction.startsWith "multi_tx_running_sender_balance_step:\n"
/-! ## multi_tx_sequential_sender_state_step

    Verdict-neutral state-threading substrate for the sequential multi-tx path.
    The caller supplies the sender's block-start balance for a new table entry,
    the current transaction's upfront cost, and the settled debit to apply after
    that transaction.  The helper deliberately is not called by block_verdict
    yet: the supported-shape whitelist and execution-derived log/deposit checks
    must land before this state can admit a new block shape.

    Entries retain the existing 64-byte `{address, running_balance}` layout.
    Return status: 0 updated, 1 upfront unaffordable, 2 settled debit underflow,
    3 table full. -/
/-! Probe-only local PC placeholder. -/
def multiTxSequentialSenderStateStepPc : Nat := 0x80000000

def multiTxSequentialSenderStateStep_prog : Program :=
  [ .ADDI .x2 .x2 (-88 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x23 .x17,
    .LD .x5 .x9 (0 : BitVec 12),
    .LI .x6 (0 : Word),
    .BGEU .x6 .x5 (brOff (multiTxSequentialSenderStateStepPc + 148) (multiTxSequentialSenderStateStepPc + 80)),
    .SLLI .x7 .x6 (6 : BitVec 6),
    .ADD .x7 .x8 .x7,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (40 : BitVec 13),
    .ADD .x30 .x7 .x28,
    .LBU .x30 .x30 (0 : BitVec 12),
    .ADD .x31 .x19 .x28,
    .LBU .x31 .x31 (0 : BitVec 12),
    .BNE .x30 .x31 (12 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-56 : BitVec 21),
    .SD .x2 .x0 (80 : BitVec 12),
    .JAL .x0 (jalOff (multiTxSequentialSenderStateStepPc + 244) (multiTxSequentialSenderStateStepPc + 144)),
    .BGEU .x5 .x18 (brOff (multiTxSequentialSenderStateStepPc + 340) (multiTxSequentialSenderStateStepPc + 148)),
    .LI .x29 (1 : Word),
    .SD .x2 .x29 (80 : BitVec 12),
    .SLLI .x7 .x5 (6 : BitVec 6),
    .ADD .x7 .x8 .x7,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (28 : BitVec 13),
    .ADD .x30 .x19 .x28,
    .LBU .x30 .x30 (0 : BitVec 12),
    .ADD .x31 .x7 .x28,
    .SB .x31 .x30 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x28 (0 : Word),
    .LI .x29 (32 : Word),
    .BEQ .x28 .x29 (32 : BitVec 13),
    .ADD .x30 .x20 .x28,
    .LBU .x30 .x30 (0 : BitVec 12),
    .ADD .x31 .x7 .x28,
    .ADDI .x31 .x31 (32 : BitVec 12),
    .SB .x31 .x30 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SD .x2 .x7 (72 : BitVec 12),
    .ADDI .x10 .x7 (32 : BitVec 12),
    .MV .x11 .x21,
    .MV .x12 .x23,
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (multiTxSequentialSenderStateStepPc + 260)),
    .LD .x5 .x23 (0 : BitVec 12),
    .BNE .x5 .x0 (brOff (multiTxSequentialSenderStateStepPc + 332) (multiTxSequentialSenderStateStepPc + 268)),
    .LD .x7 .x2 (72 : BitVec 12),
    .ADDI .x10 .x7 (32 : BitVec 12),
    .MV .x11 .x22,
    .ADDI .x12 .x7 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (multiTxSequentialSenderStateStepPc + 288)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (44 : BitVec 21),
    .LD .x5 .x2 (80 : BitVec 12),
    .BEQ .x5 .x0 (16 : BitVec 13),
    .LD .x5 .x9 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (3 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (88 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `multiTxSequentialSenderStateStep_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def multiTxSequentialSenderStateStep_relocs : RelocTable :=
  [ (65, .jal .x1 "u256_lt_be"),
    (72, .jal .x1 "u256_sub_be") ]

def multiTxSequentialSenderStateStepFunction : String :=
  "multi_tx_sequential_sender_state_step:\n" ++ emitProgramR multiTxSequentialSenderStateStep_prog multiTxSequentialSenderStateStep_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `multiTxSequentialSenderStateStep_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem multiTxSequentialSenderStateStepFunction_eq_prog :
    multiTxSequentialSenderStateStepFunction = "multi_tx_sequential_sender_state_step:\n" ++ emitProgramR multiTxSequentialSenderStateStep_prog multiTxSequentialSenderStateStep_relocs := rfl

#guard multiTxSequentialSenderStateStepFunction.startsWith "multi_tx_sequential_sender_state_step:\n"
#guard multiTxSequentialSenderStateStepFunction.startsWith "multi_tx_sequential_sender_state_step:\n"

/- Probe input after zisk length: +8 row_count, then 128-byte rows
   (sender lane, pre balance, upfront cost, settled debit). Output: status,
   count, then table. -/
def ziskMultiTxRunningSenderBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  sd zero, 0(s1); sd zero, 8(s1)\n" ++
  "  la t0, mtxrb_count; sd zero, 0(t0)\n" ++
  "  ld s2, 8(s0)                 # row_count\n" ++
  "  li s3, 0                     # i\n" ++
  ".Lmtxrb_probe_loop:\n" ++
  "  bgeu s3, s2, .Lmtxrb_probe_done_rows\n" ++
  "  li t0, 128; mul t0, s3, t0; addi t0, t0, 16; add s4, s0, t0\n" ++
  "  la a0, mtxrb_table; la a1, mtxrb_count; li a2, " ++ toString bvMtxSenderBalanceEntries ++ "; mv a3, s4; addi a4, s4, 32; addi a5, s4, 64; addi a6, s4, 96; la a7, mtxrb_lt\n" ++
  "  jal ra, multi_tx_sequential_sender_state_step\n" ++
  "  bnez a0, .Lmtxrb_probe_status\n" ++
  "  addi s3, s3, 1; j .Lmtxrb_probe_loop\n" ++
  ".Lmtxrb_probe_done_rows:\n" ++
  "  li a0, 0\n" ++
  ".Lmtxrb_probe_status:\n" ++
  "  sd a0, 0(s1)\n" ++
  "  la t0, mtxrb_count; ld t0, 0(t0); sd t0, 8(s1)\n" ++
  "  la t1, mtxrb_table; addi t2, s1, 16; li t3, 0; li t4, 240   # remaining 256-byte probe output window\n" ++
  ".Lmtxrb_probe_copy:\n" ++
  "  beq t3, t4, .Lmtxrb_probe_done\n" ++
  "  add t5, t1, t3; lbu t5, 0(t5); add t6, t2, t3; sb t5, 0(t6); addi t3, t3, 1; j .Lmtxrb_probe_copy\n" ++
  ".Lmtxrb_probe_done:\n" ++
  "  j .Lmtxrb_probe_exit\n" ++
  u256SubBeFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  multiTxRunningSenderBalanceStepFunction ++ "\n" ++
  multiTxSequentialSenderStateStepFunction ++ "\n" ++
  ".Lmtxrb_probe_exit:"

def ziskMultiTxRunningSenderBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mtxrb_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "mtxrb_table:\n  .zero " ++ toString bvMtxSenderBalanceTableBytes ++ "\n" ++
  "mtxrb_lt:\n  .zero 8\n"


end EvmAsm.Codegen
