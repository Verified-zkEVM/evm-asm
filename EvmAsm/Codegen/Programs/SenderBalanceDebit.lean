/-
  EvmAsm.Codegen.Programs.SenderBalanceDebit

  `sender_debit_from_gas` (bead bmvmx.1.6.3, balance slice) — compute a transaction
  sender's net balance debit from the runtime gas result, for the exec-vs-BAL balance
  compare. Per execution-specs amsterdam (process_transaction settlement), the sender
  is charged `receipt_inc * effective_gas_price + value`, where receipt_inc is the
  EIP-3529-refunded, EIP-7623-floored gas — exactly the `a2` output of
  `tx_gas_result_increments` (Account.lean). (The `a1`/block_inc output is the block
  gas_used, NOT the sender charge; c2 consumes that for the EIP-7778 accumulator.)

  This wraps the proven helper so the verdict's contract-recipient balance check
  matches the spec settlement without re-deriving the refund/floor math.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## sender_debit_from_gas

    Calling convention:
      a0 = tx gas_limit (u64)            a1 = gas_left after execution (u64)
      a2 = refund_counter (u64)          a3 = calldata_floor_gas_cost (u64)
      a4 = effective_gas_price ptr (32-byte big-endian)
      a5 = value ptr (32-byte big-endian)
      a6 = out debit ptr (32-byte big-endian)
    Effect:
      *a6 = receipt_inc * effective_gas_price + value, where receipt_inc =
            tx_gas_result_increments(a0..a3).a2.
    Preserves s0..s2 (saved). -/
def senderDebitFromGas_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x14,
    .MV .x9 .x15,
    .MV .x18 .x16,
    .JAL .x1 (jalOff GuestAddrs.tx_gas_result_increments (GuestAddrs.sender_debit_from_gas + 32)),
    .MV .x11 .x12,
    .MV .x10 .x8,
    .AUIPC .x12 (laHi GuestAddrs.sdfg_gascost (GuestAddrs.sender_debit_from_gas + 44)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sdfg_gascost (GuestAddrs.sender_debit_from_gas + 44)),
    .JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be (GuestAddrs.sender_debit_from_gas + 52)),
    .AUIPC .x10 (laHi GuestAddrs.sdfg_gascost (GuestAddrs.sender_debit_from_gas + 56)),
    .ADDI .x10 .x10 (laLo GuestAddrs.sdfg_gascost (GuestAddrs.sender_debit_from_gas + 56)),
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.sender_debit_from_gas + 72)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `senderDebitFromGas_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def senderDebitFromGas_relocs : RelocTable :=
  [ (8, .jal .x1 "tx_gas_result_increments"),
    (11, .la .x12 "sdfg_gascost"),
    (13, .jal .x1 "u256_mul_u64_be"),
    (14, .la .x10 "sdfg_gascost"),
    (18, .jal .x1 "u256_add_be") ]

def senderDebitFromGasFunction : String :=
  "sender_debit_from_gas:\n" ++ emitProgramR senderDebitFromGas_prog senderDebitFromGas_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `senderDebitFromGas_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem senderDebitFromGasFunction_eq_prog :
    senderDebitFromGasFunction = "sender_debit_from_gas:\n" ++ emitProgramR senderDebitFromGas_prog senderDebitFromGas_relocs := rfl

#guard senderDebitFromGasFunction.startsWith "sender_debit_from_gas:\n"
def senderDebitFromGasData : String :=
  ".balign 32\n" ++
  "sdfg_gascost:\n  .zero 32\n"

/-- `zisk_sender_debit_from_gas`: known-answer probe. gas_limit=100000, gas_left=78000,
    refund=5000, floor=21000 → before_refund=22000, refund_cap=4400, after_refund=17600,
    receipt_inc=max(17600,21000)=21000. With eff_gas_price=1, value=0: debit=21000 (0x5208).
    Output (0xa0010000): +0 receipt_inc (21000); +8 debit[31] (0x08); +16 debit[30] (0x52);
    +24 debit[0] high byte (0). -/
def ziskSenderDebitFromGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- eff_gas_price = 1 (32B BE: byte31 = 1), value = 0.
  "  la t0, sdfg_egp\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 1; sb t1, 31(t0)\n" ++
  "  la t0, sdfg_val\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  -- direct receipt_inc.
  "  li a0, 100000; li a1, 78000; li a2, 5000; li a3, 21000\n" ++
  "  jal ra, tx_gas_result_increments\n" ++
  "  sd a2, 0(s0)\n" ++                          -- receipt_inc
  -- sender_debit_from_gas.
  "  li a0, 100000; li a1, 78000; li a2, 5000; li a3, 21000\n" ++
  "  la a4, sdfg_egp; la a5, sdfg_val; la a6, sdfg_out\n" ++
  "  jal ra, sender_debit_from_gas\n" ++
  "  la t0, sdfg_out\n" ++
  "  lbu t1, 31(t0); sd t1, 8(s0)\n" ++          -- debit low byte 0x08
  "  lbu t1, 30(t0); sd t1, 16(s0)\n" ++         -- debit next byte 0x52
  "  lbu t1, 0(t0);  sd t1, 24(s0)\n" ++         -- debit high byte 0
  "  j .Lsdfg_done\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  senderDebitFromGasFunction ++ "\n" ++
  ".Lsdfg_done:"

def ziskSenderDebitFromGasDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "sdfg_egp:\n  .zero 32\n" ++
  "sdfg_val:\n  .zero 32\n" ++
  "sdfg_out:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++   -- u256_mul_u64_be scratch
  senderDebitFromGasData


end EvmAsm.Codegen
