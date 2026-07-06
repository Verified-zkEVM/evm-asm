/-
  EvmAsm.Codegen.Programs.TxRefund

  Transaction-level refund cap helpers for Amsterdam gas accounting.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_refund_cap

    Amsterdam applies the EIP-3529 refund cap after EVM execution:

      gas_used_before_refund = tx.gas - tx_output.gas_left
      gas_refund = min(gas_used_before_refund / 5, refund_counter)
      gas_used_after_refund = gas_used_before_refund - gas_refund

    Calling convention:
      a0 input  : tx gas limit
      a1 input  : gas left after execution
      a2 input  : refund counter
      a3 input  : output ptr, four u64 words:
                    +0  gas_used_before_refund
                    +8  refund cap (before_refund / 5)
                    +16 applied refund
                    +24 gas_used_after_refund
      a0 output : 0 success, 1 invalid gas_left > tx_gas_limit
-/
def txRefundCap_prog : Program :=
  [ .BLTU .x10 .x11 (64 : BitVec 13),
    .SUB .x5 .x10 .x11,
    .SD .x13 .x5 (0 : BitVec 12),
    .LI .x6 (5 : Word),
    .DIVU .x7 .x5 .x6,
    .SD .x13 .x7 (8 : BitVec 12),
    .MV .x28 .x12,
    .BLTU .x7 .x28 (12 : BitVec 13),
    .MV .x29 .x28,
    .JAL .x0 (8 : BitVec 21),
    .MV .x29 .x7,
    .SD .x13 .x29 (16 : BitVec 12),
    .SUB .x30 .x5 .x29,
    .SD .x13 .x30 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x13 .x0 (0 : BitVec 12),
    .SD .x13 .x0 (8 : BitVec 12),
    .SD .x13 .x0 (16 : BitVec 12),
    .SD .x13 .x0 (24 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def txRefundCapFunction : String :=
  "tx_refund_cap:\n" ++ emitProgram txRefundCap_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `txRefundCap_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem txRefundCapFunction_eq_prog :
    txRefundCapFunction = "tx_refund_cap:\n" ++ emitProgram txRefundCap_prog := rfl

#guard txRefundCapFunction.startsWith "tx_refund_cap:\n"
#guard txRefundCap_prog.length = 22
/-- `zisk_tx_refund_cap`: probe BuildUnit.

    Input: 24 bytes `(tx_gas_limit, gas_left, refund_counter)`.
    Output: status followed by the four `tx_refund_cap` output words. -/
def ziskTxRefundCapPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0, 8(t0)\n" ++
  "  ld a1, 16(t0)\n" ++
  "  ld a2, 24(t0)\n" ++
  "  li a3, 0xa0010008\n" ++
  "  jal ra, tx_refund_cap\n" ++
  "  li t1, 0xa0010000\n" ++
  "  sd a0, 0(t1)\n" ++
  "  j .Ltrc_probe_done\n" ++
  txRefundCapFunction ++ "\n" ++
  ".Ltrc_probe_done:"

def ziskTxRefundCapProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxRefundCapPrologue
}

end EvmAsm.Codegen
