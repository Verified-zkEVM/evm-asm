/-
  EvmAsm.Codegen.Programs.TxRefund

  Transaction-level refund cap helpers for Amsterdam gas accounting.
-/

import EvmAsm.Codegen.Layout
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
def txRefundCapFunction : String :=
  "tx_refund_cap:\n" ++
  "  bltu a0, a1, .Ltrc_invalid\n" ++
  "  sub t0, a0, a1              # gas_used_before_refund\n" ++
  "  sd t0, 0(a3)\n" ++
  "  li t1, 5\n" ++
  "  divu t2, t0, t1             # one-fifth cap\n" ++
  "  sd t2, 8(a3)\n" ++
  "  mv t3, a2\n" ++
  "  bltu t2, t3, .Ltrc_use_cap\n" ++
  "  mv t4, t3\n" ++
  "  j .Ltrc_apply\n" ++
  ".Ltrc_use_cap:\n" ++
  "  mv t4, t2\n" ++
  ".Ltrc_apply:\n" ++
  "  sd t4, 16(a3)\n" ++
  "  sub t5, t0, t4\n" ++
  "  sd t5, 24(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Ltrc_invalid:\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 8(a3)\n" ++
  "  sd zero, 16(a3)\n" ++
  "  sd zero, 24(a3)\n" ++
  "  li a0, 1\n" ++
  "  ret"

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
