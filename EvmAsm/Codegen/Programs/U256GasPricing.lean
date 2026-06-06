/-
  EvmAsm.Codegen.Programs.U256GasPricing

  EIP-1559 gas-pricing composites over the U256-BE arithmetic helpers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## priority_fee_per_gas_eip1559 -- PR-K62

    Compute the effective priority fee per gas for a post-EIP-1559
    transaction. Mirrors Python's
    `transaction_priority_fee_per_gas` from
    `forks/amsterdam/transaction_helpers.py`:

      surplus = tx.max_fee_per_gas - block.base_fee_per_gas
      priority_fee = min(tx.max_priority_fee_per_gas, surplus)

    Where `surplus = max_fee - base_fee` would underflow
    (`max_fee < base_fee`), the tx is invalid; this helper
    returns `1` so the caller can reject without inspecting the
    output. Otherwise returns `0` and the 32-byte priority fee
    is written to `*out` in big-endian.

    First higher-level helper composed on the K-stack's u256
    toolkit: PR-K52 `u256_sub_be` + PR-K59 `u256_min`. Both are
    inlined into the probe BuildUnit so this PR doesn't require
    any new external symbols.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : max_priority_fee_per_gas ptr (32 B BE)
      a1 (input)  : max_fee_per_gas ptr (32 B BE)
      a2 (input)  : base_fee_per_gas ptr (32 B BE)
      a3 (input)  : output ptr (32 B BE; receives priority fee)
      ra (input)  : return
      a0 (output) : 0 success / 1 max_fee < base_fee (reject tx). -/
def priorityFeePerGasEip1559Function : String :=
  "priority_fee_per_gas_eip1559:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # max_priority ptr\n" ++
  "  mv s1, a1                   # max_fee ptr\n" ++
  "  mv s2, a2                   # base_fee ptr\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  # surplus = max_fee - base_fee  (store in out)\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s3\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lpfee_fail        # borrow -> max_fee < base_fee\n" ++
  "  # priority_fee = min(max_priority, surplus); aliasing OK\n" ++
  "  mv a0, s0; mv a1, s3; mv a2, s3\n" ++
  "  jal ra, u256_min\n" ++
  "  li a0, 0\n" ++
  "  j .Lpfee_ret\n" ++
  ".Lpfee_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpfee_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_priority_fee_per_gas_eip1559`: probe BuildUnit. Reads
    (32B max_priority, 32B max_fee, 32B base_fee) from host
    input, writes (status, 32B priority fee BE) to OUTPUT (40
    bytes total). -/
def ziskPriorityFeePerGasEip1559Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # max_priority ptr\n" ++
  "  addi a1, a4, 40             # max_fee ptr\n" ++
  "  addi a2, a4, 72             # base_fee ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Lpfee_zout:\n" ++
  "  beqz t1, .Lpfee_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lpfee_zout\n" ++
  ".Lpfee_zout_done:\n" ++
  "  jal ra, priority_fee_per_gas_eip1559\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpfee_pdone\n" ++
  u256SubBeFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  ".Lpfee_pdone:"

def ziskPriorityFeePerGasEip1559DataSection : String :=
  ".section .data\n" ++
  "pfee_pad:\n" ++
  "  .zero 8"

def ziskPriorityFeePerGasEip1559ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskPriorityFeePerGasEip1559Prologue
  dataAsm     := ziskPriorityFeePerGasEip1559DataSection
}

/-! ## effective_gas_price_eip1559 -- PR-K70

    Compute the effective gas price for an EIP-1559 transaction:

      effective_gas_price = base_fee
                           + min(max_priority_fee, max_fee - base_fee)

    Equivalent (per Python `transaction_effective_gas_price`):

      effective_gas_price = min(max_fee, base_fee + max_priority_fee)

    The two formulations match because
    `base + min(max_priority, max_fee - base) =
     min(base + max_priority, max_fee)`.

    Composes PR-K62 `priority_fee_per_gas_eip1559` (#5612) with
    PR-K51 `u256_add_be`. The priority-fee step writes its
    result to `out`; the add step folds `base_fee` in place.

    If `max_fee < base_fee` (would-underflow in the priority-fee
    step), this helper returns `1` so the caller can reject the
    tx without inspecting the output.

    Calling convention:
      a0 (input)  : max_priority_fee_per_gas ptr (32 B BE)
      a1 (input)  : max_fee_per_gas ptr (32 B BE)
      a2 (input)  : base_fee_per_gas ptr (32 B BE)
      a3 (input)  : output ptr (32 B BE; receives effective gas price)
      ra (input)  : return
      a0 (output) : 0 success / 1 max_fee < base_fee (reject tx). -/
def effectiveGasPriceEip1559Function : String :=
  "effective_gas_price_eip1559:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # base_fee ptr\n" ++
  "  mv s1, a3                   # out ptr\n" ++
  "  # Step 1: priority_fee = priority_fee_per_gas_eip1559(...)\n" ++
  "  jal ra, priority_fee_per_gas_eip1559\n" ++
  "  bnez a0, .Legpe_fail\n" ++
  "  # Step 2: effective = base_fee + priority_fee   (out = base + out)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be         # overflow flag in a0 (always 0 in practice)\n" ++
  "  li a0, 0\n" ++
  "  j .Legpe_ret\n" ++
  ".Legpe_fail:\n" ++
  "  li a0, 1\n" ++
  ".Legpe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_effective_gas_price_eip1559`: probe BuildUnit. Reads
    (max_priority, max_fee, base_fee) from host input, writes
    (status, effective_gas_price) to OUTPUT (40 bytes). -/
def ziskEffectiveGasPriceEip1559Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # max_priority ptr\n" ++
  "  addi a1, a4, 40             # max_fee ptr\n" ++
  "  addi a2, a4, 72             # base_fee ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Legpe_zout:\n" ++
  "  beqz t1, .Legpe_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Legpe_zout\n" ++
  ".Legpe_zout_done:\n" ++
  "  jal ra, effective_gas_price_eip1559\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Legpe_pdone\n" ++
  u256SubBeFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  effectiveGasPriceEip1559Function ++ "\n" ++
  ".Legpe_pdone:"

def ziskEffectiveGasPriceEip1559DataSection : String :=
  ".section .data\n" ++
  "egpe_pad:\n" ++
  "  .zero 8"

def ziskEffectiveGasPriceEip1559ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEffectiveGasPriceEip1559Prologue
  dataAsm     := ziskEffectiveGasPriceEip1559DataSection
}

end EvmAsm.Codegen
