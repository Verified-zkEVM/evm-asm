/-
Copyright (c) 2025 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: zkSecurity
-/
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestLayout

/-! Abstract (GuestLayout-parameterised) U256 gas-pricing program.

    GH #10753 leaf: the program is parameterised over `GuestLayout`; the
    concrete instance lives in the bridge `U256GasPricing.lean`, which
    re-exposes the original names and types. -/

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

def priorityFeePerGasEip1559_prog_of (L : GuestLayout) : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x10 .x9,
    .MV .x11 .x18,
    .MV .x12 .x19,
    .JAL .x1 (jalOff L.u256_sub_be (L.priority_fee_per_gas_eip1559 + 52)),
    .BNE .x10 .x0 (28 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x19,
    .MV .x12 .x19,
    .JAL .x1 (jalOff L.u256_min (L.priority_fee_per_gas_eip1559 + 72)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `priorityFeePerGasEip1559_prog_of`: the `la`/cross-`jal` instruction
    indices kept SYMBOLIC in the emitted image text (`emitProgramR`), while
    the Program above carries the layout-parameterised immediates
    (`laHi`/`laLo`/`jalOff L.…`) for verification. -/
def priorityFeePerGasEip1559_relocs : RelocTable :=
  [ (13, .jal .x1 "u256_sub_be"),
    (18, .jal .x1 "u256_min") ]

def priorityFeePerGasEip1559Function : String :=
  "priority_fee_per_gas_eip1559:\n" ++ emitProgramR (priorityFeePerGasEip1559_prog_of .zero) priorityFeePerGasEip1559_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `priorityFeePerGasEip1559_prog_of .zero` rendered under its label with the
    `la`/`jal` relocs kept symbolic (layout-parameterised per GH #10753;
    emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp
    over the bridge's `priorityFeePerGasEip1559_prog` (`_of guestLayout`). -/
theorem priorityFeePerGasEip1559Function_eq_prog :
    priorityFeePerGasEip1559Function = "priority_fee_per_gas_eip1559:\n" ++ emitProgramR (priorityFeePerGasEip1559_prog_of .zero) priorityFeePerGasEip1559_relocs := rfl

#guard priorityFeePerGasEip1559Function.startsWith "priority_fee_per_gas_eip1559:\n"
#guard (priorityFeePerGasEip1559_prog_of .zero).length = 29

end EvmAsm.Codegen
