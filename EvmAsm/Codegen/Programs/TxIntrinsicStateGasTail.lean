/-
  EvmAsm.Codegen.Programs.TxIntrinsicStateGasTail

  Tail inline state-gas settlement helpers extracted from
  TxIntrinsicStateGas. Public names and emitted strings are unchanged.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasBase

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Complete the live per-transaction state-gas cell after execution settles.

    State refunds are presently represented by the zero-initialized
    `bvgr_tx_state_refund` substrate, so the exact current identity is the
    intrinsic/auth charge plus executed state gas for successful transactions.
    Failed transactions retain only the intrinsic/auth component. -/

def blockVerdictTxStateGasInlineFinalize_prog : Program :=
  [ .SLLI .x5 .x10 (3 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 4)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 4)),
    .ADD .x6 .x6 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .BNE .x11 .x0 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 196) (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 20)),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 24)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 24)),
    .LD .x28 .x28 (0 : BitVec 12),
    .BEQ .x28 .x0 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 216) (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 36)),
    .SD .x6 .x0 (0 : BitVec 12),
    .LI .x7 (0 : Word),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 48)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 48)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 60)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 60)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 72)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 72)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 84)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 84)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 96)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 96)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 108)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 108)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 120)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 120)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 132)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 132)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 144)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 144)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 156)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 156)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 168)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 168)),
    .SD .x28 .x0 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_top_frame_regular_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 180)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_top_frame_regular_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 180)),
    .SD .x28 .x0 (0 : BitVec 12),
    .JAL .x0 (24 : BitVec 21),
    .AUIPC .x28 (laHi GuestAddrs.bvgr_tx_exec_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 196)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bvgr_tx_exec_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 196)),
    .ADD .x28 .x28 .x5,
    .LD .x28 .x28 (0 : BitVec 12),
    .ADD .x7 .x7 .x28,
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_total_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 216)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_total_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 216)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x7 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictTxStateGasInlineFinalize_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictTxStateGasInlineFinalize_relocs : RelocTable :=
  [ (1, .la .x6 "bvgr_tx_state_gas"),
    (6, .la .x28 "runtime_tx_auth_phase_halted"),
    (12, .la .x28 "runtime_tx_auth_effect_count_checkpoint"),
    (15, .la .x28 "exec_nonstorage_effect_count"),
    (18, .la .x28 "runtime_tx_auth_effect_overflow_checkpoint"),
    (21, .la .x28 "exec_nonstorage_effect_overflow"),
    (24, .la .x28 "runtime_tx_auth_code_effect_count_checkpoint"),
    (27, .la .x28 "exec_code_effect_count"),
    (30, .la .x28 "runtime_tx_auth_code_effect_next_checkpoint"),
    (33, .la .x28 "exec_code_effect_next"),
    (36, .la .x28 "runtime_tx_auth_code_effect_overflow_checkpoint"),
    (39, .la .x28 "exec_code_effect_overflow"),
    (42, .la .x28 "runtime_tx_auth_regular_refund"),
    (45, .la .x28 "runtime_tx_top_frame_regular_gas"),
    (49, .la .x28 "bvgr_tx_exec_state_gas"),
    (54, .la .x6 "bvgr_tx_total_state_gas") ]

def blockVerdictTxStateGasInlineFinalizeFunction : String :=
  "block_verdict_tx_state_gas_inline_finalize:\n" ++ emitProgramR blockVerdictTxStateGasInlineFinalize_prog blockVerdictTxStateGasInlineFinalize_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictTxStateGasInlineFinalize_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictTxStateGasInlineFinalizeFunction_eq_prog :
    blockVerdictTxStateGasInlineFinalizeFunction = "block_verdict_tx_state_gas_inline_finalize:\n" ++ emitProgramR blockVerdictTxStateGasInlineFinalize_prog blockVerdictTxStateGasInlineFinalize_relocs := rfl

#guard blockVerdictTxStateGasInlineFinalizeFunction.startsWith "block_verdict_tx_state_gas_inline_finalize:\n"
#guard blockVerdictTxStateGasInlineFinalize_prog.length = 60

end EvmAsm.Codegen
