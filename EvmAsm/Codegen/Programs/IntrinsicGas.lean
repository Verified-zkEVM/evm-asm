/-
  EvmAsm.Codegen.Programs.IntrinsicGas

  Intrinsic-gas helpers carved out of `EvmAsm.Codegen.Programs`
  per the file-size hard cap. Hosts:

    K105  calldata_byte_counts
    K106  intrinsic_gas_calldata_floor_eip7623
    K107  init_code_cost

  Pure arithmetic — no RLP/MPT/Keccak dependencies. Self-contained:
  imports only `Rv64.Program` and `Codegen.Layout`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AmsterdamSystemTx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## calldata_byte_counts -- PR-K105

    Count zero and non-zero bytes in an arbitrary byte buffer.
    Used by intrinsic-gas pricing across all post-Istanbul forks:

      EIP-2028 standard pricing:
        data_cost = zero_count × 4  +  non_zero_count × 16
      EIP-7623 calldata-floor pricing (Pectra+):
        floor_cost = zero_count × 10  +  non_zero_count × 40

    A pure-leaf helper: no callee-saved registers used (apart from
    saving s0..s1 so the loop is human-readable), no scratch
    memory, no transitive calls. Returns both counts in one pass.

    Calling convention:
      a0 (input)  : bytes ptr
      a1 (input)  : byte length
      a2 (input)  : u64 out ptr (zero_count)
      a3 (input)  : u64 out ptr (non_zero_count)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total over the buffer).

    `zero_count + non_zero_count == byte_length` exactly. -/
def calldataByteCounts_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (0 : Word),
    .MV .x7 .x10,
    .MV .x28 .x11,
    .BEQ .x28 .x0 (36 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BNE .x29 .x0 (12 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SD .x12 .x5 (0 : BitVec 12),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def calldataByteCountsFunction : String :=
  "calldata_byte_counts:\n" ++ emitProgram calldataByteCounts_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `calldataByteCounts_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem calldataByteCountsFunction_eq_prog :
    calldataByteCountsFunction = "calldata_byte_counts:\n" ++ emitProgram calldataByteCounts_prog := rfl

#guard calldataByteCountsFunction.startsWith "calldata_byte_counts:\n"
#guard calldataByteCounts_prog.length = 17

/-! ## intrinsic_gas_calldata_floor_eip7623 -- PR-K106

    Compute the EIP-7623 calldata-floor gas cost for a tx, in
    closed form:

      tokens     = zero_count + 4 × non_zero_count
      floor_cost = tokens × GAS_TX_DATA_TOKEN_FLOOR  +  GAS_TX_BASE
                 = tokens × 10                       +  21000

    This is the lower bound on a tx's overall gas charge per
    EIP-7623; the actual charged amount is
    `max(intrinsic + execution, floor)`. PR-K46 covers the
    standard intrinsic-gas computation; K106 covers the floor
    side so callers can take the `max` cheaply.

    The Amsterdam constants are passed as arguments so the helper
    works across forks that re-cost the floor.

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : floor_gas_per_token (10 on Amsterdam mainnet)
      a3 (input)  : token_per_nonzero (4 on Amsterdam mainnet)
      a4 (input)  : base_gas (21000 on mainnet)
      a5 (input)  : u64 out ptr (floor_cost)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls. -/
def intrinsicGasCalldataFloorEip7623_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (0 : Word),
    .MV .x7 .x10,
    .MV .x28 .x11,
    .BEQ .x28 .x0 (36 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BNE .x29 .x0 (12 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .MUL .x30 .x6 .x13,
    .ADD .x30 .x30 .x5,
    .MUL .x31 .x30 .x12,
    .ADD .x31 .x31 .x14,
    .SD .x15 .x31 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def intrinsicGasCalldataFloorEip7623Function : String :=
  "intrinsic_gas_calldata_floor_eip7623:\n" ++ emitProgram intrinsicGasCalldataFloorEip7623_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `intrinsicGasCalldataFloorEip7623_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem intrinsicGasCalldataFloorEip7623Function_eq_prog :
    intrinsicGasCalldataFloorEip7623Function = "intrinsic_gas_calldata_floor_eip7623:\n" ++ emitProgram intrinsicGasCalldataFloorEip7623_prog := rfl

#guard intrinsicGasCalldataFloorEip7623Function.startsWith "intrinsic_gas_calldata_floor_eip7623:\n"
#guard intrinsicGasCalldataFloorEip7623_prog.length = 20

/-! ## init_code_cost -- PR-K107

    Compute the EIP-3860 init-code gas cost for a contract-creation
    tx's init bytecode:

      init_code_cost = GAS_CODE_INIT_PER_WORD × ceil(len / 32)
                     = 2 × ((len + 31) ÷ 32)        (mainnet)

    Used inside `calculate_intrinsic_cost(tx)` whenever
    `tx.to == empty` (CREATE-shaped tx); pre-EIP-3860 forks
    skip this term.

    The `gas_per_word` constant is passed in so the helper works
    across forks that adjust it.

    Calling convention:
      a0 (input)  : init_code_length (u64)
      a1 (input)  : gas_per_word (u64; 2 on mainnet)
      a2 (input)  : u64 out ptr (init_code_cost)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls.
    The arithmetic stays in u64; for any `init_code_length` within
    the EIP-3860 cap (`MAX_INIT_CODE_SIZE = 49_152`) and any
    `gas_per_word ≤ 2^48`, the cost fits in u64. -/
def initCodeCost_prog : Program :=
  [ .ADDI .x5 .x10 (31 : BitVec 12),
    .SRLI .x5 .x5 (5 : BitVec 6),
    .MUL .x5 .x5 .x11,
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def initCodeCostFunction : String :=
  "init_code_cost:\n" ++ emitProgram initCodeCost_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `initCodeCost_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem initCodeCostFunction_eq_prog :
    initCodeCostFunction = "init_code_cost:\n" ++ emitProgram initCodeCost_prog := rfl

#guard initCodeCostFunction.startsWith "init_code_cost:\n"
#guard initCodeCost_prog.length = 6

def intrinsicGasAmsterdamCounts_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (0 : Word),
    .MV .x7 .x10,
    .MV .x28 .x11,
    .BEQ .x28 .x0 (36 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BNE .x29 .x0 (12 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SLLI .x30 .x6 (2 : BitVec 6),
    .ADD .x30 .x30 .x5,
    .SLLI .x31 .x30 (2 : BitVec 6),
    .LUI .x29 (3 : BitVec 20),
    .ADDIW .x29 .x29 (-288 : BitVec 12),
    .ADD .x31 .x31 .x29,
    .LI .x28 (0 : Word),
    .BEQ .x12 .x0 (52 : BitVec 13),
    .LUI .x29 (3 : BitVec 20),
    .ADDIW .x29 .x29 (-1288 : BitVec 12),
    .ADD .x28 .x28 .x29,
    .ADDI .x29 .x11 (31 : BitVec 12),
    .SRLI .x29 .x29 (5 : BitVec 6),
    .SLLI .x29 .x29 (1 : BitVec 6),
    .ADD .x31 .x31 .x29,
    .LD .x29 .x2 (0 : BitVec 12),
    .BEQ .x29 .x0 (56 : BitVec 13),
    .LI .x29 (1756 : Word),
    .ADD .x28 .x28 .x29,
    .JAL .x0 (44 : BitVec 21),
    .LD .x29 .x2 (8 : BitVec 12),
    .BNE .x29 .x0 (36 : BitVec 13),
    .LUI .x29 (1 : BitVec 20),
    .ADDIW .x29 .x29 (-1096 : BitVec 12),
    .ADD .x28 .x28 .x29,
    .LD .x29 .x2 (0 : BitVec 12),
    .BEQ .x29 .x0 (16 : BitVec 13),
    .LUI .x29 (1 : BitVec 20),
    .ADDIW .x29 .x29 (1904 : BitVec 12),
    .ADD .x28 .x28 .x29,
    .ADD .x31 .x31 .x28,
    .LUI .x29 (1 : BitVec 20),
    .ADDIW .x29 .x29 (-1096 : BitVec 12),
    .MUL .x29 .x13 .x29,
    .ADD .x31 .x31 .x29,
    .LUI .x29 (1 : BitVec 20),
    .ADDIW .x29 .x29 (-1096 : BitVec 12),
    .MUL .x29 .x14 .x29,
    .ADD .x31 .x31 .x29,
    .LI .x29 (80 : Word),
    .MUL .x7 .x13 .x29,
    .LI .x29 (128 : Word),
    .MUL .x29 .x14 .x29,
    .ADD .x7 .x7 .x29,
    .SLLI .x29 .x7 (4 : BitVec 6),
    .ADD .x31 .x31 .x29,
    .LUI .x29 (2 : BitVec 20),
    .ADDIW .x29 .x29 (-376 : BitVec 12),
    .MUL .x29 .x15 .x29,
    .ADD .x31 .x31 .x29,
    .SD .x16 .x31 (0 : BitVec 12),
    .SLLI .x30 .x11 (2 : BitVec 6),
    .ADD .x30 .x30 .x7,
    .SLLI .x30 .x30 (4 : BitVec 6),
    .LUI .x29 (3 : BitVec 20),
    .ADDIW .x29 .x29 (-288 : BitVec 12),
    .ADD .x30 .x30 .x29,
    .ADD .x30 .x30 .x28,
    .SD .x17 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def intrinsicGasAmsterdamCountsFunction : String :=
  "intrinsic_gas_amsterdam_counts:\n" ++ emitProgram intrinsicGasAmsterdamCounts_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `intrinsicGasAmsterdamCounts_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem intrinsicGasAmsterdamCountsFunction_eq_prog :
    intrinsicGasAmsterdamCountsFunction = "intrinsic_gas_amsterdam_counts:\n" ++ emitProgram intrinsicGasAmsterdamCounts_prog := rfl

#guard intrinsicGasAmsterdamCountsFunction.startsWith "intrinsic_gas_amsterdam_counts:\n"
#guard intrinsicGasAmsterdamCounts_prog.length = 74

/-! ## eip8037_reservoir_split -- Amsterdam state-gas reservoir

    Mirror execution-specs Amsterdam `process_transaction` after intrinsic
    validation:

      intrinsic_total      = intrinsic.regular + intrinsic.state
      execution_gas        = tx.gas - intrinsic_total
      regular_gas_budget   = TX_MAX_GAS_LIMIT - intrinsic.regular
      gas                  = min(regular_gas_budget, execution_gas)
      state_gas_reservoir  = execution_gas - gas

    The helper intentionally accepts both intrinsic totals as inputs so it can
    compose with the existing regular/calldata probe and the EIP-8037
    intrinsic-state component without redoing either calculation. -/
def eip8037ReservoirSplit_prog : Program :=
  [ .BLTU .x10 .x11 (52 : BitVec 13),
    .LUI .x5 (4096 : BitVec 20),
    .BLTU .x5 .x12 (60 : BitVec 13),
    .SUB .x6 .x10 .x11,
    .SUB .x7 .x5 .x12,
    .MV .x28 .x6,
    .BLTU .x6 .x7 (8 : BitVec 13),
    .MV .x28 .x7,
    .SUB .x29 .x6 .x28,
    .SD .x13 .x28 (0 : BitVec 12),
    .SD .x14 .x29 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x13 .x0 (0 : BitVec 12),
    .SD .x14 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x13 .x0 (0 : BitVec 12),
    .SD .x14 .x0 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def eip8037ReservoirSplitFunction : String :=
  "eip8037_reservoir_split:\n" ++ emitProgram eip8037ReservoirSplit_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `eip8037ReservoirSplit_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem eip8037ReservoirSplitFunction_eq_prog :
    eip8037ReservoirSplitFunction = "eip8037_reservoir_split:\n" ++ emitProgram eip8037ReservoirSplit_prog := rfl

#guard eip8037ReservoirSplitFunction.startsWith "eip8037_reservoir_split:\n"
#guard eip8037ReservoirSplit_prog.length = 21

/-! ## eip8037_tx_state_gas -- Amsterdam per-tx state-gas settlement

    Mirror execution-specs Amsterdam `process_transaction` per-tx state-gas
    accounting (v0.6, fork.py:1174-1182):

      tx_state_gas = int(tx_env.intrinsic_state_gas) + tx_output.state_gas_used
      block_output.block_state_gas_used += Uint(max(0, tx_state_gas))

    There is NO v0.5.0 creation-revert refund subtraction: a failed or
    colliding creation's NEW_ACCOUNT charge is already credited back inside
    execution (`credit_state_gas_refund`, system.py:117-125/157-159), so the
    executed `state_gas_used` the dispatcher captures is net of it. The
    executed component is `frame_state_gas_used(evm) + auth_state_gas_used`
    (interpreter.py:172), captured per tx by
    `dispatcher_capture_exec_state_gas` into `bvgr_tx_exec_state_gas`.
    (The spec value is an `int` that can go negative when refunds exceed
    charges; the guest's u64 running counter guards each refund subtraction
    against underflow, so its captured value is always >= 0 — the settled sum
    here mirrors `Uint(max(0, tx_state_gas))`.) -/
/-- 4-instr leaf: `*a5 = a0 + a1; a0 = 0; ret`.
    a2–a4 are retired v0.5 args (ignored; kept so `tx_intrinsic_state_gas` ABI stands). -/
def eip8037TxStateGas_prog : Program :=
  [ .ADD .x5 .x10 .x11
  , .SD .x15 .x5 (0 : BitVec 12)
  , .LI .x10 (0 : Word)
  , .JALR .x0 .x1 (0 : BitVec 12) ]

def eip8037TxStateGasFunction : String :=
  "eip8037_tx_state_gas:\n" ++ emitProgram eip8037TxStateGas_prog

theorem eip8037TxStateGasFunction_eq_prog :
    eip8037TxStateGasFunction =
      "eip8037_tx_state_gas:\n" ++ emitProgram eip8037TxStateGas_prog := rfl

#guard eip8037TxStateGasFunction.startsWith "eip8037_tx_state_gas:\n"

/-! ## block_verdict_eip8037_tx_state_gas_net_array

    Materialize execution-spec `tx_state_gas` per transaction from arrays that
    are already available after runtime gas-result materialization (v0.6,
    fork.py:1174):

      tx_state_gas = intrinsic_state_gas + state_gas_used

    No v0.5.0 creation-revert refund subtraction: failed/colliding creation
    charges are credited back inside execution, so the captured executed
    state gas is already net.

    ABI:
      a0 = intrinsic_state_gas array ptr
      a1 = executed_state_gas array ptr (raw `evm_state_gas_used` per tx)
      a2 = count
      a3 = output tx_state_gas array ptr

    Returns:
      a0 = 0 (the v0.6 identity cannot underflow)
      a1 = 0. -/
def blockVerdictEip8037TxStateGasNetArray_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .LI .x20 (0 : Word),
    .BEQ .x20 .x18 (40 : BitVec 13),
    .SLLI .x5 .x20 (3 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LD .x10 .x6 (0 : BitVec 12),
    .ADD .x6 .x9 .x5,
    .LD .x11 .x6 (0 : BitVec 12),
    .ADD .x15 .x19 .x5,
    .JAL .x1 (jalOff GuestAddrs.eip8037_tx_state_gas (GuestAddrs.block_verdict_eip8037_tx_state_gas_net_array + 76)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .LI .x10 (0 : Word),
    .LI .x11 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictEip8037TxStateGasNetArray_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictEip8037TxStateGasNetArray_relocs : RelocTable :=
  [ (19, .jal .x1 "eip8037_tx_state_gas") ]

def blockVerdictEip8037TxStateGasNetArrayFunction : String :=
  "block_verdict_eip8037_tx_state_gas_net_array:\n" ++ emitProgramR blockVerdictEip8037TxStateGasNetArray_prog blockVerdictEip8037TxStateGasNetArray_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictEip8037TxStateGasNetArray_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictEip8037TxStateGasNetArrayFunction_eq_prog :
    blockVerdictEip8037TxStateGasNetArrayFunction = "block_verdict_eip8037_tx_state_gas_net_array:\n" ++ emitProgramR blockVerdictEip8037TxStateGasNetArray_prog blockVerdictEip8037TxStateGasNetArray_relocs := rfl

#guard blockVerdictEip8037TxStateGasNetArrayFunction.startsWith "block_verdict_eip8037_tx_state_gas_net_array:\n"
#guard blockVerdictEip8037TxStateGasNetArray_prog.length = 32

/-! ## eip8037_block_gas_used -- Amsterdam block gas_used = max(regular,state)

    Mirror execution-specs Amsterdam `apply_body` / `process_transaction` block
    gas accounting (fork.py ~1199-1202, then 358-363):

      # accumulated per transaction
      block_output.block_gas_used       += max(tx_regular_gas, intrinsic.calldata_floor)
      block_output.block_state_gas_used += tx_state_gas

      # at finalization
      block_gas_used = max(
          block_output.block_gas_used,        # block_regular
          block_output.block_state_gas_used,  # block_state
      )
      if block_gas_used != block.header.gas_used:
          raise InvalidBlock

    The guest is BAL-replay-only and does not meter opcode execution, so the
    per-tx `regular` increment (`max(tx_regular_gas, intrinsic.calldata_floor)`)
    and `tx_state_gas` are caller-supplied: in the common BAL-replay path the
    state increment is zero and the regular increment comes from the EIP-7778
    remaining-block-gas results arena. This helper isolates the pure block-level
    arithmetic — accumulate both totals across the per-tx arrays, take the max,
    and compare against the header `gas_used`. A `u64` overflow while
    accumulating either total is reported as a distinct nonzero status rather
    than wrapping. The wiring into `block_verdict` lands in a separate child
    once a real metered regular-gas accumulator exists. -/
def eip8037BlockGasUsed_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .MV .x7 .x12,
    .LI .x28 (0 : Word),
    .LI .x29 (0 : Word),
    .LI .x30 (0 : Word),
    .BEQ .x28 .x7 (56 : BitVec 13),
    .SLLI .x31 .x28 (3 : BitVec 6),
    .ADD .x15 .x5 .x31,
    .LD .x15 .x15 (0 : BitVec 12),
    .ADD .x16 .x29 .x15,
    .BLTU .x16 .x29 (80 : BitVec 13),
    .MV .x29 .x16,
    .ADD .x15 .x6 .x31,
    .LD .x15 .x15 (0 : BitVec 12),
    .ADD .x16 .x30 .x15,
    .BLTU .x16 .x30 (60 : BitVec 13),
    .MV .x30 .x16,
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-52 : BitVec 21),
    .MV .x15 .x29,
    .BGEU .x29 .x30 (8 : BitVec 13),
    .MV .x15 .x30,
    .SD .x14 .x15 (0 : BitVec 12),
    .BNE .x15 .x13 (16 : BitVec 13),
    .LI .x10 (0 : Word),
    .MV .x11 .x15,
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .MV .x11 .x15,
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x14 .x0 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def eip8037BlockGasUsedFunction : String :=
  "eip8037_block_gas_used:\n" ++ emitProgram eip8037BlockGasUsed_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `eip8037BlockGasUsed_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem eip8037BlockGasUsedFunction_eq_prog :
    eip8037BlockGasUsedFunction = "eip8037_block_gas_used:\n" ++ emitProgram eip8037BlockGasUsed_prog := rfl

#guard eip8037BlockGasUsedFunction.startsWith "eip8037_block_gas_used:\n"
#guard eip8037BlockGasUsed_prog.length = 35

end EvmAsm.Codegen
