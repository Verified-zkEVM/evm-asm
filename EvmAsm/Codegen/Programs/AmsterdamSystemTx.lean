/-
  EvmAsm.Codegen.Programs.AmsterdamSystemTx

  Shared constants for Amsterdam system transactions.  These mirror
  execution-specs `src/ethereum/forks/amsterdam/fork.py` and `vm/gas.py`:
  `process_unchecked_system_transaction` constructs a SYSTEM-address call with
  a fixed 30M regular gas budget and a bounded state-gas reservoir sized for
  16 storage-set writes.  The concrete system-contract children (EIP-4788,
  EIP-2935, EIP-7002, EIP-7251) should import this module instead of
  open-coding these numbers.
-/

namespace EvmAsm.Codegen

/-- execution-specs Amsterdam `SYSTEM_TRANSACTION_GAS`. -/
def amsterdamSystemTransactionGas : Nat := 30000000

/-- execution-specs Amsterdam `COST_PER_STATE_BYTE` (LEGACY hardcoded constant; the current EIP-8037 spec
    SCALES the per-byte cost with the block gas limit via `amsterdamStateGasPerByte` below — see drj99.1.2). -/
def amsterdamCostPerStateByte : Nat := 1530

/-! ## EIP-8037 scaling state-gas cost (`state_gas_per_byte`, origin/eips/amsterdam/eip-8037 vm/gas.py)

    The per-state-byte cost is NOT a constant: it scales with the block gas limit. At gas_limit=100M it is
    1174 (NOT the legacy 1530). The guest must compute this at runtime (per block) and use it in every
    state-gas charge + the intrinsic state gas; the legacy `amsterdamCostPerStateByte`/`amsterdam*StateGas`
    constants are stale. This Lean mirror verifies the formula so the asm helper can be checked against it. -/
def amsterdamBlocksPerYear : Nat := 2628000
def amsterdamTargetStateGrowthPerYear : Nat := 100 * 1024 ^ 3      -- 107_374_182_400
def amsterdamCostPerStateByteOffset : Nat := 9578
def amsterdamCostPerStateByteSignificantBits : Nat := 5
/-- EIP-8037 `STATE_BYTES_PER_NEW_ACCOUNT` (current = 112; the guest's legacy 120 is stale). -/
def amsterdamStateBytesPerNewAccountV2 : Nat := 112

/-- `state_gas_per_byte(gas_limit)` (EIP-8037). Nat subtraction gives `max(bit_length-bits, 0)` for free. -/
def amsterdamStateGasPerByte (gasLimit : Nat) : Nat :=
  let numerator := gasLimit * amsterdamBlocksPerYear
  let denominator := 2 * amsterdamTargetStateGrowthPerYear
  let raw := (numerator + denominator - 1) / denominator
  let shifted := raw + amsterdamCostPerStateByteOffset
  let shift := (Nat.log2 shifted + 1) - amsterdamCostPerStateByteSignificantBits  -- bit_length = log2+1
  let quantized := (shifted >>> shift) <<< shift
  if quantized > amsterdamCostPerStateByteOffset then quantized - amsterdamCostPerStateByteOffset else 1

-- Verify against the spec's documented anchor (1174 at 100M) + the legacy-mismatch (!= 1530).
#guard amsterdamStateGasPerByte 100000000 = 1174
#guard amsterdamStateGasPerByte 100000000 ≠ 1530
#guard amsterdamStateBytesPerNewAccountV2 = 112

/-- Asm helper `state_gas_per_byte` (a0 = block gas_limit -> a0 = cost), mirroring the verified
    `amsterdamStateGasPerByte`. Pure arithmetic, no sub-calls; clobbers t0-t6 + a0. The block verdict
    computes it ONCE from header.gas_limit into the `evm_state_gas_per_byte` global; every state-gas
    charge then loads that global instead of the legacy `1530`. -/
def stateGasPerByteFunction : String :=
  "state_gas_per_byte:\n" ++
  "  li t0, " ++ toString amsterdamBlocksPerYear ++ "\n" ++
  "  mul t1, a0, t0\n" ++                                  -- numerator = gas_limit * BLOCKS_PER_YEAR
  "  li t2, " ++ toString (2 * amsterdamTargetStateGrowthPerYear) ++ "\n" ++   -- 2 * TARGET_STATE_GROWTH_PER_YEAR
  "  add t3, t1, t2\n  addi t3, t3, -1\n" ++              -- numerator + denominator - 1 (ceil)
  "  divu t1, t3, t2\n" ++                                 -- raw = ceil(numerator / denominator)
  "  li t3, " ++ toString amsterdamCostPerStateByteOffset ++ "\n" ++
  "  add t1, t1, t3\n" ++                                  -- shifted = raw + OFFSET
  "  mv t4, t1\n  li t5, 0\n" ++                           -- bit_length(shifted) -> t5
  ".Lsgpb_bl:\n" ++
  "  beqz t4, .Lsgpb_bld\n" ++
  "  srli t4, t4, 1\n  addi t5, t5, 1\n  j .Lsgpb_bl\n" ++
  ".Lsgpb_bld:\n" ++
  "  addi t5, t5, -" ++ toString amsterdamCostPerStateByteSignificantBits ++ "\n" ++  -- shift = bit_length-5 (>=9; shifted>=9578)
  "  srl t4, t1, t5\n  sll t4, t4, t5\n" ++                -- quantized = (shifted >> shift) << shift
  "  li t3, " ++ toString amsterdamCostPerStateByteOffset ++ "\n" ++
  "  bgeu t3, t4, .Lsgpb_one\n" ++                         -- OFFSET >= quantized -> return 1
  "  sub a0, t4, t3\n  ret\n" ++                           -- cost = quantized - OFFSET
  ".Lsgpb_one:\n" ++
  "  li a0, 1\n  ret"

/-- Data line for the per-block state-gas cost global (set once by the verdict). -/
def evmStateGasPerByteData : String := "evm_state_gas_per_byte:\n  .zero 8\n"

/-- execution-specs Amsterdam `STATE_BYTES_PER_STORAGE_SET`. -/
def amsterdamStateBytesPerStorageSet : Nat := 64

/-- execution-specs Amsterdam `STATE_BYTES_PER_NEW_ACCOUNT`. -/
def amsterdamStateBytesPerNewAccount : Nat := 120

/-- execution-specs Amsterdam `STATE_BYTES_PER_AUTH_BASE`. -/
def amsterdamStateBytesPerAuthBase : Nat := 23

/-- execution-specs Amsterdam `SYSTEM_MAX_SSTORES_PER_CALL`. -/
def amsterdamSystemMaxSstoresPerCall : Nat := 16

/-- State gas charged for one zero-to-nonzero storage set. -/
def amsterdamStorageSetStateGas : Nat :=
  amsterdamStateBytesPerStorageSet * amsterdamCostPerStateByte

/-- State gas precharged for one new-account creation. -/
def amsterdamNewAccountStateGas : Nat :=
  amsterdamStateBytesPerNewAccount * amsterdamCostPerStateByte

/-- State gas precharged for one EIP-7702 authorization. -/
def amsterdamAuthStateGas : Nat :=
  (amsterdamStateBytesPerNewAccount + amsterdamStateBytesPerAuthBase) * amsterdamCostPerStateByte

/-- Intrinsic state gas charged per EIP-7702 authorization. -/
def amsterdamAuthStateGasPerAuth : Nat :=
  (amsterdamStateBytesPerNewAccount + amsterdamStateBytesPerAuthBase)
    * amsterdamCostPerStateByte

/-- State-gas reservoir passed to each Amsterdam system transaction. -/
def amsterdamSystemStateGasReservoir : Nat :=
  amsterdamStorageSetStateGas * amsterdamSystemMaxSstoresPerCall

/-- drj99.1.2: emit `reg = bytes * evm_state_gas_per_byte` (the EIP-8037 RUNTIME state-gas cost), replacing
    the legacy `li reg, bytes*1530`. Uses t0 as a saved/restored scratch (no caller passes t0 as `reg`), so
    net it only writes `reg` (+ a balanced stack push/pop). evm_state_gas_per_byte is set once per block by
    the verdict from `state_gas_per_byte(header.gas_limit)`. -/
def liStateGasRuntime (reg : String) (bytes : Nat) : String :=
  let tmp := if reg == "t0" then "t1" else "t0"   -- scratch != reg, saved/restored so callers are unaffected
  "  addi sp, sp, -16\n  sd " ++ tmp ++ ", 0(sp)\n" ++
  "  la " ++ tmp ++ ", evm_state_gas_per_byte\n  ld " ++ tmp ++ ", 0(" ++ tmp ++ ")\n" ++
  "  li " ++ reg ++ ", " ++ toString bytes ++ "\n" ++
  "  mul " ++ reg ++ ", " ++ reg ++ ", " ++ tmp ++ "\n" ++
  "  ld " ++ tmp ++ ", 0(sp)\n  addi sp, sp, 16\n"

def liAmsterdamStorageSetStateGas (reg : String) : String :=
  liStateGasRuntime reg amsterdamStateBytesPerStorageSet               -- 64 * cost

/-- Assembly helper for the new-account state gas (112 bytes * runtime cost, EIP-8037). -/
def liAmsterdamNewAccountStateGas (reg : String) : String :=
  liStateGasRuntime reg amsterdamStateBytesPerNewAccountV2             -- 112 * cost (was 120*1530)

/-- Assembly helper for the per-authorization state gas ((112+23) bytes * runtime cost). -/
def liAmsterdamAuthStateGas (reg : String) : String :=
  liStateGasRuntime reg (amsterdamStateBytesPerNewAccountV2 + amsterdamStateBytesPerAuthBase)  -- 135 * cost

/-- Assembly helper for the per-authorization state gas ((112+23) bytes * runtime cost). -/
def liAmsterdamAuthStateGasPerAuth (reg : String) : String :=
  liStateGasRuntime reg (amsterdamStateBytesPerNewAccountV2 + amsterdamStateBytesPerAuthBase)  -- 135 * cost

/-- Assembly `li` helper for the system transaction regular gas budget. -/
def liAmsterdamSystemTransactionGas (reg : String) : String :=
  "  li " ++ reg ++ ", " ++ toString amsterdamSystemTransactionGas ++ "\n"

/-- Assembly helper for the system transaction state-gas reservoir = (64 bytes/set * 16 sets) * runtime cost. -/
def liAmsterdamSystemStateGasReservoir (reg : String) : String :=
  liStateGasRuntime reg (amsterdamStateBytesPerStorageSet * amsterdamSystemMaxSstoresPerCall)  -- 1024 * cost

#guard amsterdamStorageSetStateGas = 97920
#guard amsterdamNewAccountStateGas = 183600
#guard amsterdamAuthStateGas = 218790
#guard amsterdamAuthStateGasPerAuth = 218790
#guard amsterdamSystemStateGasReservoir = 1566720

end EvmAsm.Codegen
