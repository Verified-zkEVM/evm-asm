/-
  EvmAsm.Stateless.SpecRef.Gas

  Port of the blob-gas / gas-limit slice of
  `execution-specs/src/ethereum/forks/amsterdam/vm/gas.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) needed by the seam shell's
  `validate_header` (bead `evm-asm-s1d19.3`):

  * the `GasCosts` constants it reads (class `GasCosts`)
  * `calculate_blob_gas_price` (function `calculate_blob_gas_price`)
  * `calculate_excess_blob_gas` (function `calculate_excess_blob_gas`)

  plus `taylor_exponential` from `ethereum/utils/numeric.py`
  (`execution-specs/src/ethereum/utils/numeric.py`, function
  `taylor_exponential`).  The full EIP-8037 gas model (two-dimensional
  regular/state gas, memory expansion) is Stack C (`s1d19.5`).

  ## Modeling note: `taylor_exponential` fuel

  The Python loop runs until the accumulated term underflows to zero
  under integer division.  The term after step `i` is bounded by
  `factor·denominator·(numerator/denominator)^i / i!`, so its peak is
  ≤ `factor·denominator·e^(numerator/denominator)` and once
  `i ≥ 2·numerator/denominator` each step at least halves it; the loop
  therefore takes at most `4·(numerator/denominator) +
  log₂(factor·denominator) + O(1)` iterations, which the fuel strictly
  over-approximates.  Exhaustion is unreachable; it rejects rather than
  returning a wrong value.
-/

import EvmAsm.Stateless.SpecRef.Types

namespace EvmAsm.Stateless.SpecRef

/-! ## `GasCosts` constants (`vm/gas.py`, class `GasCosts`) -/

namespace GasCosts

def PER_BLOB : U64 := 2^17
def BLOB_SCHEDULE_TARGET : U64 := 14
def BLOB_TARGET_GAS_PER_BLOCK : U64 := PER_BLOB * BLOB_SCHEDULE_TARGET
def BLOB_BASE_COST : Uint := 2^13
def BLOB_SCHEDULE_MAX : U64 := 21
def BLOB_MIN_GASPRICE : Uint := 1
def BLOB_BASE_FEE_UPDATE_FRACTION : Uint := 11684671
def LIMIT_ADJUSTMENT_FACTOR : Uint := 1024
def LIMIT_MINIMUM : Uint := 5000

end GasCosts

/-! ## `taylor_exponential` (`ethereum/utils/numeric.py`, function `taylor_exponential`) -/

private def taylorAux (numerator denominator : Nat) :
    Nat → Nat → Nat → Nat → Except SpecError Nat
  | _, _, 0, output => pure output
  | 0, _, _, _ => throw (.mptWriteError "taylor_exponential: fuel exhausted")
  | fuel + 1, i, acc, output =>
      taylorAux numerator denominator fuel (i + 1)
        (acc * numerator / (denominator * i)) (output + acc)

/-- `factor · e^(numerator/denominator)`, Taylor-approximated in integer
    arithmetic (see the fuel note in the header). -/
def taylor_exponential (factor numerator denominator : Uint) :
    Except SpecError Uint := do
  let output ← taylorAux numerator denominator
    (4 * (numerator / denominator) + Nat.log2 (factor * denominator + 2) + 8)
    1 (factor * denominator) 0
  pure (output / denominator)

/-! ## `calculate_blob_gas_price` (function `calculate_blob_gas_price`) -/

/-- The blob gas price for a block. -/
def calculate_blob_gas_price (excess_blob_gas : U64) : Except SpecError Uint :=
  taylor_exponential GasCosts.BLOB_MIN_GASPRICE excess_blob_gas
    GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION

/-! ## `calculate_excess_blob_gas` (function `calculate_excess_blob_gas`) -/

/-- The excess blob gas for the current block from the parent header
    (the parent is always a decoded `Header | PreviousForkHeader` on
    this path, so the Python at-fork zero defaults never apply). -/
def calculate_excess_blob_gas (parent_header : Header) :
    Except SpecError U64 := do
  let excess_blob_gas := parent_header.excessBlobGas
  let blob_gas_used := parent_header.blobGasUsed
  let base_fee_per_gas := parent_header.baseFeePerGas
  let parent_blob_gas := excess_blob_gas + blob_gas_used
  if parent_blob_gas < GasCosts.BLOB_TARGET_GAS_PER_BLOCK then
    pure 0
  else
    let target_blob_gas_price := GasCosts.PER_BLOB *
      (← calculate_blob_gas_price excess_blob_gas)
    let base_blob_tx_price := GasCosts.BLOB_BASE_COST * base_fee_per_gas
    if base_blob_tx_price > target_blob_gas_price then
      let blob_schedule_delta :=
        GasCosts.BLOB_SCHEDULE_MAX - GasCosts.BLOB_SCHEDULE_TARGET
      pure (excess_blob_gas
        + blob_gas_used * blob_schedule_delta / GasCosts.BLOB_SCHEDULE_MAX)
    else
      pure (parent_blob_gas - GasCosts.BLOB_TARGET_GAS_PER_BLOCK)

/-! ## Sanity checks (cross-checked against the Python spec at `bd8c673`) -/

-- calculate_blob_gas_price: zero excess → min price; two Python-checked
-- points on the exponential.
#guard (calculate_blob_gas_price 0).toOption == some 1
#guard (calculate_blob_gas_price 10000000).toOption == some 2
#guard (calculate_blob_gas_price 100000000).toOption == some 5209

-- calculate_excess_blob_gas on synthetic parent headers (Python-checked):
-- below target → 0; above target with cheap base fee → linear branch;
-- expensive base fee → schedule-delta branch.
private def gasTestHeader (ebg bgu bf : Nat) : Header :=
  { isCurrentFork := true, parentHash := List.replicate 32 0,
    ommersHash := List.replicate 32 0, coinbase := List.replicate 20 0,
    stateRoot := List.replicate 32 0, transactionsRoot := List.replicate 32 0,
    receiptRoot := List.replicate 32 0, bloom := List.replicate 256 0,
    difficulty := 0, number := 1, gasLimit := 30000000, gasUsed := 0,
    timestamp := 0, extraData := [], prevRandao := List.replicate 32 0,
    nonce := List.replicate 8 0, baseFeePerGas := bf,
    withdrawalsRoot := List.replicate 32 0, blobGasUsed := bgu,
    excessBlobGas := ebg, parentBeaconBlockRoot := List.replicate 32 0,
    requestsHash := List.replicate 32 0,
    blockAccessListHash := List.replicate 32 0, slotNumber := 1 }

#guard (calculate_excess_blob_gas (gasTestHeader 0 0 7)).toOption == some 0
#guard (calculate_excess_blob_gas (gasTestHeader 2000000 500000 7)).toOption
  == some 664992
#guard (calculate_excess_blob_gas (gasTestHeader 0 2621440 1000000000)).toOption
  == some 873813

end EvmAsm.Stateless.SpecRef
