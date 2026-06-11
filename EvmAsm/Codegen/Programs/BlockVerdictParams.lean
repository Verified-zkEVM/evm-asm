/-
  EvmAsm.Codegen.Programs.BlockVerdictParams

  Shared numeric parameters for the block-state-root / stateless-verdict-v2
  programs: static arena capacities and layout byte-widths.
  Extracted from BlockVerdict.lean so BlockVerdictDataSection.lean can share
  them without a circular import.
-/

import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmStorageAccessGas

namespace EvmAsm.Codegen

def bsrBalGasCost : Nat := 2000
/-- Static BAL/state replay arena capacity, sized for the Amsterdam 200M
    block-gas target: `bal_items <= block_gas_limit / 2000` = 100,000 items at
    200,000,000 gas. (The former 500,000 value was the 1G worst case, which is
    out of scope — it cost ~349 MB of the fixed 512 MiB ziskemu RAM window.)
    High declared block gas is not itself a layout error: the guest first
    applies Amsterdam's gas-derived BAL rule, then checks actual decoded item
    counts against these arenas; blocks whose actual counts exceed the
    capacities take the conservative bsr_fail path. -/
def bsrMaxBalItems : Nat := 100000
def bsrModeledSystemChanges : Nat := 2
def bsrMaxWithdrawalChanges : Nat := 16
def bsrMaxAuxChanges : Nat := bsrModeledSystemChanges + bsrMaxWithdrawalChanges
def bsrMaxStateChanges : Nat :=
  bsrMaxBalItems + bsrModeledSystemChanges + bsrMaxWithdrawalChanges
def bsrMaxAccessAccounts : Nat := runtimeAccessAccountOutcomeCapacity
def bsrMaxAccountAccessOutcomes : Nat := runtimeAccessAccountOutcomeCapacity
def bsrMaxStorageAccessOutcomes : Nat := storageAccessOutcomeMaxRecords

/-- Conservative upper bound on `witness.state` byte length accepted by
    `block_state_root`. Beyond this the post-state recompute bails conservatively
    (bsr_fail=111). This is a coarse size guard, NOT a fixed-buffer limit: the
    witness is read in place and the real structural bound is the sorted witness
    index node cap (8192, `MptWitnessIndex`). The earlier 262144 value
    false-rejected legitimately large state-creation blocks (EIP-8037 state-gas
    reservoir fixtures push >256 KiB witnesses, e.g. evm-asm-zbvak's 336 KB row);
    512 KiB keeps a guard while accepting those blocks. -/
def bsrMaxWitnessBytes : Nat := 524288
def bsrAccountRecordBytes : Nat := 24
def bsrPathBytes : Nat := 64
def bsrEncodedAccountBytes : Nat := 256
def bsrSystemAccountBytes : Nat := 128
def bsrStateChangeBytes : Nat := 40
def baapStorageDescBytes : Nat := 40

end EvmAsm.Codegen
