/-
  EvmAsm.Evm64.LogGas

  Pure dynamic gas helpers for LOG0 through LOG4 (GH #112 / #118).
-/

module

public import EvmAsm.Evm64.LogArgs
public import EvmAsm.Evm64.MemoryGas

@[expose] public section

namespace EvmAsm.Evm64
namespace LogGas

/-- Dynamic gas charged per LOG topic. -/
def logGasPerTopic : Nat := 375

/-- Dynamic gas charged per byte of LOG data. -/
def logGasPerDataByte : Nat := 8

/-- Topic-dependent dynamic gas for LOG0 through LOG4. -/
def logTopicDynamicCost (kind : LogArgs.Kind) : Nat :=
  logGasPerTopic * LogArgs.topicCount kind

/-- Data-byte dynamic gas for LOG input data. -/
def logDataDynamicCost (length : Nat) : Nat :=
  logGasPerDataByte * length

/--
  LOG dynamic gas: topic charge, data-byte charge, and memory expansion for
  the logged byte range. The opcode base cost is tracked separately by the
  static gas table.
-/
def logDynamicCost
    (kind : LogArgs.Kind) (sizeBytes offset length : Nat) : Nat :=
  logTopicDynamicCost kind + logDataDynamicCost length +
    MemoryGas.memoryAccessExpansionCost sizeBytes offset length

@[simp] theorem logTopicDynamicCost_log0 :
    logTopicDynamicCost .log0 = 0 := rfl

@[simp] theorem logDataDynamicCost_zero :
    logDataDynamicCost 0 = 0 := by
  simp [logDataDynamicCost, logGasPerDataByte]

theorem logDynamicCost_eq_charges_of_no_growth
    {kind : LogArgs.Kind} {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    logDynamicCost kind sizeBytes offset length =
      logTopicDynamicCost kind + logDataDynamicCost length := by
  simp [logDynamicCost,
    MemoryGas.memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth]

theorem logDynamicCost_eq_charges_of_access_le
    {kind : LogArgs.Kind} {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    logDynamicCost kind sizeBytes offset length =
      logTopicDynamicCost kind + logDataDynamicCost length := by
  exact logDynamicCost_eq_charges_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes offset length h_access)

@[simp] theorem logDynamicCost_log0_zero_length (sizeBytes offset : Nat) :
    logDynamicCost .log0 sizeBytes offset 0 = 0 := by
  simp [logDynamicCost]

end LogGas
end EvmAsm.Evm64
