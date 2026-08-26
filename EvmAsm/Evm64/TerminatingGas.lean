/-
  EvmAsm.Evm64.TerminatingGas

  Pure dynamic gas helpers for frame-terminating opcodes (GH #113).

  Mirrors the shape of `EvmAsm.Evm64.LogGas`: a `Kind`-keyed wrapper that
  dispatches the dynamic gas component of STOP / RETURN / REVERT / INVALID /
  SELFDESTRUCT to the appropriate primitive in `EvmAsm.Evm64.MemoryGas`.

  STOP, INVALID, and SELFDESTRUCT carry no memory-expansion charge here:
  STOP and INVALID have no dynamic component, and SELFDESTRUCT's dynamic
  cost (cold/warm beneficiary, account-creation, etc.) is modeled at the
  world-state layer rather than as a memory expansion. RETURN and REVERT
  delegate to `MemoryGas.returnDynamicCost` / `MemoryGas.revertDynamicCost`,
  which are themselves thin wrappers around `memoryAccessExpansionCost`.
-/

module

public import EvmAsm.Evm64.TerminatingArgs
public import EvmAsm.Evm64.MemoryGas

@[expose] public section

namespace EvmAsm.Evm64
namespace TerminatingGas

/--
  Dynamic gas for a frame-terminating opcode parameterised by its `Kind`.
  STOP / INVALID / SELFDESTRUCT contribute zero memory-expansion charge here;
  RETURN and REVERT delegate to the existing `MemoryGas` primitives.
-/
def terminatingDynamicCost
    (kind : TerminatingArgs.Kind) (sizeBytes offset length : Nat) : Nat :=
  match kind with
  | .stop => 0
  | .return_ => MemoryGas.returnDynamicCost sizeBytes offset length
  | .revert => MemoryGas.revertDynamicCost sizeBytes offset length
  | .invalid => 0
  | .selfdestruct => 0

@[simp] theorem terminatingDynamicCost_stop (sizeBytes offset length : Nat) :
    terminatingDynamicCost .stop sizeBytes offset length = 0 := rfl

@[simp] theorem terminatingDynamicCost_invalid (sizeBytes offset length : Nat) :
    terminatingDynamicCost .invalid sizeBytes offset length = 0 := rfl

@[simp] theorem terminatingDynamicCost_selfdestruct
    (sizeBytes offset length : Nat) :
    terminatingDynamicCost .selfdestruct sizeBytes offset length = 0 := rfl

theorem terminatingDynamicCost_return_eq (sizeBytes offset length : Nat) :
    terminatingDynamicCost .return_ sizeBytes offset length =
      MemoryGas.returnDynamicCost sizeBytes offset length := rfl

theorem terminatingDynamicCost_revert_eq (sizeBytes offset length : Nat) :
    terminatingDynamicCost .revert sizeBytes offset length =
      MemoryGas.revertDynamicCost sizeBytes offset length := rfl

@[simp] theorem terminatingDynamicCost_return_zero_length
    (sizeBytes offset : Nat) :
    terminatingDynamicCost .return_ sizeBytes offset 0 = 0 := by
  simp [terminatingDynamicCost_return_eq]

@[simp] theorem terminatingDynamicCost_revert_zero_length
    (sizeBytes offset : Nat) :
    terminatingDynamicCost .revert sizeBytes offset 0 = 0 := by
  simp [terminatingDynamicCost_revert_eq]

theorem terminatingDynamicCost_return_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    terminatingDynamicCost .return_ sizeBytes offset length = 0 := by
  rw [terminatingDynamicCost_return_eq]
  exact MemoryGas.returnDynamicCost_eq_zero_of_no_growth h_no_growth

theorem terminatingDynamicCost_revert_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    terminatingDynamicCost .revert sizeBytes offset length = 0 := by
  rw [terminatingDynamicCost_revert_eq]
  exact MemoryGas.revertDynamicCost_eq_zero_of_no_growth h_no_growth

theorem terminatingDynamicCost_return_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    terminatingDynamicCost .return_ sizeBytes offset length = 0 := by
  rw [terminatingDynamicCost_return_eq]
  exact MemoryGas.returnDynamicCost_eq_zero_of_access_le h_access

theorem terminatingDynamicCost_revert_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    terminatingDynamicCost .revert sizeBytes offset length = 0 := by
  rw [terminatingDynamicCost_revert_eq]
  exact MemoryGas.revertDynamicCost_eq_zero_of_access_le h_access

/-- Whether the kind contributes a non-trivial dynamic gas component
through this wrapper (i.e. RETURN or REVERT). SELFDESTRUCT's dynamic
cost is modeled separately at the world-state layer. -/
def hasDynamicMemoryCost : TerminatingArgs.Kind → Bool
  | .stop => false
  | .return_ => true
  | .revert => true
  | .invalid => false
  | .selfdestruct => false

@[simp] theorem hasDynamicMemoryCost_return :
    hasDynamicMemoryCost .return_ = true := rfl

@[simp] theorem hasDynamicMemoryCost_revert :
    hasDynamicMemoryCost .revert = true := rfl

@[simp] theorem hasDynamicMemoryCost_stop :
    hasDynamicMemoryCost .stop = false := rfl

@[simp] theorem hasDynamicMemoryCost_invalid :
    hasDynamicMemoryCost .invalid = false := rfl

@[simp] theorem hasDynamicMemoryCost_selfdestruct :
    hasDynamicMemoryCost .selfdestruct = false := rfl

theorem terminatingDynamicCost_eq_zero_of_no_dynamic_cost
    {kind : TerminatingArgs.Kind} {sizeBytes offset length : Nat}
    (h_kind : hasDynamicMemoryCost kind = false) :
    terminatingDynamicCost kind sizeBytes offset length = 0 := by
  cases kind <;> simp_all [hasDynamicMemoryCost]

end TerminatingGas
end EvmAsm.Evm64
