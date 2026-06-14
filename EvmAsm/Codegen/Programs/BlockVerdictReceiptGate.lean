/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptGate

  Small assembly snippets for block_verdict receipt-completeness classification.
-/

namespace EvmAsm.Codegen

/-- Clear the transaction-shape receipt enforcement classifier. -/
def bvReceiptsShapeClear : String :=
  "  la t0, bv_receipts_completeness_shape; sd zero, 0(t0)\n" ++
  "  la t0, bv_receipts_enforce_enabled; sd zero, 0(t0)\n"

/-- Set the receipt-completeness shape and enforcement bit. -/
def bvReceiptsShapeSet (shape : Nat) (enforce : Bool) : String :=
  "  li t1, " ++ toString shape ++
  "; la t0, bv_receipts_completeness_shape; sd t1, 0(t0); " ++
  "la t0, bv_receipts_enforce_enabled; " ++
  (if enforce then "li t1, 1; sd t1, 0(t0)\n" else "sd zero, 0(t0)\n")

/-- Clear the runtime-gas completeness classifier. -/
def bvRuntimeCompletenessClear : String :=
  "  la t0, bv_runtime_completeness_status; sd zero, 0(t0)\n"

/-- Set the runtime-gas completeness classifier. -/
def bvRuntimeCompletenessSet (status : Nat) : String :=
  "  li t1, " ++ toString status ++ "; la t0, bv_runtime_completeness_status; sd t1, 0(t0)\n"

/-- Classify a nonzero block_verdict_gas_result_arena_prepare status.
    Status 1/4 means tx gas extraction, arena capacity, or gas-result materialization debt;
    status 2/3 means runtime result count/pointers were incomplete. -/
def bvRuntimeCompletenessSetFromArenaStatus : String :=
  "  beqz a0, .Lbv_runtime_completeness_ok\n" ++
  "  li t0, 1; beq a0, t0, .Lbv_runtime_completeness_arena\n" ++
  "  li t0, 4; beq a0, t0, .Lbv_runtime_completeness_arena\n" ++
  "  li t1, 2; j .Lbv_runtime_completeness_store\n" ++
  ".Lbv_runtime_completeness_arena:\n" ++
  "  li t1, 1\n" ++
  ".Lbv_runtime_completeness_store:\n" ++
  "  la t0, bv_runtime_completeness_status; sd t1, 0(t0)\n" ++
  ".Lbv_runtime_completeness_ok:\n"

end EvmAsm.Codegen
