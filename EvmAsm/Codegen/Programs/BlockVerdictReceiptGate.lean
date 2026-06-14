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

end EvmAsm.Codegen
