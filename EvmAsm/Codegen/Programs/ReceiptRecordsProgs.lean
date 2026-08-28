/-
  EvmAsm.Codegen.Programs.ReceiptRecordsProgs

  The instruction lists of the two proof-first receipt-record bundle
  entries, as a `module`-side source of truth: `ReceiptRecords.lean`
  (module) emits these via `emitProgram`, and `ReceiptRecordsSAsm.lean`
  (non-module, DCode layer) pins by `#guard` that its generated code
  flattens to exactly these lists — tying the emitted bytes to the
  verified derivations across the module boundary (#12991).
-/

module

public import EvmAsm.Rv64.Program

@[expose] public section

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `receipt_records_init` (proof-first: `ReceiptRecordsSAsm.rriDeriv`
    flattens to exactly this list, pinned there by `#guard`). -/
def receiptRecordsInitProg : Program :=
  [ .SD .x10 .x0 (0 : BitVec 12),
    .SD .x10 .x11 (8 : BitVec 12),
    .SD .x10 .x12 (16 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- `receipt_records_clear` (proof-first: `ReceiptRecordsSAsm.rrcDeriv`
    flattens to exactly this list, pinned there by `#guard`). -/
def receiptRecordsClearProg : Program :=
  [ .SD .x10 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

end EvmAsm.Codegen
