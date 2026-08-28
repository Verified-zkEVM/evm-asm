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

/-- `receipt_records_append` (flat-layer spec:
    `ReceiptRecordsAppendSpec.lean`).  The `bgeu` at index 2 skips the
    18-instruction success arm to the capacity-full tail at index 18. -/
def receiptRecordsAppendProg : Program :=
  [ .LD .x5 .x10 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .BGEU .x5 .x6 (64 : BitVec 13),
    .LD .x7 .x10 (16 : BitVec 12),
    .SLLI .x28 .x5 (6 : BitVec 6),
    .ADD .x7 .x7 .x28,
    .SD .x7 .x11 (0 : BitVec 12),
    .SD .x7 .x12 (8 : BitVec 12),
    .SD .x7 .x13 (16 : BitVec 12),
    .SD .x7 .x14 (24 : BitVec 12),
    .SD .x7 .x15 (32 : BitVec 12),
    .SD .x7 .x16 (40 : BitVec 12),
    .SD .x7 .x17 (48 : BitVec 12),
    .SD .x7 .x0 (56 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .SD .x10 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- `receipt_records_append_runtime_result`: normalize the committed-log
    window, then TAIL-JUMP into `receipt_records_append` (the final `jal`
    targets bundle index 8 from bundle index 35: `(8 - 35) * 4 = -108`) —
    the cross-entry edge that makes this a genuine bundle (#12991). -/
def receiptRecordsAppendRuntimeProg : Program :=
  [ .BEQ .x12 .x0 (16 : BitVec 13),
    .BLTU .x15 .x14 (12 : BitVec 13),
    .SUB .x15 .x15 .x14,
    .JAL .x0 (8 : BitVec 21),
    .LI .x15 (0 : Word),
    .LI .x16 (0 : Word),
    .LI .x17 (0 : Word),
    .JAL .x0 (-108 : BitVec 21) ]

/-- `receipt_record_nth`: bounds check, then copy the 64-byte record out
    dword by dword.  The `bgeu` at index 1 skips to the out-of-bounds tail
    at index 23. -/
def receiptRecordNthProg : Program :=
  [ .LD .x5 .x10 (0 : BitVec 12),
    .BGEU .x11 .x5 (88 : BitVec 13),
    .LD .x6 .x10 (16 : BitVec 12),
    .SLLI .x7 .x11 (6 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .LD .x28 .x6 (0 : BitVec 12),
    .SD .x12 .x28 (0 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .SD .x12 .x28 (8 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .SD .x12 .x28 (16 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .SD .x12 .x28 (24 : BitVec 12),
    .LD .x28 .x6 (32 : BitVec 12),
    .SD .x12 .x28 (32 : BitVec 12),
    .LD .x28 .x6 (40 : BitVec 12),
    .SD .x12 .x28 (40 : BitVec 12),
    .LD .x28 .x6 (48 : BitVec 12),
    .SD .x12 .x28 (48 : BitVec 12),
    .LD .x28 .x6 (56 : BitVec 12),
    .SD .x12 .x28 (56 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- The FULL receipt-record bundle image, all five entries in emission
    order: init @0, clear @5, append @8, append_runtime_result @28,
    nth @36 (instruction indices; 61 instructions total). -/
def receiptRecordsBundleProg : Program :=
  (receiptRecordsInitProg : List Instr)
    ++ (receiptRecordsClearProg : List Instr)
    ++ (receiptRecordsAppendProg : List Instr)
    ++ (receiptRecordsAppendRuntimeProg : List Instr)
    ++ (receiptRecordNthProg : List Instr)

end EvmAsm.Codegen
