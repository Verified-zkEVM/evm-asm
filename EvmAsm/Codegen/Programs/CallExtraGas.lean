/-
  EvmAsm.Codegen.Programs.CallExtraGas

  Standalone emitted program for the CALL-family extra-gas helper.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def callExtraGas_prog : Program :=
  [ .ADDI .x5 .x0 (100 : BitVec 12),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LUI .x5 (1 : BitVec 20),
    .ADDIW .x5 .x5 (-1496 : BitVec 12),
    .BEQ .x11 .x0 (16 : BitVec 13),
    .LUI .x6 (2 : BitVec 20),
    .ADDIW .x6 .x6 (808 : BitVec 12),
    .ADD .x5 .x5 .x6,
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

#guard callExtraGas_prog.length = 10

end EvmAsm.Codegen
