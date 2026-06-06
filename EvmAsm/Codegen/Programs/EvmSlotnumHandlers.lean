/-
  EvmAsm.Codegen.Programs.EvmSlotnumHandlers

  Dispatcher handler for EIP-7843 SLOTNUM.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- EIP-7843 SLOTNUM (0x4b). The runtime input trailer carries the current
    consensus slot number as a 256-bit stack word. The dispatcher prologue
    copies that word to `evm_env + 624`; this handler pushes it unchanged. -/
def slotnumContextHandlers : List OpcodeHandlerSpec :=
  let slotnumBody : Program :=
    ADDI .x12 .x12 (-32) ;;
    LD .x15 .x20 (BitVec.ofNat 12 624) ;;
    SD .x12 .x15 0 ;;
    LD .x15 .x20 (BitVec.ofNat 12 632) ;;
    SD .x12 .x15 8 ;;
    LD .x15 .x20 (BitVec.ofNat 12 640) ;;
    SD .x12 .x15 16 ;;
    LD .x15 .x20 (BitVec.ofNat 12 648) ;;
    SD .x12 .x15 24
  [ { label := "h_SLOTNUM"
    , opcodes := [0x4b]
    , body := slotnumBody
    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
