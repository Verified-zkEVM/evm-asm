/-
  EvmAsm.Codegen.Programs.StaticContext

  Shared assembly snippets for EVM static-context write protection.
-/

namespace EvmAsm.Codegen

/-- Per-frame env flag: nonzero when the current frame is executing under
    STATICCALL. Sits between codeSize (496) and the block/blob trailer (512). -/
def staticContextFlagOff : Nat := 504

/-- Abort state-changing opcodes in a static context.
    The dispatcher supplies `.exit_static_violation`; child frames return
    failure to their parent, while depth-0 reports an INVALID-style halt. -/
def staticContextWriteGuardAsm : String :=
  "  ld x14, " ++ toString staticContextFlagOff ++ "(x20)\n" ++
  "  bnez x14, .exit_static_violation\n"

/-- Abort a value-bearing CALL in a static context when the value word is nonzero.
    EIP-214 excludes CALLCODE from this write-protection rule. -/
def staticContextValueTransferGuardAsm (valueOff : Nat) : String :=
  "  ld x14, " ++ toString valueOff ++ "(x12)\n" ++
  "  ld x15, " ++ toString (valueOff + 8) ++ "(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, " ++ toString (valueOff + 16) ++ "(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, " ++ toString (valueOff + 24) ++ "(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  beqz x14, 1f\n" ++
  "  ld x15, " ++ toString staticContextFlagOff ++ "(x20)\n" ++
  "  bnez x15, .exit_static_violation\n" ++
  "1:\n"

end EvmAsm.Codegen
