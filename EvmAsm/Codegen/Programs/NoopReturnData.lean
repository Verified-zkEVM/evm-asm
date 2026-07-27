/-
  EvmAsm.Codegen.Programs.NoopReturnData

  RETURNDATASIZE/RETURNDATACOPY runtime handlers split out of `Programs.Noop`.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Evm64.ReturnData.SizeProgram

namespace EvmAsm.Codegen

open EvmAsm.Evm64.ReturnData (evm_returndatasize)

/-- Runtime RETURNDATASIZE / RETURNDATACOPY handlers backed by
    `evm_precompile_frame`. -/
def returnDataHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_RETURNDATASIZE", opcodes := [0x3d]
    , preBody := stackOverflowGuardAsm ++ "\n" ++ "  la x14, evm_precompile_frame"
    , body := evm_returndatasize .x14 .x15
    , tail := .advanceAndRet 1 }
  , { label := "h_RETURNDATACOPY", opcodes := [0x3e]
    , body := []
    , tail := .custom <|
        "  ld x14, 0(x12)\n" ++
        "  ld x15, 32(x12)\n" ++
        "  ld x16, 64(x12)\n" ++
        memDynamicU256RangeOogGuardAsm
          "returndatacopy" "x12" "x16" "x17" "x18" 0 64 ++
        -- Unlike CODECOPY/CALLDATACOPY, RETURNDATACOPY does not zero-pad:
        -- any nonzero high limb in the source offset makes the requested
        -- range exceed returndata and must exceptionally halt.  A zero size
        -- still requires offset <= returndatasize, per execution-specs.
        "  ld x17, 40(x12)\n" ++
        "  ld x18, 48(x12)\n  or x17, x17, x18\n" ++
        "  ld x18, 56(x12)\n  or x17, x17, x18\n" ++
        "  bnez x17, .exit_invalid\n" ++
        "  la x17, evm_precompile_frame\n" ++
        "  ld x18, 8(x17)\n" ++
        -- Guards match execution-specs returndatacopy: (1) start+size wrap,
        -- (2) start+size > len(return_data) (true retlen at +8). No cap guard:
        -- staging (frame_return / precompile tails) always writes the full
        -- retlen bytes at +16 (retlen ≤ precompileFrameReturndataCapBytes), so
        -- guard (2) alone keeps the copy loop inside staged bytes.
        "  add x19, x15, x16\n" ++
        "  bltu x19, x15, .exit_invalid\n" ++
        "  bltu x18, x19, .exit_invalid\n" ++
        memDynamicArenaOogGuardAsm "returndatacopy" "x14" "x16" "x17" "x18" ++
        copyWordGasAsm "returndatacopy" "x16" "x17" "x18" "x19" ++
        updateActiveMemorySizeAsm "returndatacopy" "x14" "x16" "x17" "x18" "x19" "x6" true false ++
        "  addi x12, x12, 96\n" ++
        "  beqz x16, 2f\n" ++
        "  la x17, evm_precompile_frame\n" ++
        "  addi x17, x17, 16\n" ++
        "  add x17, x17, x15\n" ++
        "  add x18, x13, x14\n" ++
        "1:\n" ++
        "  lbu x19, 0(x17)\n" ++
        "  sb x19, 0(x18)\n" ++
        "  addi x17, x17, 1\n" ++
        "  addi x18, x18, 1\n" ++
        "  addi x16, x16, -1\n" ++
        "  bnez x16, 1b\n" ++
        "2:\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

end EvmAsm.Codegen
