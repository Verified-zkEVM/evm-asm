/-
Placement guards for the CALL-family producer read emitted by
`basicPrecompileCallTail`.

Split out of `ChildFrameHandlerTails.lean` to stay under the 1500-line
`Codegen/Programs` file-size cap (`scripts/check-file-size.sh`), which does not
support per-file exceptions. The guards must live in a module that IMPORTS the
tail generator, since they evaluate its emitted string.
-/
import EvmAsm.Codegen.Programs.ChildFrameHandlerTails

namespace EvmAsm.Codegen

/-! ### Guards on the placement of the CALL-family producer read

    `a0` IS `x10`, so `la a0, ...` clobbers it. The producer read is only safe in the
    interval the original code already ends with its own write of `x10` -- immediately
    BEFORE the `la a0, <seed scratch>` that opens the access-charge argument setup. The
    identical insert placed AFTER `runtime_access_account_charge` destroys live
    continuation state, which is how it broke in `extcodehashWitnessTail`.

    These guard the FUTURE form of that defect, not its current absence: a later
    reorder of this tail fails a guard here rather than a fixture somewhere else. -/

private def guardedCallTail : String :=
  basicPrecompileCallTail "call_target" 192 96 128 160 192 (some 64) "" false

-- The read must appear EXACTLY ONCE, sandwiched between our own `la a0` and the
-- ORIGINAL `la a0` that begins the charge's argument setup. `= 2` pins exactly one
-- occurrence, so a duplicated emission fails too.
#guard
  (guardedCallTail.splitOn
    ("  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
     "  jal ra, account_read_record\n" ++
     "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
     "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n")).length = 2

-- Negative guard: the read must NEVER sit immediately after the access charge, which
-- is exactly where `x10` is live and about to be spilled as continuation state.
-- `= 1` means zero occurrences of that sequence.
#guard
  (guardedCallTail.splitOn
    ("  jal ra, runtime_access_account_charge\n" ++
     "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
     "  jal ra, account_read_record\n")).length = 1


end EvmAsm.Codegen
