/-
Placement guards for the CALL-family producer read emitted by
`precompileMessageProcessorAsm`.

Split out of `ChildFrameHandlerTails.lean` to stay under the 1500-line
`Codegen/Programs` file-size cap (`scripts/check-file-size.sh`), which does not
support per-file exceptions. The guards must live in a module that IMPORTS the
tail generator, since they evaluate its emitted string.
-/
import EvmAsm.Codegen.Programs.ChildFrameHandlerTails

namespace EvmAsm.Codegen

/-! ### Guards on the placement of the CALL-family producer read

    The producer must not be attached to the access-charge setup: that tail runs
    before the memory part of the initial static gas check. Value-bearing calls
    first pass the non-charging CALL_VALUE availability probe, then the producer
    runs; the branch-specific path performs the single actual charge later.
    `a0` is `x10`, so the producer uses the helper's save/restore wrapper.

    These guard the routing boundary: a later reorder cannot silently put the
    producer back before the static check or move it after the branch-specific
    precompile dispatch. -/

private def guardedCallTail : String :=
  precompileMessageProcessorAsm "call_target" 192 96 128 160 192 (some 64) "" false

-- The tail must not emit the former pre-charge producer sequence.
#guard
  (guardedCallTail.splitOn
    ("  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
     "  jal ra, account_read_record\n" ++
     "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
     "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n")).length = 1

-- The value-bearing tail emits its CALL_VALUE availability probe before the first
-- target producer read.
#guard
  (guardedCallTail.splitOn
    ("  beqz t3, .Lcvga_zero_call_target\n")).length = 2

-- The tail contains exactly two producer reads: its original target after the
-- initial static check, plus the successful delegation-resolution path. The helper
-- performs the second only after its 23-byte `ef0100||address` check and successful
-- same-block resolution.
#guard
  (guardedCallTail.splitOn
    "  jal ra, account_read_record\n").length = 3

end EvmAsm.Codegen
