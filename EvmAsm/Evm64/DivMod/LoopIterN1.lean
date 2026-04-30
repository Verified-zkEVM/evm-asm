/-
  EvmAsm.Evm64.DivMod.LoopIterN1

  Umbrella file: re-exports the split LoopIterN1 sub-modules.

  Loop body cpsTripleWithin specs for n=1 (1-limb divisor). The generic LoopBodyN1
  cpsBranchWithin specs are specialized to specific j values to produce cpsTripleWithin
  specs using divK_store_loop_j0_spec_within (j=0) and divK_store_loop_jgt0_spec_within (j>0).

  For n=1, the loop runs 4 iterations (j=3 then j=2 then j=1 then j=0):
  - j=0 (final iteration): cpsTripleWithin base+448 → base+908
  - j=1, j=2, j=3:         cpsTripleWithin base+448 → base+448

  Split into:
  - LoopIterN1.Max:     BLTU not-taken path, non-BEQ addback
  - LoopIterN1.Call:    BLTU taken path, non-BEQ addback
  - LoopIterN1.MaxBeq:  BLTU not-taken path, BEQ double-addback
  - LoopIterN1.CallBeq: BLTU taken path, BEQ double-addback

  For n=1: BLTU compares u1 vs v0, div128 uses uHi=u1, uLo=u0, vTop=v0.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.Max
import EvmAsm.Evm64.DivMod.LoopIterN1.Call
import EvmAsm.Evm64.DivMod.LoopIterN1.MaxBeq
import EvmAsm.Evm64.DivMod.LoopIterN1.CallBeq
