/-
  EvmAsm.Rv64.CPSCall

  A verified **call/return** combinator for `cpsTripleWithin`. The verified leaf
  subroutines (e.g. `rlp_walk_init`, `rlp_walk_next`, `rlp_content_to_u64`) are specified
  to return to `raVal &&& ~~~1`. `cpsCallWithin` composes a `jal ra, callee` (which links
  `ra := callerPC + 4` and jumps to the callee) with such a leaf spec, yielding a triple for
  the whole call that resumes at `callerPC + 4` — letting one verified routine call another
  without a bespoke per-call argument. Built from `generic_jal_spec_within` +
  `cpsTripleWithin_frameR` + `cpsTripleWithin_seq`; no new trust.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.GenericSpecs

namespace EvmAsm.Rv64

/-- Call a verified leaf subroutine and return. At `callerPC`, `jal ra, offset` links
    `ra := callerPC + 4` and jumps to the callee `calleeEntry = callerPC + sext offset`; the
    callee (preserving the caller's frame `Prest`) runs its triple with return address
    `callerPC + 4` and returns there. Result: from `callerPC`, in `1 + n` steps, reach
    `callerPC + 4` with the callee's postcondition, having clobbered `ra`. -/
theorem cpsCallWithin {n : Nat} {callerPC calleeEntry vOld : Word} {calleeCode : CodeReq}
    {Prest Q : Assertion} (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~1 = callerPC + 4)
    (hPrest : Prest.pcFree)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint calleeCode)
    (hcallee : cpsTripleWithin n calleeEntry ((callerPC + 4) &&& ~~~1) calleeCode
        ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) callerPC (callerPC + 4)
        ((CodeReq.singleton callerPC (.JAL .x1 offset)).union calleeCode)
        ((.x1 ↦ᵣ vOld) ** Prest) Q := by
  have hjal := generic_jal_spec_within .x1 vOld offset callerPC (by decide)
  rw [hoffset] at hjal
  have hjal' := cpsTripleWithin_frameR Prest hPrest hjal
  have hseq := cpsTripleWithin_seq hdisj hjal' hcallee
  rwa [halign] at hseq

end EvmAsm.Rv64
