/-
  EvmAsm.Rv64.CPSCall

  Compatibility import for direct-call composition.  New proof scripts should
  prefer `EvmAsm.Rv64.WP.Call`, but this root-level theorem keeps older
  #9522-style CPS scripts easy to adapt.
-/

import EvmAsm.Rv64.WP.Call

namespace EvmAsm.Rv64

/-- Root-namespace compatibility alias for `WP.cpsCallWithin`. -/
theorem cpsCallWithin {nSteps : Nat} {callerPC calleeEntry vOld : Word}
    {calleeCode : CodeReq} {Prest Q : Assertion} (offset : BitVec 21)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hPrest : Prest.pcFree)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint calleeCode)
    (hcallee : cpsTripleWithin nSteps calleeEntry ((callerPC + 4) &&& ~~~(1 : Word))
      calleeCode ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + nSteps) callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union calleeCode)
      ((.x1 ↦ᵣ vOld) ** Prest) Q :=
  WP.cpsCallWithin offset hoffset halign hPrest hdisj hcallee

end EvmAsm.Rv64
