/-
  EvmAsm.Rv64.WP.Call

  Call/return combinators for the WP certificate layer.  This packages the
  common `jal ra, callee` shape as a backward calculator step: after the JAL,
  the callee sees `ra = callerPC + 4`, and a normal RISC-V return reaches the
  aligned caller continuation.
-/

import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace WP

/-- Bounded CPS rule for a direct `jal ra, callee` call.

The callee may be any separately proved code requirement.  The caller JAL and
the callee code must be disjoint, and the continuation is the architectural
return address `callerPC + 4`. -/
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
      ((.x1 ↦ᵣ vOld) ** Prest) Q := by
  have hjal0 := generic_jal_spec_within .x1 vOld offset callerPC (by decide)
  rw [hoffset] at hjal0
  have hjal : cpsTripleWithin 1 callerPC calleeEntry
      (CodeReq.singleton callerPC (.JAL .x1 offset))
      ((.x1 ↦ᵣ vOld) ** Prest)
      ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) :=
    cpsTripleWithin_frameR Prest hPrest hjal0
  have hcallee' : cpsTripleWithin nSteps calleeEntry (callerPC + 4) calleeCode
      ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) Q := by
    rw [halign] at hcallee
    exact hcallee
  exact cpsTripleWithin_seq hdisj hjal hcallee'

namespace Triple

/-- Package a direct call as a WP triple.  The callee certificate may compute a
    stronger precondition; `hlink` connects the post-JAL state to that computed
    precondition. -/
def callWithin {callerPC calleeEntry : Word} {calleeCode : CodeReq}
    {Prest Q : Assertion} (offset : BitVec 21) (vOld : Word)
    (callee : Triple calleeEntry ((callerPC + 4) &&& ~~~(1 : Word)) calleeCode Q)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hPrest : Prest.pcFree)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint calleeCode)
    (hlink : Entails ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) callee.pre) :
    Triple callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union calleeCode) Q where
  nSteps := 1 + callee.nSteps
  pre := (.x1 ↦ᵣ vOld) ** Prest
  sound := cpsCallWithin offset hoffset halign hPrest hdisj
    (callee.weakenPre hlink).sound

end Triple

namespace CFG

/-- User-facing CFG constructor for a direct call. -/
def callWithin {callerPC calleeEntry : Word} {calleeCode : CodeReq}
    {Prest Q : Assertion} (offset : BitVec 21) (vOld : Word)
    (callee : Cert calleeEntry ((callerPC + 4) &&& ~~~(1 : Word)) calleeCode Q)
    (hoffset : callerPC + signExtend21 offset = calleeEntry)
    (halign : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (hPrest : Prest.pcFree)
    (hdisj : (CodeReq.singleton callerPC (.JAL .x1 offset)).Disjoint calleeCode)
    (hlink : Entails ((.x1 ↦ᵣ (callerPC + 4)) ** Prest) callee.pre) :
    Cert callerPC (callerPC + 4)
      ((CodeReq.singleton callerPC (.JAL .x1 offset)).union calleeCode) Q :=
  Triple.callWithin offset vOld callee hoffset halign hPrest hdisj hlink

end CFG

end WP
end EvmAsm.Rv64
