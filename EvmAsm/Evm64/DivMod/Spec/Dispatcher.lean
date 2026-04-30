/-
  EvmAsm.Evm64.DivMod.Spec.Dispatcher

  Public stack-level dispatcher contract for DIV/MOD.
-/

import EvmAsm.Evm64.DivMod.Spec.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Final stack-dispatch precondition shared by DIV and MOD.

The contract intentionally keeps the caller-owned scratch registers as values
instead of hard-coding one branch's CLZ-derived register values. Branch proofs
can specialize this bundle before calling the existing n=1/2/3/4 path specs. -/
@[irreducible]
def divModStackDispatchPre (sp : Word) (a b : EvmWord)
    (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem

theorem divModStackDispatchPre_unfold {sp : Word} {a b : EvmWord}
    {v1 v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word} :
    divModStackDispatchPre sp a b v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem) := by
  delta divModStackDispatchPre
  rfl

/-- Final DIV stack-dispatch postcondition. -/
@[irreducible]
def divStackDispatchPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
  divScratchOwn sp

theorem divStackDispatchPost_unfold {sp : Word} {a b : EvmWord} :
    divStackDispatchPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
     divScratchOwn sp) := by
  delta divStackDispatchPost
  rfl

/-- Final MOD stack-dispatch postcondition. -/
@[irreducible]
def modStackDispatchPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
  divScratchOwn sp

theorem modStackDispatchPost_unfold {sp : Word} {a b : EvmWord} :
    modStackDispatchPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
     divScratchOwn sp) := by
  delta modStackDispatchPost
  rfl

end EvmAsm.Evm64
