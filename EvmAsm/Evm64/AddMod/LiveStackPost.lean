/-
  EvmAsm.Evm64.AddMod.LiveStackPost

  Live-stack post surface for the current partial ADDMOD theorem.
-/

import EvmAsm.Evm64.AddMod.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.AddMod.Compose

@[irreducible]
def evmAddModPartialLiveStackFrame (sp base : Word) (a b : EvmWord) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (a + b) **
  divScratchOwnCallNoX1 (sp + 32) **
  (.x1 ↦ᵣ ((base + 124) + 4))

theorem evmAddModPartialLiveStackFrame_unfold
    (sp base : Word) (a b : EvmWord) :
    evmAddModPartialLiveStackFrame sp base a b =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b) **
       divScratchOwnCallNoX1 (sp + 32) **
       (.x1 ↦ᵣ ((base + 124) + 4))) := by
  delta evmAddModPartialLiveStackFrame
  rfl

theorem evmAddModPartialLiveStackFrame_pcFree
    (sp base : Word) (a b : EvmWord) :
    (evmAddModPartialLiveStackFrame sp base a b).pcFree := by
  rw [evmAddModPartialLiveStackFrame_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialLiveStackFrame
    (sp base : Word) (a b : EvmWord) :
    Assertion.PCFree (evmAddModPartialLiveStackFrame sp base a b) :=
  ⟨evmAddModPartialLiveStackFrame_pcFree sp base a b⟩

@[irreducible]
def evmAddModPartialLiveStackPost (sp base : Word) (a b N : EvmWord) : Assertion :=
  ((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
  evmAddModPartialLiveStackFrame sp base a b

theorem evmAddModPartialLiveStackPost_unfold
    (sp base : Word) (a b N : EvmWord) :
    evmAddModPartialLiveStackPost sp base a b N =
      (((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
       evmAddModPartialLiveStackFrame sp base a b) := by
  delta evmAddModPartialLiveStackPost
  rfl

theorem evmAddModPartialLiveStackPost_pcFree
    (sp base : Word) (a b N : EvmWord) :
    (evmAddModPartialLiveStackPost sp base a b N).pcFree := by
  rw [evmAddModPartialLiveStackPost_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialLiveStackPost
    (sp base : Word) (a b N : EvmWord) :
    Assertion.PCFree (evmAddModPartialLiveStackPost sp base a b N) :=
  ⟨evmAddModPartialLiveStackPost_pcFree sp base a b N⟩

theorem evmAddModNoOverflowCallReturnStackPost_to_liveStackPost
    {sp base : Word} {a b N : EvmWord} {ps : PartialState}
    (h : evmAddModNoOverflowCallReturnStackPost sp base a b N ps) :
    evmAddModPartialLiveStackPost sp base a b N ps := by
  rw [evmAddModNoOverflowCallReturnStackPost_unfold] at h
  rw [evmAddModPartialLiveStackPost_unfold, evmAddModPartialLiveStackFrame_unfold]
  rw [evmStackIs_triple_flat] at h
  rw [evmStackIs_single]
  xperm_hyp h

/-- Named-domain ADDMOD theorem with the final live stack isolated at
    `sp + 64`. The old operand cells, scratch ownership, and remaining register
    resources are kept in `evmAddModPartialLiveStackFrame`. -/
theorem evm_addmod_partial_domain_named_live_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hDomain :
      evmAddModPartialDomain sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModPartialLiveStackPost sp base a b N) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModNoOverflowCallReturnStackPost_to_liveStackPost hp)
    (evm_addmod_partial_domain_named_stack_spec_within
      sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      hcallable hbase hdisjoint hDomain)

end EvmAsm.Evm64
