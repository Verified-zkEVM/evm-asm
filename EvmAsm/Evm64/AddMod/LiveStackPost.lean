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

@[irreducible]
def evmAddModPartialOwnedLiveStackFrame (sp base : Word) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordOwn sp ** evmWordOwn (sp + 32) **
  divScratchOwnCallNoX1 (sp + 32) **
  (.x1 ↦ᵣ ((base + 124) + 4))

theorem evmAddModPartialOwnedLiveStackFrame_unfold
    (sp base : Word) :
    evmAddModPartialOwnedLiveStackFrame sp base =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordOwn sp ** evmWordOwn (sp + 32) **
       divScratchOwnCallNoX1 (sp + 32) **
       (.x1 ↦ᵣ ((base + 124) + 4))) := by
  delta evmAddModPartialOwnedLiveStackFrame
  rfl

theorem evmAddModPartialOwnedLiveStackFrame_pcFree
    (sp base : Word) :
    (evmAddModPartialOwnedLiveStackFrame sp base).pcFree := by
  rw [evmAddModPartialOwnedLiveStackFrame_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialOwnedLiveStackFrame
    (sp base : Word) :
    Assertion.PCFree (evmAddModPartialOwnedLiveStackFrame sp base) :=
  ⟨evmAddModPartialOwnedLiveStackFrame_pcFree sp base⟩

@[irreducible]
def evmAddModPartialOwnedLiveStackPost (sp base : Word) (a b N : EvmWord) : Assertion :=
  ((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
  evmAddModPartialOwnedLiveStackFrame sp base

theorem evmAddModPartialOwnedLiveStackPost_unfold
    (sp base : Word) (a b N : EvmWord) :
    evmAddModPartialOwnedLiveStackPost sp base a b N =
      (((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
       evmAddModPartialOwnedLiveStackFrame sp base) := by
  delta evmAddModPartialOwnedLiveStackPost
  rfl

theorem evmAddModPartialOwnedLiveStackPost_pcFree
    (sp base : Word) (a b N : EvmWord) :
    (evmAddModPartialOwnedLiveStackPost sp base a b N).pcFree := by
  rw [evmAddModPartialOwnedLiveStackPost_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialOwnedLiveStackPost
    (sp base : Word) (a b N : EvmWord) :
    Assertion.PCFree (evmAddModPartialOwnedLiveStackPost sp base a b N) :=
  ⟨evmAddModPartialOwnedLiveStackPost_pcFree sp base a b N⟩

private theorem evmAddModPartialLiveStackFrame_to_ownedFrame
    {sp base : Word} {a b : EvmWord} {ps : PartialState}
    (h : evmAddModPartialLiveStackFrame sp base a b ps) :
    evmAddModPartialOwnedLiveStackFrame sp base ps := by
  rw [evmAddModPartialLiveStackFrame_unfold] at h
  rw [evmAddModPartialOwnedLiveStackFrame_unfold]
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (fun _ h => h)
      (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h)
            (sepConj_mono (fun _ h => h)
              (sepConj_mono (fun _ h => h)
                (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
                  (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
                    (sepConj_mono (fun _ h => h) (fun _ h => h)))))))))) _ h

theorem evmAddModPartialLiveStackPost_to_ownedLiveStackPost
    {sp base : Word} {a b N : EvmWord} {ps : PartialState}
    (h : evmAddModPartialLiveStackPost sp base a b N ps) :
    evmAddModPartialOwnedLiveStackPost sp base a b N ps := by
  rw [evmAddModPartialLiveStackPost_unfold] at h
  rw [evmAddModPartialOwnedLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => evmAddModPartialLiveStackFrame_to_ownedFrame h_frame) _ h

@[irreducible]
def evmAddModPartialReturnOwnedLiveStackFrame (sp : Word) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordOwn sp ** evmWordOwn (sp + 32) **
  divScratchOwnCallNoX1 (sp + 32) ** regOwn .x1

theorem evmAddModPartialReturnOwnedLiveStackFrame_unfold
    (sp : Word) :
    evmAddModPartialReturnOwnedLiveStackFrame sp =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordOwn sp ** evmWordOwn (sp + 32) **
       divScratchOwnCallNoX1 (sp + 32) ** regOwn .x1) := by
  delta evmAddModPartialReturnOwnedLiveStackFrame
  rfl

theorem evmAddModPartialReturnOwnedLiveStackFrame_pcFree
    (sp : Word) :
    (evmAddModPartialReturnOwnedLiveStackFrame sp).pcFree := by
  rw [evmAddModPartialReturnOwnedLiveStackFrame_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialReturnOwnedLiveStackFrame
    (sp : Word) :
    Assertion.PCFree (evmAddModPartialReturnOwnedLiveStackFrame sp) :=
  ⟨evmAddModPartialReturnOwnedLiveStackFrame_pcFree sp⟩

@[irreducible]
def evmAddModPartialReturnOwnedLiveStackPost
    (sp : Word) (a b N : EvmWord) : Assertion :=
  ((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
  evmAddModPartialReturnOwnedLiveStackFrame sp

theorem evmAddModPartialReturnOwnedLiveStackPost_unfold
    (sp : Word) (a b N : EvmWord) :
    evmAddModPartialReturnOwnedLiveStackPost sp a b N =
      (((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
       evmAddModPartialReturnOwnedLiveStackFrame sp) := by
  delta evmAddModPartialReturnOwnedLiveStackPost
  rfl

theorem evmAddModPartialReturnOwnedLiveStackPost_pcFree
    (sp : Word) (a b N : EvmWord) :
    (evmAddModPartialReturnOwnedLiveStackPost sp a b N).pcFree := by
  rw [evmAddModPartialReturnOwnedLiveStackPost_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialReturnOwnedLiveStackPost
    (sp : Word) (a b N : EvmWord) :
    Assertion.PCFree (evmAddModPartialReturnOwnedLiveStackPost sp a b N) :=
  ⟨evmAddModPartialReturnOwnedLiveStackPost_pcFree sp a b N⟩

private theorem evmAddModPartialOwnedLiveStackFrame_to_returnOwnedFrame
    {sp base : Word} {ps : PartialState}
    (h : evmAddModPartialOwnedLiveStackFrame sp base ps) :
    evmAddModPartialReturnOwnedLiveStackFrame sp ps := by
  rw [evmAddModPartialOwnedLiveStackFrame_unfold] at h
  rw [evmAddModPartialReturnOwnedLiveStackFrame_unfold]
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (fun _ h => h)
      (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h)
            (sepConj_mono (fun _ h => h)
              (sepConj_mono (fun _ h => h)
                (sepConj_mono (fun _ h => h)
                  (sepConj_mono (fun _ h => h)
                    (sepConj_mono (fun _ h => h)
                      (fun st h => regIs_implies_regOwn .x1 st h)))))))))) _ h

theorem evmAddModPartialOwnedLiveStackPost_to_returnOwnedLiveStackPost
    {sp base : Word} {a b N : EvmWord} {ps : PartialState}
    (h : evmAddModPartialOwnedLiveStackPost sp base a b N ps) :
    evmAddModPartialReturnOwnedLiveStackPost sp a b N ps := by
  rw [evmAddModPartialOwnedLiveStackPost_unfold] at h
  rw [evmAddModPartialReturnOwnedLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => evmAddModPartialOwnedLiveStackFrame_to_returnOwnedFrame h_frame) _ h

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


/-- Named-domain ADDMOD theorem with consumed operand cells weakened to
    ownership. The caller-visible live stack is isolated at `sp + 64`; the old
    input slots remain owned but unconstrained. -/
theorem evm_addmod_partial_domain_named_owned_live_stack_spec_within
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
      (evmAddModPartialOwnedLiveStackPost sp base a b N) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialLiveStackPost_to_ownedLiveStackPost hp)
    (evm_addmod_partial_domain_named_live_stack_spec_within
      sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      hcallable hbase hdisjoint hDomain)


/-- Named-domain ADDMOD theorem with the final live stack isolated at `sp + 64`,
    consumed operand cells owned, and the callable return register weakened to
    ownership. -/
theorem evm_addmod_partial_domain_named_return_owned_live_stack_spec_within
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
      (evmAddModPartialReturnOwnedLiveStackPost sp a b N) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialOwnedLiveStackPost_to_returnOwnedLiveStackPost hp)
    (evm_addmod_partial_domain_named_owned_live_stack_spec_within
      sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      hcallable hbase hdisjoint hDomain)

/-- Zero-modulus ADDMOD theorem with the current best live-stack post shape.

    This specializes the partial-domain theorem to the complete `N = 0` branch,
    avoiding the generic domain hypothesis while keeping the final live stack
    isolated at `sp + 64` and all consumed operand/return resources owned. -/
theorem evm_addmod_n0_return_owned_live_stack_spec_within
    (sp base callable_base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b (0 : EvmWord) v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModPartialReturnOwnedLiveStackPost sp a b (0 : EvmWord)) := by
  exact evm_addmod_partial_domain_named_return_owned_live_stack_spec_within
    sp base callable_base a b (0 : EvmWord) v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint (Or.inl rfl)

end EvmAsm.Evm64
