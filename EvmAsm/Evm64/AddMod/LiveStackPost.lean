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

@[irreducible]
def evmAddModPartialRegsOwnedLiveStackFrame (sp : Word) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x0 **
  evmWordOwn sp ** evmWordOwn (sp + 32) **
  divScratchOwnCallNoX1 (sp + 32) ** regOwn .x1

theorem evmAddModPartialRegsOwnedLiveStackFrame_unfold
    (sp : Word) :
    evmAddModPartialRegsOwnedLiveStackFrame sp =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** regOwn .x0 **
       evmWordOwn sp ** evmWordOwn (sp + 32) **
       divScratchOwnCallNoX1 (sp + 32) ** regOwn .x1) := by
  delta evmAddModPartialRegsOwnedLiveStackFrame
  rfl

theorem evmAddModPartialRegsOwnedLiveStackFrame_pcFree
    (sp : Word) :
    (evmAddModPartialRegsOwnedLiveStackFrame sp).pcFree := by
  rw [evmAddModPartialRegsOwnedLiveStackFrame_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialRegsOwnedLiveStackFrame
    (sp : Word) :
    Assertion.PCFree (evmAddModPartialRegsOwnedLiveStackFrame sp) :=
  ⟨evmAddModPartialRegsOwnedLiveStackFrame_pcFree sp⟩

@[irreducible]
def evmAddModPartialRegsOwnedLiveStackPost
    (sp : Word) (a b N : EvmWord) : Assertion :=
  ((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
  evmAddModPartialRegsOwnedLiveStackFrame sp

theorem evmAddModPartialRegsOwnedLiveStackPost_unfold
    (sp : Word) (a b N : EvmWord) :
    evmAddModPartialRegsOwnedLiveStackPost sp a b N =
      (((.x12 ↦ᵣ (sp + 64)) ** evmStackIs (sp + 64) [EvmWord.addmod a b N]) **
       evmAddModPartialRegsOwnedLiveStackFrame sp) := by
  delta evmAddModPartialRegsOwnedLiveStackPost
  rfl

theorem evmAddModPartialRegsOwnedLiveStackPost_pcFree
    (sp : Word) (a b N : EvmWord) :
    (evmAddModPartialRegsOwnedLiveStackPost sp a b N).pcFree := by
  rw [evmAddModPartialRegsOwnedLiveStackPost_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialRegsOwnedLiveStackPost
    (sp : Word) (a b N : EvmWord) :
    Assertion.PCFree (evmAddModPartialRegsOwnedLiveStackPost sp a b N) :=
  ⟨evmAddModPartialRegsOwnedLiveStackPost_pcFree sp a b N⟩

private theorem evmAddModPartialReturnOwnedLiveStackFrame_to_regsOwnedFrame
    {sp : Word} {ps : PartialState}
    (h : evmAddModPartialReturnOwnedLiveStackFrame sp ps) :
    evmAddModPartialRegsOwnedLiveStackFrame sp ps := by
  rw [evmAddModPartialReturnOwnedLiveStackFrame_unfold] at h
  rw [evmAddModPartialRegsOwnedLiveStackFrame_unfold]
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (fun _ h => h)
      (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h)
            (sepConj_mono (fun _ h => h)
              (sepConj_mono (fun st h => regIs_implies_regOwn .x0 st h)
                (sepConj_mono (fun _ h => h)
                  (sepConj_mono (fun _ h => h)
                    (sepConj_mono (fun _ h => h) (fun _ h => h)))))))))) _ h

theorem evmAddModPartialReturnOwnedLiveStackPost_to_regsOwnedLiveStackPost
    {sp : Word} {a b N : EvmWord} {ps : PartialState}
    (h : evmAddModPartialReturnOwnedLiveStackPost sp a b N ps) :
    evmAddModPartialRegsOwnedLiveStackPost sp a b N ps := by
  rw [evmAddModPartialReturnOwnedLiveStackPost_unfold] at h
  rw [evmAddModPartialRegsOwnedLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => evmAddModPartialReturnOwnedLiveStackFrame_to_regsOwnedFrame h_frame) _ h

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

/-- Named-domain ADDMOD theorem with the final live stack isolated at `sp + 64`
    and all leftover registers in the current frame weakened to ownership. -/
theorem evm_addmod_partial_domain_named_regs_owned_live_stack_spec_within
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
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialReturnOwnedLiveStackPost_to_regsOwnedLiveStackPost hp)
    (evm_addmod_partial_domain_named_return_owned_live_stack_spec_within
      sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      hcallable hbase hdisjoint hDomain)

/-- Runtime-guard-domain ADDMOD theorem with the final live stack isolated at
    `sp + 64` and all leftover registers in the current frame weakened to
    ownership. This is the live-stack counterpart of
    `evm_addmod_partial_or_guard_named_stack_spec_within`. -/
theorem evm_addmod_partial_or_guard_named_regs_owned_live_stack_spec_within
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
      evmAddModPartialOrGuardDomain sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      evmAddModPartialReturnOwnedLiveStackPost_to_regsOwnedLiveStackPost
        (evmAddModPartialOwnedLiveStackPost_to_returnOwnedLiveStackPost
          (evmAddModPartialLiveStackPost_to_ownedLiveStackPost
            (evmAddModNoOverflowCallReturnStackPost_to_liveStackPost hp))))
    (evm_addmod_partial_or_guard_named_stack_spec_within
      sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      hcallable hbase hdisjoint hDomain)

/-- Hidden register/scratch witness for the current partial ADDMOD surface. -/
structure EvmAddModPartialPreWitness where
  v1 : Word
  v2 : Word
  v5 : Word
  v6 : Word
  v7 : Word
  v10 : Word
  v11 : Word
  q0 : Word
  q1 : Word
  q2 : Word
  q3 : Word
  u0 : Word
  u1 : Word
  u2 : Word
  u3 : Word
  u4 : Word
  u5 : Word
  u6 : Word
  u7 : Word
  nMem : Word
  shiftMem : Word
  jMem : Word
  retMem : Word
  dMem : Word
  dloMem : Word
  scratchUn0 : Word

@[irreducible]
def evmAddModPartialExistentialPre
    (sp base callable_base : Word) (a b N : EvmWord) : Assertion :=
  fun ps => ∃ w : EvmAddModPartialPreWitness,
    evmAddModPartialDomain sp base callable_base a b N w.v2 w.v10
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ∧
    evmAddModPartialStackPre sp a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps

theorem evmAddModPartialExistentialPre_unfold
    (sp base callable_base : Word) (a b N : EvmWord) :
    evmAddModPartialExistentialPre sp base callable_base a b N =
      (fun ps => ∃ w : EvmAddModPartialPreWitness,
        evmAddModPartialDomain sp base callable_base a b N w.v2 w.v10
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ∧
        evmAddModPartialStackPre sp a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps) := by
  delta evmAddModPartialExistentialPre
  rfl

@[irreducible]
def evmAddModPartialOrGuardExistentialPre
    (sp base callable_base : Word) (a b N : EvmWord) : Assertion :=
  fun ps => ∃ w : EvmAddModPartialPreWitness,
    evmAddModPartialOrGuardDomain sp base callable_base a b N w.v2 w.v10
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ∧
    evmAddModPartialStackPre sp a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps

theorem evmAddModPartialOrGuardExistentialPre_unfold
    (sp base callable_base : Word) (a b N : EvmWord) :
    evmAddModPartialOrGuardExistentialPre sp base callable_base a b N =
      (fun ps => ∃ w : EvmAddModPartialPreWitness,
        evmAddModPartialOrGuardDomain sp base callable_base a b N w.v2 w.v10
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ∧
        evmAddModPartialStackPre sp a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps) := by
  delta evmAddModPartialOrGuardExistentialPre
  rfl

/-- Current best partial ADDMOD theorem with implementation register/scratch
    witnesses hidden in the precondition. The precondition still carries the
    honest zero-or-no-overflow domain restriction. -/
theorem evm_addmod_partial_domain_existential_regs_owned_live_stack_spec_within
    (sp base callable_base : Word) (a b N : EvmWord) (modOff : BitVec 21)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialExistentialPre sp base callable_base a b N)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  rw [evmAddModPartialExistentialPre_unfold]
  intro R hR s hcr hpre hpc
  obtain ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreExists, hR2⟩ := hpre
  obtain ⟨w, hDomain, hStackPre⟩ := hpreExists
  exact evm_addmod_partial_domain_named_regs_owned_live_stack_spec_within
    sp base callable_base a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11 modOff
    w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
    w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0
    hcallable hbase hdisjoint hDomain R hR s hcr
    ⟨hh, hcompat, h1, h2, hdisj, hunion, hStackPre, hR2⟩ hpc

/-- Runtime-guard variant of the existential ADDMOD live-stack theorem. -/
theorem evm_addmod_partial_or_guard_existential_regs_owned_live_stack_spec_within
    (sp base callable_base : Word) (a b N : EvmWord) (modOff : BitVec 21)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialOrGuardExistentialPre sp base callable_base a b N)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  rw [evmAddModPartialOrGuardExistentialPre_unfold]
  intro R hR s hcr hpre hpc
  obtain ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreExists, hR2⟩ := hpre
  obtain ⟨w, hDomain, hStackPre⟩ := hpreExists
  exact evm_addmod_partial_or_guard_named_regs_owned_live_stack_spec_within
    sp base callable_base a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11 modOff
    w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
    w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0
    hcallable hbase hdisjoint hDomain R hR s hcr
    ⟨hh, hcompat, h1, h2, hdisj, hunion, hStackPre, hR2⟩ hpc

@[irreducible]
def evmAddModN0ExistentialPre
    (sp : Word) (a b : EvmWord) : Assertion :=
  fun ps => ∃ w : EvmAddModPartialPreWitness,
    evmAddModPartialStackPre sp a b (0 : EvmWord)
      w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps

theorem evmAddModN0ExistentialPre_unfold
    (sp : Word) (a b : EvmWord) :
    evmAddModN0ExistentialPre sp a b =
      (fun ps => ∃ w : EvmAddModPartialPreWitness,
        evmAddModPartialStackPre sp a b (0 : EvmWord)
          w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps) := by
  delta evmAddModN0ExistentialPre
  rfl

@[irreducible]
def evmAddModOrZeroExistentialPre
    (sp : Word) (a b N : EvmWord) : Assertion :=
  fun ps => ∃ w : EvmAddModPartialPreWitness,
    evmAddModPartialStackPre sp a b N
      w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps

theorem evmAddModOrZeroExistentialPre_unfold
    (sp : Word) (a b N : EvmWord) :
    evmAddModOrZeroExistentialPre sp a b N =
      (fun ps => ∃ w : EvmAddModPartialPreWitness,
        evmAddModPartialStackPre sp a b N
          w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps) := by
  delta evmAddModOrZeroExistentialPre
  rfl

@[irreducible]
def evmAddModNoOverflowExistentialPre
    (sp base callable_base : Word) (a b N : EvmWord) : Assertion :=
  fun ps => ∃ w : EvmAddModPartialPreWitness,
    evmAddModNoOverflowBodyEvidence sp base callable_base a b N w.v2 w.v10
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ∧
    evmAddModPartialStackPre sp a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
      w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
      w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps

theorem evmAddModNoOverflowExistentialPre_unfold
    (sp base callable_base : Word) (a b N : EvmWord) :
    evmAddModNoOverflowExistentialPre sp base callable_base a b N =
      (fun ps => ∃ w : EvmAddModPartialPreWitness,
        evmAddModNoOverflowBodyEvidence sp base callable_base a b N w.v2 w.v10
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ∧
        evmAddModPartialStackPre sp a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11
          w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
          w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0 ps) := by
  delta evmAddModNoOverflowExistentialPre
  rfl

@[irreducible]
def evmAddModCanonicalPartialExistentialPre
    (sp base : Word) (modOff : BitVec 21) (a b N : EvmWord) : Assertion :=
  evmAddModPartialExistentialPre sp base ((base + 124) + signExtend21 modOff) a b N

theorem evmAddModCanonicalPartialExistentialPre_unfold
    (sp base : Word) (modOff : BitVec 21) (a b N : EvmWord) :
    evmAddModCanonicalPartialExistentialPre sp base modOff a b N =
      evmAddModPartialExistentialPre sp base ((base + 124) + signExtend21 modOff) a b N := by
  delta evmAddModCanonicalPartialExistentialPre
  rfl

@[irreducible]
def evmAddModCanonicalPartialOrGuardExistentialPre
    (sp base : Word) (modOff : BitVec 21) (a b N : EvmWord) : Assertion :=
  evmAddModPartialOrGuardExistentialPre sp base ((base + 124) + signExtend21 modOff) a b N

theorem evmAddModCanonicalPartialOrGuardExistentialPre_unfold
    (sp base : Word) (modOff : BitVec 21) (a b N : EvmWord) :
    evmAddModCanonicalPartialOrGuardExistentialPre sp base modOff a b N =
      evmAddModPartialOrGuardExistentialPre sp base ((base + 124) + signExtend21 modOff) a b N := by
  delta evmAddModCanonicalPartialOrGuardExistentialPre
  rfl

/-- Current best partial ADDMOD theorem over the canonical combined code shape.
    The MOD callable base is computed from the ADDMOD call site instead of
    being carried as a separate theorem parameter. -/
theorem evm_addmod_partial_domain_canonical_existential_regs_owned_live_stack_spec_within
    (sp base : Word) (a b N : EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModCanonicalPartialExistentialPre sp base modOff a b N)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  rw [evmAddModCanonicalPartialExistentialPre_unfold]
  exact evm_addmod_partial_domain_existential_regs_owned_live_stack_spec_within
    sp base ((base + 124) + signExtend21 modOff) a b N modOff rfl hbase hdisjoint

/-- Runtime-guard variant of the canonical existential ADDMOD live-stack theorem. -/
theorem evm_addmod_partial_or_guard_canonical_existential_regs_owned_live_stack_spec_within
    (sp base : Word) (a b N : EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModCanonicalPartialOrGuardExistentialPre sp base modOff a b N)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  rw [evmAddModCanonicalPartialOrGuardExistentialPre_unfold]
  exact evm_addmod_partial_or_guard_existential_regs_owned_live_stack_spec_within
    sp base ((base + 124) + signExtend21 modOff) a b N modOff rfl hbase hdisjoint

@[irreducible]
def evmAddModCanonicalPartialExistentialStackTailPre
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  evmAddModCanonicalPartialExistentialPre sp base modOff a b N **
  evmStackIs (sp + 96) rest

theorem evmAddModCanonicalPartialExistentialStackTailPre_unfold
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModCanonicalPartialExistentialStackTailPre sp base modOff a b N rest =
      (evmAddModCanonicalPartialExistentialPre sp base modOff a b N **
       evmStackIs (sp + 96) rest) := by
  delta evmAddModCanonicalPartialExistentialStackTailPre
  rfl

@[irreducible]
def evmAddModCanonicalPartialOrGuardExistentialStackTailPre
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  evmAddModCanonicalPartialOrGuardExistentialPre sp base modOff a b N **
  evmStackIs (sp + 96) rest

theorem evmAddModCanonicalPartialOrGuardExistentialStackTailPre_unfold
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModCanonicalPartialOrGuardExistentialStackTailPre sp base modOff a b N rest =
      (evmAddModCanonicalPartialOrGuardExistentialPre sp base modOff a b N **
       evmStackIs (sp + 96) rest) := by
  delta evmAddModCanonicalPartialOrGuardExistentialStackTailPre
  rfl

@[irreducible]
def evmAddModPartialRegsOwnedLiveStackTailPost
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  ((.x12 ↦ᵣ (sp + 64)) **
    evmStackIs (sp + 64) (EvmWord.addmod a b N :: rest)) **
  evmAddModPartialRegsOwnedLiveStackFrame sp

theorem evmAddModPartialRegsOwnedLiveStackTailPost_unfold
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest =
      (((.x12 ↦ᵣ (sp + 64)) **
        evmStackIs (sp + 64) (EvmWord.addmod a b N :: rest)) **
       evmAddModPartialRegsOwnedLiveStackFrame sp) := by
  delta evmAddModPartialRegsOwnedLiveStackTailPost
  rfl

theorem evmAddModPartialRegsOwnedLiveStackTailPost_pcFree
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) :
    (evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest).pcFree := by
  rw [evmAddModPartialRegsOwnedLiveStackTailPost_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialRegsOwnedLiveStackTailPost
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree (evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest) :=
  ⟨evmAddModPartialRegsOwnedLiveStackTailPost_pcFree sp a b N rest⟩

private theorem evmAddModPartialRegsOwnedLiveStackPost_tail_to_tailPost
    {sp : Word} {a b N : EvmWord} {rest : List EvmWord} {ps : PartialState}
    (h : (evmAddModPartialRegsOwnedLiveStackPost sp a b N **
           evmStackIs (sp + 96) rest) ps) :
    evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest ps := by
  rw [evmAddModPartialRegsOwnedLiveStackPost_unfold] at h
  rw [evmStackIs_single] at h
  rw [evmAddModPartialRegsOwnedLiveStackTailPost_unfold, evmStackIs_cons]
  rw [show (sp + 64 + 32 : Word) = sp + 96 from by bv_omega]
  xperm_hyp h

/-- Current partial ADDMOD theorem with an arbitrary caller stack tail framed
    through the verified zero-or-no-overflow canonical code surface. -/
theorem evm_addmod_partial_domain_canonical_existential_regs_owned_stack_tail_spec_within
    (sp base : Word) (a b N : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModCanonicalPartialExistentialStackTailPre sp base modOff a b N rest)
      (evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest) := by
  rw [evmAddModCanonicalPartialExistentialStackTailPre_unfold]
  have hFramed := cpsTripleWithin_frameR (evmStackIs (sp + 96) rest)
    pcFree_evmStackIs
    (evm_addmod_partial_domain_canonical_existential_regs_owned_live_stack_spec_within
      sp base a b N modOff hbase hdisjoint)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialRegsOwnedLiveStackPost_tail_to_tailPost hp)
    hFramed

/-- Runtime-guard variant of the current partial ADDMOD stack-tail theorem. -/
theorem evm_addmod_partial_or_guard_canonical_existential_regs_owned_stack_tail_spec_within
    (sp base : Word) (a b N : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModCanonicalPartialOrGuardExistentialStackTailPre sp base modOff a b N rest)
      (evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest) := by
  rw [evmAddModCanonicalPartialOrGuardExistentialStackTailPre_unfold]
  have hFramed := cpsTripleWithin_frameR (evmStackIs (sp + 96) rest)
    pcFree_evmStackIs
    (evm_addmod_partial_or_guard_canonical_existential_regs_owned_live_stack_spec_within
      sp base a b N modOff hbase hdisjoint)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialRegsOwnedLiveStackPost_tail_to_tailPost hp)
    hFramed

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

/-- Zero-modulus ADDMOD theorem with the stronger current live-stack post:
    the result stack is isolated at `sp + 64` and all leftover registers in the
    current frame are owned. -/
theorem evm_addmod_n0_regs_owned_live_stack_spec_within
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
      (evmAddModPartialRegsOwnedLiveStackPost sp a b (0 : EvmWord)) := by
  exact evm_addmod_partial_domain_named_regs_owned_live_stack_spec_within
    sp base callable_base a b (0 : EvmWord) v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint (Or.inl rfl)

/-- Zero-modulus ADDMOD theorem with implementation register/scratch witnesses
    hidden in the precondition. -/
theorem evm_addmod_n0_existential_regs_owned_live_stack_spec_within
    (sp base callable_base : Word) (a b : EvmWord) (modOff : BitVec 21)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModN0ExistentialPre sp a b)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b (0 : EvmWord)) := by
  rw [evmAddModN0ExistentialPre_unfold]
  intro R hR s hcr hpre hpc
  obtain ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreExists, hR2⟩ := hpre
  obtain ⟨w, hStackPre⟩ := hpreExists
  exact evm_addmod_n0_regs_owned_live_stack_spec_within
    sp base callable_base a b w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11 modOff
    w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
    w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0
    hcallable hbase hdisjoint R hR s hcr
    ⟨hh, hcompat, h1, h2, hdisj, hunion, hStackPre, hR2⟩ hpc

/-- Canonical-code zero-modulus ADDMOD theorem with implementation
    register/scratch witnesses hidden in the precondition. -/
theorem evm_addmod_n0_canonical_existential_regs_owned_live_stack_spec_within
    (sp base : Word) (a b : EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModN0ExistentialPre sp a b)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b (0 : EvmWord)) := by
  exact evm_addmod_n0_existential_regs_owned_live_stack_spec_within
    sp base ((base + 124) + signExtend21 modOff) a b modOff rfl hbase hdisjoint

@[irreducible]
def evmAddModN0ExistentialStackTailPre
    (sp : Word) (a b : EvmWord) (rest : List EvmWord) : Assertion :=
  evmAddModN0ExistentialPre sp a b ** evmStackIs (sp + 96) rest

theorem evmAddModN0ExistentialStackTailPre_unfold
    (sp : Word) (a b : EvmWord) (rest : List EvmWord) :
    evmAddModN0ExistentialStackTailPre sp a b rest =
      (evmAddModN0ExistentialPre sp a b ** evmStackIs (sp + 96) rest) := by
  delta evmAddModN0ExistentialStackTailPre
  rfl

@[irreducible]
def evmAddModOrZeroExistentialStackTailPre
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  evmAddModOrZeroExistentialPre sp a b N ** evmStackIs (sp + 96) rest

theorem evmAddModOrZeroExistentialStackTailPre_unfold
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModOrZeroExistentialStackTailPre sp a b N rest =
      (evmAddModOrZeroExistentialPre sp a b N ** evmStackIs (sp + 96) rest) := by
  delta evmAddModOrZeroExistentialStackTailPre
  rfl

@[irreducible]
def evmAddModOrZeroDomainStackTailPre
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps =>
    N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 =
      (0 : Word) ∧
    evmAddModOrZeroExistentialStackTailPre sp a b N rest ps

theorem evmAddModOrZeroDomainStackTailPre_unfold
    (sp : Word) (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModOrZeroDomainStackTailPre sp a b N rest =
      (fun ps =>
        N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 =
          (0 : Word) ∧
        evmAddModOrZeroExistentialStackTailPre sp a b N rest ps) := by
  delta evmAddModOrZeroDomainStackTailPre
  rfl

/-- Canonical-code zero-modulus ADDMOD theorem with an arbitrary caller stack
    tail preserved through the result stack. -/
theorem evm_addmod_n0_canonical_existential_regs_owned_stack_tail_spec_within
    (sp base : Word) (a b : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModN0ExistentialStackTailPre sp a b rest)
      (evmAddModPartialRegsOwnedLiveStackTailPost sp a b (0 : EvmWord) rest) := by
  rw [evmAddModN0ExistentialStackTailPre_unfold]
  have hFramed := cpsTripleWithin_frameR (evmStackIs (sp + 96) rest)
    pcFree_evmStackIs
    (evm_addmod_n0_canonical_existential_regs_owned_live_stack_spec_within
      sp base a b modOff hbase hdisjoint)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialRegsOwnedLiveStackPost_tail_to_tailPost hp)
    hFramed

@[irreducible]
def evmAddModN0RegsOwnedLiveStackTailPost
    (sp : Word) (rest : List EvmWord) : Assertion :=
  ((.x12 ↦ᵣ (sp + 64)) **
    evmStackIs (sp + 64) ((0 : EvmWord) :: rest)) **
  evmAddModPartialRegsOwnedLiveStackFrame sp

theorem evmAddModN0RegsOwnedLiveStackTailPost_unfold
    (sp : Word) (rest : List EvmWord) :
    evmAddModN0RegsOwnedLiveStackTailPost sp rest =
      (((.x12 ↦ᵣ (sp + 64)) **
        evmStackIs (sp + 64) ((0 : EvmWord) :: rest)) **
       evmAddModPartialRegsOwnedLiveStackFrame sp) := by
  delta evmAddModN0RegsOwnedLiveStackTailPost
  rfl

theorem evmAddModN0RegsOwnedLiveStackTailPost_pcFree
    (sp : Word) (rest : List EvmWord) :
    (evmAddModN0RegsOwnedLiveStackTailPost sp rest).pcFree := by
  rw [evmAddModN0RegsOwnedLiveStackTailPost_unfold]
  pcFree

instance pcFreeInst_evmAddModN0RegsOwnedLiveStackTailPost
    (sp : Word) (rest : List EvmWord) :
    Assertion.PCFree (evmAddModN0RegsOwnedLiveStackTailPost sp rest) :=
  ⟨evmAddModN0RegsOwnedLiveStackTailPost_pcFree sp rest⟩

private theorem evmAddModPartialRegsOwnedLiveStackTailPost_n0_to_zeroPost
    {sp : Word} {a b : EvmWord} {rest : List EvmWord} {ps : PartialState}
    (h : evmAddModPartialRegsOwnedLiveStackTailPost sp a b (0 : EvmWord) rest ps) :
    evmAddModN0RegsOwnedLiveStackTailPost sp rest ps := by
  rw [evmAddModPartialRegsOwnedLiveStackTailPost_unfold] at h
  rw [evmAddModN0RegsOwnedLiveStackTailPost_unfold]
  simpa using h

/-- Canonical-code zero-modulus ADDMOD theorem with the result stack exposed as
    the concrete zero word, preserving an arbitrary caller stack tail. -/
theorem evm_addmod_n0_canonical_existential_regs_owned_zero_stack_tail_spec_within
    (sp base : Word) (a b : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModN0ExistentialStackTailPre sp a b rest)
      (evmAddModN0RegsOwnedLiveStackTailPost sp rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialRegsOwnedLiveStackTailPost_n0_to_zeroPost hp)
    (evm_addmod_n0_canonical_existential_regs_owned_stack_tail_spec_within
      sp base a b rest modOff hbase hdisjoint)

/-- Canonical-code ADDMOD theorem for the zero-test branch, with the modulus
    supplied in the stack precondition and the runtime OR-fold guard supplied
    as a hypothesis. The result stack is exposed as the concrete zero word. -/
theorem evm_addmod_or_zero_canonical_existential_regs_owned_zero_stack_tail_spec_within
    (sp base : Word) (a b N : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hOr : N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 =
      (0 : Word))
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModOrZeroExistentialStackTailPre sp a b N rest)
      (evmAddModN0RegsOwnedLiveStackTailPost sp rest) := by
  have hN : N = (0 : EvmWord) := (addmod_orAll_limbs_eq_zero_iff N).mp hOr
  subst N
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmAddModOrZeroExistentialStackTailPre_unfold,
        evmAddModOrZeroExistentialPre_unfold] at hp
      rw [evmAddModN0ExistentialStackTailPre_unfold, evmAddModN0ExistentialPre_unfold]
      exact hp)
    (fun _ hp => hp)
    (evm_addmod_n0_canonical_existential_regs_owned_zero_stack_tail_spec_within
      sp base a b rest modOff hbase hdisjoint)

/-- Canonical-code ADDMOD theorem for the zero-test branch with the runtime
    OR-fold guard packaged in the precondition. The result stack is exposed as
    the concrete zero word. -/
theorem evm_addmod_or_zero_domain_canonical_existential_regs_owned_zero_stack_tail_spec_within
    (sp base : Word) (a b N : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModOrZeroDomainStackTailPre sp a b N rest)
      (evmAddModN0RegsOwnedLiveStackTailPost sp rest) := by
  rw [evmAddModOrZeroDomainStackTailPre_unfold]
  intro R hR s hcr hpre hpc
  obtain ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreDomain, hR2⟩ := hpre
  exact evm_addmod_or_zero_canonical_existential_regs_owned_zero_stack_tail_spec_within
    sp base a b N rest modOff hpreDomain.1 hbase hdisjoint R hR s hcr
    ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreDomain.2, hR2⟩ hpc

/-- No-overflow ADDMOD theorem with the current best live-stack post shape.

    This specializes the partial-domain theorem to the currently composed
    nonzero path: the addition `a + b` does not overflow and the legacy MOD
    no-NOP body evidence is supplied. -/
theorem evm_addmod_no_overflow_return_owned_live_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hEvidence :
      evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModPartialReturnOwnedLiveStackPost sp a b N) := by
  exact evm_addmod_partial_domain_named_return_owned_live_stack_spec_within
    sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint (Or.inr ⟨hNoOverflow, hEvidence⟩)

/-- No-overflow ADDMOD theorem with the stronger current live-stack post:
    the result stack is isolated at `sp + 64` and all leftover registers in the
    current frame are owned. -/
theorem evm_addmod_no_overflow_regs_owned_live_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hEvidence :
      evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  exact evm_addmod_partial_domain_named_regs_owned_live_stack_spec_within
    sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint (Or.inr ⟨hNoOverflow, hEvidence⟩)

/-- No-overflow ADDMOD theorem with implementation register/scratch witnesses and
    the legacy MOD body evidence hidden in the precondition. The arithmetic
    no-overflow fact remains an explicit input-domain hypothesis. -/
theorem evm_addmod_no_overflow_existential_regs_owned_live_stack_spec_within
    (sp base callable_base : Word) (a b N : EvmWord) (modOff : BitVec 21)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModNoOverflowExistentialPre sp base callable_base a b N)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  rw [evmAddModNoOverflowExistentialPre_unfold]
  intro R hR s hcr hpre hpc
  obtain ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreExists, hR2⟩ := hpre
  obtain ⟨w, hEvidence, hStackPre⟩ := hpreExists
  exact evm_addmod_no_overflow_regs_owned_live_stack_spec_within
    sp base callable_base a b N w.v1 w.v2 w.v5 w.v6 w.v7 w.v10 w.v11 modOff
    w.q0 w.q1 w.q2 w.q3 w.u0 w.u1 w.u2 w.u3 w.u4 w.u5 w.u6 w.u7
    w.nMem w.shiftMem w.jMem w.retMem w.dMem w.dloMem w.scratchUn0
    hNoOverflow hcallable hbase hdisjoint hEvidence R hR s hcr
    ⟨hh, hcompat, h1, h2, hdisj, hunion, hStackPre, hR2⟩ hpc

/-- Canonical-code no-overflow ADDMOD theorem with implementation
    register/scratch witnesses and the legacy MOD body evidence hidden in the
    precondition. The arithmetic no-overflow fact remains explicit. -/
theorem evm_addmod_no_overflow_canonical_existential_regs_owned_live_stack_spec_within
    (sp base : Word) (a b N : EvmWord) (modOff : BitVec 21)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModNoOverflowExistentialPre
        sp base ((base + 124) + signExtend21 modOff) a b N)
      (evmAddModPartialRegsOwnedLiveStackPost sp a b N) := by
  exact evm_addmod_no_overflow_existential_regs_owned_live_stack_spec_within
    sp base ((base + 124) + signExtend21 modOff) a b N modOff hNoOverflow rfl hbase hdisjoint

@[irreducible]
def evmAddModCanonicalNoOverflowExistentialStackTailPre
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  evmAddModNoOverflowExistentialPre
    sp base ((base + 124) + signExtend21 modOff) a b N **
  evmStackIs (sp + 96) rest

theorem evmAddModCanonicalNoOverflowExistentialStackTailPre_unfold
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModCanonicalNoOverflowExistentialStackTailPre sp base modOff a b N rest =
      (evmAddModNoOverflowExistentialPre
        sp base ((base + 124) + signExtend21 modOff) a b N **
       evmStackIs (sp + 96) rest) := by
  delta evmAddModCanonicalNoOverflowExistentialStackTailPre
  rfl

/-- Canonical-code no-overflow ADDMOD theorem with an arbitrary caller stack
    tail preserved through the result stack. -/
theorem evm_addmod_no_overflow_canonical_existential_regs_owned_stack_tail_spec_within
    (sp base : Word) (a b N : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModCanonicalNoOverflowExistentialStackTailPre sp base modOff a b N rest)
      (evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest) := by
  rw [evmAddModCanonicalNoOverflowExistentialStackTailPre_unfold]
  have hFramed := cpsTripleWithin_frameR (evmStackIs (sp + 96) rest)
    pcFree_evmStackIs
    (evm_addmod_no_overflow_canonical_existential_regs_owned_live_stack_spec_within
      sp base a b N modOff hNoOverflow hbase hdisjoint)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModPartialRegsOwnedLiveStackPost_tail_to_tailPost hp)
    hFramed

@[irreducible]
def evmAddModCanonicalNoOverflowDomainStackTailPre
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps =>
    a.toNat + b.toNat < 2 ^ 256 ∧
    evmAddModCanonicalNoOverflowExistentialStackTailPre sp base modOff a b N rest ps

theorem evmAddModCanonicalNoOverflowDomainStackTailPre_unfold
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModCanonicalNoOverflowDomainStackTailPre sp base modOff a b N rest =
      (fun ps =>
        a.toNat + b.toNat < 2 ^ 256 ∧
        evmAddModCanonicalNoOverflowExistentialStackTailPre sp base modOff a b N rest ps) := by
  delta evmAddModCanonicalNoOverflowDomainStackTailPre
  rfl

/-- Canonical-code no-overflow ADDMOD theorem with the arithmetic domain fact
    packaged in the precondition, preserving an arbitrary caller stack tail. -/
theorem evm_addmod_no_overflow_domain_canonical_existential_regs_owned_stack_tail_spec_within
    (sp base : Word) (a b N : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModCanonicalNoOverflowDomainStackTailPre sp base modOff a b N rest)
      (evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest) := by
  rw [evmAddModCanonicalNoOverflowDomainStackTailPre_unfold]
  intro R hR s hcr hpre hpc
  obtain ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreDomain, hR2⟩ := hpre
  obtain ⟨hNoOverflow, hpreStack⟩ := hpreDomain
  exact evm_addmod_no_overflow_canonical_existential_regs_owned_stack_tail_spec_within
    sp base a b N rest modOff hNoOverflow hbase hdisjoint R hR s hcr
    ⟨hh, hcompat, h1, h2, hdisj, hunion, hpreStack, hR2⟩ hpc

@[irreducible]
def evmAddModCanonicalPartialOrGuardDomainStackTailPre
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) : Assertion :=
  evmAddModCanonicalPartialOrGuardExistentialStackTailPre sp base modOff a b N rest

theorem evmAddModCanonicalPartialOrGuardDomainStackTailPre_unfold
    (sp base : Word) (modOff : BitVec 21)
    (a b N : EvmWord) (rest : List EvmWord) :
    evmAddModCanonicalPartialOrGuardDomainStackTailPre sp base modOff a b N rest =
      evmAddModCanonicalPartialOrGuardExistentialStackTailPre sp base modOff a b N rest := by
  delta evmAddModCanonicalPartialOrGuardDomainStackTailPre
  rfl

/-- Canonical-code ADDMOD stack-tail theorem using the runtime OR-guard partial
    domain hidden-witness precondition. This aliases the current existential
    guard surface under the domain-tail naming used by callers. -/
theorem evm_addmod_partial_or_guard_domain_canonical_existential_regs_owned_stack_tail_spec_within
    (sp base : Word) (a b N : EvmWord) (rest : List EvmWord) (modOff : BitVec 21)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      (evmAddModCanonicalPartialOrGuardDomainStackTailPre sp base modOff a b N rest)
      (evmAddModPartialRegsOwnedLiveStackTailPost sp a b N rest) := by
  rw [evmAddModCanonicalPartialOrGuardDomainStackTailPre_unfold]
  exact evm_addmod_partial_or_guard_canonical_existential_regs_owned_stack_tail_spec_within
    sp base a b N rest modOff hbase hdisjoint

end EvmAsm.Evm64
