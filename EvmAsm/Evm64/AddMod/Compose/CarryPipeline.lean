/-
  EvmAsm.Evm64.AddMod.Compose.CarryPipeline

  Phase-3 M3d for total ADDMOD (issue #9704): the carry-branch machine
  pipeline, composed via the FullPath pattern — every block extended onto the
  common code region `C = evm_addmod_total_program_code ∪ evm_mod_callable_code_v5`
  first, then chained with `cpsTripleWithin_seq_perm_same_cr` (one code region,
  no per-join union reconciliation).

  This file starts with the reusable code-extension brick every pipeline link
  needs (each non-callable block subsumes into the total program via its
  TotalBase `_sub`; the three MOD-call adapters carry the callable half too).
-/

import EvmAsm.Evm64.AddMod.Compose.CallAdapter
import EvmAsm.Evm64.AddMod.Compose.TotalBase

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- The common code region the whole carry branch runs over: the total ADDMOD
    program unioned with the appended v5 MOD callable. -/
abbrev addmodCarryCode (base : Word) (m1 m2 m3 mNC : BitVec 21)
    (calleeEntry : Word) : CodeReq :=
  (evm_addmod_total_program_code base m1 m2 m3 mNC).union
    (evm_mod_callable_code_v5 calleeEntry)

/-- Extend an arbitrary non-callable carry block from its own `ofProg` code
    (given a subsumption into the total program) onto the common region `C`.
    The block never touches the callable half, so plain `union_mono_left`
    (total ⊆ total ∪ callable) suffices after the block's `_sub`. -/
theorem carry_block_in_C
    {nSteps : Nat} {entry exit_ : Word} {blockCode totalCode calleeCode : CodeReq}
    {P Q : Assertion}
    (hsub : ∀ a i, blockCode a = some i → totalCode a = some i)
    (h : cpsTripleWithin nSteps entry exit_ blockCode P Q) :
    cpsTripleWithin nSteps entry exit_ (totalCode.union calleeCode) P Q :=
  cpsTripleWithin_extend_code
    (fun a i ha => CodeReq.union_mono_left a i (hsub a i ha)) h

/-- Extend one MOD-call adapter (`evm_addmod_v5_call_adapter`, over
    `singleton(JAL) ∪ callable`) onto the common region `C = totalCode ∪
    callable`. The JAL singleton subsumes into the total program via the
    call block's `_sub` (`hcallSub`); the callable half is shared, requiring
    only that the total program and the callable region are disjoint
    (`hdisjTC`, which holds because the callable sits after the total
    program's bytes). -/
theorem evm_addmod_v5_call_adapter_in_C
    (callPC F calleeEntry : Word) (modOff : BitVec 21) (divd divr : EvmWord)
    (x9In vOld v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (totalCode : CodeReq)
    (hoffset : callPC + signExtend21 modOff = calleeEntry)
    (callerAlign : (callPC + 4) &&& ~~~(1 : Word) = callPC + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton callPC (.JAL .x1 modOff)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hcallSub : ∀ a i,
      CodeReq.ofProg callPC (evm_addmod_carry_call_mod modOff) a = some i →
        totalCode a = some i)
    (hdisjTC : totalCode.Disjoint (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin (1 + (unifiedDivBound + 1)) callPC (callPC + 4)
      (totalCode.union (evm_mod_callable_code_v5 calleeEntry))
      ((divModStackDispatchPreNoX1 F divd divr x9In vOld v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) **
       ((F + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableX9Owned F divd divr (callPC + 4) **
       memOwn (F + signExtend12 3936)) := by
  -- singleton(JAL@callPC) ⊆ totalCode: it heads the call block's ofProg code.
  have hjalSub : ∀ a i, CodeReq.singleton callPC (.JAL .x1 modOff) a = some i →
      totalCode a = some i := by
    intro a i ha
    refine hcallSub a i ?_
    rw [← evm_addmod_carry_call_mod_code_eq_ofProg]
    exact CodeReq.union_mono_left a i ha
  refine cpsTripleWithin_extend_code
    (CodeReq.union_sub
      (fun a i ha => CodeReq.union_mono_left a i (hjalSub a i ha))
      (CodeReq.mono_union_right hdisjTC (fun _ _ h => h)))
    (evm_addmod_v5_call_adapter callPC F calleeEntry modOff divd divr
      x9In vOld v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hoffset callerAlign retAlign hdisj)

end EvmAsm.Evm64.AddMod.Compose
