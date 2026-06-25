/-
  EvmAsm.Rv64.RLP.ValidatingFieldWalk

  Composition glue for the untrusted RLP field walker (F1 of the verified guest-decoder plan,
  #9373). The validating single-item decoders are 2-exit `cpsBranchWithin`s whose SUCCESS is the
  *taken* exit and FAIL the fall-through. To advance to the next field after a successful decode,
  we must sequence the pointer-advance instructions on the **taken** (success) exit — but the
  existing `cpsBranchWithin_seq_cpsTripleWithin_same_cr` (CPSSpec) only sequences on the fall side.

  `cpsBranchWithin_seq_cpsTripleWithin_taken` is the missing dual: it continues the taken branch
  into a follow-on triple (keeping the fall exit as the abort path), with a CodeReq union. It is the
  reusable step that turns "validating-decode at offset O" into "validating-decode-and-advance".
-/

import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64

/-- Sequence a triple onto the **taken** (success) exit of a branch, keeping the fall-through exit
    as the (abort) exit. Dual of `cpsBranchWithin_seq_cpsTripleWithin_same_cr`, with a CodeReq
    union. Bounds add. -/
theorem cpsBranchWithin_seq_cpsTripleWithin_taken {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q_t1 Q_f1 Q_t2 : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr1 P mid Q_t1 exit_f Q_f1)
    (h2 : cpsTripleWithin nSteps2 mid target cr2 Q_t1 Q_t2) :
    cpsBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P target Q_t2 exit_f Q_f1 := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr1 hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · -- taken (success): continue into the follow-on triple.
    have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQ_t2R⟩ := h2 R hR s1 hcr2' hQ_t1R hpc_t1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
      Or.inl ⟨hpc2, hQ_t2R⟩⟩
  · -- fall (abort): keep the fall-through exit.
    exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      Or.inr ⟨hpc_f1, hQ_f1R⟩⟩

end EvmAsm.Rv64
