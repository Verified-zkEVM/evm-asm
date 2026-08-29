/- A finite outer-loop fold for the K70 round adapter (#12851).

   The round proof exposes the ordinary exits followed by one QBACK exit.
   This file supplies the list-level induction that repeats that shape a
   finite number of times and then consumes a terminal continuation.  The
   state invariant and the arithmetic relation between successive states are
   intentionally supplied by the caller; this theorem does not weaken either
   the round post or the CodeReq.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundParityComposition

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen

set_option maxRecDepth 8000

/- Consume the last (QBACK) exit of one round with an arbitrary continuation.
   The ordinary exits in `terminal` remain available, while the continuation
   supplies the exits of the next round. -/
theorem nbranch_extend_last
    {n1 n2 : Nat} {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {terminal exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (terminal ++ [(mid, Q)]))
    (h2 : cpsNBranchWithin n2 mid cr Q exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P (terminal ++ exits2) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hterminal | hmid
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, List.mem_append.mpr (Or.inl hterminal), hpc1, hQ1⟩
  · rcases hmid with hmid | hnil
    · subst ex
      have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
      obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
        h2 R hR s1 hcr' hQ1 hpc1
      exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
        stepN_add_eq hstep1 hstep2, ex2,
        List.mem_append.mpr (Or.inr hmem2), hpc2, hQ2⟩
    · simp at hnil

/- When the continuation has the same terminal list as the current round,
   discard the duplicate copy introduced by ordinary list concatenation. -/
theorem nbranch_extend_last_same_terminal
    {n1 n2 : Nat} {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {terminal : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (terminal ++ [(mid, Q)]))
    (h2 : cpsNBranchWithin n2 mid cr Q terminal) :
    cpsNBranchWithin (n1 + n2) entry cr P terminal := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hterminal | hmid
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, hterminal, hpc1, hQ1⟩
  · rcases hmid with hmid | hnil
    · subst ex
      have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
      obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
        h2 R hR s1 hcr' hQ1 hpc1
      exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
        stepN_add_eq hstep1 hstep2, ex2, hmem2, hpc2, hQ2⟩
    · simp at hnil

/- A finite fold of a round with a fixed terminal exit list.  Each of the
   first `N` rounds has the same terminal list and a QBACK transition to the
   next invariant.  The final continuation is supplied separately at `inv N`;
   this avoids treating a zero-round run as if it had already reached a
   terminal arm. -/
theorem finite_nbranch_loop_spec
    {N m mLast : Nat} {hdr : Word} {cr : CodeReq}
    {inv : Nat → Assertion} {terminal : List (Word × Assertion)}
    (hround : ∀ j, j < N →
      cpsNBranchWithin m hdr cr (inv j)
        (terminal ++ [(hdr, inv (j + 1))]))
    (htail : cpsNBranchWithin mLast hdr cr (inv N) terminal) :
    cpsNBranchWithin (m * N + mLast) hdr cr (inv 0) terminal := by
  revert mLast inv
  induction N using Nat.strongRecOn with
  | _ N ih =>
      intro mLast inv hround htail
      cases N with
      | zero =>
          simpa using htail
      | succ N =>
          have hfirst := hround 0 (by omega)
          have hround' : ∀ j, j < N →
              cpsNBranchWithin m hdr cr (inv (j + 1))
                (terminal ++ [(hdr, inv ((j + 1) + 1))]) := by
            intro j hj
            exact hround (j + 1) (by omega)
          have htail' : cpsNBranchWithin mLast hdr cr (inv (N + 1)) terminal := by
            simpa [Nat.succ_eq_add_one] using htail
          have hrest := ih N (by omega) (mLast := mLast)
            (inv := fun j => inv (j + 1)) hround' htail'
          have hfold := nbranch_extend_last_same_terminal hfirst hrest
          simpa [Nat.succ_eq_add_one, Nat.mul_succ, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using hfold

theorem taylor_outer_fold_from_rounds
    {N m mLast : Nat} {hdr : Word} {cr : CodeReq}
    {inv : Nat → Assertion} {terminal : List (Word × Assertion)}
    (hround : ∀ j, j < N →
      cpsNBranchWithin m hdr cr (inv j)
        (terminal ++ [(hdr, inv (j + 1))]))
    (htail : cpsNBranchWithin mLast hdr cr (inv N) terminal) :
    cpsNBranchWithin (m * N + mLast) hdr cr (inv 0) terminal :=
  finite_nbranch_loop_spec hround htail

#print axioms finite_nbranch_loop_spec
#print axioms taylor_outer_fold_from_rounds
#print axioms nbranch_extend_last
#print axioms nbranch_extend_last_same_terminal

end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
