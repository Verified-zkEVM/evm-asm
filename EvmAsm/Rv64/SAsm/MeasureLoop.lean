/-
  EvmAsm.Rv64.SAsm.MeasureLoop

  Measure-indexed loop folds over `cpsNBranchWithin` (bead evm-asm-4ch8f.43.5).

  The find-last-tuple loops of `bal_account_nonstorage_finals` (and the
  cursor-walk loops of the wider `.43` family) have a shape none of the
  countdown folds (`retLoop_spec` / `twoBreakRetLoop_spec` /
  `twoExitRetLoop_spec`) cover:

  * the iteration count is DATA-DEPENDENT (items are walked until the cursor
    reaches the window end; the item count is not a spec parameter), and
  * each round has THREE outcomes — the head test exits CLEAN (cursor = end),
    the in-body callee status check exits REJECT (parse failure), or the round
    returns to the header having strictly advanced the cursor.

  The fold here is by a strictly-decreasing Nat MEASURE (for RLP walks: the
  remaining byte gap `end - cursor`, which every `rlpItemDecode` shrinks by at
  least one): a round from `inv j` either lands on one of the two final exits
  or returns to the header with `inv j'` for SOME `j' < j`.  Strong induction
  on `j` then bounds the whole loop by `m * (j + 1)` steps.

  Rounds are `cpsNBranchWithin` (the N-exit CPS form); §2 provides the
  bridges to build a 3-exit round from the head branch + body branch and to
  project the folded 2-exit result back to `cpsBranchWithin` for downstream
  `cpsBranchWithin_merge_*` composition.
-/

import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-! ## §1  The measure fold -/

/-- **Measure-indexed two-exit loop fold.**  If every round from `inv j`
    either exits to `e1`/`e2` (the final stations) or returns to the header
    `hdr` with `inv j'` for some strictly smaller `j'`, then from `inv j` the
    loop reaches `e1` or `e2` within `m * (j + 1)` steps. -/
theorem measureTwoExitLoop_spec {hdr e1 e2 : Word} {cr : CodeReq}
    {Q1 Q2 : Assertion} (m : Nat) (inv : Nat → Assertion)
    (hround : ∀ j, cpsNBranchWithin m hdr cr (inv j)
      [(e1, Q1), (e2, Q2), (hdr, fun h => ∃ j', j' < j ∧ inv j' h)]) :
    ∀ j, cpsNBranchWithin (m * (j + 1)) hdr cr (inv j) [(e1, Q1), (e2, Q2)] := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro R hR s hcr hPR hpc
    obtain ⟨k1, hk1, s1, hstep1, exit1, hmem, hpc1, hQ1⟩ := hround j R hR s hcr hPR hpc
    have hcr1 := CodeReq.SatisfiedBy_preserved hstep1 hcr
    have hmono : m ≤ m * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; exact Nat.le_add_left m (m * j)
    -- which of the three round exits fired?
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · -- e1: done
      subst h
      exact ⟨k1, Nat.le_trans hk1 hmono, s1, hstep1, (e1, Q1), by simp, hpc1, hQ1⟩
    · -- e2: done
      subst h
      exact ⟨k1, Nat.le_trans hk1 hmono, s1, hstep1, (e2, Q2), by simp, hpc1, hQ1⟩
    · -- header with a smaller measure: extract j' and recurse
      subst h
      obtain ⟨hp1, hcompat1, h1, h2, hd12, hu12, hex, hR2⟩ := hQ1
      obtain ⟨j', hlt, hinv⟩ := hex
      have hPR' : (inv j' ** R).holdsFor s1 :=
        ⟨hp1, hcompat1, h1, h2, hd12, hu12, hinv, hR2⟩
      obtain ⟨k2, hk2, s2, hstep2, exit2, hmem2, hpc2, hQ2⟩ :=
        ih j' hlt R hR s1 hcr1 hPR' hpc1
      refine ⟨k1 + k2, ?_, s2, stepN_add_eq hstep1 hstep2, exit2, hmem2, hpc2, hQ2⟩
      have hle : m * (j' + 1) ≤ m * j := Nat.mul_le_mul_left m (by omega)
      have hsum : m * (j + 1) = m + m * j := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [hsum]
      exact Nat.le_trans (Nat.add_le_add hk1 hk2) (Nat.add_le_add_left hle m)

/-! ## §2  Bridges between the 2-exit and N-exit forms -/

/-- A two-exit `cpsBranchWithin` as a 2-entry N-branch. -/
theorem cpsNBranchWithin_of_branch {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    (h : cpsBranchWithin n entry cr P e1 Q1 e2 Q2) :
    cpsNBranchWithin n entry cr P [(e1, Q1), (e2, Q2)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ := h R hR s hcr hPR hpc
  rcases hcase with ⟨hpc', hQ⟩ | ⟨hpc', hQ⟩
  · exact ⟨k, hk, s', hstep, (e1, Q1), by simp, hpc', hQ⟩
  · exact ⟨k, hk, s', hstep, (e2, Q2), by simp, hpc', hQ⟩

/-- A 2-entry N-branch back as a two-exit `cpsBranchWithin` (for downstream
    `cpsBranchWithin_merge_*` composition). -/
theorem cpsBranchWithin_of_nBranch2 {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    (h : cpsNBranchWithin n entry cr P [(e1, Q1), (e2, Q2)]) :
    cpsBranchWithin n entry cr P e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, exit, hmem, hpc', hQ⟩ := h R hR s hcr hPR hpc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hh | hh
  · subst hh; exact ⟨k, hk, s', hstep, Or.inl ⟨hpc', hQ⟩⟩
  · subst hh; exact ⟨k, hk, s', hstep, Or.inr ⟨hpc', hQ⟩⟩

/-- **Round builder**: a two-exit head branch (exit `eA` / fall to `mid`)
    followed by a two-exit body branch from `mid` (exit `eB` / exit `eC`)
    is a 3-exit round.  For the find-last shape: `eA` = the clean head exit,
    `eB` = the reject station, `eC` = the header (with the smaller measure). -/
theorem cpsNBranchWithin_head_body {n m : Nat} {entry mid : Word} {cr : CodeReq}
    {P Qmid : Assertion} {eA : Word} {QA : Assertion}
    {eB : Word} {QB : Assertion} {eC : Word} {QC : Assertion}
    (hhead : cpsBranchWithin n entry cr P eA QA mid Qmid)
    (hbody : cpsBranchWithin m mid cr Qmid eB QB eC QC) :
    cpsNBranchWithin (n + m) entry cr P [(eA, QA), (eB, QB), (eC, QC)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hcase⟩ := hhead R hR s hcr hPR hpc
  have hcr1 := CodeReq.SatisfiedBy_preserved hstep1 hcr
  rcases hcase with ⟨hpc1, hQ⟩ | ⟨hpc1, hQ⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n m), s1, hstep1, (eA, QA), by simp, hpc1, hQ⟩
  · obtain ⟨k2, hk2, s2, hstep2, hcase2⟩ := hbody R hR s1 hcr1 hQ hpc1
    rcases hcase2 with ⟨hpc2, hQ2⟩ | ⟨hpc2, hQ2⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        (eB, QB), by simp, hpc2, hQ2⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        (eC, QC), by simp, hpc2, hQ2⟩

/-- Weaken an N-branch entry's target assertion (covariant per-exit
    consequence, stated for the 3-exit round shape used here). -/
theorem cpsNBranchWithin3_weaken {n : Nat} {entry : Word} {cr : CodeReq}
    {P P' : Assertion} {e1 e2 e3 : Word} {Q1 Q1' Q2 Q2' Q3 Q3' : Assertion}
    (hpre : ∀ h, P' h → P h)
    (h1 : ∀ h, Q1 h → Q1' h) (h2 : ∀ h, Q2 h → Q2' h) (h3 : ∀ h, Q3 h → Q3' h)
    (h : cpsNBranchWithin n entry cr P [(e1, Q1), (e2, Q2), (e3, Q3)]) :
    cpsNBranchWithin n entry cr P' [(e1, Q1'), (e2, Q2'), (e3, Q3')] := by
  intro R hR s hcr hPR hpc
  have hPR' : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, hk, s', hstep, exit, hmem, hpc', hQ⟩ := h R hR s hcr hPR' hpc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hh | hh | hh
  · subst hh
    obtain ⟨hp, hc, hpq⟩ := hQ
    exact ⟨k, hk, s', hstep, (e1, Q1'), by simp, hpc',
      ⟨hp, hc, sepConj_mono_left h1 hp hpq⟩⟩
  · subst hh
    obtain ⟨hp, hc, hpq⟩ := hQ
    exact ⟨k, hk, s', hstep, (e2, Q2'), by simp, hpc',
      ⟨hp, hc, sepConj_mono_left h2 hp hpq⟩⟩
  · subst hh
    obtain ⟨hp, hc, hpq⟩ := hQ
    exact ⟨k, hk, s', hstep, (e3, Q3'), by simp, hpc',
      ⟨hp, hc, sepConj_mono_left h3 hp hpq⟩⟩

/-! ## §3  Disjunctive-precondition elimination

    The verified callee contracts export N-way disjunctive posts
    (`rlp_walk_next`'s six outcomes); the caller's continuation is proven
    per-arm and recombined here. -/

/-- Case-split a disjunctive precondition of a branch. -/
theorem cpsBranchWithin_pre_or {n : Nat} {entry : Word} {cr : CodeReq}
    {P1 P2 : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    (h1 : cpsBranchWithin n entry cr P1 e1 Q1 e2 Q2)
    (h2 : cpsBranchWithin n entry cr P2 e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr (fun h => P1 h ∨ P2 h) e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hor, hRb⟩ := hPR
  rcases hor with hP | hP
  · exact h1 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  · exact h2 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

/-- Case-split a disjunctive precondition of a triple. -/
theorem cpsTripleWithin_pre_or {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P1 P2 Q : Assertion}
    (h1 : cpsTripleWithin n entry exit_ cr P1 Q)
    (h2 : cpsTripleWithin n entry exit_ cr P2 Q) :
    cpsTripleWithin n entry exit_ cr (fun h => P1 h ∨ P2 h) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hor, hRb⟩ := hPR
  rcases hor with hP | hP
  · exact h1 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  · exact h2 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

/-- Distribute a separating frame over a pointwise disjunction:
    `A ** (B ∨ C) ⟹ (A ** B) ∨ (A ** C)` (used to case-split callee posts
    of the form `frame ** (arm₁ ∨ … ∨ armₙ)` before `*_pre_or`). -/
theorem sepConj_or_split {A B C : Assertion} :
    ∀ h, (A ** (fun h' => B h' ∨ C h')) h → ((A ** B) h ∨ (A ** C) h) := by
  intro h ⟨h1, h2, hd, hu, hA, hor⟩
  rcases hor with hB | hB
  · exact Or.inl ⟨h1, h2, hd, hu, hA, hB⟩
  · exact Or.inr ⟨h1, h2, hd, hu, hA, hB⟩

end EvmAsm.Rv64.SAsm
