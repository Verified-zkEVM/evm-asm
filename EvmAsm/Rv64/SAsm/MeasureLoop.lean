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

/-- Eliminate an assertion-level existential in an N-branch precondition. -/
theorem cpsNBranchWithin_exists_pre {α : Sort _} {n : Nat} {entry : Word}
    {cr : CodeReq} {P : α → Assertion} {exits : List (Word × Assertion)}
    (h : ∀ x, cpsNBranchWithin n entry cr (P x) exits) :
    cpsNBranchWithin n entry cr (fun hp => ∃ x, P x hp) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, ⟨x, hP⟩, hRb⟩ := hPR
  exact h x R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

/-- Eliminate an assertion-level existential in a branch precondition. -/
theorem cpsBranchWithin_exists_pre {α : Sort _} {n : Nat} {entry : Word}
    {cr : CodeReq} {P : α → Assertion} {e1 : Word} {Q1 : Assertion}
    {e2 : Word} {Q2 : Assertion}
    (h : ∀ x, cpsBranchWithin n entry cr (P x) e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr (fun hp => ∃ x, P x hp) e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, ⟨x, hP⟩, hRb⟩ := hPR
  exact h x R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

/-- Extract a trailing pure fact from an N-branch precondition. -/
theorem cpsNBranchWithin_pure_pre {fact : Prop} {n : Nat} {entry : Word}
    {cr : CodeReq} {P : Assertion} {exits : List (Word × Assertion)}
    (h : fact → cpsNBranchWithin n entry cr P exits) :
    cpsNBranchWithin n entry cr (P ** ⌜fact⌝) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hPf, hRb⟩ := hPR
  obtain ⟨hP, hf⟩ := (sepConj_pure_right ha).1 hPf
  exact h hf R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

/-- Sequence a triple into a following branch (same CodeReq). -/
theorem cpsTripleWithin_seq_branch_same_cr {n m : Nat} {entry mid : Word}
    {cr : CodeReq} {P Q : Assertion} {e1 : Word} {Q1 : Assertion}
    {e2 : Word} {Q2 : Assertion}
    (h1 : cpsTripleWithin n entry mid cr P Q)
    (h2 : cpsBranchWithin m mid cr Q e1 Q1 e2 Q2) :
    cpsBranchWithin (n + m) entry cr P e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr hPR hpc
  have hcr1 := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, hcase⟩ := h2 R hR s1 hcr1 hQR hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hcase⟩

/-- A single-exit triple as an N-branch, at any member exit. -/
theorem cpsNBranchWithin_of_triple {n : Nat} {entry e : Word} {cr : CodeReq}
    {P Q : Assertion} {exits : List (Word × Assertion)}
    (hmem : (e, Q) ∈ exits)
    (h : cpsTripleWithin n entry e cr P Q) :
    cpsNBranchWithin n entry cr P exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, (e, Q), hmem, hpc', hQR⟩

/-- A two-exit branch as an N-branch, at any two member exits. -/
theorem cpsNBranchWithin_of_branch_mem {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    {exits : List (Word × Assertion)}
    (hm1 : (e1, Q1) ∈ exits) (hm2 : (e2, Q2) ∈ exits)
    (h : cpsBranchWithin n entry cr P e1 Q1 e2 Q2) :
    cpsNBranchWithin n entry cr P exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ := h R hR s hcr hPR hpc
  rcases hcase with ⟨hpc', hQR⟩ | ⟨hpc', hQR⟩
  · exact ⟨k, hk, s', hstep, (e1, Q1), hm1, hpc', hQR⟩
  · exact ⟨k, hk, s', hstep, (e2, Q2), hm2, hpc', hQR⟩

/-- Pointwise: extract an existential from the RIGHT factor of a `**`. -/
theorem sepConj_exists_right {α : Sort _} {A : Assertion} {B : α → Assertion} :
    ∀ h, (A ** (fun h' => ∃ x, B x h')) h → ∃ x, (A ** B x) h := by
  intro h ⟨h1, h2, hd, hu, hA, ⟨x, hB⟩⟩
  exact ⟨x, h1, h2, hd, hu, hA, hB⟩

/-- Introduce TWO owned registers' values at once (trailing `regOwn` pair). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn2
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 : Reg} {P Q : Assertion}
    {cr : CodeReq}
    (h : ∀ v1 v2, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** regOwn r1 ** regOwn r2) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨h3, h4, hd2, hu2, hP3, hOwn⟩ := hPP
  obtain ⟨h5, h6, hd3, hu3, ⟨v1, hv1⟩, ⟨v2, hv2⟩⟩ := hOwn
  exact h v1 v2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨h3, h4, hd2, hu2, hP3, h5, h6, hd3, hu3, hv1, hv2⟩, hRb⟩ hpc

/-- Extract a TRAILING pure fact from a branch precondition (the
    `TwoBreakWritable.cpsBranchWithin_pure_pre` twin, pure on the right). -/
theorem cpsBranchWithin_pure_pre_right {fact : Prop} {n : Nat} {entry : Word}
    {cr : CodeReq} {P : Assertion} {e1 : Word} {Q1 : Assertion}
    {e2 : Word} {Q2 : Assertion}
    (h : fact → cpsBranchWithin n entry cr P e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr (P ** ⌜fact⌝) e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hPf, hRb⟩ := hPR
  obtain ⟨hP, hf⟩ := (sepConj_pure_right ha).1 hPf
  exact h hf R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

/-- Introduce NINE owned registers' values at once (trailing `regOwn` chain)
    for an N-branch — the bulk clobbered-register intro for call-bearing
    loop rounds. -/
theorem cpsNBranchWithin_of_forall_regIs_to_regOwn9
    {n : Nat} {entry : Word} {r1 r2 r3 r4 r5 r6 r7 r8 r9 : Reg}
    {P : Assertion} {exits : List (Word × Assertion)} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9, cpsNBranchWithin n entry cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) **
       (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7) ** (r8 ↦ᵣ v8) **
       (r9 ↦ᵣ v9)) exits) :
    cpsNBranchWithin n entry cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7 ** regOwn r8 ** regOwn r9) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, hO7⟩ := hO6
  obtain ⟨g14, g15, d8, u8, ⟨v7, hv7⟩, hO8⟩ := hO7
  obtain ⟨g16, g17, d9, u9, ⟨v8, hv8⟩, ⟨v9, hv9⟩⟩ := hO8
  exact h v1 v2 v3 v4 v5 v6 v7 v8 v9 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2,
       g6, g7, d4, u4, hv3, g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, g14, g15, d8, u8, hv7, g16, g17, d9, u9,
       hv8, hv9⟩, hRb⟩ hpc

end EvmAsm.Rv64.SAsm
