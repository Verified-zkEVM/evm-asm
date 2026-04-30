/-
  EvmAsm.Rv64.CPSSpec

  CPS-style (continuation-passing style) Hoare triples for branching code,
  with a built-in frame rule.

  Following Jensen/Benton/Kennedy (POPL 2013, PPDP 2013), we specify code
  with multiple exits using CPS-style specifications:
  "if it is safe to continue at each exit point, then it is safe to enter."

  The frame rule is baked into the definitions: all specs universally
  quantify over a pcFree frame R, so P/Q only describe the resources
  the code actually reads/writes.

  Key types:
  - cpsTripleWithin: single-exit specification (entry → exit with P → Q)
  - cpsBranchWithin: two-exit specification (entry → exit_t with Q_t OR exit_f with Q_f)

  Structural rules:
  - cpsTriple_seq: sequential composition
  - cpsTriple_weaken: pre/post strengthening/weakening
  - cpsBranch_merge: merge two branch exits into a single continuation

  All assertions are `Assertion` (predicates on PartialState), bridged to
  MachineState via `holdsFor`.
-/

-- `SepLogic` transitively imports `Basic` and `Execution`.
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Rv64

-- ============================================================================
-- CPS-style specifications (with built-in frame rule)
-- ============================================================================

/-- CPS-style code specification with built-in frame rule:
    For any pcFree frame R, starting from any state where (P ** R) holds
    and PC = entry, and cr is satisfied, execution reaches a state where
    (Q ** R) holds and PC = exit.

    The universal quantification over R means P and Q only describe the
    resources the code actually reads/writes.
    The CodeReq cr is a persistent side-condition: it is not consumed. -/
def cpsTripleWithin (nSteps : Nat) (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k, k ≤ nSteps ∧ ∃ s', stepN k s = some s' ∧ s'.pc = exit_ ∧ (Q ** R).holdsFor s'

/-- Step-bounded two-exit CPS specification.
    Every framed execution reaches one of the two exits in at most
    `nSteps` steps. -/
def cpsBranchWithin (nSteps : Nat) (entry : Word) (cr : CodeReq) (P : Assertion)
    (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k, k ≤ nSteps ∧ ∃ s', stepN k s = some s' ∧
      ((s'.pc = exit_t ∧ (Q_t ** R).holdsFor s') ∨ (s'.pc = exit_f ∧ (Q_f ** R).holdsFor s'))

theorem cpsTripleWithin_weaken {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P P' Q Q' : Assertion}
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr P' Q' := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Consequence for step-bounded branches. -/
theorem cpsBranchWithin_weaken {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P P' : Assertion} {exit_t : Word} {Q_t Q_t' : Assertion}
    {exit_f : Word} {Q_f Q_f' : Assertion}
    (hpre : ∀ h, P' h → P h)
    (hpost_t : ∀ h, Q_t h → Q_t' h)
    (hpost_f : ∀ h, Q_f h → Q_f' h)
    (h : cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry cr P' exit_t Q_t' exit_f Q_f' := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · left
    exact ⟨hpc_t, by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_t
      exact ⟨hp, hcompat, sepConj_mono_left hpost_t hp hpq⟩⟩
  · right
    exact ⟨hpc_f, by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_f
      exact ⟨hp, hcompat, sepConj_mono_left hpost_f hp hpq⟩⟩

/-- Bounded sequence: bounds add under sequential composition. -/
theorem cpsTripleWithin_seq {nSteps1 nSteps2 : Nat} {l1 l2 l3 : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q R : Assertion}
    (h1 : cpsTripleWithin nSteps1 l1 l2 cr1 P Q)
    (h2 : cpsTripleWithin nSteps2 l2 l3 cr2 Q R) :
    cpsTripleWithin (nSteps1 + nSteps2) l1 l3 (cr1.union cr2) P R := by
  intro F hF s hcr hPF hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr1 hPF hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hRF⟩ := h2 F hF s1 hcr2' hQF hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hRF⟩

/-- Bounded sequence: a triple followed by a branch. Bounds add under
    sequential composition. -/
theorem cpsTripleWithin_seq_cpsBranchWithin {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (h1 : cpsTripleWithin nSteps1 entry mid cr1 P Q)
    (h2 : cpsBranchWithin nSteps2 mid cr2 Q exit_t Q_t exit_f Q_f) :
    cpsBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr1 hPR hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
  obtain ⟨k2, hk2, s2, hstep2, hcase⟩ := h2 R hR s1 hcr2' hQR hpc1
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, ?_⟩
  exact hcase

/-- Bounded sequence with the same CodeReq on both sides. Bounds add under
    sequential composition. -/
theorem cpsTripleWithin_seq_same_cr {nSteps1 nSteps2 : Nat}
    {l1 l2 l3 : Word} {cr : CodeReq} {P Q R : Assertion}
    (h1 : cpsTripleWithin nSteps1 l1 l2 cr P Q)
    (h2 : cpsTripleWithin nSteps2 l2 l3 cr Q R) :
    cpsTripleWithin (nSteps1 + nSteps2) l1 l3 cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr hPF hpc
  have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hRF⟩ := h2 F hF s1 hcr' hQF hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hRF⟩

/-- Bounded sequential composition with midpoint permutation and the same
    CodeReq on both sides. -/
theorem cpsTripleWithin_seq_perm_same_cr {nSteps1 nSteps2 : Nat}
    {s m e : Word} {cr : CodeReq} {P Q1 Q2 R : Assertion}
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTripleWithin nSteps1 s m cr P Q1)
    (h2 : cpsTripleWithin nSteps2 m e cr Q2 R) :
    cpsTripleWithin (nSteps1 + nSteps2) s e cr P R :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_weaken (fun _ hp => hp) hperm h1) h2

/-- Bounded sequence with the same CodeReq: a triple followed by a branch. -/
theorem cpsTripleWithin_seq_cpsBranchWithin_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (h1 : cpsTripleWithin nSteps1 entry mid cr P Q)
    (h2 : cpsBranchWithin nSteps2 mid cr Q exit_t Q_t exit_f Q_f) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr hPR hpc
  have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, hcase⟩ := h2 R hR s1 hcr' hQR hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hcase⟩

/-- Bounded same-CodeReq triple/branch composition with midpoint permutation. -/
theorem cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr : CodeReq}
    {P Q1 Q2 : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTripleWithin nSteps1 entry mid cr P Q1)
    (h2 : cpsBranchWithin nSteps2 mid cr Q2 exit_t Q_t exit_f Q_f) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P exit_t Q_t exit_f Q_f :=
  cpsTripleWithin_seq_cpsBranchWithin_same_cr
    (cpsTripleWithin_weaken (fun _ hp => hp) hperm h1) h2

/-- Zero-step bounded triple. The bound is `0` because the post is reached in
    `0 ≤ 0` steps. -/
theorem cpsTripleWithin_refl {addr : Word} {P Q : Assertion}
    (h : ∀ hp, P hp → Q hp) :
    cpsTripleWithin 0 addr addr CodeReq.empty P Q := by
  intro R hR s _hcr hPR hpc
  exact ⟨0, Nat.le_refl 0, s, rfl, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

/-- Monotonicity in the step bound. -/
theorem cpsTripleWithin_mono_nSteps {nSteps nSteps' : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion}
    (hle : nSteps ≤ nSteps')
    (h : cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps' entry exit_ cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, Nat.le_trans hk hle, s', hstep, hpc', hQR⟩

/-- Monotonicity in the step bound for branches. -/
theorem cpsBranchWithin_mono_nSteps {nSteps nSteps' : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hle : nSteps ≤ nSteps')
    (h : cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps' entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  exact ⟨k, Nat.le_trans hk hle, s', hstep, hbranch⟩

/-- Swap the two branch targets of a bounded cpsBranchWithin. The step bound is
    unchanged. -/
theorem cpsBranchWithin_swap {nSteps : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry cr P exit_f Q_f exit_t Q_t := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hbranch.symm⟩

-- ============================================================================
-- Structural rules
-- ============================================================================

theorem cpsTripleWithin_strip_pure_and_convert
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop} (Q' : Assertion)
    (hbody : cpsTripleWithin nSteps entry exit_ cr P Q)
    (hpost : fact → ∀ h, Q h → Q' h) :
    cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q' := by
  intro R hR s hcr hPFR hpc
  have hfact : fact := by
    obtain ⟨hp, _, hpq⟩ := hPFR
    obtain ⟨h1, _, _, _, hPF, _⟩ := hpq
    exact ((sepConj_pure_right h1).1 hPF).2
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hPFR
    exact ⟨hp, hcompat, by
      obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
      exact ⟨h1, h2, hd, hunion, ((sepConj_pure_right h1).1 hPF).1, hR_⟩⟩
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := hbody R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hpc', by
    obtain ⟨hp', hcompat', hpq'⟩ := hQR
    exact ⟨hp', hcompat', sepConj_mono_left (hpost hfact) hp' hpq'⟩⟩

/-- Rule of consequence for cpsBranchWithin: strengthen pre, weaken both posts.

    All pre/post-condition arguments are implicit: `P`/`Q_t`/`Q_f` unify from
    the branch `h`, and `P'`/`Q_t'`/`Q_f'` from the expected goal type. -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn
    {nSteps : Nat} {entry exit_ r P Q} {cr : CodeReq}
    (h : ∀ vOld, cpsTripleWithin nSteps entry exit_ cr (P ** (r ↦ᵣ vOld)) Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨vOld, hv4⟩⟩ := hPown1
  exact h vOld R hR s hcr
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Bounded variant of `cpsTriple_of_forall_regIs_to_regOwn_single`. The step
    bound is unchanged. -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn_single
    {nSteps : Nat} {entry exit_ r Q} {cr : CodeReq}
    (h : ∀ vOld, cpsTripleWithin nSteps entry exit_ cr (r ↦ᵣ vOld) Q) :
    cpsTripleWithin nSteps entry exit_ cr (regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hunion, ⟨vOld, hv⟩, hR2⟩ := hPR
  exact h vOld R hR s hcr ⟨hp, hcompat, h1, h2, hd, hunion, hv, hR2⟩ hpc

/-- Bounded variant of `cpsTriple_of_forall_memIs_to_memOwn`. The step bound is
    unchanged. -/
theorem cpsTripleWithin_of_forall_memIs_to_memOwn
    {nSteps : Nat} {entry exit_ a P Q} {cr : CodeReq}
    (h : ∀ vOld, cpsTripleWithin nSteps entry exit_ cr (P ** (a ↦ₘ vOld)) Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** memOwn a) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨vOld, hv4⟩⟩ := hPown1
  exact h vOld R hR s hcr
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Branch elimination: if both branch exits lead to the same
    continuation exit with R, merge back into a single cpsTripleWithin.
    All position/code/assertion arguments are implicit — inferred from `hbr`/`h_t`/`h_f`. -/
theorem cpsBranchWithin_merge {nSteps1 nSteps2 : Nat}
    {entry l_t l_f exit_ : Word} {cr1 cr_t cr_f : CodeReq}
    (hd1 : cr1.Disjoint (cr_t.union cr_f)) (hd2 : cr_t.Disjoint cr_f)
    {P Q_t Q_f R : Assertion}
    (hbr   : cpsBranchWithin nSteps1 entry cr1 P l_t Q_t l_f Q_f)
    (h_t   : cpsTripleWithin nSteps2 l_t exit_ cr_t Q_t R)
    (h_f   : cpsTripleWithin nSteps2 l_f exit_ cr_f Q_f R) :
    cpsTripleWithin (nSteps1 + nSteps2) entry exit_ (cr1.union (cr_t.union cr_f)) P R := by
  intro F hF s hcr hPF hpc
  rw [CodeReq.union_satisfiedBy hd1] at hcr
  obtain ⟨hcr1, hcr_tf⟩ := hcr
  rw [CodeReq.union_satisfiedBy hd2] at hcr_tf
  obtain ⟨hcrt, hcrf⟩ := hcr_tf
  obtain ⟨k1, hk1, s1, hstep1, hbranch⟩ := hbr F hF s hcr1 hPF hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · have hcrt' := CodeReq.SatisfiedBy_preserved hstep1 hcrt
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hcrt' hQ_t hpc_t
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hR⟩
  · have hcrf' := CodeReq.SatisfiedBy_preserved hstep1 hcrf
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hcrf' hQ_f hpc_f
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hR⟩

/-- Bounded same-CodeReq branch elimination. Bounds add, using the larger
    continuation bound for both paths. -/
theorem cpsBranchWithin_merge_same_cr {nSteps1 nSteps2 : Nat}
    {entry l_t l_f exit_ : Word} {cr : CodeReq}
    {P Q_t Q_f R : Assertion}
    (hbr   : cpsBranchWithin nSteps1 entry cr P l_t Q_t l_f Q_f)
    (h_t   : cpsTripleWithin nSteps2 l_t exit_ cr Q_t R)
    (h_f   : cpsTripleWithin nSteps2 l_f exit_ cr Q_f R) :
    cpsTripleWithin (nSteps1 + nSteps2) entry exit_ cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, hk1, s1, hstep1, hbranch⟩ := hbr F hF s hcr hPF hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hcr' hQ_t hpc_t
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hcr' hQ_f hpc_f
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hR⟩

/-- Extract the taken path from a cpsBranchWithin when the not-taken postcondition
    is unsatisfiable (e.g., contains a contradictory pure fact).
    All position/code/pre/post arguments are implicit — unify from `hbr`. -/
theorem cpsTripleWithin_extend_code {nSteps : Nat} {entry exit_ : Word} {cr cr' : CodeReq}
    {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr' P Q := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

/-- Monotonicity for bounded cpsBranchWithin: extend to a larger CodeReq. -/
theorem cpsBranchWithin_extend_code {nSteps : Nat} {entry : Word} {cr cr' : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry cr' P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc
def cpsNBranchWithin (nSteps : Nat) (entry : Word) (cr : CodeReq) (P : Assertion)
    (exits : List (Word × Assertion)) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k, k ≤ nSteps ∧ ∃ s', stepN k s = some s' ∧
      ∃ exit ∈ exits, s'.pc = exit.1 ∧ (exit.2 ** R).holdsFor s'

theorem cpsTripleWithin_as_cpsNBranchWithin {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (h : cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsNBranchWithin nSteps entry cr P [(exit_, Q)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, (exit_, Q), List.Mem.head _, hpc', hQR⟩

/-- A bounded singleton cpsNBranchWithin gives back a bounded cpsTripleWithin with the same
    step bound. -/
theorem cpsNBranchWithin_as_cpsTripleWithin {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (h : cpsNBranchWithin nSteps entry cr P [(exit_, Q)]) :
    cpsTripleWithin nSteps entry exit_ cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  cases hmem with
  | head => exact ⟨k, hk, s', hstep, hpc', hQR⟩
  | tail _ h => exact absurd h List.not_mem_nil

/-- A bounded 2-exit cpsBranchWithin can be viewed as a bounded cpsNBranchWithin with the
    same step bound. -/
theorem cpsBranchWithin_as_cpsNBranchWithin {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion}
    {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f) :
    cpsNBranchWithin nSteps entry cr P [(exit_t, Q_t), (exit_f, Q_f)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k, hk, s', hstep, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · exact ⟨k, hk, s', hstep, (exit_f, Q_f), List.Mem.tail _ (List.Mem.head _), hpc_f, hQ_f⟩

/-- A bounded 2-element cpsNBranchWithin gives back a bounded cpsBranchWithin with the same
    step bound. -/
theorem cpsNBranchWithin_as_cpsBranchWithin {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion}
    {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f : Assertion}
    (h : cpsNBranchWithin nSteps entry cr P [(exit_t, Q_t), (exit_f, Q_f)]) :
    cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  cases hmem with
  | head => left; exact ⟨hpc', hQR⟩
  | tail _ htail =>
    cases htail with
    | head => right; exact ⟨hpc', hQR⟩
    | tail _ h => exact absurd h List.not_mem_nil

/-- Monotonicity in the step bound for N-branches. -/
theorem cpsNBranchWithin_mono_nSteps {nSteps nSteps' : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exits : List (Word × Assertion)}
    (hle : nSteps ≤ nSteps')
    (h : cpsNBranchWithin nSteps entry cr P exits) :
    cpsNBranchWithin nSteps' entry cr P exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, Nat.le_trans hk hle, s', hstep, ex, hmem, hpc', hQR⟩

/-- Consequence: strengthen the precondition of a bounded N-branch. The step
    bound is unchanged. -/
theorem cpsNBranchWithin_weaken_pre {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P P' : Assertion}
    {exits : List (Word × Assertion)}
    (hpre : ∀ h, P' h → P h) (h : cpsNBranchWithin nSteps entry cr P exits) :
    cpsNBranchWithin nSteps entry cr P' exits := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  exact h R hR s hcr hPR hpc

/-- Monotonicity: expand the exit list of a bounded N-branch. The step bound
    is unchanged. -/
theorem cpsNBranchWithin_weaken_exits {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion}
    {exits : List (Word × Assertion)} (exits' : List (Word × Assertion))
    (hsub : ∀ ex, ex ∈ exits → ex ∈ exits') (h : cpsNBranchWithin nSteps entry cr P exits) :
    cpsNBranchWithin nSteps entry cr P exits' := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, ex, hsub ex hmem, hpc', hQR⟩

/-- Weaken postconditions of all exits in a bounded N-branch. The step bound
    is unchanged. -/
theorem cpsNBranchWithin_weaken_posts {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exits exits' : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry cr P exits)
    (hmap : ∀ ex ∈ exits, ∃ ex' ∈ exits', ex'.1 = ex.1 ∧ ∀ h, ex.2 h → ex'.2 h) :
    cpsNBranchWithin nSteps entry cr P exits' := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hER⟩ := h R hR s hcr hPR hpc
  obtain ⟨ex', hmem', heq, hpost⟩ := hmap ex hmem
  rw [← heq] at hpc'
  exact ⟨k, hk, s', hstep, ex', hmem', hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hER
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Monotonicity for bounded N-branches: extend to a larger CodeReq. -/
theorem cpsNBranchWithin_extend_code {nSteps : Nat} {entry : Word} {cr cr' : CodeReq}
    {P : Assertion} {exits : List (Word × Assertion)}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsNBranchWithin nSteps entry cr P exits) :
    cpsNBranchWithin nSteps entry cr' P exits := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

/-- Frame a bounded `cpsNBranchWithin` by a PC-free assertion. The step bound is
    unchanged and the frame is attached to every exit assertion. -/
theorem cpsNBranchWithin_frameR {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exits : List (Word × Assertion)} {F : Assertion}
    (hF : F.pcFree) (h : cpsNBranchWithin nSteps entry cr P exits) :
    cpsNBranchWithin nSteps entry cr (P ** F) (exits.map (fun ex => (ex.1, ex.2 ** F))) := by
  intro R hR s hcr hPFR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have hPFR' : (P ** (F ** R)).holdsFor s :=
    holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQFR⟩ :=
    h (F ** R) hFR s hcr hPFR' hpc
  refine ⟨k, hk, s', hstep, (ex.1, ex.2 ** F), ?_, hpc',
    holdsFor_sepConj_assoc.mpr hQFR⟩
  exact List.mem_map.mpr ⟨ex, hmem, rfl⟩

/-- Bounded N-branch merge: if every exit has a continuation with a uniform
    step bound, compose into a single bounded triple. Bounds add. -/
theorem cpsNBranchWithin_merge {nSteps1 nSteps2 : Nat}
    {entry exit_ : Word} {cr : CodeReq}
    {P R : Assertion}
    {exits : List (Word × Assertion)}
    (hbr : cpsNBranchWithin nSteps1 entry cr P exits)
    (hall : ∀ exit ∈ exits, cpsTripleWithin nSteps2 exit.1 exit_ cr exit.2 R) :
    cpsTripleWithin (nSteps1 + nSteps2) entry exit_ cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQF⟩ :=
    hbr F hF s hcr hPF hpc
  have hcr1 := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hRF⟩ :=
    hall ex hmem F hF s1 hcr1 hQF hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hRF⟩

/-- Bounded sequence: a triple followed by an N-branch. Bounds add under
    sequential composition. -/
theorem cpsTripleWithin_seq_cpsNBranchWithin {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {exits : List (Word × Assertion)}
    (h1 : cpsTripleWithin nSteps1 entry mid cr1 P Q)
    (h2 : cpsNBranchWithin nSteps2 mid cr2 Q exits) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P exits := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr1 hPR hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
  obtain ⟨k2, hk2, s2, hstep2, ex, hmem, hpc2, hER⟩ :=
    h2 R hR s1 hcr2' hQR hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
    ex, hmem, hpc2, hER⟩

/-- Extend the head exit of a bounded N-branch by composing a bounded triple
    after it. The head path bound adds; non-head paths use monotonicity into
    the summed bound. -/
theorem cpsNBranchWithin_extend_head {nSteps1 nSteps2 : Nat} {entry l l' : Word} {cr : CodeReq}
    {P Q R : Assertion}
    {others : List (Word × Assertion)}
    (hbr : cpsNBranchWithin nSteps1 entry cr P ((l, Q) :: others))
    (hseq : cpsTripleWithin nSteps2 l l' cr Q R) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry cr P ((l', R) :: others) := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hcr hPF hpc
  cases hmem with
  | head =>
    have hcr1 := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hRF⟩ := hseq F hF s1 hcr1 hQF hpc1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
           (l', R), List.Mem.head _, hpc2, hRF⟩
  | tail _ htail =>
    exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
           ex, List.Mem.tail _ htail, hpc1, hQF⟩

/-- Bounded sequence with the same CodeReq: a triple followed by an N-branch. -/
theorem cpsTripleWithin_seq_cpsNBranchWithin_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {exits : List (Word × Assertion)}
    (h1 : cpsTripleWithin nSteps1 entry mid cr P Q)
    (h2 : cpsNBranchWithin nSteps2 mid cr Q exits) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry cr P exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr hPR hpc
  have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h2 R hR s1 hcr' hQR hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
    ex, hmem, hpc2, hER⟩

/-- Bounded same-CodeReq triple/N-branch composition with midpoint permutation. -/
theorem cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr : CodeReq}
    {P Q1 Q2 : Assertion} {exits : List (Word × Assertion)}
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTripleWithin nSteps1 entry mid cr P Q1)
    (h2 : cpsNBranchWithin nSteps2 mid cr Q2 exits) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry cr P exits :=
  cpsTripleWithin_seq_cpsNBranchWithin_same_cr
    (cpsTripleWithin_weaken (fun _ hp => hp) hperm h1) h2

/-- Bounded N-branch reflexivity: zero steps, one exit at the same address. -/
theorem cpsNBranchWithin_refl (addr : Word)
    (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsNBranchWithin 0 addr CodeReq.empty P [(addr, Q)] := by
  intro R hR s _hcr hPR hpc
  exact ⟨0, Nat.le_refl 0, s, rfl, (addr, Q), List.Mem.head _, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

/-- Compose a bounded cpsBranchWithin with a bounded cpsNBranchWithin on the not-taken
    path. Bounds add under sequential composition. -/
theorem cpsBranchWithin_cons_cpsNBranchWithin {nSteps1 nSteps2 : Nat}
    {entry : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P : Assertion} {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f : Assertion}
    {exits : List (Word × Assertion)}
    (hbr : cpsBranchWithin nSteps1 entry cr1 P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranchWithin nSteps2 exit_f cr2 Q_f exits) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P ((exit_t, Q_t) :: exits) := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hbranch⟩ := hbr R hR s hcr1 hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
    obtain ⟨k2, hk2, s2, hstep2, ex, hmem, hpc2, hER⟩ :=
      h_rest R hR s1 hcr2' hQ_f hpc_f
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
      ex, List.Mem.tail _ hmem, hpc2, hER⟩

/-- Compose a bounded cpsBranchWithin with a bounded cpsNBranchWithin, with permutation
    on the not-taken path. Bounds add under sequential composition. -/
theorem cpsBranchWithin_cons_cpsNBranchWithin_with_perm {nSteps1 nSteps2 : Nat}
    {entry : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P : Assertion} {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f Q_f' : Assertion}
    {exits : List (Word × Assertion)}
    (hperm : ∀ h, Q_f h → Q_f' h)
    (hbr : cpsBranchWithin nSteps1 entry cr1 P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranchWithin nSteps2 exit_f cr2 Q_f' exits) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P ((exit_t, Q_t) :: exits) := by
  exact cpsBranchWithin_cons_cpsNBranchWithin hd
    (cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hp => hp) hperm hbr)
    h_rest

/-- Compose a bounded cpsBranchWithin with a bounded cpsNBranchWithin on the not-taken
    path when both specs use the same CodeReq. -/
theorem cpsBranchWithin_cons_cpsNBranchWithin_same_cr {nSteps1 nSteps2 : Nat}
    {entry : Word} {cr : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f : Assertion}
    {exits : List (Word × Assertion)}
    (hbr : cpsBranchWithin nSteps1 entry cr P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranchWithin nSteps2 exit_f cr Q_f exits) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry cr P ((exit_t, Q_t) :: exits) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hbranch⟩ := hbr R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, ex, hmem, hpc2, hER⟩ :=
      h_rest R hR s1 hcr' hQ_f hpc_f
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
      ex, List.Mem.tail _ hmem, hpc2, hER⟩

/-- Compose a bounded cpsBranchWithin with a bounded cpsNBranchWithin using the same
    CodeReq, with permutation on the not-taken path. -/
theorem cpsBranchWithin_cons_cpsNBranchWithin_with_perm_same_cr {nSteps1 nSteps2 : Nat}
    {entry : Word} {cr : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion}
    {exit_f : Word} {Q_f Q_f' : Assertion}
    {exits : List (Word × Assertion)}
    (hperm : ∀ h, Q_f h → Q_f' h)
    (hbr : cpsBranchWithin nSteps1 entry cr P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranchWithin nSteps2 exit_f cr Q_f' exits) :
    cpsNBranchWithin (nSteps1 + nSteps2) entry cr P ((exit_t, Q_t) :: exits) :=
  cpsBranchWithin_cons_cpsNBranchWithin_same_cr
    (cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hp => hp) hperm hbr)
    h_rest

-- ============================================================================
-- Edge cases
-- ============================================================================

/-- An N-branch with no exits is vacuously false (no reachable exit).
    All position/code/assertion arguments are implicit — inferred from `h`. -/
def isHalted (s : MachineState) : Bool :=
  (step s).isNone

/-- CPS-style halt specification with built-in frame rule:
    For any pcFree frame R, starting from any state where cr is satisfied,
    (P ** R) holds and PC = entry, execution reaches a halted state where (Q ** R) holds.
    Unlike `cpsTripleWithin`, there is no exit address — execution simply terminates. -/
def cpsHaltTripleWithin (nSteps : Nat) (entry : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k, k ≤ nSteps ∧ ∃ s', stepN k s = some s' ∧ isHalted s' = true ∧ (Q ** R).holdsFor s'

theorem cpsTripleWithin_as_cpsHaltTripleWithin {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ cr P Q)
    (hhalt : ∀ (R : Assertion), R.pcFree → ∀ s, (Q ** R).holdsFor s → s.pc = exit_ →
      isHalted s = true) :
    cpsHaltTripleWithin nSteps entry cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hhalt R hR s' hQR hpc', hQR⟩

/-- Weaken a bounded halt triple. -/
theorem cpsHaltTripleWithin_weaken {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P P' Q Q' : Assertion}
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsHaltTripleWithin nSteps entry cr P Q) :
    cpsHaltTripleWithin nSteps entry cr P' Q' := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, hk, s', hstep, hhalt, hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hhalt, by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Monotonicity in the step bound for halt triples. -/
theorem cpsHaltTripleWithin_mono_nSteps {nSteps nSteps' : Nat} {entry : Word} {cr : CodeReq}
    {P Q : Assertion}
    (hle : nSteps ≤ nSteps')
    (h : cpsHaltTripleWithin nSteps entry cr P Q) :
    cpsHaltTripleWithin nSteps' entry cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hhalt, hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, Nat.le_trans hk hle, s', hstep, hhalt, hQR⟩

/-- Monotonicity for bounded halt triples: extend to a larger CodeReq. The
    step bound is unchanged. -/
theorem cpsHaltTripleWithin_extend_code {nSteps : Nat} {entry : Word} {cr cr' : CodeReq}
    {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsHaltTripleWithin nSteps entry cr P Q) :
    cpsHaltTripleWithin nSteps entry cr' P Q := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

/-- Frame on the right for bounded halt triples. The step bound is unchanged. -/
theorem cpsHaltTripleWithin_frameR {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P Q : Assertion} (F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTripleWithin nSteps entry cr P Q) :
    cpsHaltTripleWithin nSteps entry cr (P ** F) (Q ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, s', hstep, hhalt, hpost⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, hk, s', hstep, hhalt, holdsFor_sepConj_assoc.mpr hpost⟩

/-- Sequence a bounded triple followed by a bounded halt triple. Bounds add. -/
theorem cpsTripleWithin_seq_haltWithin {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q R : Assertion}
    (h1 : cpsTripleWithin nSteps1 entry mid cr1 P Q)
    (h2 : cpsHaltTripleWithin nSteps2 mid cr2 Q R) :
    cpsHaltTripleWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P R := by
  intro F hF s hcr hPF hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr1 hPF hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
  obtain ⟨k2, hk2, s2, hstep2, hhalt, hRF⟩ := h2 F hF s1 hcr2' hQF hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hhalt, hRF⟩

/-- Sequence a bounded triple followed by a bounded halt triple with the same
    CodeReq. Bounds add. -/
theorem cpsTripleWithin_seq_haltWithin_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr : CodeReq}
    {P Q R : Assertion}
    (h1 : cpsTripleWithin nSteps1 entry mid cr P Q)
    (h2 : cpsHaltTripleWithin nSteps2 mid cr Q R) :
    cpsHaltTripleWithin (nSteps1 + nSteps2) entry cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr hPF hpc
  have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, hhalt, hRF⟩ := h2 F hF s1 hcr' hQF hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hhalt, hRF⟩

/-- Promote a `cpsTripleWithin` to a `cpsHaltTripleWithin` when the exit address is halted.
    If execution reaches exit_ with Q, and every state satisfying (Q ** R) at exit_ is halted,
    then the program halts with Q.
    All position/code/assertion arguments are implicit — inferred from `h`/`hhalt`. -/
theorem cpsTripleWithin_seq_with_perm {nSteps1 nSteps2 : Nat}
    {s m e : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q1 Q2 R : Assertion}
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTripleWithin nSteps1 s m cr1 P Q1)
    (h2 : cpsTripleWithin nSteps2 m e cr2 Q2 R) :
    cpsTripleWithin (nSteps1 + nSteps2) s e (cr1.union cr2) P R :=
  cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ hp => hp) hperm h1) h2

/-- Sequence with same CodeReq: compose two CPS triples sharing the same CodeReq.
    Unlike `cpsTriple_seq`, does not require disjointness (same cr on both sides).
    All position/code/assertion arguments are implicit — inferred from `h1`/`h2`. -/
theorem cpsTripleWithin_seq_cpsBranchWithin_with_perm {nSteps1 nSteps2 : Nat}
    {entry mid : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q1 Q2 : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTripleWithin nSteps1 entry mid cr1 P Q1)
    (h2 : cpsBranchWithin nSteps2 mid cr2 Q2 exit_t Q_t exit_f Q_f) :
    cpsBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P exit_t Q_t exit_f Q_f :=
  cpsTripleWithin_seq_cpsBranchWithin hd
    (cpsTripleWithin_weaken (fun _ hp => hp) hperm h1) h2

/-- Compose a cpsBranchWithin with a cpsNBranchWithin on the not-taken (false) path.
    The taken path becomes a new exit prepended to the cpsNBranchWithin exits. -/
theorem cpsBranchWithin_seq_cpsBranchWithin {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q_t1 Q_f1 Q_t2 Q_f2 Q_t : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr1 P target Q_t1 mid Q_f1)
    (h2 : cpsBranchWithin nSteps2 mid cr2 Q_f1 target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P target Q_t exit_f Q_f2 := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr1 hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      Or.inl ⟨hpc_t1, by
        obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
        exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · have hcr2' := CodeReq.SatisfiedBy_preserved hstep1 hcr2
    obtain ⟨k2, hk2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hcr2' hQ_f1R hpc_f1
    rcases hbranch2 with ⟨hpc_t2, hQ_t2R⟩ | ⟨hpc_f2, hQ_f2R⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inl ⟨hpc_t2, by
          obtain ⟨hp, hcompat, hpq⟩ := hQ_t2R
          exact ⟨hp, hcompat, sepConj_mono_left ht2 hp hpq⟩⟩⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inr ⟨hpc_f2, hQ_f2R⟩⟩

/-- Bounded version of `cpsBranch_seq_cpsBranch_with_perm`. Bounds add. -/
theorem cpsBranchWithin_seq_cpsBranchWithin_with_perm
    {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q_t1 Q_f1 R Q_t2 Q_f2 Q_t : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr1 P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsBranchWithin nSteps2 mid cr2 R target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranchWithin (nSteps1 + nSteps2) entry (cr1.union cr2) P target Q_t exit_f Q_f2 :=
  cpsBranchWithin_seq_cpsBranchWithin hd
    (cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1 ht2

/-- Weaken postconditions of all exits in a cpsNBranchWithin.
    All position/code/assertion arguments are implicit — inferred from `h`/goal type. -/
theorem cpsTripleWithin_frameR {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (F : Assertion) (hF : F.pcFree)
    (h : cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** F) (Q ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, s', hstep, hpc', hpost⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, hk, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hpost⟩

/-- Frame a pcFree assertion `F` on the left of a bounded cpsTripleWithin. The step
    bound is unchanged. -/
theorem cpsTripleWithin_frameL {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (F : Assertion) (hF : F.pcFree)
    (h : cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr (F ** P) (F ** Q) := by
  intro R hR s hcr hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, hk, s', hstep, hpc', hpost⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR hpc
  exact ⟨k, hk, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hpost⟩

/-- Frame a pcFree assertion `F` on the right of a bounded cpsBranchWithin. The step
    bound is unchanged. -/
theorem cpsBranchWithin_frameR {nSteps : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranchWithin nSteps entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry cr (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, s', hstep, hcase⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, hk, s', hstep, hcase.elim
    (fun ⟨hpc', hpost⟩ => Or.inl ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)
    (fun ⟨hpc', hpost⟩ => Or.inr ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)⟩

/-- Extract the taken path from a bounded cpsBranchWithin when the not-taken
    postcondition is unsatisfiable. -/
theorem cpsBranchWithin_takenPath {nSteps : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P Q_t Q_f : Assertion}
    (hbr : cpsBranchWithin nSteps entry cr P l_t Q_t l_f Q_f)
    (h_absurd : ∀ hp, Q_f hp → False) :
    cpsTripleWithin nSteps entry l_t cr P Q_t := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := hbr R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_tR⟩ | ⟨hpc_f, hQ_fR⟩
  · exact ⟨k, hk, s', hstep, hpc_t, hQ_tR⟩
  · obtain ⟨hp, hcompat, h1, h2, hd, hu, hQf, hR'⟩ := hQ_fR
    exact absurd hQf (h_absurd h1)

/-- Extract the not-taken path from a bounded cpsBranchWithin when the taken
    postcondition is unsatisfiable. -/
theorem cpsBranchWithin_ntakenPath {nSteps : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P Q_t Q_f : Assertion}
    (hbr : cpsBranchWithin nSteps entry cr P l_t Q_t l_f Q_f)
    (h_absurd : ∀ hp, Q_t hp → False) :
    cpsTripleWithin nSteps entry l_f cr P Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := hbr R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_tR⟩ | ⟨hpc_f, hQ_fR⟩
  · obtain ⟨hp, hcompat, h1, h2, hd, hu, hQt, hR'⟩ := hQ_tR
    exact absurd hQt (h_absurd h1)
  · exact ⟨k, hk, s', hstep, hpc_f, hQ_fR⟩

/-- Bounded version of `cpsBranch_takenStripPure2`. -/
theorem cpsBranchWithin_takenStripPure2
    {nSteps : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P A B : Assertion} {Prop_t : Prop} {Q_f : Assertion}
    (hbr : cpsBranchWithin nSteps entry cr P l_t (A ** B ** ⌜Prop_t⌝) l_f Q_f)
    (h_absurd : ∀ hp, Q_f hp → False) :
    cpsTripleWithin nSteps entry l_t cr P (A ** B) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    sepConj_strip_pure_end2
    (cpsBranchWithin_takenPath hbr h_absurd)

/-- Bounded version of `cpsBranch_takenStripPure3`. -/
theorem cpsBranchWithin_takenStripPure3
    {nSteps : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P A B C : Assertion} {Prop_t : Prop} {Q_f : Assertion}
    (hbr : cpsBranchWithin nSteps entry cr P l_t (A ** B ** C ** ⌜Prop_t⌝) l_f Q_f)
    (h_absurd : ∀ hp, Q_f hp → False) :
    cpsTripleWithin nSteps entry l_t cr P (A ** B ** C) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    sepConj_strip_pure_end3
    (cpsBranchWithin_takenPath hbr h_absurd)

/-- Bounded version of `cpsBranch_ntakenStripPure2`. -/
theorem cpsBranchWithin_ntakenStripPure2
    {nSteps : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P A B : Assertion} {Prop_f : Prop} {Q_t : Assertion}
    (hbr : cpsBranchWithin nSteps entry cr P l_t Q_t l_f (A ** B ** ⌜Prop_f⌝))
    (h_absurd : ∀ hp, Q_t hp → False) :
    cpsTripleWithin nSteps entry l_f cr P (A ** B) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    sepConj_strip_pure_end2
    (cpsBranchWithin_ntakenPath hbr h_absurd)

/-- Bounded version of `cpsBranch_ntakenStripPure3`. -/
theorem cpsBranchWithin_ntakenStripPure3
    {nSteps : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P A B C : Assertion} {Prop_f : Prop} {Q_t : Assertion}
    (hbr : cpsBranchWithin nSteps entry cr P l_t Q_t l_f (A ** B ** C ** ⌜Prop_f⌝))
    (h_absurd : ∀ hp, Q_t hp → False) :
    cpsTripleWithin nSteps entry l_f cr P (A ** B ** C) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    sepConj_strip_pure_end3
    (cpsBranchWithin_ntakenPath hbr h_absurd)

/-- Frame a pcFree assertion `F` on the right of a cpsTripleWithin: pre becomes
    `P ** F` and post becomes `Q ** F`. Position/code/pre/post args are all
    implicit. -/
theorem cpsBranchWithin_seq_cpsBranchWithin_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr : CodeReq}
    {P Q_t1 Q_f1 Q_t2 Q_f2 Q_t : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr P target Q_t1 mid Q_f1)
    (h2 : cpsBranchWithin nSteps2 mid cr Q_f1 target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P target Q_t exit_f Q_f2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      Or.inl ⟨hpc_t1, by
        obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
        exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hcr' hQ_f1R hpc_f1
    rcases hbranch2 with ⟨hpc_t2, hQ_t2R⟩ | ⟨hpc_f2, hQ_f2R⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inl ⟨hpc_t2, by
          obtain ⟨hp, hcompat, hpq⟩ := hQ_t2R
          exact ⟨hp, hcompat, sepConj_mono_left ht2 hp hpq⟩⟩⟩
    · exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
        Or.inr ⟨hpc_f2, hQ_f2R⟩⟩

/-- Bounded same-CodeReq version of `cpsBranch_seq_cpsBranch_with_perm_same_cr`.
    Bounds add. -/
theorem cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr : CodeReq}
    {P Q_t1 Q_f1 R Q_t2 Q_f2 Q_t : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsBranchWithin nSteps2 mid cr R target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P target Q_t exit_f Q_f2 :=
  cpsBranchWithin_seq_cpsBranchWithin_same_cr
    (cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1 ht2

/-- Compose a cpsBranchWithin (ntaken exit) with a cpsTripleWithin, same CodeReq.
    The taken exit is passed through with a postcondition weakening. -/
theorem cpsBranchWithin_seq_cpsTripleWithin_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr : CodeReq}
    {P Q_t1 Q_f1 Q_f2 Q_t : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr P target Q_t1 mid Q_f1)
    (h2 : cpsTripleWithin nSteps2 mid exit_f cr Q_f1 Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P target Q_t exit_f Q_f2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right nSteps1 nSteps2), s1, hstep1,
      Or.inl ⟨hpc_t1, by
        obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
        exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQ_f2R⟩ := h2 R hR s1 hcr' hQ_f1R hpc_f1
    exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2,
           Or.inr ⟨hpc2, hQ_f2R⟩⟩

/-- Bounded same-CodeReq composition of a branch and triple with a permutation
    on the not-taken postcondition. Bounds add. -/
theorem cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr {nSteps1 nSteps2 : Nat}
    {entry mid target exit_f : Word} {cr : CodeReq}
    {P Q_t1 Q_f1 R Q_f2 Q_t : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsTripleWithin nSteps2 mid exit_f cr R Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P target Q_t exit_f Q_f2 :=
  cpsBranchWithin_seq_cpsTripleWithin_same_cr
    (cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1

end EvmAsm.Rv64
