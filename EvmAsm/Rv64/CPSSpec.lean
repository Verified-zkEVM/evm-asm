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
  - cpsTriple: single-exit specification (entry → exit with P → Q)
  - cpsBranch: two-exit specification (entry → exit_t with Q_t OR exit_f with Q_f)

  Structural rules:
  - cpsTriple_seq: sequential composition
  - cpsTriple_consequence: pre/post strengthening/weakening
  - cpsBranch_merge: merge two branch exits into a single continuation

  All assertions are `Assertion` (predicates on PartialState), bridged to
  MachineState via `holdsFor`.
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Execution

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
def cpsTriple (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧ s'.pc = exit_ ∧ (Q ** R).holdsFor s'

/-- CPS spec for code with two exits (the branch pattern) with built-in frame:
    "For any pcFree frame R, if cr is satisfied and (P ** R) holds at entry,
     execution reaches EITHER exit_t with (Q_t ** R) OR exit_f with (Q_f ** R)." -/
def cpsBranch (entry : Word) (cr : CodeReq) (P : Assertion)
    (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧
      ((s'.pc = exit_t ∧ (Q_t ** R).holdsFor s') ∨ (s'.pc = exit_f ∧ (Q_f ** R).holdsFor s'))

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- Sequence: compose two CPS triples sharing a midpoint. -/
theorem cpsTriple_seq (l1 l2 l3 : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q R : Assertion)
    (h1 : cpsTriple l1 l2 cr1 P Q)
    (h2 : cpsTriple l2 l3 cr2 Q R) :
    cpsTriple l1 l3 (cr1.union cr2) P R := by
  intro F hF s hcr hPF hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr1 hPF hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved cr2 k1 s s1 hstep1 hcr2
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := h2 F hF s1 hcr2' hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen precondition and weaken postcondition.
    Note: implications are at the assertion (PartialState) level, not holdsFor level,
    because (P' ** R).holdsFor s → (P ** R).holdsFor s requires P' h → P h pointwise.

    All pre/post-condition arguments are implicit: `P`/`Q` unify from the triple
    `h`, `P'`/`Q'` from the expected goal type. Prefer this over
    `cpsTriple_consequence` (which takes seven explicit `_` arguments). -/
theorem cpsTriple_weaken {entry exit_ : Word} {cr : CodeReq}
    {P P' Q Q' : Assertion}
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr P' Q' := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Explicit-argument variant of `cpsTriple_weaken`. Kept for backwards
    compatibility; prefer `cpsTriple_weaken` in new code. -/
@[deprecated cpsTriple_weaken (since := "2026-04-19")]
theorem cpsTriple_consequence (entry exit_ : Word) (cr : CodeReq)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr P' Q' :=
  cpsTriple_weaken hpre hpost h

/-- Strip a pure hypothesis from a `cpsTriple`'s precondition and use it
    simultaneously to weaken the postcondition. The pre-assertion `P ** ⌜fact⌝`
    lets the consumer simultaneously extract the pure `fact` and the non-pure
    part `P` — this is the exact shape that arises after `cpsBranch` elimination
    (the branch's taken/not-taken pre-assertion carries the concrete branch
    condition as a pure fact that the post-processing step needs).

    Shared across the Evm64 opcode compositions (`Byte/Spec.lean`,
    `SignExtend/Compose.lean`, `Shift/{Compose, ShlCompose, SarCompose}.lean`)
    that previously each re-declared this as a `private theorem`. -/
theorem cpsTriple_strip_pure_and_convert
    {entry exit_ : Word} {cr : CodeReq}
    {P Q Q' : Assertion} {fact : Prop}
    (hbody : cpsTriple entry exit_ cr P Q)
    (hpost : fact → ∀ h, Q h → Q' h) :
    cpsTriple entry exit_ cr (P ** ⌜fact⌝) Q' := by
  intro R hR s hcr hPFR hpc
  have hfact : fact := by
    obtain ⟨hp, _, hpq⟩ := hPFR
    obtain ⟨h1, _, _, _, hPF, _⟩ := hpq
    exact ((sepConj_pure_right P fact h1).1 hPF).2
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hPFR
    exact ⟨hp, hcompat, by
      obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
      exact ⟨h1, h2, hd, hunion, ((sepConj_pure_right P fact h1).1 hPF).1, hR_⟩⟩
  obtain ⟨k, s', hstep, hpc', hQR⟩ := hbody R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp', hcompat', hpq'⟩ := hQR
    exact ⟨hp', hcompat', sepConj_mono_left (hpost hfact) hp' hpq'⟩⟩

/-- Rule of consequence for cpsBranch: strengthen pre, weaken both posts.

    All pre/post-condition arguments are implicit: `P`/`Q_t`/`Q_f` unify from
    the branch `h`, and `P'`/`Q_t'`/`Q_f'` from the expected goal type. Prefer
    this over `cpsBranch_consequence` (which takes nine explicit `_` arguments). -/
theorem cpsBranch_weaken {entry : Word} {cr : CodeReq}
    {P P' : Assertion} {exit_t : Word} {Q_t Q_t' : Assertion}
    {exit_f : Word} {Q_f Q_f' : Assertion}
    (hpre : ∀ h, P' h → P h)
    (hpost_t : ∀ h, Q_t h → Q_t' h)
    (hpost_f : ∀ h, Q_f h → Q_f' h)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P' exit_t Q_t' exit_f Q_f' := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQR_t⟩ | ⟨hpc_f, hQR_f⟩
  · exact ⟨k, s', hstep, Or.inl ⟨hpc_t, by
      obtain ⟨hp, hcompat, hpq⟩ := hQR_t
      exact ⟨hp, hcompat, sepConj_mono_left hpost_t hp hpq⟩⟩⟩
  · exact ⟨k, s', hstep, Or.inr ⟨hpc_f, by
      obtain ⟨hp, hcompat, hpq⟩ := hQR_f
      exact ⟨hp, hcompat, sepConj_mono_left hpost_f hp hpq⟩⟩⟩

/-- Explicit-argument variant of `cpsBranch_weaken`. Kept for backwards
    compatibility; prefer `cpsBranch_weaken` in new code. -/
@[deprecated cpsBranch_weaken (since := "2026-04-19")]
theorem cpsBranch_consequence (entry : Word) (cr : CodeReq)
    (P P' : Assertion) (exit_t : Word) (Q_t Q_t' : Assertion)
    (exit_f : Word) (Q_f Q_f' : Assertion)
    (hpre : ∀ h, P' h → P h)
    (hpost_t : ∀ h, Q_t h → Q_t' h)
    (hpost_f : ∀ h, Q_f h → Q_f' h)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P' exit_t Q_t' exit_f Q_f' :=
  cpsBranch_weaken hpre hpost_t hpost_f h

/-- Swap the two branch targets of a cpsBranch. -/
theorem cpsBranch_swap (entry : Word) (cr : CodeReq) (P : Assertion)
    (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P exit_f Q_f exit_t Q_t := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hbranch.symm⟩

/-- Extract cpsTriple from cpsBranch when the taken-branch postcondition is unsatisfiable. -/
theorem cpsBranch_exit_absurd (entry : Word) (cr : CodeReq) (P : Assertion)
    (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f)
    (habsurd : ∀ h, Q_t h → False) :
    cpsTriple entry exit_f cr P Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQt⟩ | ⟨hpc_f, hQf⟩
  · obtain ⟨_, _, h1, _, _, _, hQ1, _⟩ := hQt
    exact absurd hQ1 (habsurd h1)
  · exact ⟨k, s', hstep, hpc_f, hQf⟩

-- ============================================================================
-- regOwn / memOwn lifting helpers
-- ============================================================================

/-- Lift a spec quantified over v_old to one with regOwn in tail position:
    (∀ v_old, cpsTriple ... cr (P ** (r ↦ᵣ v_old)) Q) → cpsTriple ... cr (P ** regOwn r) Q -/
theorem cpsTriple_of_forall_regIs_to_regOwn
    {entry exit_ r P Q} (cr : CodeReq)
    (h : ∀ v_old, cpsTriple entry exit_ cr (P ** (r ↦ᵣ v_old)) Q) :
    cpsTriple entry exit_ cr (P ** regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨v_old, hv4⟩⟩ := hPown1
  exact h v_old R hR s hcr
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Lift a spec quantified over v_old to one with regOwn as entire precondition:
    (∀ v_old, cpsTriple ... cr (r ↦ᵣ v_old) Q) → cpsTriple ... cr (regOwn r) Q -/
theorem cpsTriple_of_forall_regIs_to_regOwn_single
    {entry exit_ r Q} (cr : CodeReq)
    (h : ∀ v_old, cpsTriple entry exit_ cr (r ↦ᵣ v_old) Q) :
    cpsTriple entry exit_ cr (regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hunion, ⟨v_old, hv⟩, hR2⟩ := hPR
  exact h v_old R hR s hcr ⟨hp, hcompat, h1, h2, hd, hunion, hv, hR2⟩ hpc

/-- Lift a spec quantified over v_old to one with memOwn in tail position:
    (∀ v_old, cpsTriple ... cr (P ** (a ↦ₘ v_old)) Q) → cpsTriple ... cr (P ** memOwn a) Q -/
theorem cpsTriple_of_forall_memIs_to_memOwn
    {entry exit_ a P Q} (cr : CodeReq)
    (h : ∀ v_old, cpsTriple entry exit_ cr (P ** (a ↦ₘ v_old)) Q) :
    cpsTriple entry exit_ cr (P ** memOwn a) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨v_old, hv4⟩⟩ := hPown1
  exact h v_old R hR s hcr
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Branch elimination: if both branch exits lead to the same
    continuation exit with R, merge back into a single cpsTriple. -/
theorem cpsBranch_merge (entry l_t l_f exit_ : Word) (cr1 cr_t cr_f : CodeReq)
    (hd1 : cr1.Disjoint (cr_t.union cr_f)) (hd2 : cr_t.Disjoint cr_f)
    (P Q_t Q_f R : Assertion)
    (hbr   : cpsBranch entry cr1 P l_t Q_t l_f Q_f)
    (h_t   : cpsTriple l_t exit_ cr_t Q_t R)
    (h_f   : cpsTriple l_f exit_ cr_f Q_f R) :
    cpsTriple entry exit_ (cr1.union (cr_t.union cr_f)) P R := by
  intro F hF s hcr hPF hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd1] at hcr
  obtain ⟨hcr1, hcr_tf⟩ := hcr
  rw [CodeReq.union_satisfiedBy _ _ _ hd2] at hcr_tf
  obtain ⟨hcrt, hcrf⟩ := hcr_tf
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr F hF s hcr1 hPF hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · have hcrt' := CodeReq.SatisfiedBy_preserved cr_t k1 s s1 hstep1 hcrt
    obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hcrt' hQ_t hpc_t
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hR⟩
  · have hcrf' := CodeReq.SatisfiedBy_preserved cr_f k1 s s1 hstep1 hcrf
    obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hcrf' hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hR⟩

/-- Like cpsBranch_merge but with the same CodeReq for all three specs.
    No disjointness needed since code requirements are shared. -/
theorem cpsBranch_merge_same_cr (entry l_t l_f exit_ : Word) (cr : CodeReq)
    (P Q_t Q_f R : Assertion)
    (hbr   : cpsBranch entry cr P l_t Q_t l_f Q_f)
    (h_t   : cpsTriple l_t exit_ cr Q_t R)
    (h_f   : cpsTriple l_f exit_ cr Q_f R) :
    cpsTriple entry exit_ cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr F hF s hcr hPF hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hcr' hQ_t hpc_t
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hcr' hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hR⟩

/-- Extract the taken path from a cpsBranch when the not-taken postcondition
    is unsatisfiable (e.g., contains a contradictory pure fact).
    All position/code/pre/post arguments are implicit — unify from `hbr`. -/
theorem cpsBranch_takenPath {entry l_t l_f : Word} {cr : CodeReq}
    {P Q_t Q_f : Assertion}
    (hbr : cpsBranch entry cr P l_t Q_t l_f Q_f)
    (h_absurd : ∀ hp, Q_f hp → False) :
    cpsTriple entry l_t cr P Q_t := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := hbr R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_tR⟩ | ⟨hpc_f, hQ_fR⟩
  · exact ⟨k, s', hstep, hpc_t, hQ_tR⟩
  · obtain ⟨hp, hcompat, h1, h2, hd, hu, hQf, hR'⟩ := hQ_fR
    exact absurd hQf (h_absurd h1)

/-- Explicit-argument variant of `cpsBranch_takenPath`. Kept for backwards
    compatibility; prefer `cpsBranch_takenPath` in new code. -/
@[deprecated cpsBranch_takenPath (since := "2026-04-19")]
theorem cpsBranch_elim_taken (entry l_t l_f : Word) (cr : CodeReq)
    (P Q_t Q_f : Assertion)
    (hbr : cpsBranch entry cr P l_t Q_t l_f Q_f)
    (h_absurd : ∀ hp, Q_f hp → False) :
    cpsTriple entry l_t cr P Q_t :=
  cpsBranch_takenPath hbr h_absurd

/-- Extract the not-taken path from a cpsBranch when the taken postcondition
    is unsatisfiable (e.g., contains a contradictory pure fact).
    All position/code/pre/post arguments are implicit — unify from `hbr`. -/
theorem cpsBranch_ntakenPath {entry l_t l_f : Word} {cr : CodeReq}
    {P Q_t Q_f : Assertion}
    (hbr : cpsBranch entry cr P l_t Q_t l_f Q_f)
    (h_absurd : ∀ hp, Q_t hp → False) :
    cpsTriple entry l_f cr P Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := hbr R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_tR⟩ | ⟨hpc_f, hQ_fR⟩
  · obtain ⟨hp, hcompat, h1, h2, hd, hu, hQt, hR'⟩ := hQ_tR
    exact absurd hQt (h_absurd h1)
  · exact ⟨k, s', hstep, hpc_f, hQ_fR⟩

/-- Explicit-argument variant of `cpsBranch_ntakenPath`. Kept for backwards
    compatibility; prefer `cpsBranch_ntakenPath` in new code. -/
@[deprecated cpsBranch_ntakenPath (since := "2026-04-19")]
theorem cpsBranch_elim_ntaken (entry l_t l_f : Word) (cr : CodeReq)
    (P Q_t Q_f : Assertion)
    (hbr : cpsBranch entry cr P l_t Q_t l_f Q_f)
    (h_absurd : ∀ hp, Q_t hp → False) :
    cpsTriple entry l_f cr P Q_f :=
  cpsBranch_ntakenPath hbr h_absurd

/-- Eliminate the not-taken path from a cpsBranch AND strip the trailing pure fact
    from the taken postcondition (depth 2: A ** B ** ⌜P⌝ → A ** B). All arguments
    except the two proofs are implicit — inferred from `hbr`. -/
theorem cpsBranch_takenStripPure2
    {entry l_t l_f : Word} {cr : CodeReq} {P A B : Assertion} {Prop_t : Prop} {Q_f : Assertion}
    (hbr : cpsBranch entry cr P l_t (A ** B ** ⌜Prop_t⌝) l_f Q_f)
    (h_absurd : ∀ hp, Q_f hp → False) :
    cpsTriple entry l_t cr P (A ** B) :=
  cpsTriple_weaken
    (fun _ hp => hp)
    (sepConj_strip_pure_end2 A B Prop_t)
    (cpsBranch_takenPath hbr h_absurd)

/-- Eliminate the not-taken path from a cpsBranch AND strip the trailing pure fact
    from the taken postcondition (depth 3: A ** B ** C ** ⌜P⌝ → A ** B ** C).
    All arguments except the two proofs are implicit — inferred from `hbr`. -/
theorem cpsBranch_takenStripPure3
    {entry l_t l_f : Word} {cr : CodeReq} {P A B C : Assertion} {Prop_t : Prop} {Q_f : Assertion}
    (hbr : cpsBranch entry cr P l_t (A ** B ** C ** ⌜Prop_t⌝) l_f Q_f)
    (h_absurd : ∀ hp, Q_f hp → False) :
    cpsTriple entry l_t cr P (A ** B ** C) :=
  cpsTriple_weaken
    (fun _ hp => hp)
    (sepConj_strip_pure_end3 A B C Prop_t)
    (cpsBranch_takenPath hbr h_absurd)

/-- Eliminate the taken path from a cpsBranch AND strip the trailing pure fact
    from the not-taken postcondition (depth 2: A ** B ** ⌜P⌝ → A ** B).
    All arguments except the two proofs are implicit — inferred from `hbr`. -/
theorem cpsBranch_ntakenStripPure2
    {entry l_t l_f : Word} {cr : CodeReq} {P A B : Assertion} {Prop_f : Prop} {Q_t : Assertion}
    (hbr : cpsBranch entry cr P l_t Q_t l_f (A ** B ** ⌜Prop_f⌝))
    (h_absurd : ∀ hp, Q_t hp → False) :
    cpsTriple entry l_f cr P (A ** B) :=
  cpsTriple_weaken
    (fun _ hp => hp)
    (sepConj_strip_pure_end2 A B Prop_f)
    (cpsBranch_ntakenPath hbr h_absurd)

/-- Eliminate the taken path from a cpsBranch AND strip the trailing pure fact
    from the not-taken postcondition (depth 3: A ** B ** C ** ⌜P⌝ → A ** B ** C).
    All arguments except the two proofs are implicit — inferred from `hbr`. -/
theorem cpsBranch_ntakenStripPure3
    {entry l_t l_f : Word} {cr : CodeReq} {P A B C : Assertion} {Prop_f : Prop} {Q_t : Assertion}
    (hbr : cpsBranch entry cr P l_t Q_t l_f (A ** B ** C ** ⌜Prop_f⌝))
    (h_absurd : ∀ hp, Q_t hp → False) :
    cpsTriple entry l_f cr P (A ** B ** C) :=
  cpsTriple_weaken
    (fun _ hp => hp)
    (sepConj_strip_pure_end3 A B C Prop_f)
    (cpsBranch_ntakenPath hbr h_absurd)

/-- A cpsTriple with zero steps: if entry = exit and P implies Q, trivially holds. -/
theorem cpsTriple_refl (addr : Word) (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsTriple addr addr CodeReq.empty P Q := by
  intro R hR s _hcr hPR hpc
  exact ⟨0, s, rfl, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

/-- Monotonicity: if cr' subsumes cr (cr' ⊇ cr), extend a cpsTriple to require more code. -/
theorem cpsTriple_extend_code {entry exit_ : Word} {cr cr' : CodeReq} {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr' P Q := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono s hmono hcr') hPR hpc

/-- Monotonicity for cpsBranch: extend to a larger CodeReq. -/
theorem cpsBranch_extend_code {entry : Word} {cr cr' : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr' P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono s hmono hcr') hPR hpc

/-- Sequential composition: cpsTriple followed by cpsBranch, same CodeReq.
    Unlike `cpsTriple_seq_cpsBranch`, does not require disjointness. -/
theorem cpsTriple_seq_cpsBranch_same_cr (entry mid : Word) (cr : CodeReq)
    (P Q : Assertion) (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion)
    (h1 : cpsTriple entry mid cr P Q)
    (h2 : cpsBranch mid cr Q exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr hPR hpc
  have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, hbranch⟩ := h2 R hR s1 hcr' hQR hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hbranch⟩

/-- Sequential composition with permutation: cpsTriple followed by cpsBranch, same CodeReq.
    All position/code/pre/post args implicit — \`entry\`/\`mid\`/\`cr\`/\`P\`/\`Q1\` unify
    from \`h1\`, \`Q2\`/\`exit_t\`/\`Q_t\`/\`exit_f\`/\`Q_f\` from \`h2\`. -/
theorem cpsTriple_seq_cpsBranch_perm_same_cr {entry mid : Word} {cr : CodeReq}
    {P Q1 Q2 : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid cr P Q1)
    (h2 : cpsBranch mid cr Q2 exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P exit_t Q_t exit_f Q_f :=
  cpsTriple_seq_cpsBranch_same_cr entry mid cr P Q2 exit_t Q_t exit_f Q_f
    (cpsTriple_consequence entry mid cr P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Explicit-argument variant of `cpsTriple_seq_cpsBranch_perm_same_cr`. Deprecated;
    prefer `cpsTriple_seq_cpsBranch_perm_same_cr` in new code. -/
@[deprecated cpsTriple_seq_cpsBranch_perm_same_cr (since := "2026-04-19")]
theorem cpsTriple_seq_cpsBranch_with_perm_same_cr (entry mid : Word) (cr : CodeReq)
    (P Q1 Q2 : Assertion) (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid cr P Q1)
    (h2 : cpsBranch mid cr Q2 exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P exit_t Q_t exit_f Q_f :=
  cpsTriple_seq_cpsBranch_perm_same_cr hperm h1 h2

-- ============================================================================
-- N-exit CPS specifications
-- ============================================================================

/-- CPS spec for code with N exits with built-in frame rule:
    "For any pcFree frame R, if cr is satisfied and (P ** R) holds at entry, execution reaches
    some exit in the list, with (exit.2 ** R) holding."

    Generalizes `cpsBranch` from 2 exits to an arbitrary list. -/
def cpsNBranch (entry : Word) (cr : CodeReq) (P : Assertion)
    (exits : List (Word × Assertion)) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧
      ∃ exit ∈ exits, s'.pc = exit.1 ∧ (exit.2 ** R).holdsFor s'

-- ============================================================================
-- Edge cases
-- ============================================================================

/-- An N-branch with no exits is vacuously false (no reachable exit). -/
theorem cpsNBranch_nil_false (entry : Word) (cr : CodeReq) (P : Assertion)
    (h : cpsNBranch entry cr P [])
    (s : MachineState) (hcr : cr.SatisfiedBy s) (hP : P.holdsFor s) (hpc : s.pc = entry) : False := by
  -- Use empAssertion as the frame
  have hPemp : (P ** empAssertion).holdsFor s := by
    obtain ⟨hp, hcompat, hph⟩ := hP
    exact ⟨hp, hcompat, hp, PartialState.empty, PartialState.Disjoint_empty_right hp,
           PartialState.union_empty_right hp, hph, rfl⟩
  obtain ⟨k, s', _, ex, hmem, _, _⟩ := h empAssertion pcFree_emp s hcr hPemp hpc
  exact List.not_mem_nil hmem

/-- An N-branch with impossible precondition vacuously holds for any exits. -/
theorem cpsNBranch_nil_of_false (entry : Word) (cr : CodeReq) :
    cpsNBranch entry cr (fun _ => False) [] := by
  intro R _ s _ ⟨_, _, h1, h2, _, _, hf, _⟩ _
  exact absurd hf id

/-- Reflexivity: zero steps, one exit at the same address. -/
theorem cpsNBranch_refl (addr : Word)
    (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsNBranch addr CodeReq.empty P [(addr, Q)] := by
  intro R hR s _hcr hPR hpc
  exact ⟨0, s, rfl, (addr, Q), List.Mem.head _, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

-- ============================================================================
-- Equivalences with existing types
-- ============================================================================

/-- A single-exit cpsTriple can be viewed as a cpsNBranch with one exit. -/
theorem cpsTriple_to_cpsNBranch (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) (h : cpsTriple entry exit_ cr P Q) :
    cpsNBranch entry cr P [(exit_, Q)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, (exit_, Q), List.Mem.head _, hpc', hQR⟩

/-- A singleton cpsNBranch gives back a cpsTriple. -/
theorem cpsNBranch_to_cpsTriple (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) (h : cpsNBranch entry cr P [(exit_, Q)]) :
    cpsTriple entry exit_ cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  cases hmem with
  | head => exact ⟨k, s', hstep, hpc', hQR⟩
  | tail _ h => exact absurd h List.not_mem_nil

/-- A 2-exit cpsBranch can be viewed as a cpsNBranch with two exits. -/
theorem cpsBranch_to_cpsNBranch (entry : Word) (cr : CodeReq)
    (P : Assertion)
    (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f : Assertion)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsNBranch entry cr P [(exit_t, Q_t), (exit_f, Q_f)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k, s', hstep, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · exact ⟨k, s', hstep, (exit_f, Q_f), List.Mem.tail _ (List.Mem.head _), hpc_f, hQ_f⟩

/-- A 2-element cpsNBranch gives back a cpsBranch. -/
theorem cpsNBranch_to_cpsBranch (entry : Word) (cr : CodeReq)
    (P : Assertion)
    (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f : Assertion)
    (h : cpsNBranch entry cr P [(exit_t, Q_t), (exit_f, Q_f)]) :
    cpsBranch entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  refine ⟨k, s', hstep, ?_⟩
  cases hmem with
  | head => left; exact ⟨hpc', hQR⟩
  | tail _ htail =>
    cases htail with
    | head => right; exact ⟨hpc', hQR⟩
    | tail _ h => exact absurd h List.not_mem_nil

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- N-branch merge: if every exit leads to the same continuation,
    compose into a single cpsTriple. This is the main structural rule.
    Uses the same cr for all parts (simpler; use cpsTriple_extend_code to adapt). -/
theorem cpsNBranch_merge (entry exit_ : Word) (cr : CodeReq)
    (P R : Assertion)
    (exits : List (Word × Assertion))
    (hbr : cpsNBranch entry cr P exits)
    (hall : ∀ exit ∈ exits, cpsTriple exit.1 exit_ cr exit.2 R) :
    cpsTriple entry exit_ cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hcr hPF hpc
  have hcr1 := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hall ex hmem F hF s1 hcr1 hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen the precondition of an N-branch. -/
theorem cpsNBranch_weaken_pre (entry : Word) (cr : CodeReq)
    (P P' : Assertion)
    (exits : List (Word × Assertion))
    (hpre : ∀ h, P' h → P h) (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr P' exits := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  exact h R hR s hcr hPR hpc

/-- Monotonicity: expand the exit list (weaken the exit constraint). -/
theorem cpsNBranch_weaken_exits (entry : Word) (cr : CodeReq)
    (P : Assertion)
    (exits exits' : List (Word × Assertion))
    (hsub : ∀ ex, ex ∈ exits → ex ∈ exits') (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr P exits' := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, ex, hsub ex hmem, hpc', hQR⟩

/-- Weaken the code requirement of a `cpsNBranch` via monotonic extension.
    Shared across the Evm64 opcode compositions (Shift/{Compose,ShlCompose,
    SarCompose}, Byte/Spec, SignExtend/Compose) that previously each
    re-declared this as a `private theorem`. -/
theorem cpsNBranch_extend_code {entry : Word} {cr cr' : CodeReq}
    {P : Assertion} {exits : List (Word × Assertion)}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr' P exits := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono s hmono hcr') hPR hpc

/-- Frame a `cpsNBranch` on the left by a PC-free frame `F`: the pre-assertion
    becomes `P ** F` and each exit assertion in the list becomes `ex.2 ** F`.
    Shared across Evm64 opcode compositions — previously 5× `private theorem`
    duplicates. -/
theorem cpsNBranch_frame_left {entry : Word} {cr : CodeReq}
    {P : Assertion} {exits : List (Word × Assertion)} {F : Assertion}
    (hF : F.pcFree) (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr (P ** F) (exits.map (fun ex => (ex.1, ex.2 ** F))) := by
  intro R hR s hcr hPFR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have hPFR' : (P ** (F ** R)).holdsFor s :=
    holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQFR⟩ :=
    h (F ** R) hFR s hcr hPFR' hpc
  refine ⟨k, s', hstep, (ex.1, ex.2 ** F), ?_, hpc', holdsFor_sepConj_assoc.mpr hQFR⟩
  exact List.mem_map.mpr ⟨ex, hmem, rfl⟩

/-- Extend the head exit by composing a cpsTriple after it. -/
theorem cpsNBranch_extend_head (entry l l' : Word) (cr : CodeReq)
    (P Q R : Assertion)
    (others : List (Word × Assertion))
    (hbr : cpsNBranch entry cr P ((l, Q) :: others))
    (hseq : cpsTriple l l' cr Q R) :
    cpsNBranch entry cr P ((l', R) :: others) := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hcr hPF hpc
  cases hmem with
  | head =>
    -- ex = (l, Q), compose with hseq
    have hcr1 := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hseq F hF s1 hcr1 hQF hpc1
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           (l', R), List.Mem.head _, hpc2, hRF⟩
  | tail _ htail =>
    -- ex ∈ others, pass through
    exact ⟨k1, s1, hstep1, ex, List.Mem.tail _ htail, hpc1, hQF⟩

-- ============================================================================
-- Halt-aware CPS specifications
-- ============================================================================

/-- A state is halted when `step` returns `none` (HALT syscall or no instruction). -/
def isHalted (s : MachineState) : Bool :=
  (step s).isNone

/-- CPS-style halt specification with built-in frame rule:
    For any pcFree frame R, starting from any state where cr is satisfied,
    (P ** R) holds and PC = entry, execution reaches a halted state where (Q ** R) holds.
    Unlike `cpsTriple`, there is no exit address — execution simply terminates. -/
def cpsHaltTriple (entry : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧ isHalted s' = true ∧ (Q ** R).holdsFor s'

/-- Promote a `cpsTriple` to a `cpsHaltTriple` when the exit address is halted.
    If execution reaches exit_ with Q, and every state satisfying (Q ** R) at exit_ is halted,
    then the program halts with Q. -/
theorem cpsTriple_to_cpsHaltTriple (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion)
    (h : cpsTriple entry exit_ cr P Q)
    (hhalt : ∀ (R : Assertion), R.pcFree → ∀ s, (Q ** R).holdsFor s → s.pc = exit_ →
      isHalted s = true) :
    cpsHaltTriple entry cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hhalt R hR s' hQR hpc', hQR⟩

/-- Consequence: strengthen precondition and weaken postcondition of a halt triple. -/
theorem cpsHaltTriple_consequence (entry : Word) (cr : CodeReq)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsHaltTriple entry cr P Q) :
    cpsHaltTriple entry cr P' Q' := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hhalt, hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hhalt, by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Sequence a `cpsTriple` followed by a `cpsHaltTriple`:
    if code reaches midpoint with Q, and from midpoint it halts with R, then
    the composition halts with R. -/
theorem cpsTriple_seq_halt (entry mid : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q R : Assertion)
    (h1 : cpsTriple entry mid cr1 P Q)
    (h2 : cpsHaltTriple mid cr2 Q R) :
    cpsHaltTriple entry (cr1.union cr2) P R := by
  intro F hF s hcr hPF hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr1 hPF hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved cr2 k1 s s1 hstep1 hcr2
  obtain ⟨k2, s2, hstep2, hhalt, hRF⟩ := h2 F hF s1 hcr2' hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hhalt, hRF⟩

/-- Sequential composition with midpoint permutation:
    compose h1 : cpsTriple s m cr1 P Q1 with h2 : cpsTriple m e cr2 Q2 R
    when Q1 and Q2 are AC-permutations (proved by hperm).
    Both Q1 and Q2 are fully determined by h1/h2, so the permutation
    obligation has no metavar ambiguity. -/
theorem cpsTriple_seq_with_perm (s m e : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q1 Q2 R : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple s m cr1 P Q1)
    (h2 : cpsTriple m e cr2 Q2 R) :
    cpsTriple s e (cr1.union cr2) P R :=
  cpsTriple_seq s m e cr1 cr2 hd P Q2 R
    (cpsTriple_consequence s m cr1 P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Sequence with same CodeReq: compose two CPS triples sharing the same CodeReq.
    Unlike `cpsTriple_seq`, does not require disjointness (same cr on both sides). -/
theorem cpsTriple_seq_same_cr (l1 l2 l3 : Word) (cr : CodeReq)
    (P Q R : Assertion)
    (h1 : cpsTriple l1 l2 cr P Q) (h2 : cpsTriple l2 l3 cr Q R) :
    cpsTriple l1 l3 cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr hPF hpc
  have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := h2 F hF s1 hcr' hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Sequential composition with midpoint permutation (same CodeReq).
    Like `cpsTriple_seq_with_perm` but for same-CR (no disjointness required).

    All position/code/assertion arguments are implicit: `s`, `m`, `e`, `cr`,
    `P`, `Q1`, `R` unify from `h1`/`h2`, and `Q2` from `hperm`. Prefer this
    over `cpsTriple_seq_with_perm_same_cr` (which takes nine explicit
    arguments before the proof inputs). -/
theorem cpsTriple_seq_perm_same_cr {s m e : Word} {cr : CodeReq}
    {P Q1 Q2 R : Assertion} (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple s m cr P Q1) (h2 : cpsTriple m e cr Q2 R) :
    cpsTriple s e cr P R :=
  cpsTriple_seq_same_cr s m e cr P Q2 R
    (cpsTriple_consequence s m cr P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Explicit-argument variant of `cpsTriple_seq_perm_same_cr`. Kept for
    backwards compatibility; prefer `cpsTriple_seq_perm_same_cr` in new code. -/
@[deprecated cpsTriple_seq_perm_same_cr (since := "2026-04-19")]
theorem cpsTriple_seq_with_perm_same_cr (s m e : Word) (cr : CodeReq)
    (P Q1 Q2 R : Assertion) (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple s m cr P Q1) (h2 : cpsTriple m e cr Q2 R) :
    cpsTriple s e cr P R :=
  cpsTriple_seq_perm_same_cr hperm h1 h2

-- ============================================================================
-- Cascade composition (for dispatch chains like Phase C)
-- ============================================================================

/-- Sequential composition: cpsTriple followed by cpsNBranch.
    If code reaches mid with Q, and from mid it branches to one of exits,
    then code branches from entry to one of exits. -/
theorem cpsTriple_seq_cpsNBranch (entry mid : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q : Assertion) (exits : List (Word × Assertion))
    (h1 : cpsTriple entry mid cr1 P Q)
    (h2 : cpsNBranch mid cr2 Q exits) :
    cpsNBranch entry (cr1.union cr2) P exits := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr1 hPR hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved cr2 k1 s s1 hstep1 hcr2
  obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h2 R hR s1 hcr2' hQR hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, ex, hmem, hpc2, hER⟩

/-- Sequential composition with permutation: cpsTriple followed by cpsNBranch
    when the intermediate assertions are permutations. -/
theorem cpsTriple_seq_cpsNBranch_with_perm (entry mid : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q1 Q2 : Assertion) (exits : List (Word × Assertion))
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid cr1 P Q1)
    (h2 : cpsNBranch mid cr2 Q2 exits) :
    cpsNBranch entry (cr1.union cr2) P exits :=
  cpsTriple_seq_cpsNBranch entry mid cr1 cr2 hd P Q2 exits
    (cpsTriple_consequence entry mid cr1 P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Sequential composition: cpsTriple followed by cpsBranch.
    If code reaches mid with Q, and from mid it branches, then the
    composition branches from entry. -/
theorem cpsTriple_seq_cpsBranch (entry mid : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q : Assertion) (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion)
    (h1 : cpsTriple entry mid cr1 P Q)
    (h2 : cpsBranch mid cr2 Q exit_t Q_t exit_f Q_f) :
    cpsBranch entry (cr1.union cr2) P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr1 hPR hpc
  have hcr2' := CodeReq.SatisfiedBy_preserved cr2 k1 s s1 hstep1 hcr2
  obtain ⟨k2, s2, hstep2, hbranch⟩ := h2 R hR s1 hcr2' hQR hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hbranch⟩

/-- Sequential composition with permutation: cpsTriple followed by cpsBranch. -/
theorem cpsTriple_seq_cpsBranch_with_perm (entry mid : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q1 Q2 : Assertion) (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid cr1 P Q1)
    (h2 : cpsBranch mid cr2 Q2 exit_t Q_t exit_f Q_f) :
    cpsBranch entry (cr1.union cr2) P exit_t Q_t exit_f Q_f :=
  cpsTriple_seq_cpsBranch entry mid cr1 cr2 hd P Q2 exit_t Q_t exit_f Q_f
    (cpsTriple_consequence entry mid cr1 P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Compose a cpsBranch with a cpsNBranch on the not-taken (false) path.
    The taken path becomes a new exit prepended to the cpsNBranch exits. -/
theorem cpsBranch_cons_cpsNBranch (entry : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P : Assertion) (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f : Assertion)
    (exits : List (Word × Assertion))
    (hbr : cpsBranch entry cr1 P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranch exit_f cr2 Q_f exits) :
    cpsNBranch entry (cr1.union cr2) P ((exit_t, Q_t) :: exits) := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr R hR s hcr1 hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, s1, hstep1, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · have hcr2' := CodeReq.SatisfiedBy_preserved cr2 k1 s s1 hstep1 hcr2
    obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h_rest R hR s1 hcr2' hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           ex, List.Mem.tail _ hmem, hpc2, hER⟩

/-- Compose a cpsBranch with a cpsNBranch, with permutation on the not-taken path. -/
theorem cpsBranch_cons_cpsNBranch_with_perm (entry : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P : Assertion) (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f Q_f' : Assertion)
    (exits : List (Word × Assertion))
    (hperm : ∀ h, Q_f h → Q_f' h)
    (hbr : cpsBranch entry cr1 P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranch exit_f cr2 Q_f' exits) :
    cpsNBranch entry (cr1.union cr2) P ((exit_t, Q_t) :: exits) := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr R hR s hcr1 hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, s1, hstep1, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · have hQ_f' : (Q_f' ** R).holdsFor s1 := by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_f
      exact ⟨hp, hcompat, sepConj_mono_left hperm hp hpq⟩
    have hcr2' := CodeReq.SatisfiedBy_preserved cr2 k1 s s1 hstep1 hcr2
    obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h_rest R hR s1 hcr2' hQ_f' hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           ex, List.Mem.tail _ hmem, hpc2, hER⟩

/-- Compose two sequential cpsBranch specs where the first's not-taken path leads
    to the second's entry, and both taken paths go to the same target.
    The two taken postconditions are merged into a common one via weakening functions. -/
theorem cpsBranch_seq_cpsBranch (entry mid target exit_f : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q_t1 Q_f1 Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr1 P target Q_t1 mid Q_f1)
    (h2 : cpsBranch mid cr2 Q_f1 target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry (cr1.union cr2) P target Q_t exit_f Q_f2 := by
  intro R hR s hcr hPR hpc
  rw [CodeReq.union_satisfiedBy _ _ _ hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr1 hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · -- First branch taken → target
    exact ⟨k1, s1, hstep1, Or.inl ⟨hpc_t1, by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
      exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · -- First branch not taken → mid, execute second
    have hcr2' := CodeReq.SatisfiedBy_preserved cr2 k1 s s1 hstep1 hcr2
    obtain ⟨k2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hcr2' hQ_f1R hpc_f1
    rcases hbranch2 with ⟨hpc_t2, hQ_t2R⟩ | ⟨hpc_f2, hQ_f2R⟩
    · -- Second branch taken → target
      exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
             Or.inl ⟨hpc_t2, by
               obtain ⟨hp, hcompat, hpq⟩ := hQ_t2R
               exact ⟨hp, hcompat, sepConj_mono_left ht2 hp hpq⟩⟩⟩
    · -- Second branch not taken → exit_f
      exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
             Or.inr ⟨hpc_f2, hQ_f2R⟩⟩

/-- Like `cpsBranch_seq_cpsBranch` but with a permutation between Q_f1 and R. -/
theorem cpsBranch_seq_cpsBranch_with_perm
    (entry mid target exit_f : Word) (cr1 cr2 : CodeReq)
    (hd : cr1.Disjoint cr2)
    (P Q_t1 Q_f1 R Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr1 P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsBranch mid cr2 R target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry (cr1.union cr2) P target Q_t exit_f Q_f2 :=
  cpsBranch_seq_cpsBranch entry mid target exit_f cr1 cr2 hd P Q_t1 R Q_t2 Q_f2 Q_t
    (cpsBranch_consequence entry cr1
      _ _ _ _ _ _ _ _
      (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1 ht2

/-- Weaken postconditions of all exits in a cpsNBranch. -/
theorem cpsNBranch_weaken_posts (entry : Word) (cr : CodeReq)
    (P : Assertion) (exits exits' : List (Word × Assertion))
    (h : cpsNBranch entry cr P exits)
    (hmap : ∀ ex ∈ exits, ∃ ex' ∈ exits', ex'.1 = ex.1 ∧ ∀ h, ex.2 h → ex'.2 h) :
    cpsNBranch entry cr P exits' := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hER⟩ := h R hR s hcr hPR hpc
  obtain ⟨ex', hmem', heq, hpost⟩ := hmap ex hmem
  rw [← heq] at hpc'
  exact ⟨k, s', hstep, ex', hmem', hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hER
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

-- ============================================================================
-- Frame rules
-- ============================================================================

/-- Frame a pcFree assertion `F` on the right of a cpsTriple: pre becomes
    `P ** F` and post becomes `Q ** F`. Position/code/pre/post args are all
    implicit; prefer this over `cpsTriple_frame_left` (which takes five
    explicit `_` arguments before the frame `F`). -/
theorem cpsTriple_frameR {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr (P ** F) (Q ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hpost⟩

/-- Explicit-argument variant of `cpsTriple_frameR`. Kept for backwards
    compatibility; prefer `cpsTriple_frameR` in new code. Note the name
    is a misnomer — it adds `F` to the *right* of the sepConj chain. -/
@[deprecated cpsTriple_frameR (since := "2026-04-19")]
theorem cpsTriple_frame_left (entry exit_ : Word) (cr : CodeReq)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr (P ** F) (Q ** F) :=
  cpsTriple_frameR F hF h

/-- Frame a pcFree assertion `F` on the left of a cpsTriple: pre becomes
    `F ** P` and post becomes `F ** Q`. Position/code/pre/post args are all
    implicit; prefer this over `cpsTriple_frame_right`. -/
theorem cpsTriple_frameL {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr (F ** P) (F ** Q) := by
  intro R hR s hcr hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hpost⟩

/-- Frame for cpsBranch: add `F` on the right. Position/code/pre/post args
    are all implicit; prefer this over `cpsBranch_frame_left` (which takes
    seven explicit `_` arguments before the frame `F`). -/
theorem cpsBranch_frameR {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hcase⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, s', hstep, hcase.elim
    (fun ⟨hpc', hpost⟩ => Or.inl ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)
    (fun ⟨hpc', hpost⟩ => Or.inr ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)⟩

/-- Explicit-argument variant of `cpsBranch_frameR`. Kept for backwards
    compatibility; prefer `cpsBranch_frameR` in new code. -/
@[deprecated cpsBranch_frameR (since := "2026-04-19")]
theorem cpsBranch_frame_left (entry : Word) (cr : CodeReq)
    (P : Assertion) (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f : Assertion)
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) :=
  cpsBranch_frameR F hF h

/-- Frame on the right for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_left (entry : Word) (cr : CodeReq)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry cr P Q) :
    cpsHaltTriple entry cr (P ** F) (Q ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hhalt, hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_assoc.mpr hpost⟩

-- ============================================================================
-- Loop rules
-- ============================================================================

/-- Loop rule: prove a loop correct by induction on a decreasing variant.
    h_base: when variant = 0, the code must exit (no more iterations).
    h_step: when variant = n+1, one iteration either exits with Q
            or returns to entry with inv n (variant decreased by 1). -/
theorem cpsTriple_loop
    (entry exit_ : Word) (cr : CodeReq)
    (inv : Nat → Assertion)
    (Q : Assertion)
    (h_base : cpsTriple entry exit_ cr (inv 0) Q)
    (h_step : ∀ n, cpsBranch entry cr (inv (n + 1))
                              exit_ Q
                              entry (inv n))
    : ∀ n, cpsTriple entry exit_ cr (inv n) Q := by
  intro n
  induction n with
  | zero => exact h_base
  | succ k ih =>
    intro R hR s hcr hPR hpc
    obtain ⟨k1, s1, hstep1, hbranch⟩ := h_step k R hR s hcr hPR hpc
    rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
    · exact ⟨k1, s1, hstep1, hpc_t, hQ_t⟩
    · have hcr1 := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
      obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := ih R hR s1 hcr1 hQ_f hpc_f
      exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Simplified loop rule where the step spec has the same cr. -/
theorem cpsTriple_loop_simple
    (entry exit_ : Word) (cr : CodeReq)
    (inv : Nat → Assertion)
    (Q : Assertion)
    (h_base : cpsTriple entry exit_ cr (inv 0) Q)
    (h_step : ∀ n, cpsBranch entry cr (inv (n + 1))
                              exit_ Q
                              entry (inv n))
    : ∀ n, cpsTriple entry exit_ cr (inv n) Q :=
  cpsTriple_loop entry exit_ cr inv Q h_base h_step

/-- Loop rule with permutation on back-edge and exit postconditions. -/
theorem cpsTriple_loop_with_perm
    (entry exit_ : Word) (cr : CodeReq)
    (inv : Nat → Assertion)
    (Q : Assertion)
    (inv' : Nat → Assertion)
    (Q' : Assertion)
    (h_base : cpsTriple entry exit_ cr (inv 0) Q)
    (h_step : ∀ n, cpsBranch entry cr (inv (n + 1))
                              exit_ Q'
                              entry (inv' n))
    (hperm_inv : ∀ n h, inv' n h → inv n h)
    (hperm_Q : ∀ h, Q' h → Q h)
    : ∀ n, cpsTriple entry exit_ cr (inv n) Q := by
  have h_step' : ∀ n, cpsBranch entry cr (inv (n + 1)) exit_ Q entry (inv n) :=
    fun n => cpsBranch_consequence entry cr
      (inv (n + 1)) (inv (n + 1)) exit_ Q' Q entry (inv' n) (inv n)
      (fun _ h => h) hperm_Q (hperm_inv n) (h_step n)
  exact cpsTriple_loop entry exit_ cr inv Q h_base h_step'

-- ============================================================================
-- Same-CR variants for cascade/branch composition
-- ============================================================================

/-- Like cpsBranch_seq_cpsBranch but with same CodeReq (no disjointness needed). -/
theorem cpsBranch_seq_cpsBranch_same_cr (entry mid target exit_f : Word) (cr : CodeReq)
    (P Q_t1 Q_f1 Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr P target Q_t1 mid Q_f1)
    (h2 : cpsBranch mid cr Q_f1 target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry cr P target Q_t exit_f Q_f2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · exact ⟨k1, s1, hstep1, Or.inl ⟨hpc_t1, by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
      exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hcr' hQ_f1R hpc_f1
    rcases hbranch2 with ⟨hpc_t2, hQ_t2R⟩ | ⟨hpc_f2, hQ_f2R⟩
    · exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
             Or.inl ⟨hpc_t2, by
               obtain ⟨hp, hcompat, hpq⟩ := hQ_t2R
               exact ⟨hp, hcompat, sepConj_mono_left ht2 hp hpq⟩⟩⟩
    · exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
             Or.inr ⟨hpc_f2, hQ_f2R⟩⟩

/-- Like cpsBranch_seq_cpsBranch_with_perm but with same CodeReq. -/
theorem cpsBranch_seq_cpsBranch_with_perm_same_cr
    (entry mid target exit_f : Word) (cr : CodeReq)
    (P Q_t1 Q_f1 R Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsBranch mid cr R target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry cr P target Q_t exit_f Q_f2 :=
  cpsBranch_seq_cpsBranch_same_cr entry mid target exit_f cr P Q_t1 R Q_t2 Q_f2 Q_t
    (cpsBranch_consequence entry cr
      _ _ _ _ _ _ _ _
      (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1 ht2

/-- Compose a cpsBranch (ntaken exit) with a cpsTriple, same CodeReq.
    The taken exit is passed through with a postcondition weakening. -/
theorem cpsBranch_seq_cpsTriple_same_cr (entry mid target exit_f : Word) (cr : CodeReq)
    (P Q_t1 Q_f1 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr P target Q_t1 mid Q_f1)
    (h2 : cpsTriple mid exit_f cr Q_f1 Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h) :
    cpsBranch entry cr P target Q_t exit_f Q_f2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · exact ⟨k1, s1, hstep1, Or.inl ⟨hpc_t1, by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
      exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hpc2, hQ_f2R⟩ := h2 R hR s1 hcr' hQ_f1R hpc_f1
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           Or.inr ⟨hpc2, hQ_f2R⟩⟩

/-- Like cpsBranch_seq_cpsTriple_same_cr but with a permutation between Q_f1 and the
    cpsTriple precondition. -/
theorem cpsBranch_seq_cpsTriple_with_perm_same_cr (entry mid target exit_f : Word) (cr : CodeReq)
    (P Q_t1 Q_f1 R Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsTriple mid exit_f cr R Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h) :
    cpsBranch entry cr P target Q_t exit_f Q_f2 :=
  cpsBranch_seq_cpsTriple_same_cr entry mid target exit_f cr P Q_t1 R Q_f2 Q_t
    (cpsBranch_consequence entry cr _ _ _ _ _ _ _ _
      (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1

/-- Compose a cpsBranch with a cpsNBranch on the not-taken path, same CodeReq. -/
theorem cpsBranch_cons_cpsNBranch_same_cr (entry : Word) (cr : CodeReq)
    (P : Assertion) (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f : Assertion)
    (exits : List (Word × Assertion))
    (hbr : cpsBranch entry cr P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranch exit_f cr Q_f exits) :
    cpsNBranch entry cr P ((exit_t, Q_t) :: exits) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, s1, hstep1, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h_rest R hR s1 hcr' hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           ex, List.Mem.tail _ hmem, hpc2, hER⟩

/-- Compose a cpsBranch with a cpsNBranch, with permutation on the not-taken path, same CodeReq. -/
theorem cpsBranch_cons_cpsNBranch_with_perm_same_cr (entry : Word) (cr : CodeReq)
    (P : Assertion) (exit_t : Word) (Q_t : Assertion)
    (exit_f : Word) (Q_f Q_f' : Assertion)
    (exits : List (Word × Assertion))
    (hperm : ∀ h, Q_f h → Q_f' h)
    (hbr : cpsBranch entry cr P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranch exit_f cr Q_f' exits) :
    cpsNBranch entry cr P ((exit_t, Q_t) :: exits) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, s1, hstep1, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · have hQ_f' : (Q_f' ** R).holdsFor s1 := by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_f
      exact ⟨hp, hcompat, sepConj_mono_left hperm hp hpq⟩
    have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h_rest R hR s1 hcr' hQ_f' hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           ex, List.Mem.tail _ hmem, hpc2, hER⟩

end EvmAsm.Rv64
