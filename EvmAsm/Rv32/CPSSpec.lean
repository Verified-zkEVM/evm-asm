/-
  EvmAsm.Rv32.CPSSpec

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

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.Execution

namespace EvmAsm

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
def cpsTriple (entry exit_ : Addr) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧ s'.pc = exit_ ∧ (Q ** R).holdsFor s'

/-- CPS spec for code with two exits (the branch pattern) with built-in frame:
    "For any pcFree frame R, if cr is satisfied and (P ** R) holds at entry,
     execution reaches EITHER exit_t with (Q_t ** R) OR exit_f with (Q_f ** R)." -/
def cpsBranch (entry : Addr) (cr : CodeReq) (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧
      ((s'.pc = exit_t ∧ (Q_t ** R).holdsFor s') ∨ (s'.pc = exit_f ∧ (Q_f ** R).holdsFor s'))

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- Sequence: compose two CPS triples sharing a midpoint. -/
theorem cpsTriple_seq (l1 l2 l3 : Addr) (cr : CodeReq)
    (P Q R : Assertion)
    (h1 : cpsTriple l1 l2 cr P Q)
    (h2 : cpsTriple l2 l3 cr Q R) :
    cpsTriple l1 l3 cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr hPF hpc
  have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := h2 F hF s1 hcr' hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen precondition and weaken postcondition.
    Note: implications are at the assertion (PartialState) level, not holdsFor level,
    because (P' ** R).holdsFor s → (P ** R).holdsFor s requires P' h → P h pointwise. -/
theorem cpsTriple_consequence (entry exit_ : Addr) (cr : CodeReq)
    (P P' Q Q' : Assertion)
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

/-- Rule of consequence for cpsBranch: strengthen pre, weaken both posts. -/
theorem cpsBranch_consequence (entry : Addr) (cr : CodeReq)
    (P P' : Assertion) (exit_t : Addr) (Q_t Q_t' : Assertion)
    (exit_f : Addr) (Q_f Q_f' : Assertion)
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
theorem cpsBranch_merge (entry l_t l_f exit_ : Addr) (cr : CodeReq)
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

/-- A cpsTriple with zero steps: if entry = exit and P implies Q, trivially holds. -/
theorem cpsTriple_refl (addr : Addr) (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsTriple addr addr CodeReq.empty P Q := by
  intro R hR s _hcr hPR hpc
  exact ⟨0, s, rfl, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

/-- Monotonicity: if cr' subsumes cr (cr' ⊇ cr), extend a cpsTriple to require more code. -/
theorem cpsTriple_extend_code {entry exit_ : Addr} {cr cr' : CodeReq} {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr' P Q := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono s hmono hcr') hPR hpc

-- ============================================================================
-- N-exit CPS specifications
-- ============================================================================

/-- CPS spec for code with N exits with built-in frame rule:
    "For any pcFree frame R, if cr is satisfied and (P ** R) holds at entry, execution reaches
    some exit in the list, with (exit.2 ** R) holding."

    Generalizes `cpsBranch` from 2 exits to an arbitrary list. -/
def cpsNBranch (entry : Addr) (cr : CodeReq) (P : Assertion)
    (exits : List (Addr × Assertion)) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧
      ∃ exit ∈ exits, s'.pc = exit.1 ∧ (exit.2 ** R).holdsFor s'

-- ============================================================================
-- Edge cases
-- ============================================================================

/-- An N-branch with no exits is vacuously false (no reachable exit). -/
theorem cpsNBranch_nil_false (entry : Addr) (cr : CodeReq) (P : Assertion)
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
theorem cpsNBranch_nil_of_false (entry : Addr) (cr : CodeReq) :
    cpsNBranch entry cr (fun _ => False) [] := by
  intro R _ s _ ⟨_, _, h1, h2, _, _, hf, _⟩ _
  exact absurd hf id

/-- Reflexivity: zero steps, one exit at the same address. -/
theorem cpsNBranch_refl (addr : Addr)
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
theorem cpsTriple_to_cpsNBranch (entry exit_ : Addr) (cr : CodeReq)
    (P Q : Assertion) (h : cpsTriple entry exit_ cr P Q) :
    cpsNBranch entry cr P [(exit_, Q)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, (exit_, Q), List.Mem.head _, hpc', hQR⟩

/-- A singleton cpsNBranch gives back a cpsTriple. -/
theorem cpsNBranch_to_cpsTriple (entry exit_ : Addr) (cr : CodeReq)
    (P Q : Assertion) (h : cpsNBranch entry cr P [(exit_, Q)]) :
    cpsTriple entry exit_ cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  cases hmem with
  | head => exact ⟨k, s', hstep, hpc', hQR⟩
  | tail _ h => exact absurd h List.not_mem_nil

/-- A 2-exit cpsBranch can be viewed as a cpsNBranch with two exits. -/
theorem cpsBranch_to_cpsNBranch (entry : Addr) (cr : CodeReq)
    (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsNBranch entry cr P [(exit_t, Q_t), (exit_f, Q_f)] := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k, s', hstep, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · exact ⟨k, s', hstep, (exit_f, Q_f), List.Mem.tail _ (List.Mem.head _), hpc_f, hQ_f⟩

/-- A 2-element cpsNBranch gives back a cpsBranch. -/
theorem cpsNBranch_to_cpsBranch (entry : Addr) (cr : CodeReq)
    (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
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
    compose into a single cpsTriple. This is the main structural rule. -/
theorem cpsNBranch_merge (entry exit_ : Addr) (cr : CodeReq)
    (P R : Assertion)
    (exits : List (Addr × Assertion))
    (hbr : cpsNBranch entry cr P exits)
    (hall : ∀ exit ∈ exits, cpsTriple exit.1 exit_ cr exit.2 R) :
    cpsTriple entry exit_ cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hcr hPF hpc
  have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hall ex hmem F hF s1 hcr' hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen the precondition of an N-branch. -/
theorem cpsNBranch_weaken_pre (entry : Addr) (cr : CodeReq)
    (P P' : Assertion)
    (exits : List (Addr × Assertion))
    (hpre : ∀ h, P' h → P h) (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr P' exits := by
  intro R hR s hcr hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  exact h R hR s hcr hPR hpc

/-- Monotonicity: expand the exit list (weaken the exit constraint). -/
theorem cpsNBranch_weaken_exits (entry : Addr) (cr : CodeReq)
    (P : Assertion)
    (exits exits' : List (Addr × Assertion))
    (hsub : ∀ ex, ex ∈ exits → ex ∈ exits') (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr P exits' := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, ex, hsub ex hmem, hpc', hQR⟩

/-- Extend the head exit by composing a cpsTriple after it. -/
theorem cpsNBranch_extend_head (entry l l' : Addr) (cr : CodeReq)
    (P Q R : Assertion)
    (others : List (Addr × Assertion))
    (hbr : cpsNBranch entry cr P ((l, Q) :: others))
    (hseq : cpsTriple l l' cr Q R) :
    cpsNBranch entry cr P ((l', R) :: others) := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hcr hPF hpc
  cases hmem with
  | head =>
    -- ex = (l, Q), compose with hseq
    have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hseq F hF s1 hcr' hQF hpc1
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
def cpsHaltTriple (entry : Addr) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, cr.SatisfiedBy s → (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧ isHalted s' = true ∧ (Q ** R).holdsFor s'

/-- Promote a `cpsTriple` to a `cpsHaltTriple` when the exit address is halted.
    If execution reaches exit_ with Q, and every state satisfying (Q ** R) at exit_ is halted,
    then the program halts with Q. -/
theorem cpsTriple_to_cpsHaltTriple (entry exit_ : Addr) (cr : CodeReq)
    (P Q : Assertion)
    (h : cpsTriple entry exit_ cr P Q)
    (hhalt : ∀ (R : Assertion), R.pcFree → ∀ s, (Q ** R).holdsFor s → s.pc = exit_ →
      isHalted s = true) :
    cpsHaltTriple entry cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
  exact ⟨k, s', hstep, hhalt R hR s' hQR hpc', hQR⟩

/-- Consequence: strengthen precondition and weaken postcondition of a halt triple. -/
theorem cpsHaltTriple_consequence (entry : Addr) (cr : CodeReq)
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
theorem cpsTriple_seq_halt (entry mid : Addr) (cr : CodeReq)
    (P Q R : Assertion)
    (h1 : cpsTriple entry mid cr P Q)
    (h2 : cpsHaltTriple mid cr Q R) :
    cpsHaltTriple entry cr P R := by
  intro F hF s hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hcr hPF hpc
  have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, hhalt, hRF⟩ := h2 F hF s1 hcr' hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hhalt, hRF⟩

/-- Sequential composition with midpoint permutation:
    compose h1 : cpsTriple s m cr P Q1 with h2 : cpsTriple m e cr Q2 R
    when Q1 and Q2 are AC-permutations (proved by hperm).
    Both Q1 and Q2 are fully determined by h1/h2, so the permutation
    obligation has no metavar ambiguity. -/
theorem cpsTriple_seq_with_perm (s m e : Addr) (cr : CodeReq)
    (P Q1 Q2 R : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple s m cr P Q1)
    (h2 : cpsTriple m e cr Q2 R) :
    cpsTriple s e cr P R :=
  cpsTriple_seq s m e cr P Q2 R
    (cpsTriple_consequence s m cr P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Sequential composition lifting two specs with different CodeReqs to a common cr.
    Used by the `seqFrame`/`runBlock` tactics when composing specs that have
    different CodeReq singletons. Both are extended to `cr` via monotonicity. -/
theorem cpsTriple_seq_ext (l1 l2 l3 : Addr) (cr cr1 cr2 : CodeReq)
    (hmono1 : ∀ a i, cr1 a = some i → cr a = some i)
    (hmono2 : ∀ a i, cr2 a = some i → cr a = some i)
    (P Q R : Assertion)
    (h1 : cpsTriple l1 l2 cr1 P Q)
    (h2 : cpsTriple l2 l3 cr2 Q R) :
    cpsTriple l1 l3 cr P R :=
  cpsTriple_seq l1 l2 l3 cr P Q R
    (cpsTriple_extend_code hmono1 h1) (cpsTriple_extend_code hmono2 h2)

/-- Like `cpsTriple_seq_ext` but with midpoint permutation. -/
theorem cpsTriple_seq_ext_with_perm (l1 l2 l3 : Addr) (cr cr1 cr2 : CodeReq)
    (hmono1 : ∀ a i, cr1 a = some i → cr a = some i)
    (hmono2 : ∀ a i, cr2 a = some i → cr a = some i)
    (P Q1 Q2 R : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple l1 l2 cr1 P Q1)
    (h2 : cpsTriple l2 l3 cr2 Q2 R) :
    cpsTriple l1 l3 cr P R :=
  cpsTriple_seq_with_perm l1 l2 l3 cr P Q1 Q2 R hperm
    (cpsTriple_extend_code hmono1 h1) (cpsTriple_extend_code hmono2 h2)

-- ============================================================================
-- Cascade composition (for dispatch chains like Phase C)
-- ============================================================================

/-- Sequential composition: cpsTriple followed by cpsNBranch.
    If code reaches mid with Q, and from mid it branches to one of exits,
    then code branches from entry to one of exits. -/
theorem cpsTriple_seq_cpsNBranch (entry mid : Addr) (cr : CodeReq)
    (P Q : Assertion) (exits : List (Addr × Assertion))
    (h1 : cpsTriple entry mid cr P Q)
    (h2 : cpsNBranch mid cr Q exits) :
    cpsNBranch entry cr P exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr hPR hpc
  have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h2 R hR s1 hcr' hQR hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, ex, hmem, hpc2, hER⟩

/-- Sequential composition with permutation: cpsTriple followed by cpsNBranch
    when the intermediate assertions are permutations. -/
theorem cpsTriple_seq_cpsNBranch_with_perm (entry mid : Addr) (cr : CodeReq)
    (P Q1 Q2 : Assertion) (exits : List (Addr × Assertion))
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid cr P Q1)
    (h2 : cpsNBranch mid cr Q2 exits) :
    cpsNBranch entry cr P exits :=
  cpsTriple_seq_cpsNBranch entry mid cr P Q2 exits
    (cpsTriple_consequence entry mid cr P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Sequential composition: cpsTriple followed by cpsBranch.
    If code reaches mid with Q, and from mid it branches, then the
    composition branches from entry. -/
theorem cpsTriple_seq_cpsBranch (entry mid : Addr) (cr : CodeReq)
    (P Q : Assertion) (exit_t : Addr) (Q_t : Assertion) (exit_f : Addr) (Q_f : Assertion)
    (h1 : cpsTriple entry mid cr P Q)
    (h2 : cpsBranch mid cr Q exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr hPR hpc
  have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
  obtain ⟨k2, s2, hstep2, hbranch⟩ := h2 R hR s1 hcr' hQR hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hbranch⟩

/-- Sequential composition with permutation: cpsTriple followed by cpsBranch. -/
theorem cpsTriple_seq_cpsBranch_with_perm (entry mid : Addr) (cr : CodeReq)
    (P Q1 Q2 : Assertion) (exit_t : Addr) (Q_t : Assertion) (exit_f : Addr) (Q_f : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid cr P Q1)
    (h2 : cpsBranch mid cr Q2 exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr P exit_t Q_t exit_f Q_f :=
  cpsTriple_seq_cpsBranch entry mid cr P Q2 exit_t Q_t exit_f Q_f
    (cpsTriple_consequence entry mid cr P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Compose a cpsBranch with a cpsNBranch on the not-taken (false) path.
    The taken path becomes a new exit prepended to the cpsNBranch exits. -/
theorem cpsBranch_cons_cpsNBranch (entry : Addr) (cr : CodeReq)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (exits : List (Addr × Assertion))
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

/-- Compose a cpsBranch with a cpsNBranch, with permutation on the not-taken path. -/
theorem cpsBranch_cons_cpsNBranch_with_perm (entry : Addr) (cr : CodeReq)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f Q_f' : Assertion)
    (exits : List (Addr × Assertion))
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

/-- Compose two sequential cpsBranch specs where the first's not-taken path leads
    to the second's entry, and both taken paths go to the same target.
    The two taken postconditions are merged into a common one via weakening functions. -/
theorem cpsBranch_seq_cpsBranch (entry mid target exit_f : Addr) (cr : CodeReq)
    (P Q_t1 Q_f1 Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr P target Q_t1 mid Q_f1)
    (h2 : cpsBranch mid cr Q_f1 target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry cr P target Q_t exit_f Q_f2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch1⟩ := h1 R hR s hcr hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · -- First branch taken → target
    exact ⟨k1, s1, hstep1, Or.inl ⟨hpc_t1, by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
      exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · -- First branch not taken → mid, execute second
    have hcr' := CodeReq.SatisfiedBy_preserved cr k1 s s1 hstep1 hcr
    obtain ⟨k2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hcr' hQ_f1R hpc_f1
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
    (entry mid target exit_f : Addr) (cr : CodeReq)
    (P Q_t1 Q_f1 R Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry cr P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsBranch mid cr R target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry cr P target Q_t exit_f Q_f2 :=
  cpsBranch_seq_cpsBranch entry mid target exit_f cr P Q_t1 R Q_t2 Q_f2 Q_t
    (cpsBranch_consequence entry cr
      _ _ _ _ _ _ _ _
      (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1 ht2

/-- Weaken postconditions of all exits in a cpsNBranch. -/
theorem cpsNBranch_weaken_posts (entry : Addr) (cr : CodeReq)
    (P : Assertion) (exits exits' : List (Addr × Assertion))
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
-- Loop rules
-- ============================================================================

/-- Loop rule: prove a loop correct by induction on a decreasing variant.
    h_base: when variant = 0, the code must exit (no more iterations).
    h_step: when variant = n+1, one iteration either exits with Q
            or returns to entry with inv n (variant decreased by 1). -/
theorem cpsTriple_loop
    (entry exit_ : Addr) (cr : CodeReq)
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
    (entry exit_ : Addr) (cr : CodeReq)
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
    (entry exit_ : Addr) (cr : CodeReq)
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
  exact cpsTriple_loop_simple entry exit_ cr inv Q h_base h_step'

end EvmAsm
