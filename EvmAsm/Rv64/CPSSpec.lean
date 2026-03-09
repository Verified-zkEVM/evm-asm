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
    and PC = entry, execution reaches a state where (Q ** R) holds and PC = exit.

    The universal quantification over R means P and Q only describe the
    resources the code actually reads/writes. -/
def cpsTriple (entry exit_ : Addr)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧ s'.pc = exit_ ∧ (Q ** R).holdsFor s'

/-- CPS spec for code with two exits (the branch pattern) with built-in frame:
    "For any pcFree frame R, if (P ** R) holds at entry, execution reaches
     EITHER exit_t with (Q_t ** R) OR exit_f with (Q_f ** R)." -/
def cpsBranch (entry : Addr) (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧
      ((s'.pc = exit_t ∧ (Q_t ** R).holdsFor s') ∨ (s'.pc = exit_f ∧ (Q_f ** R).holdsFor s'))

-- ============================================================================
-- Structural rules
-- ============================================================================

/-- Sequence: compose two CPS triples sharing a midpoint. -/
theorem cpsTriple_seq (l1 l2 l3 : Addr)
    (P Q R : Assertion)
    (h1 : cpsTriple l1 l2 P Q)
    (h2 : cpsTriple l2 l3 Q R) :
    cpsTriple l1 l3 P R := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hPF hpc
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := h2 F hF s1 hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen precondition and weaken postcondition.
    Note: implications are at the assertion (PartialState) level, not holdsFor level,
    because (P' ** R).holdsFor s → (P ** R).holdsFor s requires P' h → P h pointwise. -/
theorem cpsTriple_consequence (entry exit_ : Addr)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsTriple entry exit_ P Q) :
    cpsTriple entry exit_ P' Q' := by
  intro R hR s hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Rule of consequence for cpsBranch: strengthen pre, weaken both posts. -/
theorem cpsBranch_consequence (entry : Addr)
    (P P' : Assertion) (exit_t : Addr) (Q_t Q_t' : Assertion)
    (exit_f : Addr) (Q_f Q_f' : Assertion)
    (hpre : ∀ h, P' h → P h)
    (hpost_t : ∀ h, Q_t h → Q_t' h)
    (hpost_f : ∀ h, Q_f h → Q_f' h)
    (h : cpsBranch entry P exit_t Q_t exit_f Q_f) :
    cpsBranch entry P' exit_t Q_t' exit_f Q_f' := by
  intro R hR s hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hPR hpc
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
    (∀ v_old, cpsTriple ... (P ** (r ↦ᵣ v_old)) Q) → cpsTriple ... (P ** regOwn r) Q -/
theorem cpsTriple_of_forall_regIs_to_regOwn
    {entry exit_ r P Q}
    (h : ∀ v_old, cpsTriple entry exit_ (P ** (r ↦ᵣ v_old)) Q) :
    cpsTriple entry exit_ (P ** regOwn r) Q := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨v_old, hv4⟩⟩ := hPown1
  exact h v_old R hR s
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Lift a spec quantified over v_old to one with regOwn as entire precondition:
    (∀ v_old, cpsTriple ... (r ↦ᵣ v_old) Q) → cpsTriple ... (regOwn r) Q -/
theorem cpsTriple_of_forall_regIs_to_regOwn_single
    {entry exit_ r Q}
    (h : ∀ v_old, cpsTriple entry exit_ (r ↦ᵣ v_old) Q) :
    cpsTriple entry exit_ (regOwn r) Q := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hunion, ⟨v_old, hv⟩, hR2⟩ := hPR
  exact h v_old R hR s ⟨hp, hcompat, h1, h2, hd, hunion, hv, hR2⟩ hpc

/-- Lift a spec quantified over v_old to one with memOwn in tail position:
    (∀ v_old, cpsTriple ... (P ** (a ↦ₘ v_old)) Q) → cpsTriple ... (P ** memOwn a) Q -/
theorem cpsTriple_of_forall_memIs_to_memOwn
    {entry exit_ a P Q}
    (h : ∀ v_old, cpsTriple entry exit_ (P ** (a ↦ₘ v_old)) Q) :
    cpsTriple entry exit_ (P ** memOwn a) Q := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hunion12, hPown1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hunion34, hP3, ⟨v_old, hv4⟩⟩ := hPown1
  exact h v_old R hR s
    ⟨hp, hcompat, h1, h2, hd12, hunion12, ⟨h3, h4, hd34, hunion34, hP3, hv4⟩, hR2⟩ hpc

/-- Branch elimination: if both branch exits lead to the same
    continuation exit with R, merge back into a single cpsTriple. -/
theorem cpsBranch_merge (entry l_t l_f exit_ : Addr)
    (P Q_t Q_f R : Assertion)
    (hbr   : cpsBranch entry P l_t Q_t l_f Q_f)
    (h_t   : cpsTriple l_t exit_ Q_t R)
    (h_f   : cpsTriple l_f exit_ Q_f R) :
    cpsTriple entry exit_ P R := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr F hF s hPF hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hQ_t hpc_t
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hR⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hR⟩

/-- A cpsTriple with zero steps: if entry = exit and P implies Q, trivially holds. -/
theorem cpsTriple_refl (addr : Addr) (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsTriple addr addr P Q := by
  intro R hR s hPR hpc
  exact ⟨0, s, rfl, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

-- ============================================================================
-- N-exit CPS specifications
-- ============================================================================

/-- CPS spec for code with N exits with built-in frame rule:
    "For any pcFree frame R, if (P ** R) holds at entry, execution reaches
    some exit in the list, with (exit.2 ** R) holding."

    Generalizes `cpsBranch` from 2 exits to an arbitrary list. -/
def cpsNBranch (entry : Addr) (P : Assertion)
    (exits : List (Addr × Assertion)) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧
      ∃ exit ∈ exits, s'.pc = exit.1 ∧ (exit.2 ** R).holdsFor s'

-- ============================================================================
-- Edge cases
-- ============================================================================

/-- An N-branch with no exits is vacuously false (no reachable exit). -/
theorem cpsNBranch_nil_false (entry : Addr) (P : Assertion)
    (h : cpsNBranch entry P [])
    (s : MachineState) (hP : P.holdsFor s) (hpc : s.pc = entry) : False := by
  -- Use empAssertion as the frame
  have hPemp : (P ** empAssertion).holdsFor s := by
    obtain ⟨hp, hcompat, hph⟩ := hP
    exact ⟨hp, hcompat, hp, PartialState.empty, PartialState.Disjoint_empty_right hp,
           PartialState.union_empty_right hp, hph, rfl⟩
  obtain ⟨k, s', _, ex, hmem, _, _⟩ := h empAssertion pcFree_emp s hPemp hpc
  exact List.not_mem_nil hmem

/-- An N-branch with impossible precondition vacuously holds for any exits. -/
theorem cpsNBranch_nil_of_false (entry : Addr) :
    cpsNBranch entry (fun _ => False) [] := by
  intro R _ s ⟨_, _, h1, h2, _, _, hf, _⟩ _
  exact absurd hf id

/-- Reflexivity: zero steps, one exit at the same address. -/
theorem cpsNBranch_refl (addr : Addr)
    (P Q : Assertion)
    (h : ∀ hp, P hp → Q hp) :
    cpsNBranch addr P [(addr, Q)] := by
  intro R hR s hPR hpc
  exact ⟨0, s, rfl, (addr, Q), List.Mem.head _, hpc, by
    obtain ⟨hp, hcompat, hpq⟩ := hPR
    exact ⟨hp, hcompat, sepConj_mono_left h hp hpq⟩⟩

-- ============================================================================
-- Equivalences with existing types
-- ============================================================================

/-- A single-exit cpsTriple can be viewed as a cpsNBranch with one exit. -/
theorem cpsTriple_to_cpsNBranch (entry exit_ : Addr)
    (P Q : Assertion) (h : cpsTriple entry exit_ P Q) :
    cpsNBranch entry P [(exit_, Q)] := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, (exit_, Q), List.Mem.head _, hpc', hQR⟩

/-- A singleton cpsNBranch gives back a cpsTriple. -/
theorem cpsNBranch_to_cpsTriple (entry exit_ : Addr)
    (P Q : Assertion) (h : cpsNBranch entry P [(exit_, Q)]) :
    cpsTriple entry exit_ P Q := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hPR hpc
  cases hmem with
  | head => exact ⟨k, s', hstep, hpc', hQR⟩
  | tail _ h => exact absurd h List.not_mem_nil

/-- A 2-exit cpsBranch can be viewed as a cpsNBranch with two exits. -/
theorem cpsBranch_to_cpsNBranch (entry : Addr)
    (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (h : cpsBranch entry P exit_t Q_t exit_f Q_f) :
    cpsNBranch entry P [(exit_t, Q_t), (exit_f, Q_f)] := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, hbranch⟩ := h R hR s hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k, s', hstep, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · exact ⟨k, s', hstep, (exit_f, Q_f), List.Mem.tail _ (List.Mem.head _), hpc_f, hQ_f⟩

/-- A 2-element cpsNBranch gives back a cpsBranch. -/
theorem cpsNBranch_to_cpsBranch (entry : Addr)
    (P : Assertion)
    (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (h : cpsNBranch entry P [(exit_t, Q_t), (exit_f, Q_f)]) :
    cpsBranch entry P exit_t Q_t exit_f Q_f := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hPR hpc
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
theorem cpsNBranch_merge (entry exit_ : Addr)
    (P R : Assertion)
    (exits : List (Addr × Assertion))
    (hbr : cpsNBranch entry P exits)
    (hall : ∀ exit ∈ exits, cpsTriple exit.1 exit_ exit.2 R) :
    cpsTriple entry exit_ P R := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hPF hpc
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hall ex hmem F hF s1 hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hpc2, hRF⟩

/-- Consequence: strengthen the precondition of an N-branch. -/
theorem cpsNBranch_weaken_pre (entry : Addr)
    (P P' : Assertion)
    (exits : List (Addr × Assertion))
    (hpre : ∀ h, P' h → P h) (h : cpsNBranch entry P exits) :
    cpsNBranch entry P' exits := by
  intro R hR s hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  exact h R hR s hPR hpc

/-- Monotonicity: expand the exit list (weaken the exit constraint). -/
theorem cpsNBranch_weaken_exits (entry : Addr)
    (P : Assertion)
    (exits exits' : List (Addr × Assertion))
    (hsub : ∀ ex, ex ∈ exits → ex ∈ exits') (h : cpsNBranch entry P exits) :
    cpsNBranch entry P exits' := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, ex, hsub ex hmem, hpc', hQR⟩

/-- Extend the head exit by composing a cpsTriple after it. -/
theorem cpsNBranch_extend_head (entry l l' : Addr)
    (P Q R : Assertion)
    (others : List (Addr × Assertion))
    (hbr : cpsNBranch entry P ((l, Q) :: others))
    (hseq : cpsTriple l l' Q R) :
    cpsNBranch entry P ((l', R) :: others) := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, ex, hmem, hpc1, hQF⟩ := hbr F hF s hPF hpc
  cases hmem with
  | head =>
    -- ex = (l, Q), compose with hseq
    obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ := hseq F hF s1 hQF hpc1
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
    For any pcFree frame R, starting from any state where (P ** R) holds
    and PC = entry, execution reaches a halted state where (Q ** R) holds.
    Unlike `cpsTriple`, there is no exit address — execution simply terminates. -/
def cpsHaltTriple (entry : Addr)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree → ∀ s, (P ** R).holdsFor s → s.pc = entry →
    ∃ k s', stepN k s = some s' ∧ isHalted s' = true ∧ (Q ** R).holdsFor s'

/-- Promote a `cpsTriple` to a `cpsHaltTriple` when the exit address is halted.
    If execution reaches exit_ with Q, and every state satisfying (Q ** R) at exit_ is halted,
    then the program halts with Q. -/
theorem cpsTriple_to_cpsHaltTriple (entry exit_ : Addr)
    (P Q : Assertion)
    (h : cpsTriple entry exit_ P Q)
    (hhalt : ∀ (R : Assertion), R.pcFree → ∀ s, (Q ** R).holdsFor s → s.pc = exit_ →
      isHalted s = true) :
    cpsHaltTriple entry P Q := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, hhalt R hR s' hQR hpc', hQR⟩

/-- Consequence: strengthen precondition and weaken postcondition of a halt triple. -/
theorem cpsHaltTriple_consequence (entry : Addr)
    (P P' Q Q' : Assertion)
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cpsHaltTriple entry P Q) :
    cpsHaltTriple entry P' Q' := by
  intro R hR s hP'R hpc
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, hpq⟩ := hP'R
    exact ⟨hp, hcompat, sepConj_mono_left hpre hp hpq⟩
  obtain ⟨k, s', hstep, hhalt, hQR⟩ := h R hR s hPR hpc
  exact ⟨k, s', hstep, hhalt, by
    obtain ⟨hp, hcompat, hpq⟩ := hQR
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

/-- Sequence a `cpsTriple` followed by a `cpsHaltTriple`:
    if code reaches midpoint with Q, and from midpoint it halts with R, then
    the composition halts with R. -/
theorem cpsTriple_seq_halt (entry mid : Addr)
    (P Q R : Assertion)
    (h1 : cpsTriple entry mid P Q)
    (h2 : cpsHaltTriple mid Q R) :
    cpsHaltTriple entry P R := by
  intro F hF s hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hPF hpc
  obtain ⟨k2, s2, hstep2, hhalt, hRF⟩ := h2 F hF s1 hQF hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hhalt, hRF⟩

/-- Sequential composition with midpoint permutation:
    compose h1 : cpsTriple s m P Q1 with h2 : cpsTriple m e Q2 R
    when Q1 and Q2 are AC-permutations (proved by hperm).
    Both Q1 and Q2 are fully determined by h1/h2, so the permutation
    obligation has no metavar ambiguity. -/
theorem cpsTriple_seq_with_perm (s m e : Addr)
    (P Q1 Q2 R : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple s m P Q1)
    (h2 : cpsTriple m e Q2 R) :
    cpsTriple s e P R :=
  cpsTriple_seq s m e P Q2 R
    (cpsTriple_consequence s m P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

-- ============================================================================
-- Cascade composition (for dispatch chains like Phase C)
-- ============================================================================

/-- Sequential composition: cpsTriple followed by cpsNBranch.
    If code reaches mid with Q, and from mid it branches to one of exits,
    then code branches from entry to one of exits. -/
theorem cpsTriple_seq_cpsNBranch (entry mid : Addr)
    (P Q : Assertion) (exits : List (Addr × Assertion))
    (h1 : cpsTriple entry mid P Q)
    (h2 : cpsNBranch mid Q exits) :
    cpsNBranch entry P exits := by
  intro R hR s hPR hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hPR hpc
  obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h2 R hR s1 hQR hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, ex, hmem, hpc2, hER⟩

/-- Sequential composition with permutation: cpsTriple followed by cpsNBranch
    when the intermediate assertions are permutations. -/
theorem cpsTriple_seq_cpsNBranch_with_perm (entry mid : Addr)
    (P Q1 Q2 : Assertion) (exits : List (Addr × Assertion))
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid P Q1)
    (h2 : cpsNBranch mid Q2 exits) :
    cpsNBranch entry P exits :=
  cpsTriple_seq_cpsNBranch entry mid P Q2 exits
    (cpsTriple_consequence entry mid P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Sequential composition: cpsTriple followed by cpsBranch.
    If code reaches mid with Q, and from mid it branches, then the
    composition branches from entry. -/
theorem cpsTriple_seq_cpsBranch (entry mid : Addr)
    (P Q : Assertion) (exit_t : Addr) (Q_t : Assertion) (exit_f : Addr) (Q_f : Assertion)
    (h1 : cpsTriple entry mid P Q)
    (h2 : cpsBranch mid Q exit_t Q_t exit_f Q_f) :
    cpsBranch entry P exit_t Q_t exit_f Q_f := by
  intro R hR s hPR hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hPR hpc
  obtain ⟨k2, s2, hstep2, hbranch⟩ := h2 R hR s1 hQR hpc1
  exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2, hbranch⟩

/-- Sequential composition with permutation: cpsTriple followed by cpsBranch. -/
theorem cpsTriple_seq_cpsBranch_with_perm (entry mid : Addr)
    (P Q1 Q2 : Assertion) (exit_t : Addr) (Q_t : Assertion) (exit_f : Addr) (Q_f : Assertion)
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsTriple entry mid P Q1)
    (h2 : cpsBranch mid Q2 exit_t Q_t exit_f Q_f) :
    cpsBranch entry P exit_t Q_t exit_f Q_f :=
  cpsTriple_seq_cpsBranch entry mid P Q2 exit_t Q_t exit_f Q_f
    (cpsTriple_consequence entry mid P P Q1 Q2 (fun _ hp => hp) hperm h1) h2

/-- Compose a cpsBranch with a cpsNBranch on the not-taken (false) path.
    The taken path becomes a new exit prepended to the cpsNBranch exits. -/
theorem cpsBranch_cons_cpsNBranch (entry : Addr)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (exits : List (Addr × Assertion))
    (hbr : cpsBranch entry P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranch exit_f Q_f exits) :
    cpsNBranch entry P ((exit_t, Q_t) :: exits) := by
  intro R hR s hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr R hR s hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, s1, hstep1, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h_rest R hR s1 hQ_f hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           ex, List.Mem.tail _ hmem, hpc2, hER⟩

/-- Compose a cpsBranch with a cpsNBranch, with permutation on the not-taken path. -/
theorem cpsBranch_cons_cpsNBranch_with_perm (entry : Addr)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f Q_f' : Assertion)
    (exits : List (Addr × Assertion))
    (hperm : ∀ h, Q_f h → Q_f' h)
    (hbr : cpsBranch entry P exit_t Q_t exit_f Q_f)
    (h_rest : cpsNBranch exit_f Q_f' exits) :
    cpsNBranch entry P ((exit_t, Q_t) :: exits) := by
  intro R hR s hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch⟩ := hbr R hR s hPR hpc
  rcases hbranch with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · exact ⟨k1, s1, hstep1, (exit_t, Q_t), List.Mem.head _, hpc_t, hQ_t⟩
  · have hQ_f' : (Q_f' ** R).holdsFor s1 := by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_f
      exact ⟨hp, hcompat, sepConj_mono_left hperm hp hpq⟩
    obtain ⟨k2, s2, hstep2, ex, hmem, hpc2, hER⟩ := h_rest R hR s1 hQ_f' hpc_f
    exact ⟨k1 + k2, s2, stepN_add_eq k1 k2 s s1 s2 hstep1 hstep2,
           ex, List.Mem.tail _ hmem, hpc2, hER⟩

/-- Compose two sequential cpsBranch specs where the first's not-taken path leads
    to the second's entry, and both taken paths go to the same target.
    The two taken postconditions are merged into a common one via weakening functions. -/
theorem cpsBranch_seq_cpsBranch (entry mid target exit_f : Addr)
    (P Q_t1 Q_f1 Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry P target Q_t1 mid Q_f1)
    (h2 : cpsBranch mid Q_f1 target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry P target Q_t exit_f Q_f2 := by
  intro R hR s hPR hpc
  obtain ⟨k1, s1, hstep1, hbranch1⟩ := h1 R hR s hPR hpc
  rcases hbranch1 with ⟨hpc_t1, hQ_t1R⟩ | ⟨hpc_f1, hQ_f1R⟩
  · -- First branch taken → target
    exact ⟨k1, s1, hstep1, Or.inl ⟨hpc_t1, by
      obtain ⟨hp, hcompat, hpq⟩ := hQ_t1R
      exact ⟨hp, hcompat, sepConj_mono_left ht1 hp hpq⟩⟩⟩
  · -- First branch not taken → mid, execute second
    obtain ⟨k2, s2, hstep2, hbranch2⟩ := h2 R hR s1 hQ_f1R hpc_f1
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
    (entry mid target exit_f : Addr)
    (P Q_t1 Q_f1 R Q_t2 Q_f2 Q_t : Assertion)
    (h1 : cpsBranch entry P target Q_t1 mid Q_f1)
    (hperm : ∀ h, Q_f1 h → R h)
    (h2 : cpsBranch mid R target Q_t2 exit_f Q_f2)
    (ht1 : ∀ h, Q_t1 h → Q_t h)
    (ht2 : ∀ h, Q_t2 h → Q_t h) :
    cpsBranch entry P target Q_t exit_f Q_f2 :=
  cpsBranch_seq_cpsBranch entry mid target exit_f P Q_t1 R Q_t2 Q_f2 Q_t
    (cpsBranch_consequence entry _ _ _ _ _ _ _ _
      (fun _ hp => hp) (fun _ hp => hp) hperm h1)
    h2 ht1 ht2

/-- Weaken postconditions of all exits in a cpsNBranch. -/
theorem cpsNBranch_weaken_posts (entry : Addr)
    (P : Assertion) (exits exits' : List (Addr × Assertion))
    (h : cpsNBranch entry P exits)
    (hmap : ∀ ex ∈ exits, ∃ ex' ∈ exits', ex'.1 = ex.1 ∧ ∀ h, ex.2 h → ex'.2 h) :
    cpsNBranch entry P exits' := by
  intro R hR s hPR hpc
  obtain ⟨k, s', hstep, ex, hmem, hpc', hER⟩ := h R hR s hPR hpc
  obtain ⟨ex', hmem', heq, hpost⟩ := hmap ex hmem
  rw [← heq] at hpc'
  exact ⟨k, s', hstep, ex', hmem', hpc', by
    obtain ⟨hp, hcompat, hpq⟩ := hER
    exact ⟨hp, hcompat, sepConj_mono_left hpost hp hpq⟩⟩

-- ============================================================================
-- Frame rules
-- ============================================================================

/-- Frame on the right: if cpsTriple P → Q, then cpsTriple (P ** F) → (Q ** F). -/
theorem cpsTriple_frame_left (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ P Q) :
    cpsTriple entry exit_ (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR' hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hpost⟩

/-- Frame on the left: if cpsTriple P → Q, then cpsTriple (F ** P) → (F ** Q). -/
theorem cpsTriple_frame_right (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ P Q) :
    cpsTriple entry exit_ (F ** P) (F ** Q) := by
  intro R hR s hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hpost⟩

/-- Frame for cpsBranch: if cpsBranch P → Q_t | Q_f, then cpsBranch (P ** F) → (Q_t ** F) | (Q_f ** F). -/
theorem cpsBranch_frame_left (entry : Addr)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch entry P exit_t Q_t exit_f Q_f) :
    cpsBranch entry (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) := by
  intro R hR s hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hcase⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR' hpc
  exact ⟨k, s', hstep, hcase.elim
    (fun ⟨hpc', hpost⟩ => Or.inl ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)
    (fun ⟨hpc', hpost⟩ => Or.inr ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)⟩

/-- Frame on the right for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_left (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry P Q) :
    cpsHaltTriple entry (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hhalt, hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR' hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_assoc.mpr hpost⟩

-- ============================================================================
-- Loop rules
-- ============================================================================

/-- Loop rule: prove a loop correct by induction on a decreasing variant.
    h_base: when variant = 0, the code must exit (no more iterations).
    h_step: when variant = n+1, one iteration either exits with Q
            or returns to entry with inv n (variant decreased by 1). -/
theorem cpsTriple_loop
    (entry exit_ : Addr)
    (inv : Nat → Assertion)
    (Q : Assertion)
    (h_base : cpsTriple entry exit_ (inv 0) Q)
    (h_step : ∀ n, cpsBranch entry (inv (n + 1))
                              exit_ Q
                              entry (inv n))
    : ∀ n, cpsTriple entry exit_ (inv n) Q := by
  intro n
  induction n with
  | zero => exact h_base
  | succ k ih =>
    exact cpsBranch_merge entry exit_ entry exit_
      (inv (k + 1)) Q (inv k) Q
      (h_step k) (cpsTriple_refl exit_ Q Q (fun _ h => h)) ih

/-- Loop rule with permutation on back-edge and exit postconditions. -/
theorem cpsTriple_loop_with_perm
    (entry exit_ : Addr)
    (inv : Nat → Assertion)
    (Q : Assertion)
    (inv' : Nat → Assertion)
    (Q' : Assertion)
    (h_base : cpsTriple entry exit_ (inv 0) Q)
    (h_step : ∀ n, cpsBranch entry (inv (n + 1))
                              exit_ Q'
                              entry (inv' n))
    (hperm_inv : ∀ n h, inv' n h → inv n h)
    (hperm_Q : ∀ h, Q' h → Q h)
    : ∀ n, cpsTriple entry exit_ (inv n) Q := by
  have h_step' : ∀ n, cpsBranch entry (inv (n + 1)) exit_ Q entry (inv n) :=
    fun n => cpsBranch_consequence entry
      (inv (n + 1)) (inv (n + 1)) exit_ Q' Q entry (inv' n) (inv n)
      (fun _ h => h) hperm_Q (hperm_inv n) (h_step n)
  exact cpsTriple_loop entry exit_ inv Q h_base h_step'

end EvmAsm.Rv64
