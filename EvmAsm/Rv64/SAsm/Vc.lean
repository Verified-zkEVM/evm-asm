/-
  EvmAsm.Rv64.SAsm.Vc

  The SAsm verification-condition generator: a strongest-postcondition-style
  pass over the structured AST that produces labeled *pure* propositions.

  - `Stmt.sp` is the reachable-set transformer over the exposed register file
    (`Reach := RegFile → Prop`).
  - `Stmt.vcs` collects the labeled proof obligations: block support checks,
    `assert` conditions, and loop invariant initialization / preservation /
    fuel-exhaustion.
  - `asrtOf` embeds a reachable set as a separation-logic assertion.

  Both are plain structurally-recursive functions: crunching a program into
  VCs is definitional unfolding, linear in the AST, with no tactic recursion
  (docs/sasm-design.md §3.5).
-/

import EvmAsm.Rv64.WP.Loop
import EvmAsm.Rv64.SAsm.Ast
import EvmAsm.Rv64.SAsm.Flatten
import EvmAsm.Rv64.SAsm.Sym
import EvmAsm.Rv64.SAsm.RegFileSep

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Labeled verification conditions
-- ============================================================================

/-- A labeled pure proof obligation.  The label encodes the path through the
    program (`vcgen` names goals with it). -/
structure VC where
  label : String
  prop : Prop

namespace VCs

/-- All conditions in the list hold. -/
def Hold (vcs : List VC) : Prop := ∀ vc ∈ vcs, vc.prop

theorem Hold.nil : Hold [] := fun _ h => nomatch h

theorem Hold.head {vc : VC} {rest : List VC} (h : Hold (vc :: rest)) : vc.prop :=
  h vc (List.mem_cons_self ..)

theorem Hold.tail {vc : VC} {rest : List VC} (h : Hold (vc :: rest)) : Hold rest :=
  fun v hv => h v (List.mem_cons_of_mem _ hv)

theorem Hold.left {v₁ v₂ : List VC} (h : Hold (v₁ ++ v₂)) : Hold v₁ :=
  fun v hv => h v (List.mem_append_left _ hv)

theorem Hold.right {v₁ v₂ : List VC} (h : Hold (v₁ ++ v₂)) : Hold v₂ :=
  fun v hv => h v (List.mem_append_right _ hv)

/-- Introduction form used by `vcgen` to split the VC list into goals. -/
theorem Hold.cons_intro {vc : VC} {rest : List VC}
    (h1 : vc.prop) (h2 : Hold rest) : Hold (vc :: rest) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h1
  · exact h2 v hv

/-- Introduction form used by `vcgen` to split the VC list into goals. -/
theorem Hold.append_intro {v₁ v₂ : List VC}
    (h1 : Hold v₁) (h2 : Hold v₂) : Hold (v₁ ++ v₂) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact h1 v hv
  · exact h2 v hv

end VCs

-- ============================================================================
-- The reachable-set transformer
-- ============================================================================

namespace Stmt

/-- Strongest-postcondition transformer over the symbolic state (exposed
    register file + writable-region contents), reading loads from the
    read-only region `reg` and routing writable-region accesses by address.
    A `call` replaces the reachable set by the callee's postcondition (the
    callee owns the whole exposed file and the regions; ghost data relates
    them). -/
def sp (reg : Region) (rw : RwRegion) : Stmt → Reach → Reach
  | block _ is, reach => fun rf' ws' A' => ∃ rf ws, ws.length = rw.len
      ∧ reach rf ws A'
      ∧ rf' = (execBlock reg rw.base rf ws is).1
      ∧ ws' = (execBlock reg rw.base rf ws is).2
  | seq a b, reach => sp reg rw b (sp reg rw a reach)
  | ite _ c t e, reach => fun rf' ws' A' =>
      sp reg rw t (fun rf ws A => reach rf ws A ∧ c.holds rf) rf' ws' A' ∨
      sp reg rw e (fun rf ws A => reach rf ws A ∧ ¬ c.holds rf) rf' ws' A'
  | when _ c b, reach => fun rf' ws' A' =>
      sp reg rw b (fun rf ws A => reach rf ws A ∧ c.holds rf) rf' ws' A'
        ∨ (reach rf' ws' A' ∧ ¬ c.holds rf')
  | assert _ P, reach => fun rf ws A => reach rf ws A ∧ P rf ws A
  | ghost _ R, reach => fun rf ws A' => ∃ A, reach rf ws A
      ∧ (∃ hp, A hp) ∧ R rf ws A A'
  | blockAt _ p winR is, reach => fun rf' ws' A'' => ∃ rf A win rest,
      ws'.length = rw.len ∧ reach rf ws' A
      ∧ (∃ hp, (bytesRegion (rf.get p) win ** rest) hp)
      ∧ winR rf ws' A win rest
      ∧ rf' = (execBlock reg (rf.get p) rf win is).1
      ∧ A'' = (bytesRegion (rf.get p) (execBlock reg (rf.get p) rf win is).2
          ** rest)
  | «while» _ c fuel inv _, _ =>
      fun rf ws A => (∃ i, i ≤ fuel ∧ inv i rf ws A) ∧ ¬ c.holds rf
  | call _ f, _ => fun rf ws A => f.post rf ws A

/-- Labeled verification conditions of a statement, given the reachable set
    at its entry.  `pfx` is the path prefix for labels. -/
def vcs (reg : Region) (rw : RwRegion) : Stmt → String → Reach → List VC
  | block lbl is, pfx, reach =>
      ⟨pfx ++ lbl ++ ".ok", blockOk is = true⟩ ::
      (if hasLoad is then
        [⟨pfx ++ lbl ++ ".mem", ∀ rf ws A, ws.length = rw.len → reach rf ws A →
            blockVCs reg rw.base rf ws is⟩]
      else [])
  | seq a b, pfx, reach =>
      vcs reg rw a pfx reach ++ vcs reg rw b pfx (sp reg rw a reach)
  | ite lbl c t e, pfx, reach =>
      vcs reg rw t (pfx ++ lbl ++ ".t.") (fun rf ws A => reach rf ws A ∧ c.holds rf) ++
      vcs reg rw e (pfx ++ lbl ++ ".e.") (fun rf ws A => reach rf ws A ∧ ¬ c.holds rf)
  | when lbl c b, pfx, reach =>
      vcs reg rw b (pfx ++ lbl ++ ".") (fun rf ws A => reach rf ws A ∧ c.holds rf)
  | assert lbl P, pfx, reach =>
      [⟨pfx ++ lbl, ∀ rf ws A, reach rf ws A → P rf ws A⟩]
  | ghost lbl R, pfx, reach =>
      [⟨pfx ++ lbl, ∀ rf ws A, reach rf ws A → A.pcFree → (∃ hp, A hp) →
          ∃ A', R rf ws A A' ∧ (∀ hp, A hp → A' hp) ∧ A'.pcFree⟩]
  | blockAt lbl p winR is, pfx, reach =>
      ⟨pfx ++ lbl ++ ".ok", blockOk is = true⟩ ::
      ⟨pfx ++ lbl ++ ".focus", ∀ rf ws A, reach rf ws A → A.pcFree →
          ∀ hp, A hp →
          ∃ win rest, winR rf ws A win rest
            ∧ (bytesRegion (rf.get p) win ** rest) hp
            ∧ rest.pcFree ∧ RwRegion.wf ⟨rf.get p, win.length⟩⟩ ::
      (if hasLoad is then
        [⟨pfx ++ lbl ++ ".mem", ∀ rf ws A win rest, ws.length = rw.len →
            reach rf ws A → winR rf ws A win rest →
            (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
            blockVCs reg (rf.get p) rf win is⟩]
      else [])
  | «while» lbl c fuel inv b, pfx, reach =>
      ⟨pfx ++ lbl ++ ".inv_init", ∀ rf ws A, reach rf ws A → inv 0 rf ws A⟩ ::
      ⟨pfx ++ lbl ++ ".inv_step", ∀ i, i < fuel →
          ∀ rf' ws' A', sp reg rw b (fun rf ws A => inv i rf ws A ∧ c.holds rf) rf' ws' A' →
            inv (i + 1) rf' ws' A'⟩ ::
      ⟨pfx ++ lbl ++ ".exhausted", ∀ rf ws A, inv fuel rf ws A → ¬ c.holds rf⟩ ::
      vcs reg rw b (pfx ++ lbl ++ ".body.")
        (fun rf ws A => ∃ i, i < fuel ∧ inv i rf ws A ∧ c.holds rf)
  | call lbl f, pfx, reach =>
      [⟨pfx ++ lbl ++ ".pre", ∀ rf ws A, reach rf ws A → f.pre rf ws A⟩]

/-- Exact step bound of a statement (docs/sasm-design.md §3.5; the loop bound
    is `WP.loopBound`). -/
def steps : Stmt → Nat
  | block _ is => is.length
  | seq a b => a.steps + b.steps
  | ite _ _ t e => 1 + max (t.steps + 1) e.steps
  | when _ _ b => 1 + b.steps
  | assert _ _ => 0
  | ghost _ _ => 0
  | blockAt _ _ _ is => is.length
  | «while» _ _ fuel _ b => WP.loopBound 1 (b.steps + 1) 1 fuel
  | call _ f => 1 + f.nSteps

/-- `sp` is monotone in the reachable set. -/
theorem sp_mono (reg : Region) (rw : RwRegion) (s : Stmt) {r₁ r₂ : Reach}
    (h : ∀ rf ws A, r₁ rf ws A → r₂ rf ws A) :
    ∀ rf ws A, sp reg rw s r₁ rf ws A → sp reg rw s r₂ rf ws A := by
  induction s generalizing r₁ r₂ with
  | block lbl is =>
      rintro rf ws A ⟨rf₀, ws₀, hlen, hr, hrf, hws⟩
      exact ⟨rf₀, ws₀, hlen, h rf₀ ws₀ A hr, hrf, hws⟩
  | seq a b iha ihb =>
      exact fun rf ws A => ihb (iha h) rf ws A
  | ite lbl c t e iht ihe =>
      rintro rf ws A (ht | he)
      · exact Or.inl (iht (fun rf ws A hr => ⟨h rf ws A hr.1, hr.2⟩) rf ws A ht)
      · exact Or.inr (ihe (fun rf ws A hr => ⟨h rf ws A hr.1, hr.2⟩) rf ws A he)
  | «when» lbl c b ihb =>
      rintro rf ws A (hb | hskip)
      · exact Or.inl (ihb (fun rf ws A hr => ⟨h rf ws A hr.1, hr.2⟩) rf ws A hb)
      · exact Or.inr ⟨h rf ws A hskip.1, hskip.2⟩
  | assert lbl P =>
      exact fun rf ws A hr => ⟨h rf ws A hr.1, hr.2⟩
  | ghost lbl R =>
      rintro rf ws A' ⟨A, hr, hsat, hR⟩
      exact ⟨A, h rf ws A hr, hsat, hR⟩
  | blockAt lbl p winR is =>
      rintro rf' ws' A'' ⟨rf, A, win, rest, hlen, hr, hsat, hR, hrf, hA⟩
      exact ⟨rf, A, win, rest, hlen, h rf ws' A hr, hsat, hR, hrf, hA⟩
  | «while» lbl c fuel inv b ihb =>
      exact fun rf ws A hr => hr
  | call lbl f =>
      exact fun rf ws A hr => hr

-- ============================================================================
-- Structural `sp` eliminators (docs/sasm-howto.md, "Branchy straight-line
-- code"): prove `∀ rf ws A, sp s reach rf ws A → P rf ws A` by the shape
-- of `s`, without hand-destructuring the raw existentials/disjunctions.
-- ============================================================================

/-- `sp` through `;;;`, as a rewrite. -/
theorem sp_seq_eq (reg : Region) (rw : RwRegion) (a b : Stmt) (reach : Reach) :
    sp reg rw (.seq a b) reach = sp reg rw b (sp reg rw a reach) := rfl

/-- `sp` through `.assert`, as a rewrite. -/
theorem sp_assert_eq (reg : Region) (rw : RwRegion) (lbl : String)
    (P reach : Reach) :
    sp reg rw (.assert lbl P) reach
      = fun rf ws A => reach rf ws A ∧ P rf ws A := rfl

/-- **The cut**: downstream of an `.assert`, the pre-assert reachable set
    may be forgotten — any `sp` continuation from `sp (assert P) reach`
    is also an `sp` continuation from `P` alone.  Apply this first in a
    VC whose reach passes through an assert; the rest of the proof only
    ever sees the summary `P`. -/
theorem sp_cut (reg : Region) (rw : RwRegion) (s : Stmt) (lbl : String)
    {reach P : Reach} :
    ∀ rf ws A, sp reg rw s (sp reg rw (.assert lbl P) reach) rf ws A →
      sp reg rw s P rf ws A :=
  sp_mono reg rw s (fun _ _ _ h => h.2)

/-- Split an `.ite` elimination into its two branches. -/
theorem sp_ite_split (reg : Region) (rw : RwRegion) {lbl : String}
    {c : Cond} {t e : Stmt} {reach : Reach} {P : Reach}
    (ht : ∀ rf ws A,
      sp reg rw t (fun rf ws A => reach rf ws A ∧ c.holds rf) rf ws A →
      P rf ws A)
    (he : ∀ rf ws A,
      sp reg rw e (fun rf ws A => reach rf ws A ∧ ¬ c.holds rf) rf ws A →
      P rf ws A) :
    ∀ rf ws A, sp reg rw (.ite lbl c t e) reach rf ws A → P rf ws A := by
  rintro rf ws A (h | h)
  · exact ht rf ws A h
  · exact he rf ws A h

/-- Split a `.when` elimination into its body and skip paths. -/
theorem sp_when_split (reg : Region) (rw : RwRegion) {lbl : String}
    {c : Cond} {b : Stmt} {reach : Reach} {P : Reach}
    (hb : ∀ rf ws A,
      sp reg rw b (fun rf ws A => reach rf ws A ∧ c.holds rf) rf ws A →
      P rf ws A)
    (hskip : ∀ rf ws A, reach rf ws A → ¬ c.holds rf → P rf ws A) :
    ∀ rf ws A, sp reg rw (.when lbl c b) reach rf ws A → P rf ws A := by
  rintro rf ws A (h | ⟨hr, hn⟩)
  · exact hb rf ws A h
  · exact hskip rf ws A hr hn

/-- Eliminate a `.block`: prove `P` of the engine result at every
    reachable entry state. -/
theorem sp_block_split (reg : Region) (rw : RwRegion) {lbl : String}
    {is : List Instr} {reach : Reach} {P : Reach}
    (h : ∀ rf ws A, ws.length = rw.len → reach rf ws A →
      P (execBlock reg rw.base rf ws is).1
        (execBlock reg rw.base rf ws is).2 A) :
    ∀ rf ws A, sp reg rw (.block lbl is) reach rf ws A → P rf ws A := by
  rintro rf' ws' A ⟨rf, ws, hlen, hr, rfl, rfl⟩
  exact h rf ws A hlen hr

/-- Eliminate a `.blockAt`: prove `P` of the engine result over the
    focused window at every reachable entry state — the post-VC shape
    after a focus block, without hand-destructuring the six-tuple. -/
theorem sp_blockAt_split (reg : Region) (rw : RwRegion) {lbl : String}
    {p : Reg}
    {winR : RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop}
    {is : List Instr} {reach : Reach} {P : Reach}
    (h : ∀ rf ws A win rest, ws.length = rw.len → reach rf ws A →
      (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
      winR rf ws A win rest →
      P (execBlock reg (rf.get p) rf win is).1 ws
        ((bytesRegion (rf.get p) (execBlock reg (rf.get p) rf win is).2)
          ** rest)) :
    ∀ rf' ws' A'', sp reg rw (.blockAt lbl p winR is) reach rf' ws' A'' →
      P rf' ws' A'' := by
  rintro rf' ws' A'' ⟨rf, A, win, rest, hlen, hr, hsat, hwinR, rfl, rfl⟩
  exact h rf ws' A win rest hlen hr hsat hwinR

/-- Eliminate a `.ghost`. -/
theorem sp_ghost_split (reg : Region) (rw : RwRegion) {lbl : String}
    {R : RegFile → List (BitVec 8) → Assertion → Assertion → Prop}
    {reach : Reach} {P : Reach}
    (h : ∀ rf ws A A', reach rf ws A → (∃ hp, A hp) → R rf ws A A' →
      P rf ws A') :
    ∀ rf ws A', sp reg rw (.ghost lbl R) reach rf ws A' → P rf ws A' := by
  rintro rf ws A' ⟨A, hr, hsat, hR⟩
  exact h rf ws A A' hr hsat hR

/-- Every control path through the statement ends in `.assert P`
    (syntactically).  This is the *branch-tail summary* shape: instead of
    one `.assert` after an `ite` cascade (whose VC must destructure the
    whole disjunction), place the SAME assert at the tail of every
    branch — each assert VC then sees only its own linear path, and
    `sp_of_endsWith` hands the downstream the summary with no case
    analysis at all. -/
def EndsWith (P : Reach) : Stmt → Prop
  | .assert _ Q => Q = P
  | .seq _ b => b.EndsWith P
  | .ite _ _ t e => t.EndsWith P ∧ e.EndsWith P
  | _ => False

/-- The branch-tail summary: if every path ends in `.assert P`, the
    strongest postcondition entails `P` — for any entry reachable set. -/
theorem sp_of_endsWith (reg : Region) (rw : RwRegion) {P : Reach}
    {s : Stmt} (h : s.EndsWith P) :
    ∀ {reach : Reach} (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
      sp reg rw s reach rf ws A → P rf ws A := by
  induction s with
  | assert lbl Q =>
      intro reach rf ws A hsp
      exact h ▸ hsp.2
  | seq a b iha ihb =>
      intro reach rf ws A hsp
      exact ihb h rf ws A hsp
  | ite lbl c t e iht ihe =>
      rintro reach rf ws A (hsp | hsp)
      · exact iht h.1 rf ws A hsp
      · exact ihe h.2 rf ws A hsp
  | block lbl is => exact nomatch h
  | «when» lbl c b ih => exact nomatch h
  | blockAt lbl p winR is => exact nomatch h
  | ghost lbl R => exact nomatch h
  | «while» lbl c fuel inv b ih => exact nomatch h
  | call lbl f => exact nomatch h

/-- `vcs` is antitone in the reachable set: obligations proven for a larger
    reachable set cover any smaller one.  Used to specialize loop-body VCs
    (generated at the union over iterations) to a specific iteration. -/
theorem vcs_antitone (reg : Region) (rw : RwRegion) (s : Stmt) (pfx : String)
    {r₁ r₂ : Reach}
    (h : ∀ rf ws A, r₁ rf ws A → r₂ rf ws A) (hvcs : VCs.Hold (vcs reg rw s pfx r₂)) :
    VCs.Hold (vcs reg rw s pfx r₁) := by
  induction s generalizing r₁ r₂ pfx with
  | block lbl is =>
      intro vc hvc
      simp only [vcs, List.mem_cons] at hvc
      rcases hvc with rfl | hvc
      · exact hvcs.head
      · by_cases hl : hasLoad is
        · rw [if_pos hl] at hvc
          have hvcs2 := hvcs.tail
          rw [show vcs reg rw (.block lbl is) pfx r₂
              = ⟨pfx ++ lbl ++ ".ok", blockOk is = true⟩ ::
                [⟨pfx ++ lbl ++ ".mem", ∀ rf ws A, ws.length = rw.len → r₂ rf ws A →
                    blockVCs reg rw.base rf ws is⟩]
            from by simp [vcs, hl]] at hvcs
          simp only [List.mem_singleton] at hvc
          subst hvc
          exact fun rf ws A hlen hr => hvcs.tail.head rf ws A hlen (h rf ws A hr)
        · rw [if_neg hl] at hvc
          exact absurd hvc (List.not_mem_nil)
  | seq a b iha ihb =>
      intro vc hvc
      simp only [vcs, List.mem_append] at hvc ⊢
      rcases hvc with hvc | hvc
      · exact iha pfx h hvcs.left vc hvc
      · exact ihb pfx (sp_mono reg rw a h) hvcs.right vc hvc
  | ite lbl c t e iht ihe =>
      intro vc hvc
      simp only [vcs, List.mem_append] at hvc
      rcases hvc with hvc | hvc
      · exact iht _ (fun rf ws A hr => ⟨h rf ws A hr.1, hr.2⟩) hvcs.left vc hvc
      · exact ihe _ (fun rf ws A hr => ⟨h rf ws A hr.1, hr.2⟩) hvcs.right vc hvc
  | «when» lbl c b ihb =>
      intro vc hvc
      exact ihb _ (fun rf ws A hr => ⟨h rf ws A hr.1, hr.2⟩) hvcs vc hvc
  | assert lbl P =>
      intro vc hvc
      simp only [vcs, List.mem_singleton] at hvc
      subst hvc
      exact fun rf ws A hr => hvcs.head rf ws A (h rf ws A hr)
  | ghost lbl R =>
      intro vc hvc
      simp only [vcs, List.mem_singleton] at hvc
      subst hvc
      exact fun rf ws A hr hApc hsat => hvcs.head rf ws A (h rf ws A hr) hApc hsat
  | blockAt lbl p winR is =>
      intro vc hvc
      simp only [vcs, List.mem_cons] at hvc
      rcases hvc with rfl | rfl | hvc
      · exact hvcs.head
      · exact fun rf ws A hr => hvcs.tail.head rf ws A (h rf ws A hr)
      · by_cases hl : hasLoad is
        · rw [if_pos hl] at hvc
          rw [show vcs reg rw (.blockAt lbl p winR is) pfx r₂
              = ⟨pfx ++ lbl ++ ".ok", blockOk is = true⟩ ::
                ⟨pfx ++ lbl ++ ".focus", ∀ rf ws A, r₂ rf ws A → A.pcFree →
                    ∀ hp, A hp →
                    ∃ win rest, winR rf ws A win rest
                      ∧ (bytesRegion (rf.get p) win ** rest) hp
                      ∧ rest.pcFree ∧ RwRegion.wf ⟨rf.get p, win.length⟩⟩ ::
                [⟨pfx ++ lbl ++ ".mem", ∀ rf ws A win rest, ws.length = rw.len →
                    r₂ rf ws A → winR rf ws A win rest →
                    (∃ hp, (bytesRegion (rf.get p) win ** rest) hp) →
                    blockVCs reg (rf.get p) rf win is⟩]
            from by simp [vcs, hl]] at hvcs
          simp only [List.mem_singleton] at hvc
          subst hvc
          exact fun rf ws A win rest hlen hr hR hsat =>
            hvcs.tail.tail.head rf ws A win rest hlen (h rf ws A hr) hR hsat
        · rw [if_neg hl] at hvc
          exact absurd hvc (List.not_mem_nil)
  | «while» lbl c fuel inv b ihb =>
      intro vc hvc
      simp only [vcs, List.mem_cons] at hvc
      rcases hvc with rfl | rfl | rfl | hvc
      · exact fun rf ws A hr => hvcs.head rf ws A (h rf ws A hr)
      · exact hvcs.tail.head
      · exact hvcs.tail.tail.head
      · exact hvcs.tail.tail.tail vc hvc
  | call lbl f =>
      intro vc hvc
      simp only [vcs, List.mem_singleton] at hvc
      subst hvc
      exact fun rf ws A hr => hvcs.head rf ws A (h rf ws A hr)

/-- Per call site: the callee's code is contained in `cr` and the callee
    shares the caller's regions.  Stated structurally (rather than as a union
    of `CodeReq`s) so sub-statement obligations project out without overlap
    side conditions. -/
def CalleesIn (s : Stmt) (reg : Region) (rw : RwRegion) (cr : CodeReq) : Prop :=
  match s with
  | block _ _ => True
  | seq a b => a.CalleesIn reg rw cr ∧ b.CalleesIn reg rw cr
  | ite _ _ t e => t.CalleesIn reg rw cr ∧ e.CalleesIn reg rw cr
  | when _ _ b => b.CalleesIn reg rw cr
  | assert _ _ => True
  | ghost _ _ => True
  | blockAt _ _ _ _ => True
  | «while» _ _ _ _ b => b.CalleesIn reg rw cr
  | call _ f => (∀ a i, f.code a = some i → cr a = some i)
      ∧ f.region = reg ∧ f.rw = rw

end Stmt

end SAsm
end EvmAsm.Rv64
