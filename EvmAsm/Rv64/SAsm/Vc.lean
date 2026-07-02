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
