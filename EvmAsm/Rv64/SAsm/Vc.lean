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

/-- Strongest-postcondition transformer over the exposed register file.
    A `call` replaces the reachable set by the callee's postcondition (the
    callee owns the whole exposed file; ghost data relates them). -/
def sp : Stmt → Reach → Reach
  | block _ is, reach => fun rf' => ∃ rf, reach rf ∧ rf' = execBlock rf is
  | seq a b, reach => b.sp (a.sp reach)
  | ite _ c t e, reach => fun rf' =>
      t.sp (fun rf => reach rf ∧ c.holds rf) rf' ∨
      e.sp (fun rf => reach rf ∧ ¬ c.holds rf) rf'
  | when _ c b, reach => fun rf' =>
      b.sp (fun rf => reach rf ∧ c.holds rf) rf' ∨ (reach rf' ∧ ¬ c.holds rf')
  | assert _ P, reach => fun rf => reach rf ∧ P rf
  | «while» _ c fuel inv _, _ =>
      fun rf => (∃ i, i ≤ fuel ∧ inv i rf) ∧ ¬ c.holds rf
  | call _ f, _ => fun rf => f.post rf

/-- Labeled verification conditions of a statement, given the reachable set
    at its entry.  `pfx` is the path prefix for labels. -/
def vcs : Stmt → String → Reach → List VC
  | block lbl is, pfx, _ =>
      [⟨pfx ++ lbl ++ ".ok", blockOk is = true⟩]
  | seq a b, pfx, reach =>
      a.vcs pfx reach ++ b.vcs pfx (a.sp reach)
  | ite lbl c t e, pfx, reach =>
      t.vcs (pfx ++ lbl ++ ".t.") (fun rf => reach rf ∧ c.holds rf) ++
      e.vcs (pfx ++ lbl ++ ".e.") (fun rf => reach rf ∧ ¬ c.holds rf)
  | when lbl c b, pfx, reach =>
      b.vcs (pfx ++ lbl ++ ".") (fun rf => reach rf ∧ c.holds rf)
  | assert lbl P, pfx, reach =>
      [⟨pfx ++ lbl, ∀ rf, reach rf → P rf⟩]
  | «while» lbl c fuel inv b, pfx, reach =>
      ⟨pfx ++ lbl ++ ".inv_init", ∀ rf, reach rf → inv 0 rf⟩ ::
      ⟨pfx ++ lbl ++ ".inv_step", ∀ i, i < fuel →
          ∀ rf', b.sp (fun rf => inv i rf ∧ c.holds rf) rf' → inv (i + 1) rf'⟩ ::
      ⟨pfx ++ lbl ++ ".exhausted", ∀ rf, inv fuel rf → ¬ c.holds rf⟩ ::
      b.vcs (pfx ++ lbl ++ ".body.")
        (fun rf => ∃ i, i < fuel ∧ inv i rf ∧ c.holds rf)
  | call lbl f, pfx, reach =>
      [⟨pfx ++ lbl ++ ".pre", ∀ rf, reach rf → f.pre rf⟩]

/-- Exact step bound of a statement (docs/sasm-design.md §3.5; the loop bound
    is `WP.loopBound`). -/
def steps : Stmt → Nat
  | block _ is => is.length
  | seq a b => a.steps + b.steps
  | ite _ _ t e => 1 + max (t.steps + 1) e.steps
  | when _ _ b => 1 + b.steps
  | assert _ _ => 0
  | «while» _ _ fuel _ b => WP.loopBound 1 (b.steps + 1) 1 fuel
  | call _ f => 1 + f.nSteps

/-- `sp` is monotone in the reachable set. -/
theorem sp_mono (s : Stmt) {r₁ r₂ : Reach} (h : ∀ rf, r₁ rf → r₂ rf) :
    ∀ rf, s.sp r₁ rf → s.sp r₂ rf := by
  induction s generalizing r₁ r₂ with
  | block lbl is =>
      rintro rf ⟨rf₀, hr, hrf⟩
      exact ⟨rf₀, h rf₀ hr, hrf⟩
  | seq a b iha ihb =>
      exact fun rf => ihb (iha h) rf
  | ite lbl c t e iht ihe =>
      rintro rf (ht | he)
      · exact Or.inl (iht (fun rf hr => ⟨h rf hr.1, hr.2⟩) rf ht)
      · exact Or.inr (ihe (fun rf hr => ⟨h rf hr.1, hr.2⟩) rf he)
  | «when» lbl c b ihb =>
      rintro rf (hb | hskip)
      · exact Or.inl (ihb (fun rf hr => ⟨h rf hr.1, hr.2⟩) rf hb)
      · exact Or.inr ⟨h rf hskip.1, hskip.2⟩
  | assert lbl P =>
      exact fun rf hr => ⟨h rf hr.1, hr.2⟩
  | «while» lbl c fuel inv b ihb =>
      exact fun rf hr => hr
  | call lbl f =>
      exact fun rf hr => hr

/-- `vcs` is antitone in the reachable set: obligations proven for a larger
    reachable set cover any smaller one.  Used to specialize loop-body VCs
    (generated at the union over iterations) to a specific iteration. -/
theorem vcs_antitone (s : Stmt) (pfx : String) {r₁ r₂ : Reach}
    (h : ∀ rf, r₁ rf → r₂ rf) (hvcs : VCs.Hold (s.vcs pfx r₂)) :
    VCs.Hold (s.vcs pfx r₁) := by
  induction s generalizing r₁ r₂ pfx with
  | block lbl is =>
      exact fun vc hvc => hvcs vc (by simpa [vcs] using hvc)
  | seq a b iha ihb =>
      intro vc hvc
      simp only [vcs, List.mem_append] at hvc ⊢
      rcases hvc with hvc | hvc
      · exact iha pfx h hvcs.left vc hvc
      · exact ihb pfx (sp_mono a h) hvcs.right vc hvc
  | ite lbl c t e iht ihe =>
      intro vc hvc
      simp only [vcs, List.mem_append] at hvc
      rcases hvc with hvc | hvc
      · exact iht _ (fun rf hr => ⟨h rf hr.1, hr.2⟩) hvcs.left vc hvc
      · exact ihe _ (fun rf hr => ⟨h rf hr.1, hr.2⟩) hvcs.right vc hvc
  | «when» lbl c b ihb =>
      intro vc hvc
      exact ihb _ (fun rf hr => ⟨h rf hr.1, hr.2⟩) hvcs vc hvc
  | assert lbl P =>
      intro vc hvc
      simp only [vcs, List.mem_singleton] at hvc
      subst hvc
      exact fun rf hr => hvcs.head rf (h rf hr)
  | «while» lbl c fuel inv b ihb =>
      intro vc hvc
      simp only [vcs, List.mem_cons] at hvc
      rcases hvc with rfl | rfl | rfl | hvc
      · exact fun rf hr => hvcs.head rf (h rf hr)
      · exact hvcs.tail.head
      · exact hvcs.tail.tail.head
      · exact hvcs.tail.tail.tail vc hvc
  | call lbl f =>
      intro vc hvc
      simp only [vcs, List.mem_singleton] at hvc
      subst hvc
      exact fun rf hr => hvcs.head rf (h rf hr)

/-- The callee code of every call site is contained in `cr`.  Stated
    structurally (rather than as a union of `CodeReq`s) so sub-statement
    obligations project out without overlap side conditions. -/
def CalleesIn (s : Stmt) (cr : CodeReq) : Prop :=
  match s with
  | block _ _ => True
  | seq a b => a.CalleesIn cr ∧ b.CalleesIn cr
  | ite _ _ t e => t.CalleesIn cr ∧ e.CalleesIn cr
  | when _ _ b => b.CalleesIn cr
  | assert _ _ => True
  | «while» _ _ _ _ b => b.CalleesIn cr
  | call _ f => ∀ a i, f.code a = some i → cr a = some i

end Stmt

end SAsm
end EvmAsm.Rv64
