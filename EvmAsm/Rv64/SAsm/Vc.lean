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
  | block _ is, reach => fun rf' ws' => ∃ rf ws, ws.length = rw.len
      ∧ reach rf ws
      ∧ rf' = (execBlock reg rw.base rf ws is).1
      ∧ ws' = (execBlock reg rw.base rf ws is).2
  | seq a b, reach => sp reg rw b (sp reg rw a reach)
  | ite _ c t e, reach => fun rf' ws' =>
      sp reg rw t (fun rf ws => reach rf ws ∧ c.holds rf) rf' ws' ∨
      sp reg rw e (fun rf ws => reach rf ws ∧ ¬ c.holds rf) rf' ws'
  | when _ c b, reach => fun rf' ws' =>
      sp reg rw b (fun rf ws => reach rf ws ∧ c.holds rf) rf' ws'
        ∨ (reach rf' ws' ∧ ¬ c.holds rf')
  | assert _ P, reach => fun rf ws => reach rf ws ∧ P rf ws
  | «while» _ c fuel inv _, _ =>
      fun rf ws => (∃ i, i ≤ fuel ∧ inv i rf ws) ∧ ¬ c.holds rf
  | call _ f, _ => fun rf ws => f.post rf ws

/-- Labeled verification conditions of a statement, given the reachable set
    at its entry.  `pfx` is the path prefix for labels. -/
def vcs (reg : Region) (rw : RwRegion) : Stmt → String → Reach → List VC
  | block lbl is, pfx, reach =>
      ⟨pfx ++ lbl ++ ".ok", blockOk is = true⟩ ::
      (if hasLoad is then
        [⟨pfx ++ lbl ++ ".mem", ∀ rf ws, ws.length = rw.len → reach rf ws →
            blockVCs reg rw.base rf ws is⟩]
      else [])
  | seq a b, pfx, reach =>
      vcs reg rw a pfx reach ++ vcs reg rw b pfx (sp reg rw a reach)
  | ite lbl c t e, pfx, reach =>
      vcs reg rw t (pfx ++ lbl ++ ".t.") (fun rf ws => reach rf ws ∧ c.holds rf) ++
      vcs reg rw e (pfx ++ lbl ++ ".e.") (fun rf ws => reach rf ws ∧ ¬ c.holds rf)
  | when lbl c b, pfx, reach =>
      vcs reg rw b (pfx ++ lbl ++ ".") (fun rf ws => reach rf ws ∧ c.holds rf)
  | assert lbl P, pfx, reach =>
      [⟨pfx ++ lbl, ∀ rf ws, reach rf ws → P rf ws⟩]
  | «while» lbl c fuel inv b, pfx, reach =>
      ⟨pfx ++ lbl ++ ".inv_init", ∀ rf ws, reach rf ws → inv 0 rf ws⟩ ::
      ⟨pfx ++ lbl ++ ".inv_step", ∀ i, i < fuel →
          ∀ rf' ws', sp reg rw b (fun rf ws => inv i rf ws ∧ c.holds rf) rf' ws' →
            inv (i + 1) rf' ws'⟩ ::
      ⟨pfx ++ lbl ++ ".exhausted", ∀ rf ws, inv fuel rf ws → ¬ c.holds rf⟩ ::
      vcs reg rw b (pfx ++ lbl ++ ".body.")
        (fun rf ws => ∃ i, i < fuel ∧ inv i rf ws ∧ c.holds rf)
  | call lbl f, pfx, reach =>
      [⟨pfx ++ lbl ++ ".pre", ∀ rf ws, reach rf ws → f.pre rf ws⟩]

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
theorem sp_mono (reg : Region) (rw : RwRegion) (s : Stmt) {r₁ r₂ : Reach}
    (h : ∀ rf ws, r₁ rf ws → r₂ rf ws) :
    ∀ rf ws, sp reg rw s r₁ rf ws → sp reg rw s r₂ rf ws := by
  induction s generalizing r₁ r₂ with
  | block lbl is =>
      rintro rf ws ⟨rf₀, ws₀, hlen, hr, hrf, hws⟩
      exact ⟨rf₀, ws₀, hlen, h rf₀ ws₀ hr, hrf, hws⟩
  | seq a b iha ihb =>
      exact fun rf ws => ihb (iha h) rf ws
  | ite lbl c t e iht ihe =>
      rintro rf ws (ht | he)
      · exact Or.inl (iht (fun rf ws hr => ⟨h rf ws hr.1, hr.2⟩) rf ws ht)
      · exact Or.inr (ihe (fun rf ws hr => ⟨h rf ws hr.1, hr.2⟩) rf ws he)
  | «when» lbl c b ihb =>
      rintro rf ws (hb | hskip)
      · exact Or.inl (ihb (fun rf ws hr => ⟨h rf ws hr.1, hr.2⟩) rf ws hb)
      · exact Or.inr ⟨h rf ws hskip.1, hskip.2⟩
  | assert lbl P =>
      exact fun rf ws hr => ⟨h rf ws hr.1, hr.2⟩
  | «while» lbl c fuel inv b ihb =>
      exact fun rf ws hr => hr
  | call lbl f =>
      exact fun rf ws hr => hr

/-- `vcs` is antitone in the reachable set: obligations proven for a larger
    reachable set cover any smaller one.  Used to specialize loop-body VCs
    (generated at the union over iterations) to a specific iteration. -/
theorem vcs_antitone (reg : Region) (rw : RwRegion) (s : Stmt) (pfx : String)
    {r₁ r₂ : Reach}
    (h : ∀ rf ws, r₁ rf ws → r₂ rf ws) (hvcs : VCs.Hold (vcs reg rw s pfx r₂)) :
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
                [⟨pfx ++ lbl ++ ".mem", ∀ rf ws, ws.length = rw.len → r₂ rf ws →
                    blockVCs reg rw.base rf ws is⟩]
            from by simp [vcs, hl]] at hvcs
          simp only [List.mem_singleton] at hvc
          subst hvc
          exact fun rf ws hlen hr => hvcs.tail.head rf ws hlen (h rf ws hr)
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
      · exact iht _ (fun rf ws hr => ⟨h rf ws hr.1, hr.2⟩) hvcs.left vc hvc
      · exact ihe _ (fun rf ws hr => ⟨h rf ws hr.1, hr.2⟩) hvcs.right vc hvc
  | «when» lbl c b ihb =>
      intro vc hvc
      exact ihb _ (fun rf ws hr => ⟨h rf ws hr.1, hr.2⟩) hvcs vc hvc
  | assert lbl P =>
      intro vc hvc
      simp only [vcs, List.mem_singleton] at hvc
      subst hvc
      exact fun rf ws hr => hvcs.head rf ws (h rf ws hr)
  | «while» lbl c fuel inv b ihb =>
      intro vc hvc
      simp only [vcs, List.mem_cons] at hvc
      rcases hvc with rfl | rfl | rfl | hvc
      · exact fun rf ws hr => hvcs.head rf ws (h rf ws hr)
      · exact hvcs.tail.head
      · exact hvcs.tail.tail.head
      · exact hvcs.tail.tail.tail vc hvc
  | call lbl f =>
      intro vc hvc
      simp only [vcs, List.mem_singleton] at hvc
      subst hvc
      exact fun rf ws hr => hvcs.head rf ws (h rf ws hr)

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
  | «while» _ _ _ _ b => b.CalleesIn reg rw cr
  | call _ f => (∀ a i, f.code a = some i → cr a = some i)
      ∧ f.region = reg ∧ f.rw = rw

end Stmt

end SAsm
end EvmAsm.Rv64
