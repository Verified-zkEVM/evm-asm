/-
  EvmAsm.Rv64.SAsm.AssertionSpec

  Bridges between the SAsm state atoms and plain separation-logic
  assertions, plus consequence rules at the `Fn`/`FnHandle` level.

  - `regFileOn`/`regFileIs_eq_atoms`: the single `regFileIs` atom equals
    the separating conjunction of the 15 per-register atoms.  This is the
    keystone for packaging existing hand-verified `cpsTripleWithin`
    routines (stated over `↦ᵣ` chains) as SAsm callees, and for exporting
    SAsm specs in atom form.
  - `FnHandle.weaken` / `Fn.spec_conseq`: strengthen preconditions and
    weaken postconditions of packaged handles and function specs.  The
    frame rule needs no counterpart here: everything outside a handle's
    footprint is framed by `cpsTripleWithin` itself
    (`cpsTripleWithin_frameR` for hand proofs).
-/

import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- The register file as per-register atoms
-- ============================================================================

/-- The partial state owning exactly the registers in `rs`, valued by `rf`. -/
def _root_.EvmAsm.Rv64.PartialState.onRegs (rs : List Reg) (rf : RegFile) :
    PartialState where
  regs := fun r => if r ∈ rs then some (rf.get r) else none
  mem  := fun _ => none
  code := fun _ => none
  pc   := none

/-- Ownership of exactly the registers in `rs`, valued by `rf`. -/
def regFileOn (rs : List Reg) (rf : RegFile) : Assertion :=
  fun h => h = PartialState.onRegs rs rf

theorem regFileOn_nil (rf : RegFile) : regFileOn [] rf = empAssertion := by
  have hX : PartialState.onRegs [] rf = PartialState.empty := by
    unfold PartialState.onRegs PartialState.empty
    congr 1
  funext h
  show (h = PartialState.onRegs [] rf) = (h = PartialState.empty)
  rw [hX]

private theorem union_singleton_onRegs (r : Reg) (rs : List Reg) (rf : RegFile) :
    (PartialState.singletonReg r (rf.get r)).union (PartialState.onRegs rs rf)
      = PartialState.onRegs (r :: rs) rf := by
  unfold PartialState.union PartialState.onRegs PartialState.singletonReg
  congr 1
  funext r'
  by_cases hr : r' = r
  · subst hr
    simp
  · simp [hr]

/-- Peel one register off a duplicate-free register-set atom. -/
theorem regFileOn_cons (r : Reg) (rs : List Reg) (rf : RegFile)
    (hnd : r ∉ rs) :
    regFileOn (r :: rs) rf = ((r ↦ᵣ rf.get r) ** regFileOn rs rf) := by
  funext h
  apply propext
  constructor
  · intro hh
    refine ⟨PartialState.singletonReg r (rf.get r), PartialState.onRegs rs rf,
      ?_, ?_, rfl, rfl⟩
    · refine ⟨fun r' => ?_, fun a => Or.inl rfl, fun a => Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      by_cases hr : r' = r
      · subst hr
        right
        simp [PartialState.onRegs, hnd]
      · left
        simp [PartialState.singletonReg, hr]
    · rw [hh, union_singleton_onRegs]
  · rintro ⟨h1, h2, hd, hu, hh1, hh2⟩
    have hh1' : h1 = PartialState.singletonReg r (rf.get r) := hh1
    have hh2' : h2 = PartialState.onRegs rs rf := hh2
    show h = PartialState.onRegs (r :: rs) rf
    rw [← hu, hh1', hh2', union_singleton_onRegs]

theorem pcFree_regFileOn (rs : List Reg) (rf : RegFile) :
    (regFileOn rs rf).pcFree := by
  intro h hp
  rw [hp]
  rfl

/-- `regFileOn` is a set: any membership-equivalent register list names the
    same atom.  Use to bring the registers a routine touches to the front
    before peeling with `regFileOn_cons`. -/
theorem regFileOn_perm (rs₁ rs₂ : List Reg) (rf : RegFile)
    (h : ∀ r, r ∈ rs₁ ↔ r ∈ rs₂) :
    regFileOn rs₁ rf = regFileOn rs₂ rf := by
  have hX : PartialState.onRegs rs₁ rf = PartialState.onRegs rs₂ rf := by
    unfold PartialState.onRegs
    congr 1
    funext r
    by_cases hr : r ∈ rs₁
    · rw [if_pos hr, if_pos ((h r).mp hr)]
    · rw [if_neg hr, if_neg (fun hm => hr ((h r).mpr hm))]
  funext hp
  show (hp = _) = (hp = _)
  rw [hX]

/-- `regFileOn` only reads the listed registers: valuations agreeing there
    name the same atom.  Use to re-fold the untouched remainder after a
    hand-verified routine updates some registers. -/
theorem regFileOn_congr (rs : List Reg) (rf rf' : RegFile)
    (h : ∀ r ∈ rs, rf.get r = rf'.get r) :
    regFileOn rs rf = regFileOn rs rf' := by
  have hX : PartialState.onRegs rs rf = PartialState.onRegs rs rf' := by
    unfold PartialState.onRegs
    congr 1
    funext r
    by_cases hr : r ∈ rs
    · rw [if_pos hr, if_pos hr, h r hr]
    · rw [if_neg hr, if_neg hr]
  funext hp
  show (hp = _) = (hp = _)
  rw [hX]

/-- `regFileIs` is the register-set atom over the exposed registers. -/
theorem regFileIs_eq_regFileOn (rf : RegFile) :
    regFileIs rf = regFileOn exposedRegs rf := by
  have hX : PartialState.ofRegFile rf = PartialState.onRegs exposedRegs rf := by
    unfold PartialState.ofRegFile PartialState.onRegs
    congr 1
    funext r
    by_cases hr : Reg.isExposed r = true
    · rw [if_pos hr, if_pos ((Reg.isExposed_iff_mem r).mp hr)]
    · rw [if_neg hr, if_neg (fun hm => hr ((Reg.isExposed_iff_mem r).mpr hm))]
  funext h
  show (h = PartialState.ofRegFile rf) = (h = PartialState.onRegs exposedRegs rf)
  rw [hX]

/-- **The keystone bridge**: the register-file atom is the separating
    conjunction of the 15 per-register atoms (t0–t6, a0–a7).  Rewrite left
    to right to hand individual registers to a hand-verified routine's
    atom-form triple; right to left to rebuild the SAsm state from a
    routine's atom-form postcondition. -/
theorem regFileIs_eq_atoms (rf : RegFile) :
    regFileIs rf
      = ((.x5 ↦ᵣ rf.get .x5) ** ((.x6 ↦ᵣ rf.get .x6) ** ((.x7 ↦ᵣ rf.get .x7) **
        ((.x28 ↦ᵣ rf.get .x28) ** ((.x29 ↦ᵣ rf.get .x29) **
        ((.x30 ↦ᵣ rf.get .x30) ** ((.x31 ↦ᵣ rf.get .x31) **
        ((.x10 ↦ᵣ rf.get .x10) ** ((.x11 ↦ᵣ rf.get .x11) **
        ((.x12 ↦ᵣ rf.get .x12) ** ((.x13 ↦ᵣ rf.get .x13) **
        ((.x14 ↦ᵣ rf.get .x14) ** ((.x15 ↦ᵣ rf.get .x15) **
        ((.x16 ↦ᵣ rf.get .x16) ** (.x17 ↦ᵣ rf.get .x17))))))))))))))) := by
  rw [regFileIs_eq_regFileOn,
    show exposedRegs = [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
      .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] from rfl,
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide),
    regFileOn_cons _ _ _ (by decide), regFileOn_nil,
    sepConj_emp_right']

-- ============================================================================
-- Consequence rules
-- ============================================================================

/-- Consequence at the handle level: a packaged routine may be re-published
    with a stronger precondition and a weaker postcondition (e.g. to
    specialize ghost data at a particular call site). -/
def FnHandle.weaken (f : FnHandle) (pre' post' : Reach)
    (hpre : ∀ rf ws A, pre' rf ws A → f.pre rf ws A)
    (hpost : ∀ rf ws A, f.post rf ws A → post' rf ws A) : FnHandle where
  entry := f.entry
  code := f.code
  nSteps := f.nSteps
  region := f.region
  rw := f.rw
  pre := pre'
  post := post'
  sound := fun ret halign =>
    cpsTripleWithin_weaken
      (fun hp => sepConj_mono_right (asrtM_mono hpre) hp)
      (fun hp => sepConj_mono_right (asrtM_mono hpost) hp)
      (f.sound ret halign)

/-- Consequence at the function-spec level: a proved `Fn.Spec` transports to
    the same function with a stronger pre and weaker post. -/
theorem Fn.spec_conseq (f : Fn) (base : Word) {pre' post' : Reach}
    (hspec : f.Spec base)
    (hpre : ∀ rf ws A, pre' rf ws A → f.pre rf ws A)
    (hpost : ∀ rf ws A, f.post rf ws A → post' rf ws A) :
    ({ f with pre := pre', post := post' } : Fn).Spec base :=
  cpsTripleWithin_weaken (asrtM_mono hpre) (asrtM_mono hpost) hspec

end SAsm
end EvmAsm.Rv64
