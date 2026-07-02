/-
  EvmAsm.Rv64.SAsm.RegFileSep

  The separation-logic view of the exposed register file: `regFileIs rf` owns
  exactly the exposed registers, with values `rf`.  Defined as a single
  `PartialState` equality (like `regIs`) so that to the separation-logic
  layer the whole register file is one atom — block soundness needs no
  permutation reasoning over a 15-way `**` chain.

  Design: docs/sasm-design.md §3.1.
-/

import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.RegFile

namespace EvmAsm.Rv64
namespace SAsm

/-- Exposed registers are never x0. -/
theorem Reg.isExposed_ne_x0 {r : Reg} (h : Reg.isExposed r = true) : r ≠ .x0 := by
  cases r <;> simp_all [Reg.isExposed]

/-- The partial state owning exactly the exposed registers, valued by `rf`. -/
def _root_.EvmAsm.Rv64.PartialState.ofRegFile (rf : RegFile) : PartialState where
  regs := fun r => if Reg.isExposed r then some (rf.get r) else none
  mem  := fun _ => none
  code := fun _ => none
  pc   := none

/-- Ownership of the exposed register file with values `rf`. -/
def regFileIs (rf : RegFile) : Assertion :=
  fun h => h = PartialState.ofRegFile rf

theorem pcFree_regFileIs (rf : RegFile) : (regFileIs rf).pcFree := by
  intro h hp
  rw [hp]
  rfl

/-- A set of symbolic states — exposed register file plus the current
    contents of the function's writable region: the pure abstraction of the
    machine state between SAsm nodes. -/
def Reach := RegFile → List (BitVec 8) → Prop

/-- Extract exposed-register values from a framed `regFileIs`. -/
theorem holdsFor_regFileIs_getReg {rf : RegFile} {R : Assertion} {s : MachineState}
    (hPR : ((regFileIs rf) ** R).holdsFor s)
    {r : Reg} (hr : Reg.isExposed r = true) :
    s.getReg r = rf.get r := by
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hh1, _⟩ := hPR
  rw [regFileIs] at hh1; subst hh1
  rw [← hu] at hcompat
  have hc1 := ((PartialState.CompatibleWith_union hd).mp hcompat).1
  exact hc1.1 r (rf.get r) (by simp [PartialState.ofRegFile, hr])

/-- Register agreement on the sources a block leaf may read: exposed
    registers agree by ownership, x0 agrees because both sides read zero. -/
theorem holdsFor_regFileIs_agree {rf : RegFile} {R : Assertion} {s : MachineState}
    (hPR : ((regFileIs rf) ** R).holdsFor s)
    {r : Reg} (hr : (Reg.isExposed r || r == .x0) = true) :
    s.getReg r = rf.get r := by
  rcases Bool.or_eq_true_iff.mp hr with h | h
  · exact holdsFor_regFileIs_getReg hPR h
  · have : r = .x0 := by simpa using h
    subst this
    rfl

/-- Frame-preserving register-file update: writing an exposed register keeps
    the frame intact and moves `regFileIs` to the updated valuation.  The SAsm
    analogue of `holdsFor_sepConj_regIs_setReg`. -/
theorem holdsFor_sepConj_regFileIs_setReg {rf : RegFile} {R : Assertion}
    {s : MachineState} {rd : Reg} {v : Word}
    (hrd : Reg.isExposed rd = true)
    (hPR : ((regFileIs rf) ** R).holdsFor s) :
    ((regFileIs (rf.set rd v)) ** R).holdsFor (s.setReg rd v) := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [regFileIs] at hh1; subst hh1
  rw [← hunion] at hcompat
  -- The frame doesn't own rd.
  have hr2 : h2.regs rd = none := by
    rcases hdisj.1 rd with h | h
    · simp [PartialState.ofRegFile, hrd] at h
    · exact h
  -- Disjointness is preserved: the updated file owns the same register set.
  have hdisj' : (PartialState.ofRegFile (rf.set rd v)).Disjoint h2 := by
    refine ⟨fun r => ?_, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, hdisj.2.2.2.2⟩
    rcases hdisj.1 r with h | h
    · left
      simp only [PartialState.ofRegFile] at h ⊢
      split at h
      · exact absurd h (by simp)
      · simp [*]
    · exact Or.inr h
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- Updated file compatible with the updated machine state.
  have hc1' : (PartialState.ofRegFile (rf.set rd v)).CompatibleWith (s.setReg rd v) := by
    refine ⟨fun r w hw => ?_,
            fun a w ha => by simp [PartialState.ofRegFile] at ha,
            fun a i hi => by simp [PartialState.ofRegFile] at hi,
            fun w hw => by simp [PartialState.ofRegFile] at hw,
            fun w hw => by simp [PartialState.ofRegFile] at hw,
            fun w hw => by simp [PartialState.ofRegFile] at hw,
            fun w hw => by simp [PartialState.ofRegFile] at hw⟩
    simp only [PartialState.ofRegFile] at hw
    split at hw
    case isTrue hr =>
      have hw' : w = (rf.set rd v).get r := by simpa using hw.symm
      subst hw'
      by_cases hrrd : r = rd
      · subst hrrd
        rw [MachineState.getReg_setReg_eq (Reg.isExposed_ne_x0 hrd)]
        rw [RegFile.get_set_self _ _ _ (Reg.isExposed_ne_x0 hrd)]
      · rw [MachineState.getReg_setReg_ne s rd r v (fun h => hrrd h.symm)]
        rw [RegFile.get_set_ne _ _ _ _ hrrd]
        exact hc1.1 r (rf.get r) (by simp [PartialState.ofRegFile, hr])
    case isFalse => exact absurd hw (by simp)
  -- The frame stays compatible: it doesn't own rd.
  have hc2' : h2.CompatibleWith (s.setReg rd v) :=
    PartialState.CompatibleWith_setReg hc2 hr2
  refine ⟨(PartialState.ofRegFile (rf.set rd v)).union h2,
    (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
    PartialState.ofRegFile (rf.set rd v), h2, hdisj', rfl, rfl, hh2⟩

end SAsm
end EvmAsm.Rv64
