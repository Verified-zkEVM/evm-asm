/-
  EvmAsm.Rv64.SAsm.ExamplesVc

  End-to-end demos of the SAsm verification pipeline: define an `Fn`,
  state its `Spec`, run `vcgen`, and discharge the remaining named pure
  goals.  These double as regression tests for the tactic.
-/

import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace ExamplesVc

open Stmt

/-- `min(a0, a1)` into a0: if a0 ≥u a1 then a0 := a1. -/
def clampFn (x y : Word) : Fn where
  name := "clamp"
  pre := fun rf => rf.get .x10 = x ∧ rf.get .x11 = y
  post := fun rf =>
    rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
  body := .when "cap" (.bgeu .x10 .x11) (.block "set" [.MV .x10 .x11])

theorem clampFn_spec (x y base : Word) : (clampFn x y).Spec base := by
  vcgen
  case clamp.post =>
    intro rf h
    show rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
    rcases h with ⟨rf₀, ⟨⟨hx, hy⟩, hge⟩, rfl⟩ | ⟨⟨hx, hy⟩, hlt⟩
    · -- took the branch: ¬ x <u y, a0 := a1
      simp only [Cond.holds] at hge
      rw [hx, hy] at hge
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      constructor
      · rw [RegFile.get_set_self _ _ _ (by decide), hy,
          if_neg (by simpa using hge)]
      · rw [RegFile.get_set_ne _ _ _ _ (by decide), hy]
    · -- fell through: x <u y, registers unchanged
      simp only [Cond.holds] at hlt
      rw [hx, hy] at hlt
      rw [if_pos (Decidable.of_not_not hlt)]
      exact ⟨hx, hy⟩

/-- Count up from 0 to 10 in t0: init; while (t0 <u t1) t0 += 1. -/
def countFn : Fn where
  name := "count"
  pre := fun _ => True
  post := fun rf => rf.get .x5 = 10
  body :=
    .block "init" [.LI .x5 0, .LI .x6 10] ;;;
    .«while» "loop" (.bltu .x5 .x6) 10
      (fun i rf => rf.get .x5 = BitVec.ofNat 64 i ∧ rf.get .x6 = 10 ∧ i ≤ 10)
      (.block "step" [.ADDI .x5 .x5 1])

theorem countFn_spec (base : Word) : countFn.Spec base := by
  vcgen
  case count.loop.inv_init =>
    rintro rf ⟨rf₀, -, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case count.loop.inv_step =>
    rintro i hi rf' ⟨rf₀, ⟨⟨hx5, hx6, hle⟩, hlt⟩, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6
  case count.loop.exhausted =>
    rintro rf ⟨hx5, hx6, -⟩
    simp only [Cond.holds]
    rw [hx5, hx6]
    decide
  case count.post =>
    intro rf h
    show rf.get .x5 = 10
    obtain ⟨⟨i, hle, hx5, hx6, -⟩, hnc⟩ := h
    simp only [Cond.holds] at hnc
    rw [hx5, hx6] at hnc
    rw [hx5]
    have : i = 10 := by
      simp only [BitVec.ult, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
        decide_eq_true_eq] at hnc
      omega
    subst this
    decide

end ExamplesVc
end SAsm
end EvmAsm.Rv64
