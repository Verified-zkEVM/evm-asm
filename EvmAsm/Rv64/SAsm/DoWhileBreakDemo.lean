/-
  EvmAsm.Rv64.SAsm.DoWhileBreakDemo

  Minimal regression for `Stmt.doWhileBreak`: a single-exit bottom-entry loop
  whose only exit test is a mid-body branch past the synthesized back-edge.
-/

import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace DoWhileBreakDemo

open Stmt

/-- Invariant at the i-th entry to the increment-and-break body. -/
def countBreakInv (i : Nat) : Reach := fun rf _ _ =>
  rf.get .x5 = BitVec.ofNat 64 i ∧ rf.get .x10 = 3 ∧ i ≤ 2

/-- The loop exits only after the increment has reached 3. -/
def countBreakPost : Reach := fun rf _ _ =>
  rf.get .x5 = 3 ∧ rf.get .x10 = 3

/-- Count from 0 to 3 using the bottom-loop mid-exit shape:
    `ADDI; BEQ exit; JAL loop`. -/
def countBreakFn : Fn where
  name := "countBreak"
  pre := fun _ _ _ => True
  post := countBreakPost
  body :=
    .block "init" [.LI .x5 0, .LI .x10 3] ;;;
    .«doWhileBreak» "loop" 2 countBreakInv countBreakPost
      (.block "inc" [.ADDI .x5 .x5 1]) (.beq .x5 .x10)
      (.block "cont" [])

#guard countBreakFn.body.flatten 0 =
  [ .LI .x5 0,
    .LI .x10 3,
    .ADDI .x5 .x5 (1 : BitVec 12),
    .BEQ .x5 .x10 (8 : BitVec 13),
    .JAL .x0 (-8 : BitVec 21) ]

#guard countBreakFn.body.flatten 0 = countBreakFn.body.flatten 0x80000000

theorem countBreakFn_spec (base : Word) : countBreakFn.Spec base := by
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  vcgen
  case countBreak.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, _hpre, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [countBreakFn, execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case countBreak.loop.inv_step =>
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, _hnbreak⟩, hrf', hws'⟩ := hsp
    change wsa.length = 0 at hwsa
    obtain rfl := List.eq_nil_of_length_eq_zero hwsa
    obtain ⟨rfb, wsb, hwsb, ⟨hx5, hx10, hile⟩, hrfa, _hwsa⟩ := hspbb
    change wsb.length = 0 at hwsb
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    subst hrf'
    subst hws'
    refine ⟨?_, ?_, by omega⟩
    · rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0)]
      rw [hx5, hse1]
      bv_omega
    · rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]
      exact hx10
  case countBreak.loop.exhausted =>
    rintro rf' ws' A' hspbb
    obtain ⟨rfb, wsb, hwsb, ⟨hx5, hx10, _hile⟩, hrf', _hws'⟩ := hspbb
    change wsb.length = 0 at hwsb
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    simp only [Cond.holds]
    rw [hrf']
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
      RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]
    rw [hx5, hx10, hse1]
    rfl
  case countBreak.loop.break =>
    rintro i hi rf' ws' A' hspbb hbreak
    obtain ⟨rfb, wsb, hwsb, ⟨_hx5, hx10, _hile⟩, hrf', _hws'⟩ := hspbb
    change wsb.length = 0 at hwsb
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    simp only [Cond.holds] at hbreak
    have hx10' : rf'.get .x10 = 3 := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]
      exact hx10
    refine ⟨?_, hx10'⟩
    rw [hbreak]
    exact hx10'
  case countBreak.post =>
    intro rf ws A h
    exact h


end DoWhileBreakDemo
end SAsm
end EvmAsm.Rv64
