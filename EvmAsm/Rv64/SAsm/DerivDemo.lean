/-
  EvmAsm.Rv64.SAsm.DerivDemo

  Worked examples of the proof-first derivation layer (docs/sasm-deriv.md):
  the constructive separation-logic proof is written FIRST, as a calc-style
  chain from precondition to postcondition, and the RISC-V code is
  GENERATED from it (`DCode.program`), together with its bounded CPS
  triple (`DCode.fn_spec`).

  - `sum3`: a calc chain of two machine blocks.
  - `umax`: if/fi — execution splits on a `Cond`, the arms start from the
    precondition strengthened by the condition and rejoin at one post;
    the else-arm is a pure step (zero instructions).
  - `countdown`: a while loop — the body derivation is a family over the
    iteration index `i` (assertions mention `i`, code cannot), followed by
    a pure step massaging the loop exit into the stated post.
-/

import EvmAsm.Rv64.SAsm.Deriv

namespace EvmAsm.Rv64
namespace SAsm
namespace DerivDemo

/-- Demo derivations are register-only: no read-only region, no writable
    window. -/
local infix:36 " ⤳ " => DCode Region.empty RwRegion.empty

-- ============================================================================
-- 1. Straight-line calc chain: x10 := a + b + c
-- ============================================================================

/-- Proof-first `a + b + c`: two machine steps, each naming the states it
    starts from and reaches.  A clobbered register would fail at the very
    step that clobbers it — the next step's precondition would not match. -/
def sum3 (a b c : Word) :
    (fun rf _ _ => rf.get .x10 = a ∧ rf.get .x11 = b ∧ rf.get .x12 = c)
      ⤳ (fun rf _ _ => rf.get .x10 = a + b + c) :=
  calc (fun rf _ _ => rf.get .x10 = a ∧ rf.get .x11 = b ∧ rf.get .x12 = c : Reach)
    _ ⤳ (fun rf _ _ => rf.get .x10 = a + b ∧ rf.get .x12 = c : Reach) :=
      DCode.block "add_ab" [.ADD .x10 .x10 .x11] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨h10, h11, h12⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          simp [h10, h11, h12])
    _ ⤳ (fun rf _ _ => rf.get .x10 = a + b + c : Reach) :=
      DCode.block "add_c" [.ADD .x10 .x10 .x12] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨h10, h12⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          simp [h10, h12])

/-- The generated code. -/
def sum3Prog : Program := (sum3 0 0 0).program 0

example : sum3Prog = [.ADD .x10 .x10 .x11, .ADD .x10 .x10 .x12] := rfl

/-- The generated spec: an ordinary bounded CPS triple of the generated
    code, at any base — layout side conditions close by `rfl` (autoparams)
    even though `a b c` are symbolic. -/
theorem sum3_spec (a b c : Word) (base : Word) :
    ((sum3 a b c).fn "sum3").Spec base :=
  DCode.fn_spec "sum3" (sum3 a b c) base Region.empty_wf RwRegion.empty_wf

-- ============================================================================
-- 2. if/fi: x10 := max(a, b) (unsigned)
-- ============================================================================

/-- Proof-first unsigned max.  Execution splits on `bltu x10 x11`; both
    arms carry the same postcondition (modulo the branch condition, which
    each arm's precondition records).  The else-arm needs no instructions
    at all — it is a pure step. -/
def umax (a b : Word) :
    (fun rf _ _ => rf.get .x10 = a ∧ rf.get .x11 = b)
      ⤳ (fun rf _ _ => rf.get .x10 = if BitVec.ult a b then b else a) :=
  DCode.ite "umax" (.bltu .x10 .x11)
    (DCode.block "take_b" [.MV .x10 .x11] (by decide)
      (fun h => absurd h (by decide))
      (by
        rintro rf ws A _ ⟨⟨h10, h11⟩, hc⟩
        simp only [Cond.holds, h10, h11] at hc
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        simp [h11, hc]))
    (DCode.pure "keep_a"
      (by
        rintro rf ws A ⟨⟨h10, h11⟩, hc⟩
        simp only [Cond.holds, h10, h11] at hc
        simp [h10, hc]))

example : ((umax 0 0).program 0).length = 3 := rfl  -- branch + mv + join jump

theorem umax_spec (a b : Word) (base : Word) :
    ((umax a b).fn "umax").Spec base :=
  DCode.fn_spec "umax" (umax a b) base Region.empty_wf RwRegion.empty_wf

-- ============================================================================
-- 3. Loop: transfer a counter (x5 = 4 counts down, x6 counts up)
-- ============================================================================

/-- Loop invariant, indexed by the iteration count `i`: after `i`
    iterations the counter has moved `i` units from `x5` to `x6`. -/
def cdInv (i : Nat) : Reach :=
  fun rf _ _ => i ≤ 4 ∧ rf.get .x5 = BitVec.ofNat 64 (4 - i)
    ∧ rf.get .x6 = BitVec.ofNat 64 i

/-- Proof-first countdown loop.  The body is given per iteration `i` —
    its assertions mention `i`, its code cannot (the shared statement
    index would fail to unify) — followed by a pure step turning the
    loop-exit shape `(∃ i ≤ fuel, inv i) ∧ ¬guard` into the stated post. -/
def countdown :
    (fun rf _ _ => rf.get .x5 = 4 ∧ rf.get .x6 = 0)
      ⤳ (fun rf _ _ => rf.get .x5 = 0 ∧ rf.get .x6 = 4) :=
  calc (fun rf _ _ => rf.get .x5 = 4 ∧ rf.get .x6 = 0 : Reach)
    _ ⤳ (fun rf ws A => (∃ i, i ≤ 4 ∧ cdInv i rf ws A)
          ∧ ¬ (Cond.bne .x5 .x0).holds rf : Reach) :=
      DCode.dwhile "loop" (.bne .x5 .x0) 4 cdInv
        (fun rf ws A h =>
          ⟨by omega, by rw [h.1]; decide, by rw [h.2]; decide⟩)
        (fun i =>
          DCode.block "step" [.ADDI .x6 .x6 1, .ADDI .x5 .x5 (-1)]
            (by decide)
            (fun h => absurd h (by decide))
            (by
              rintro rf ws A _ ⟨hi, ⟨hle, h5, h6⟩, hc⟩
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
                cdInv]
              refine ⟨by omega, ?_, ?_⟩
              · rw [RegFile.get_set_self _ _ _ (by decide),
                  RegFile.get_set_ne _ _ _ _ (by decide), h5,
                  show signExtend12 (-1 : BitVec 12) = (-1 : Word) from
                    by decide]
                bv_omega
              · rw [RegFile.get_set_ne _ _ _ _ (by decide),
                  RegFile.get_set_self _ _ _ (by decide), h6,
                  show signExtend12 (1 : BitVec 12) = (1 : Word) from
                    by decide]
                bv_omega))
        (fun rf ws A h => by
          rcases h with ⟨-, h5, -⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not]
          rw [h5]
          decide)
    _ ⤳ (fun rf _ _ => rf.get .x5 = 0 ∧ rf.get .x6 = 4 : Reach) :=
      DCode.pure "exit"
        (by
          rintro rf ws A ⟨⟨i, hle, hle4, h5, h6⟩, hc⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hc
          have hi4 : i = 4 := by rw [h5] at hc; bv_omega
          subst hi4
          exact ⟨hc, by simp [h6]⟩)

/-- The generated code: guard-negation branch, two ADDIs, back-edge. -/
def countdownProg : Program := countdown.program 0

example : countdownProg.length = 4 := rfl

theorem countdown_spec (base : Word) :
    (countdown.fn "countdown").Spec base :=
  DCode.fn_spec "countdown" countdown base Region.empty_wf RwRegion.empty_wf

end DerivDemo
end SAsm
end EvmAsm.Rv64
