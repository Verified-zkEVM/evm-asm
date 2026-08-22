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

-- ============================================================================
-- 4. Nested loops: 2 outer iterations × 3 inner increments (dwhileS)
-- ============================================================================

/-- Outer invariant: after `j` outer iterations, `x7` has counted down `j`
    and `x6` has accumulated `3·j`. -/
def outerInv (j : Nat) : Reach :=
  fun rf _ _ => j ≤ 2 ∧ rf.get .x7 = BitVec.ofNat 64 (2 - j)
    ∧ rf.get .x6 = BitVec.ofNat 64 (3 * j)

/-- Inner invariant, parameterized by the **entry snapshot** `rf₀`.  It
    must not mention the outer index `j` (it is an annotation inside the
    shared code skeleton) — the outer accumulator and counter survive as
    `rf₀.get .x6` / `rf₀.get .x7`. -/
def innerInv (rf₀ : RegFile) (_ : List (BitVec 8)) (_ : Assertion)
    (i : Nat) : Reach :=
  fun rf _ _ => i ≤ 3 ∧ rf.get .x5 = BitVec.ofNat 64 (3 - i)
    ∧ rf.get .x6 = rf₀.get .x6 + BitVec.ofNat 64 i
    ∧ rf.get .x7 = rf₀.get .x7

/-- Inner-loop entry states, at outer iteration `j` (after `li x5, 3`). -/
def innerPre (j : Nat) : Reach :=
  fun rf _ _ => j < 2 ∧ rf.get .x5 = 3
    ∧ rf.get .x6 = BitVec.ofNat 64 (3 * j)
    ∧ rf.get .x7 = BitVec.ofNat 64 (2 - j)

/-- Inner-loop exit, resolved back to outer-indexed facts. -/
def innerPost (j : Nat) : Reach :=
  fun rf _ _ => j < 2 ∧ rf.get .x6 = BitVec.ofNat 64 (3 * j) + 3
    ∧ rf.get .x7 = BitVec.ofNat 64 (2 - j)

/-- The outer-loop body at iteration `j`, as its own calc chain: set the
    inner counter, run the inner loop (routing the outer facts through
    the `dwhileS` snapshot), resolve the snapshot back to `j`-indexed
    facts, decrement the outer counter.  Assertions mention `j`
    throughout; the code (including the inner loop's invariant
    annotation) does not — which is exactly what the outer loop's shared
    skeleton requires. -/
def nestedBody (j : Nat) :
    (fun rf ws A => j < 2 ∧ outerInv j rf ws A
      ∧ (Cond.bne .x7 .x0).holds rf) ⤳ (outerInv (j + 1)) :=
  calc (fun rf ws A => j < 2 ∧ outerInv j rf ws A
        ∧ (Cond.bne .x7 .x0).holds rf : Reach)
    _ ⤳ (fun rf ws A => innerPre j rf ws A : Reach) :=
      DCode.block "setx5" [.LI .x5 3] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨hj, ⟨-, h7, h6⟩, -⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF,
            aluSem, innerPre]
          refine ⟨hj, ?_, ?_, ?_⟩
          · rw [RegFile.get_set_self _ _ _ (by decide)]
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h6]
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h7])
    _ ⤳ (fun rf ws A => ∃ rf₀ ws₀ A₀, innerPre j rf₀ ws₀ A₀
          ∧ (∃ i, i ≤ 3 ∧ innerInv rf₀ ws₀ A₀ i rf ws A)
          ∧ ¬ (Cond.bne .x5 .x0).holds rf : Reach) :=
      DCode.dwhileS "inner" (.bne .x5 .x0) 3 innerInv
        (fun rf ws A h => by
          rcases h with ⟨-, h5, -, -⟩
          refine ⟨by omega, by rw [h5]; decide, by simp, rfl⟩)
        (fun rf₀ ws₀ A₀ i =>
          DCode.block "istep" [.ADDI .x6 .x6 1, .ADDI .x5 .x5 (-1)]
            (by decide)
            (fun h => absurd h (by decide))
            (by
              rintro rf ws A _ ⟨-, hi, ⟨hle, h5, h6, h7⟩, -⟩
              simp only [execBlock_cons, execBlock_nil, execInstrRF,
                aluSem, innerInv]
              refine ⟨by omega, ?_, ?_, ?_⟩
              · rw [RegFile.get_set_self _ _ _ (by decide),
                  RegFile.get_set_ne _ _ _ _ (by decide), h5,
                  show signExtend12 (-1 : BitVec 12) = (-1 : Word)
                    from by decide]
                bv_omega
              · rw [RegFile.get_set_ne _ _ _ _ (by decide),
                  RegFile.get_set_self _ _ _ (by decide), h6,
                  show signExtend12 (1 : BitVec 12) = (1 : Word)
                    from by decide]
                bv_omega
              · rw [RegFile.get_set_ne _ _ _ _ (by decide),
                  RegFile.get_set_ne _ _ _ _ (by decide), h7]))
        (fun rf₀ ws₀ A₀ _ rf ws A h => by
          rcases h with ⟨-, h5, -, -⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not]
          rw [h5]
          decide)
    _ ⤳ (fun rf ws A => innerPost j rf ws A : Reach) :=
      DCode.pure "iexit"
        (by
          rintro rf ws A ⟨rf₀, ws₀, A₀, ⟨hj, -, h6₀, h7₀⟩,
            ⟨i, -, hle3, h5, h6, h7⟩, hc⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hc
          have hi3 : i = 3 := by rw [h5] at hc; bv_omega
          subst hi3
          refine ⟨hj, ?_, by rw [h7, h7₀]⟩
          rw [h6, h6₀]
          rfl)
    _ ⤳ (fun rf ws A => outerInv (j + 1) rf ws A : Reach) :=
      DCode.block "decx7" [.ADDI .x7 .x7 (-1)] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨hj, h6, h7⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF,
            aluSem, outerInv]
          refine ⟨by omega, ?_, ?_⟩
          · rw [RegFile.get_set_self _ _ _ (by decide), h7,
              show signExtend12 (-1 : BitVec 12) = (-1 : Word)
                from by decide]
            bv_omega
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h6]
            bv_omega)

/-- Proof-first nested loop: 2 outer iterations, each running a 3-step
    inner loop; the accumulator ends at 6.  The inner loop needs
    `dwhileS`: its invariant is part of the shared code skeleton and so
    cannot mention `j` — outer facts survive through the snapshot. -/
def nested :
    (fun rf _ _ => rf.get .x7 = 2 ∧ rf.get .x6 = 0)
      ⤳ (fun rf _ _ => rf.get .x6 = 6 ∧ rf.get .x7 = 0) :=
  calc (fun rf _ _ => rf.get .x7 = 2 ∧ rf.get .x6 = 0 : Reach)
    _ ⤳ (fun rf ws A => (∃ j, j ≤ 2 ∧ outerInv j rf ws A)
          ∧ ¬ (Cond.bne .x7 .x0).holds rf : Reach) :=
      DCode.dwhile "outer" (.bne .x7 .x0) 2 outerInv
        (fun rf ws A h =>
          ⟨by omega, by rw [h.1]; decide, by rw [h.2]; decide⟩)
        nestedBody
        (fun rf ws A h => by
          rcases h with ⟨-, h7, -⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not]
          rw [h7]
          decide)
    _ ⤳ (fun rf _ _ => rf.get .x6 = 6 ∧ rf.get .x7 = 0 : Reach) :=
      DCode.pure "oexit"
        (by
          rintro rf ws A ⟨⟨j, hle, -, h7, h6⟩, hc⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hc
          have hj2 : j = 2 := by rw [h7] at hc; bv_omega
          subst hj2
          exact ⟨by rw [h6]; decide, hc⟩)

def nestedProg : Program := nested.program 0

example : nestedProg.length = 8 := rfl

theorem nested_spec (base : Word) : (nested.fn "nested").Spec base :=
  DCode.fn_spec "nested" nested base Region.empty_wf RwRegion.empty_wf

-- ============================================================================
-- 5. Scan with early break (dwhileBreak)
-- ============================================================================

/-- Scan invariant: `i` never exceeds 1 because the break fires on the
    second iteration — the invariant carries reachability, making the
    guard-exit vacuous. -/
def scanInv (i : Nat) : Reach :=
  fun rf _ _ => i ≤ 1 ∧ rf.get .x5 = BitVec.ofNat 64 (4 - i)
    ∧ rf.get .x6 = BitVec.ofNat 64 i ∧ rf.get .x7 = 2

/-- Mid-states: after the `bump` half of iteration `i`, before the break
    test. -/
def scanMid (i : Nat) : Reach :=
  fun rf _ _ => i ≤ 1 ∧ rf.get .x5 = BitVec.ofNat 64 (4 - i)
    ∧ rf.get .x6 = BitVec.ofNat 64 (i + 1) ∧ rf.get .x7 = 2

/-- Proof-first "scan until found": increment `x6` until it reaches the
    limit in `x7`, breaking out mid-body; the decrement of `x5` after the
    break test never runs on the final iteration. -/
def scanBreak :
    (fun rf _ _ => rf.get .x5 = 4 ∧ rf.get .x6 = 0 ∧ rf.get .x7 = 2)
      ⤳ (fun rf _ _ => rf.get .x5 = 3 ∧ rf.get .x6 = 2) :=
  DCode.dwhileBreak "scan" (.bne .x5 .x0) 4 scanInv scanMid
    (.beq .x6 .x7)
    (fun rf ws A h =>
      ⟨by omega, by rw [h.1]; decide, by rw [h.2.1]; decide, h.2.2⟩)
    (fun i =>
      DCode.block "bump" [.ADDI .x6 .x6 1] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨-, ⟨hle, h5, h6, h7⟩, -⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
            scanMid]
          refine ⟨hle, ?_, ?_, ?_⟩
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h5]
          · rw [RegFile.get_set_self _ _ _ (by decide), h6,
              show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
            bv_omega
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h7]))
    (fun i =>
      DCode.block "dec" [.ADDI .x5 .x5 (-1)] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨hi, ⟨hle, h5, h6, h7⟩, hnbr⟩
          simp only [Cond.holds, h6, h7] at hnbr
          have hi0 : i = 0 := by bv_omega
          subst hi0
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
            scanInv]
          refine ⟨by omega, ?_, ?_, ?_⟩
          · rw [RegFile.get_set_self _ _ _ (by decide), h5,
              show signExtend12 (-1 : BitVec 12) = (-1 : Word)
                from by decide]
            decide
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h6]
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h7]))
    (fun rf ws A h => absurd h.1 (by omega))
    (fun i _ rf ws A hinv hng => by
      exfalso
      rcases hinv with ⟨hle, h5, -, -⟩
      simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hng
      rw [h5] at hng
      bv_omega)
    (fun i _ rf ws A hmid hbr => by
      rcases hmid with ⟨hle, h5, h6, h7⟩
      simp only [Cond.holds, h6, h7] at hbr
      have hi1 : i = 1 := by bv_omega
      subst hi1
      exact ⟨by rw [h5]; decide, by rw [h6]; decide⟩)

def scanBreakProg : Program := scanBreak.program 0

example : scanBreakProg.length = 5 := rfl

theorem scanBreak_spec (base : Word) :
    (scanBreak.fn "scanBreak").Spec base :=
  DCode.fn_spec "scanBreak" scanBreak base Region.empty_wf RwRegion.empty_wf

end DerivDemo
end SAsm
end EvmAsm.Rv64
