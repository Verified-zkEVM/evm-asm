/-
  EvmAsm.Codegen.Proofs.DoWhileDemo

  End-to-end demo for the bottom-test loop combinators `Stmt.doWhile`
  (bead evm-asm-4ch8f.68) and its snapshot-parameterized sibling
  `Stmt.doWhileS` (bead evm-asm-4ch8f.69), mirroring the merged top-test
  `«while»`/`«whileS»`/`«whileBreak»` combinators (#9804).

  Three independent pieces:

  1. **Byte-identity to a real converter loop.**  The emitted BE↔LE
     field-element converters (`bnfBeToLe_prog`, `Bn254Field.lean:85`) are
     *nested bottom-test* loops — `body ++ [BNE cond → body-start]`, no
     header guard, no `JAL` — which no top-test combinator can byte-match.
     `bnfInnerLoopSlice`/`bnfOuterNestedSlice` below pin `Stmt.doWhile`
     (nested, with a straight-line block between the inner loop and the
     outer back-edge) byte-for-byte against the real instruction stream,
     proving the primitive is *sufficient* for the `.11.11` port's *shape*
     (a separate bead; not done here). `doWhileS` flattens identically
     (§3), so the same byte-identity carries over to the functional port.
  2. **A fully verified nested `doWhile`.**  `nestedDoWhileDemoFn` is a
     smaller, self-contained (no memory) nested counter using the same
     shape — `doWhile` inside `doWhile`, with a straight-line block after
     the inner loop and before the outer back-edge — carried all the way
     through `Fn.sound`, demonstrating the VC generator handles nested
     bottom-test loops end-to-end.  Its outer loop only runs once (`fuel =
     0`) because plain `doWhile` cannot recover a register's pre-inner-loop
     value afterward (§2's docstring; the motivation for `doWhileS`).
  3. **The case plain `doWhile` couldn't do.**  `nestedDoWhileSDemoFn`
     replaces the *inner* loop with `doWhileS`: its invariant is
     parameterized by the state at the inner loop's own entry, so `x5` (set
     before the inner loop, by the *outer* iteration in progress) survives
     the inner loop's otherwise-erasing `sp` and is legible again in
     `outerTail`, *after* the inner loop — exactly the `bnfBeToLe_prog`
     pattern (`x5` addresses the destination limb post-inner-loop).  The
     outer loop is now a genuinely-counting plain `doWhile` (`fuel = 1`,
     two real iterations), and its post is a function of the *recovered*
     value, no ∃-escape: `x5 = 2`.
-/

import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Field

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm Stmt

-- ============================================================================
-- 1. Byte-identity to `bnfBeToLe_prog`'s nested bottom-test loops
-- ============================================================================

/-- The inner loop of `bnfBeToLe_prog` (instructions `[7, 13)`): accumulate one
    little-endian limb byte-by-byte, `BNE x29,x0` looping back to the very
    first body instruction — the bottom-test shape `body ++ [B guard → body]`
    with no header guard and no `JAL`. -/
def bnfInnerLoopSlice : Stmt :=
  .doWhile "bnfInner" (.bne .x29 .x0) 6
    (fun _ _ _ _ => True)
    (.block "body"
      [ .SLLI .x28 .x28 (8 : BitVec 6),
        .LBU .x30 .x6 (0 : BitVec 12),
        .OR .x28 .x28 .x30,
        .ADDI .x6 .x6 (1 : BitVec 12),
        .ADDI .x29 .x29 (-1 : BitVec 12) ])

-- **Byte-identity pin**: the inner `doWhile`'s flattened code is exactly the
-- 6-instruction slice `bnfBeToLe_prog[7:13]` (`Bn254Field.lean:99-104`).
#guard bnfInnerLoopSlice.flatten 0 =
  [ .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x30 .x6 (0 : BitVec 12),
    .OR .x28 .x28 .x30,
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-20 : BitVec 13) ]

#guard bnfInnerLoopSlice.flatten 0 = (bnfBeToLe_prog.drop 7).take 6

/-- The full nested loop region of `bnfBeToLe_prog` (instructions `[1, 19)`,
    i.e. everything but the outer counter's `LI x5,0` prologue and the final
    `ret`): the outer `doWhile` (`BNE x5,x6` back-edge) whose body is a
    straight-line setup block, `bnfInnerLoopSlice`, and a straight-line
    tail block (`SD`-shaped store-limb sequence) before the outer back-edge —
    exactly the required nesting shape (`doWhile` inside `doWhile`, with a
    block between the inner loop's end and the outer back-edge). -/
def bnfOuterNestedSlice : Stmt :=
  .doWhile "bnfOuter" (.bne .x5 .x6) 17
    (fun _ _ _ _ => True)
    ( .block "setup"
        [ .LI .x6 (24 : Word),
          .SLLI .x7 .x5 (3 : BitVec 6),
          .SUB .x6 .x6 .x7,
          .ADD .x6 .x10 .x6,
          .LI .x28 (0 : Word),
          .LI .x29 (8 : Word) ] ;;;
      bnfInnerLoopSlice ;;;
      .block "storeLimb"
        [ .SLLI .x7 .x5 (3 : BitVec 6),
          .ADD .x7 .x11 .x7,
          .SD .x7 .x28 (0 : BitVec 12),
          .ADDI .x5 .x5 (1 : BitVec 12),
          .LI .x6 (4 : Word) ] )

-- **Byte-identity pin**: the nested nested `doWhile` reproduces
-- `bnfBeToLe_prog`'s entire loop region (prologue `LI x5,0` prepended,
-- final `ret` excluded) byte-for-byte — the tie that proves `doWhile` is
-- sufficient for the `.11.11` port (a separate bead; not done here).
#guard (.block "init" [.LI .x5 (0 : Word)] ;;; bnfOuterNestedSlice : Stmt).flatten 0
    = bnfBeToLe_prog.take 19

/-- `doWhileS`'s flatten is *identical* to `doWhile`'s (same `body.flatten
    ++ [guard.toInstr (brOfsBack body.size)]`, the snapshot only changes
    the invariant's soundness argument) — so the byte-identity pins above
    carry over unchanged to a `doWhileS`-based `.11.11` port. -/
def bnfInnerLoopSliceS : Stmt :=
  .doWhileS "bnfInnerS" (.bne .x29 .x0) 6
    (fun _ _ _ _ _ _ _ => True)
    (.block "body"
      [ .SLLI .x28 .x28 (8 : BitVec 6),
        .LBU .x30 .x6 (0 : BitVec 12),
        .OR .x28 .x28 .x30,
        .ADDI .x6 .x6 (1 : BitVec 12),
        .ADDI .x29 .x29 (-1 : BitVec 12) ])

#guard bnfInnerLoopSliceS.flatten 0 = bnfInnerLoopSlice.flatten 0
#guard bnfInnerLoopSliceS.flatten 0 = (bnfBeToLe_prog.drop 7).take 6

-- ============================================================================
-- 2. A fully verified nested `doWhile`: a self-contained counter with no
-- memory access, carried through `Fn.sound`.
-- ============================================================================

/-- Outer loop invariant (`fuel = 0`: the outer body runs exactly once, so
    there is only ever the one index `0` — see the note on nesting below).
    `x29 = 0` is re-asserted here (not merely inner's local fact) because it
    must survive `outerTail`, a plain block downstream of the inner loop. -/
def outerInv : Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun _ rf _ _ => rf.get .x5 = 1 ∧ rf.get .x6 = 1 ∧ rf.get .x29 = 0

/-- Inner loop invariant, post-`(j+1)`-th run: `x29` counts down from the
    fixed inner bound; `x6 = 1` is carried along unchanged (set once, before
    the outer loop, by `init`) purely so it survives to `outerInv` — a
    `doWhile`/`sp` node's strongest postcondition depends only on its own
    `inv`, so anything the *enclosing* context needs after a nested loop
    must be re-asserted in the nested loop's own invariant. -/
def innerInv : Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun j rf _ _ => rf.get .x29 = BitVec.ofNat 64 (2 - j) ∧ rf.get .x6 = 1

/-- `doWhile` nested inside `doWhile`, with a straight-line block
    (`outerTail`) between the inner loop's end and the outer back-edge —
    the shape required for the BE↔LE converters (§1 above pins the exact
    byte match), exercised here with a minimal register-only counter (no
    memory) so the demo turns on the control-flow machinery alone.

    **Why the outer loop only runs once** (`fuel = 0`): `Stmt.sp` for a
    `doWhile` node depends only on its own invariant, forgetting everything
    about the state that reached it (exactly like `«while»`, and exactly
    why `«whileS»` exists as its snapshot-parameterized sibling — see
    `Stmt.whileS`'s docstring).  A genuinely-counting *outer* loop wrapped
    around a nested `doWhile` would need `x5`'s pre-inner-loop value to
    survive the inner loop's own erasure to be incremented afterward, which
    requires relating the inner loop's exit state back to its entry state —
    a `doWhileS` capability this bead does not build.  (The real
    `bnfBeToLe_prog` outer loop needs exactly this: `x5` is read again,
    after the inner loop, to address the destination limb — so a full
    functional port of `.11.11`'s outer loop will need a `doWhileS`
    sibling, not plain `doWhile`; that is a natural follow-up, not built
    here.)  Running the outer body exactly once sidesteps this while still
    exercising the full nested-composition machinery this bead adds. -/
def nestedDoWhileDemoFn : Fn where
  name := "nestedDoWhileDemo"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x5 = 1 ∧ rf.get .x6 = 1 ∧ rf.get .x29 = 0
  body :=
    .block "init" [.LI .x6 (1 : Word)] ;;;
    .doWhile "outer" (.bne .x5 .x6) 0 outerInv
      ( .block "innerInit" [.LI .x29 (3 : Word)] ;;;
        .doWhile "inner" (.bne .x29 .x0) 2 innerInv
          (.block "innerBody" [.ADDI .x29 .x29 (-1 : BitVec 12)]) ;;;
        .block "outerTail" [.LI .x5 (1 : Word)] )

theorem nestedDoWhileDemoFn_spec (base : Word) : nestedDoWhileDemoFn.Spec base := by
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case nestedDoWhileDemo.outer.body.inner.inv_init =>
    rintro rf' ws' A' ⟨rf, ws, hws, hreach, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    obtain ⟨rf₀, ws₀, hws₀, hR0, rfl, rfl⟩ := hreach
    rcases hR0 with hR0 | ⟨i, hi, -⟩
    · obtain ⟨rfI, wsI, hwsI, -, rfl, rfl⟩ := hR0
      constructor <;>
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
      decide
    · exact absurd hi (by omega)
  case nestedDoWhileDemo.outer.body.inner.inv_step =>
    rintro j hj rf' ws' A' ⟨rf, ws, hws, ⟨⟨hx29, hx6⟩, hg⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx29, hsem1]
      have h1 : (BitVec.ofNat 64 (2 - j)).toNat = 2 - j := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (2 - (j + 1))).toNat = 2 - (j + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x29), hx6]
  case nestedDoWhileDemo.outer.body.inner.exhausted =>
    rintro rf ws A ⟨hx29, -⟩
    intro hc
    apply hc
    rw [hx29]
    show (BitVec.ofNat 64 (2 - 2) : Word) = (0 : Word)
    decide
  case nestedDoWhileDemo.outer.inv_init =>
    rintro rf' ws' A' ⟨rf, ws, hws, ⟨⟨j, hj, hx29, hx6⟩, hng⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hx0 : rf.get .x29 = rf.get .x0 := Decidable.of_not_not hng
    rw [RegFile.get_x0] at hx0
    refine ⟨?_, ?_, ?_⟩
    · simp [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x5)]
      exact hx6
    · simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : (Reg.x29 : Reg) ≠ .x5)]
      exact hx0
  case nestedDoWhileDemo.outer.inv_step =>
    intro i hi
    exact absurd hi (by omega)
  case nestedDoWhileDemo.outer.exhausted =>
    rintro rf ws A ⟨hx5, hx6, -⟩
    intro hc
    apply hc
    rw [hx5, hx6]
  case nestedDoWhileDemo.post =>
    rintro rf ws A ⟨⟨i, hi, hx5, hx6, hx29⟩, -⟩
    exact ⟨hx5, hx6, hx29⟩

#print axioms nestedDoWhileDemoFn_spec

-- ============================================================================
-- 3. A fully verified nested `doWhileS`: the outer loop rereads a register
-- after the inner loop — the case plain `doWhile` couldn't do.
-- ============================================================================

/-- Outer loop invariant (plain `doWhile`, genuinely counting: `x5` is the
    completed-iteration count). -/
def outerInvS : Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ => rf.get .x5 = BitVec.ofNat 64 (i + 1) ∧ rf.get .x6 = 2

/-- Inner loop invariant, **snapshot-parameterized**: `x29` counts down from
    the fixed inner bound (as in the plain-`doWhile` demo), but `x5` is now
    tied to `rf₀.get .x5` — the value `x5` held at the *inner loop's own
    entry* — rather than a fixed constant.  Since `(rf₀, ws₀, A₀)` is
    re-instantiated fresh every time the outer loop re-enters this `doWhileS`
    node, this lets `x5` survive the inner loop *whatever value it happens
    to hold that outer iteration* — the capability plain `doWhile`'s
    non-parameterized `inv : Nat → Reach` cannot express. -/
def innerInvS : RegFile → List (BitVec 8) → Assertion →
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf₀ _ _ j rf _ _ =>
    rf.get .x29 = BitVec.ofNat 64 (2 - j)
      ∧ rf.get .x5 = rf₀.get .x5 ∧ rf.get .x6 = rf₀.get .x6

/-- `doWhileS` inside a genuinely-counting `doWhile`: `outerTail` rereads
    `x5` *after* the inner loop runs — a plain (non-snapshotted) `doWhile`
    inner loop would erase `x5`'s value entirely (§2's docstring); the
    snapshot in `innerInvS` is what lets `outerTail`'s `ADDI x5,x5,1`
    recover it.  This is exactly the `bnfBeToLe_prog` outer-loop pattern
    (rereads its counter after the inner limb-assembly loop, to address the
    destination), reproduced here with a minimal register-only counter (no
    memory).  Two outer iterations, three inner iterations each. -/
def nestedDoWhileSDemoFn : Fn where
  name := "nestedDoWhileSDemo"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x5 = 2 ∧ rf.get .x6 = 2
  body :=
    .block "init" [.LI .x5 (0 : Word), .LI .x6 (2 : Word)] ;;;
    .doWhile "outer" (.bne .x5 .x6) 1 outerInvS
      ( .block "innerInit" [.LI .x29 (3 : Word)] ;;;
        .doWhileS "inner" (.bne .x29 .x0) 2 innerInvS
          (.block "innerBody" [.ADDI .x29 .x29 (-1 : BitVec 12)]) ;;;
        .block "outerTail" [.ADDI .x5 .x5 (1 : BitVec 12)] )

theorem nestedDoWhileSDemoFn_spec (base : Word) : nestedDoWhileSDemoFn.Spec base := by
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case nestedDoWhileSDemo.outer.body.inner.inv_init =>
    rintro rf₀ ws₀ A₀ hreach₀ rf' ws' A' ⟨rf, ws, hws, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    -- `hreach₀` records that `innerInit` (`LI x29,3`) already ran.
    obtain ⟨rfJ, wsJ, hwsJ, -, rfl, rfl⟩ := hreach₀
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem] <;> decide
  case nestedDoWhileSDemo.outer.body.inner.inv_step =>
    rintro rf₀ ws₀ A₀ hreach₀ j hj rf' ws' A' ⟨rf, ws, hws, ⟨⟨hx29, hx5, hx6⟩, hg⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx29, hsem1]
      have h1 : (BitVec.ofNat 64 (2 - j)).toNat = 2 - j := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (2 - (j + 1))).toNat = 2 - (j + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x29), hx5]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x29), hx6]
  case nestedDoWhileSDemo.outer.body.inner.exhausted =>
    rintro rf₀ ws₀ A₀ hreach₀ rf ws A ⟨hx29, -, -⟩
    intro hc
    apply hc
    rw [hx29]
    show (BitVec.ofNat 64 (2 - 2) : Word) = (0 : Word)
    decide
  case nestedDoWhileSDemo.outer.inv_init =>
    -- `sp` through `innerInit ;;; inner ;;; outerTail`, starting from the
    -- statement's own entry reach (`init`'s block).
    rintro rf' ws' A'
      ⟨rf2, ws2, hws2, ⟨rf0, ws0, A0, hSp0, ⟨j, hj, hx29_0, hx5_0, hx6_0⟩, hgInner⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws2
    have hRF0 : rf0.get .x5 = 0 ∧ rf0.get .x6 = 2 := by
      obtain ⟨rfR, wsR, hwsR, hR, rfl, rfl⟩ := hSp0
      obtain rfl := List.eq_nil_of_length_eq_zero hwsR
      obtain ⟨rfI, wsI, hwsI, -, rfl, rfl⟩ := hR
      constructor <;> simp [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_⟩
    · simp [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
      rw [hx5_0, hRF0.1]
      decide
    · simp [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
      rw [hx6_0, hRF0.2]
      decide
  case nestedDoWhileSDemo.outer.inv_step =>
    rintro i hi rf' ws' A'
      ⟨rf2, ws2, hws2, ⟨rf0, ws0, A0, hSp0, ⟨j, hj, hx29_0, hx5_0, hx6_0⟩, hgInner⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws2
    have hRF0 : rf0.get .x5 = BitVec.ofNat 64 (i + 1) ∧ rf0.get .x6 = 2 := by
      obtain ⟨rfR, wsR, hwsR, ⟨⟨hx5', hx6'⟩, -⟩, rfl, rfl⟩ := hSp0
      obtain rfl := List.eq_nil_of_length_eq_zero hwsR
      constructor
      · simpa [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem] using hx5'
      · simpa [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem] using hx6'
    refine ⟨?_, ?_⟩
    · simp [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
      rw [hx5_0, hRF0.1]
      have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
      have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1 + 1)).toNat = i + 1 + 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · simp [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
      rw [hx6_0, hRF0.2]
      decide
  case nestedDoWhileSDemo.outer.exhausted =>
    rintro rf ws A ⟨hx5, hx6⟩
    intro hc
    apply hc
    rw [hx5, hx6]
    decide
  case nestedDoWhileSDemo.post =>
    rintro rf ws A ⟨⟨i, hi, hx5, hx6⟩, hng⟩
    have heq : rf.get .x5 = rf.get .x6 := Decidable.of_not_not hng
    exact ⟨heq.trans hx6, hx6⟩

#print axioms nestedDoWhileSDemoFn_spec

end EvmAsm.Codegen.Proofs
