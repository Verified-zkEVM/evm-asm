/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadReshuffle

  The reload-boundary pointer reshuffle for the fixed-x19 EXP loop.

  At a 64-bit limb boundary the loop body has already executed the reload
  (`LD x19 ← [x16]; ADDI x16 x16 -8`), so the loop-back post carries
  `expTwoMulFixedIterReloadPointerFrame ptr nextLimb = (x16 ↦ ptr-8) **
  (ptr ↦ nextLimb)`: the pointer register `x16` has advanced to `ptr-8`,
  but the live memory cell is still at the now-stale address `ptr`.

  The next iteration's `expTwoMulFixedIterPointerFrame (ptr-8) nextNextLimb`
  instead needs the cell at the *new* pointer `ptr-8`.  That cell is the next
  exponent limb, which lives in the induction residual `R` (the entry residual
  `expTwoMulFixedFirstIterEntryResidual` stages exactly the not-yet-loaded
  lower limbs).  So the reshuffle is a *pure* separation-logic re-partition:
  pull the `ptr-8` cell out of `R` into the pointer frame and push the stale
  `ptr` cell back into `R`.  No code step is required — the reload instructions
  already ran inside the finished iteration body.

  This lemma isolates that re-partition at the pointer-frame level; the
  256-iteration merged loop induction threads the exponent residual `R` so the
  `ptr-8` cell is in scope at each of the three limb boundaries.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Reload-boundary pointer reshuffle (pure re-partition).

    Given the post-reload pointer frame `(x16 ↦ ptr-8) ** (ptr ↦ nextLimb)`
    together with the next-limb cell at `ptr-8` (supplied from the induction
    residual), regroup into the next iteration's pointer frame
    `(x16 ↦ ptr-8) ** (ptr-8 ↦ nextNextLimb)` plus the stale `ptr` cell
    (returned to the residual).  This is the entire content of the reload
    transition once the residual cell is in scope: a `sep_perm`. -/
theorem expTwoMulFixedIterReloadPointerFrame_reshuffle_to_pointerFrame
    {ptr nextLimb nextNextLimb : Word} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadPointerFrame ptr nextLimb **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps) :
    (expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
        nextNextLimb **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps := by
  rw [expTwoMulFixedIterReloadPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPointerFrame_unfold]
  sep_perm h

/-- The reverse re-partition: the next pointer frame plus the stale `ptr` cell
    regroup back into the post-reload reload-pointer frame plus the `ptr-8`
    cell.  Records that the reshuffle is an honest bijection on the heap
    (no cell is created or destroyed), useful when threading the residual in
    either direction. -/
theorem expTwoMulFixedIterPointerFrame_reshuffle_to_reloadPointerFrame
    {ptr nextLimb nextNextLimb : Word} {ps : PartialState}
    (h :
      (expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
          nextNextLimb **
        ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps) :
    (expTwoMulFixedIterReloadPointerFrame ptr nextLimb **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps := by
  rw [expTwoMulFixedIterPointerFrame_unfold] at h
  rw [expTwoMulFixedIterReloadPointerFrame_unfold]
  sep_perm h

/-- Suffix-level reload reshuffle (conditional-multiply branch).

    Lifts the pointer-cell reshuffle to the full reload-cond scratch suffix
    frame that appears in the merged loop-back reload disjunct: given that
    suffix together with the next-limb cell at `ptr-8` (from the induction
    residual), regroup the `reloadPointerFrame` into the next iteration's
    `IterPointerFrame (ptr-8)` and return the stale `ptr` cell.  All other
    suffix atoms (the cursor `x19`, reset counter `x20`, saved bit `x18`, the
    `c6New = 0` / `bit ≠ 0` pures, the `SkipCondRestScratchSuffix`) are
    unchanged — this is a pure `sep_perm` once the pointer frames unfold. -/
theorem expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame_reshuffle
    {e c6 ptr nextLimb nextNextLimb base : Word} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps) :
    (expTwoMulFixedIterSkipCondRestScratchSuffix base **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
        nextNextLimb **
      ⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps := by
  simp only [expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame,
    expTwoMulFixedIterReloadPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPointerFrame_unfold]
  sep_perm h

/-- Suffix-level reload reshuffle (skip / no-conditional-multiply branch).
    The skip variant of
    `expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame_reshuffle`: the
    suffix carries the `x1` return slot and the `IterBaseFrame` instead of the
    `SkipCondRestScratchSuffix`, and the `bit = 0` pure; the reshuffle is again
    a pure `sep_perm`. -/
theorem expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame_reshuffle
    {e c6 ptr nextLimb nextNextLimb evmSp a0 a1 a2 a3 base : Word}
    {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps) :
    ((.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
        nextNextLimb **
      ⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0⌝ **
      expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3 **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps := by
  simp only [expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame,
    expTwoMulFixedIterReloadPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPointerFrame_unfold]
  sep_perm h

/-- Reload→`IterPre` assembler (conditional-multiply branch).

    The merged loop-back reload-cond disjunct's residual
    (`SkipCondCountPostScratchPrefix ** ScratchIs ** ReloadCondCountPostScratchSuffix`)
    together with the next-limb cell at `ptr-8` (from the induction residual)
    assembles into the *next* iteration's `expTwoMulFixedIterPre` at the advanced
    pointer `ptr-8`, with the reloaded cursor `x19 = nextLimb`, the reset counter
    `x20 = 64`, and the stale `ptr` cell returned to the residual.  This is the
    reload analogue of `expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame`,
    with the committed suffix reshuffle applied first to fix the pointer cell. -/
theorem expTwoMulFixedIterReloadCondScratchFrame_to_iterPre_frame
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterReloadCondCountPostScratchSuffix e c6 ptr nextLimb base **
          (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))) **
        frame) ps) :
    ((expTwoMulFixedIterPre
      nextLimb
      ((0 : Word) + signExtend12 (64 : BitVec 12))
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
      (((base + 44) + 140) + 68)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
      d0 d1 d2 d3
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
      a0 a1 a2 a3 v7 v11) **
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        frame)) ps := by
  -- Extract the pure facts (exit condition, reload `c6New = 0`, branch taken)
  -- from the original residual before reshaping.
  obtain ⟨h_exit, h_c6, h_bit⟩ :=
    expTwoMulFixedIterReloadCondScratchFrame_pures
      (show ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
          expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
          expTwoMulFixedIterReloadCondCountPostScratchSuffix e c6 ptr nextLimb base) **
          ((((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame)) ps
        from by sep_perm h)
  -- Convert the reload-cond suffix to its frame form, then reshuffle the
  -- pointer cell using the committed suffix reshuffle.
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (fun ps' hh =>
          expTwoMulFixedIterReloadCondCountPostScratchSuffix_frame hh)))) _ h
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right
      (fun ps' hh =>
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame_reshuffle hh))) _ h
  -- Weaken the surrendered `x6` scratch value to ownership.
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ h
  -- Strip the pure facts produced by the reshuffle.
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterSkipCondRestScratchPrefix
    expTwoMulFixedIterSkipCondRestScratchSuffix at h
  rw [expTwoMulFixedIterPointerFrame_unfold] at h
  -- Strip the pure facts now that they are known true.
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at h
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ : Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at h
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0⌝ :
        Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at h
  simp only [sepConj_emp_left', sepConj_emp_right'] at h
  rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  simp only [evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    show (140 : Word) + 68 = 208 from by decide,
    show (44 : Word) + 208 = 252 from by decide,
    BitVec.add_assoc] at h ⊢
  xperm_hyp h

/-- Reload→`IterPre` assembler (skip / no-conditional-multiply branch).

    The skip analogue of `expTwoMulFixedIterReloadCondScratchFrame_to_iterPre_frame`:
    the merged loop-back reload-skip disjunct's residual together with the next-limb
    cell at `ptr-8` assembles into the next iteration's `expTwoMulFixedIterPre` at
    `ptr-8` with the squaring result (`squareW`, since the conditional multiply is
    skipped), reloaded cursor and reset counter, returning the stale `ptr` cell. -/
theorem expTwoMulFixedIterReloadSkipScratchFrame_to_iterPre_frame
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base **
          (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))) **
        frame) ps) :
    ((expTwoMulFixedIterPre
      nextLimb
      ((0 : Word) + signExtend12 (64 : BitVec 12))
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
      (((base + 44) + 32) + 68)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
      d0 d1 d2 d3
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
      a0 a1 a2 a3 v7 v11) **
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        frame)) ps := by
  obtain ⟨h_exit, h_c6, h_bit⟩ :=
    expTwoMulFixedIterReloadSkipScratchFrame_pures
      (show ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 exitCond **
          expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
          expTwoMulFixedIterReloadSkipCountPostScratchSuffix
            e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
          ((((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame)) ps
        from by sep_perm h)
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (fun ps' hh =>
          expTwoMulFixedIterReloadSkipCountPostScratchSuffix_frame hh)))) _ h
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right
      (fun ps' hh =>
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame_reshuffle hh))) _ h
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ h
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterSkipRestScratchPrefix at h
  rw [expTwoMulFixedIterPointerFrame_unfold] at h
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at h
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ : Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at h
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0⌝ :
        Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at h
  simp only [sepConj_emp_left', sepConj_emp_right'] at h
  rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  simp only [expTwoMulFixedIterBaseFrame,
    evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    show (32 : Word) + 68 = 100 from by decide,
    show (44 : Word) + 100 = 144 from by decide,
    BitVec.add_assoc] at h ⊢
  xperm_hyp h

end EvmAsm.Evm64.Exp.Compose
