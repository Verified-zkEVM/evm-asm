/-
  EvmAsm.Evm64.MulMod.Compose.DispatchZero

  Top-level dispatch composition for the `evm_mulmod` program over the
  `N = 0` arm.

  The prefix branch (`evm_mulmod_nonzero_or_zero_prefix`) ORs the four limbs
  of `n` and branches: `orAll ≠ 0` jumps to the product/reduce body at
  `base + 56`, `orAll = 0` falls through to the zero path at `base + 32`.
  Because `orAll = 0 ↔ n = 0` (`orAll_limbs_eq_zero_iff`) and the hypothesis
  fixes `n = 0` (`hnz`), the N ≠ 0 (taken) path is unreachable: the taken
  postcondition carries `⌜orAll ≠ 0⌝`, which contradicts `n = 0`, so
  `cpsBranchWithin_ntakenPath` extracts the not-taken arm directly. That arm is
  then sequenced with the N = 0 tail (`evm_mulmod_zero_path_tail`), which zeroes
  the result window and jumps to the program exit. The result slots
  `sp + 64 .. sp + 88` hold `0 = EvmWord.mulmod a b n` (since `n = 0`); rewritten
  as `EvmWord.getLimbN (EvmWord.mulmod a b n) k` to match the N ≠ 0 dispatch's
  post shape. The product window and accumulator window are untouched.

  Exit address: `(base + 52) + signExtend21 2108 = base + 2160`, the program
  exit.
-/

import EvmAsm.Evm64.MulMod.Compose.Dispatch
import EvmAsm.Evm64.MulMod.Compose.ZeroPathTail
import EvmAsm.Evm64.MulMod.MulModResultWord
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.DropPure

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- Full `evm_mulmod` dispatch over the `N = 0` arm.

    Entry `base`, exit `base + 2160` (the program exit). The precondition is the
    ambient `evm_mulmod` machine state: `x12 ↦ sp`, the `a`/`b`/`n` argument
    windows (`sp + 0 .. sp + 88`), the eight-cell product scratch window
    (`sp - 160 .. sp - 104`, arbitrary input garbage `p0..p7`), the modular
    accumulator window (`sp - 32 .. sp - 8`, garbage `r0..r3`), and the
    scratch registers `x0, x5 .. x20`. The branch ORs `n`'s four limbs; since
    `n = 0` forces `orAll = 0`, the N ≠ 0 path is unreachable and the zero path
    zeroes the result window. The result window `sp + 64 .. sp + 88` holds the
    limbs of `EvmWord.mulmod a b n` (which is `0`); `x12` advances to
    `sp + 64`. The product window (`p0..p7`) and accumulator window (`r0..r3`)
    are untouched. -/
theorem evm_mulmod_dispatch_zero_evm_mulmod_spec_within
    (sp base : Word) (a b n : EvmWord)
    (v5Old v6Old : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word)
    (hnz : n = 0) :
    cpsTripleWithin (8 + (4 + 1 + 1))
      base (base + 2160) (evm_mulmod_program_code base)
      -- Ambient pre: identical to the N ≠ 0 dispatch PRE.
      (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v5Old) ** (.x5 ↦ᵣ v6Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n.getLimbN 0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n.getLimbN 1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n.getLimbN 2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n.getLimbN 3)) **
       ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
        ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
        ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ p0) **
        ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ p1) **
        ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7) **
        (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) ** (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) **
        (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) **
        (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
        regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20))
      -- Post: result limbs are `EvmWord.mulmod a b n` (= 0); inputs untouched.
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 3)) **
       ((.x6 ↦ᵣ (n.getLimbN 0 ||| n.getLimbN 1 ||| n.getLimbN 2 ||| n.getLimbN 3)) **
        (.x5 ↦ᵣ n.getLimbN 3) ** (.x0 ↦ᵣ 0) **
        (sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
        ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
        ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ p0) **
        ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ p1) **
        ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7) **
        (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) ** (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) **
        (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) **
        (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
        regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20)) := by
  -- R_amb: resources beyond the branch's not-taken post `Q_f` (everything that
  -- frames untouched through the zero path).
  set Ramb : Assertion :=
    ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
     ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
     ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
     ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
     ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ p0) **
     ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ p1) **
     ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
     ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
     ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
     ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
     ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
     ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7) **
     (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) ** (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) **
     (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) **
     (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) **
     ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
     ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
     ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
     ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
     regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20) with hRamb
  -- Prefix branch, framed with `Ramb`.
  have hbr0 := evm_mulmod_nonzero_or_zero_prefix_evm_mulmod_spec_within
    sp v6Old v5Old (n.getLimbN 0) (n.getLimbN 1) (n.getLimbN 2) (n.getLimbN 3) base
  simp only [] at hbr0
  have hbr := cpsBranchWithin_frameR Ramb (by pcFree) hbr0
  -- The N ≠ 0 path is unreachable: `⌜orAll ≠ 0⌝` contradicts `n = 0`.
  have h_f0 := cpsBranchWithin_ntakenPath hbr (Q_t := _) ?_h_absurd
  · -- The not-taken arm runs `base → base + 32`, leaving `Q_f ** Ramb`.
    -- The N = 0 tail, instantiated so the n-cells double as result slots.
    have htail := evm_mulmod_zero_path_tail_evm_mulmod_spec_within
      sp (n.getLimbN 0) (n.getLimbN 1) (n.getLimbN 2) (n.getLimbN 3) base
    -- Frame the tail with everything `Q_f ** Ramb` carries beyond `x12` + n-cells.
    have htailF := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ (n.getLimbN 0 ||| n.getLimbN 1 ||| n.getLimbN 2 ||| n.getLimbN 3)) **
       (.x5 ↦ᵣ n.getLimbN 3) ** (.x0 ↦ᵣ 0) ** ⌜(n.getLimbN 0 ||| n.getLimbN 1 ||| n.getLimbN 2 ||| n.getLimbN 3 : Word) = 0⌝ ** Ramb)
      (by rw [hRamb]; pcFree)
      htail
    -- Sequence the not-taken arm with the framed tail; the perm aligns shapes.
    have hcomp := cpsTripleWithin_seq_perm_same_cr
      (Q1 := _) (Q2 := _)
      (fun h hp => by
        xperm_hyp hp)
      h_f0 htailF
    -- Exit alignment: `(base + 52) + signExtend21 2108 = base + 2160`.
    have hexit : (base + 52) + signExtend21 (2108 : BitVec 21) = base + 2160 := by
      rw [BitVec.add_assoc]; congr 1
    rw [hexit] at hcomp
    -- The zeroed result slots equal `EvmWord.getLimbN (EvmWord.mulmod a b n) k`.
    have hres : ∀ k, EvmWord.getLimbN (EvmWord.mulmod a b n) k = (0 : Word) := by
      intro k; rw [hnz, EvmWord.mulmod_zero, EvmWord.getLimbN_zero]
    -- Final consequence: rewrite the goal's result slots to `0`, then strip the
    -- `⌜orAll = 0⌝` pure fact that `hcomp`'s post carries beyond the stated post.
    refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hcomp
    intro h hp
    rw [hres 0, hres 1, hres 2, hres 3]
    drop_pure hp
    xperm_hyp hp
  case _h_absurd =>
    intro hp hQt
    obtain ⟨_, _, _, _, hQtL, _⟩ := hQt
    obtain ⟨_, _, _, _, _, r1⟩ := hQtL
    obtain ⟨_, _, _, _, _, r2⟩ := r1
    obtain ⟨_, _, _, _, _, r3⟩ := r2
    obtain ⟨_, _, _, _, _, r4⟩ := r3
    obtain ⟨_, _, _, _, _, r5⟩ := r4
    obtain ⟨_, _, _, _, _, r6⟩ := r5
    obtain ⟨_, _, _, _, _, r7⟩ := r6
    have horall : n.getLimbN 0 ||| n.getLimbN 1 ||| n.getLimbN 2 ||| n.getLimbN 3 ≠ 0 :=
      ((sepConj_pure_right _).1 r7).2
    exact horall ((orAll_limbs_eq_zero_iff n).2 hnz)

end EvmAsm.Evm64.MulMod.Compose
