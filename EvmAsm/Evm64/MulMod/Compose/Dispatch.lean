/-
  EvmAsm.Evm64.MulMod.Compose.Dispatch

  Top-level dispatch composition for the `evm_mulmod` program over the
  `N ≠ 0` arm (`0 < n.toNat`, any modulus).

  The prefix branch (`evm_mulmod_nonzero_or_zero_prefix`) ORs the four limbs
  of `n` and branches: `orAll ≠ 0` jumps to the product/reduce body at
  `base + 56`, `orAll = 0` falls through to the zero path at `base + 32`.
  Because `orAll = 0 ↔ n = 0` (`orAll_limbs_eq_zero_iff`) and the hypothesis
  fixes `n ≠ 0` (`0 < n.toNat`), the zero path is unreachable: the not-taken
  postcondition carries `⌜orAll = 0⌝`, which contradicts `n ≠ 0`, so
  `cpsBranchWithin_takenPath` extracts the taken arm directly. That arm is then
  sequenced with the `N ≠ 0` body
  (`evm_mulmod_product_reduce_value_evm_mulmod_spec_within`), whose result slots
  are rewritten from `BitVec.ofNat 256 (a·b mod n)` to `EvmWord.mulmod a b n`
  via `EvmWord.mulmod_of_ne_zero`.

  Exit address: `(base + 1816) + 344 = base + 2160`, the program exit.
-/

import EvmAsm.Evm64.MulMod.Compose.ProductReduceValue
import EvmAsm.Evm64.MulMod.Compose.ZeroPathTail
import EvmAsm.Evm64.MulMod.MulModResultWord
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- The OR-fold of `n`'s four 64-bit limbs is zero iff `n` is the zero word. -/
theorem orAll_limbs_eq_zero_iff (n : EvmWord) :
    (n.getLimbN 0 ||| n.getLimbN 1 ||| n.getLimbN 2 ||| n.getLimbN 3 = (0 : Word)) ↔ n = 0 := by
  rw [EvmWord.eq_zero_iff_limbs, EvmWord.getLimb_as_getLimbN_0,
      EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
      EvmWord.getLimb_as_getLimbN_3]
  constructor
  · intro h
    have h12 := EvmAsm.Evm64.EvmWord.bv_or_eq_zero
      (show (n.getLimbN 0 ||| n.getLimbN 1) ||| (n.getLimbN 2 ||| n.getLimbN 3) = 0 by
        rw [← h]; ac_rfl)
    exact ⟨(EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.1).1,
           (EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.1).2,
           (EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.2).1,
           (EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.2).2⟩
  · rintro ⟨h0, h1, h2, h3⟩; rw [h0, h1, h2, h3]; simp

/-- `n ≠ 0` from `0 < n.toNat`. -/
theorem evmWord_ne_zero_of_toNat_pos {n : EvmWord} (h : 0 < n.toNat) : n ≠ 0 := by
  intro hc; rw [hc] at h; simp at h

/-- Full `evm_mulmod` dispatch over the `N ≠ 0` arm.

    Entry `base`, exit `base + 2160` (the program exit). The precondition is the
    ambient `evm_mulmod` machine state: `x12 ↦ sp`, the `a`/`b`/`n` argument
    windows (`sp + 0 .. sp + 88`), the eight-cell product scratch window
    (`sp - 160 .. sp - 104`, arbitrary input garbage `p0..p7`), the modular
    accumulator window (`sp - 32 .. sp - 8`, garbage `r0..r3`), and the
    scratch registers `x0, x5 .. x20`. The branch ORs `n`'s four limbs; since
    `0 < n.toNat` forces `n ≠ 0` (hence `orAll ≠ 0`), the zero path is
    unreachable and the body computes the modular product. The result window
    `sp + 64 .. sp + 88` (and the mirror copy in `x5`/`sp - 32 .. sp - 8`)
    holds the limbs of `EvmWord.mulmod a b n`; `x12` advances to `sp + 64`. -/
theorem evm_mulmod_dispatch_evm_mulmod_spec_within
    (sp base : Word) (a b n : EvmWord)
    (v5Old v6Old : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word)
    (hn0 : 0 < n.toNat) :
    cpsTripleWithin (8 + (440 + (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1)))
      base (base + 2160) (evm_mulmod_program_code base)
      -- Ambient pre: branch entry state ** the body's extra resources.
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
      -- Post: result limbs are `EvmWord.mulmod a b n`; everything else is junk.
      (((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
        ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
        regOwn .x9 ** regOwn .x14) **
       ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (((.x5 ↦ᵣ EvmWord.getLimbN (EvmWord.mulmod a b n) 3) **
          ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 0) **
          ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 1) **
          ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 2) **
          ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 3) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 3)) **
         (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
           regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
           regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
          limbChain (sp + signExtend12 (3992 : BitVec 12)) (fun i => productLimb a b (7 - i)) 8)))) := by
  -- R_amb: resources the N ≠ 0 body needs beyond the branch's taken post `Q_t`.
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
  -- The zero path is unreachable: `⌜orAll = 0⌝` contradicts `n ≠ 0`.
  have h_t0 := cpsBranchWithin_takenPath hbr (Q_f := _) ?_h_absurd
  · -- Align the taken-exit address `base + 28 + signExtend13 28 = base + 56`.
    have hexit : base + 28 + signExtend13 (28 : BitVec 13) = base + 56 := by
      rw [BitVec.add_assoc]; congr 1
    rw [hexit] at h_t0
    -- N ≠ 0 body, instantiated with `x5Old := n.getLimbN 3`, `x6Old := orAll`.
    have hbody := evm_mulmod_product_reduce_value_evm_mulmod_spec_within
      sp base a b n p0 p1 p2 p3 p4 p5 p6 p7
      (n.getLimbN 3) (n.getLimbN 0 ||| n.getLimbN 1 ||| n.getLimbN 2 ||| n.getLimbN 3)
      x7Old x8Old x9Old x10Old x11Old x13Old x14Old
      v16Old v18Old r0 r1 r2 r3 hn0
    -- Sequence the taken arm with the body; the midpoint coercion strips the
    -- `⌜orAll ≠ 0⌝` pure fact, normalizes the n-cell addresses, and permutes.
    have hcomp := cpsTripleWithin_seq_perm_same_cr
      (Q1 := _) (Q2 := _)
      (fun h hp => by
        have se72 : signExtend12 (72 : BitVec 12) = (72 : Word) := by decide
        have se80 : signExtend12 (80 : BitVec 12) = (80 : Word) := by decide
        have se88 : signExtend12 (88 : BitVec 12) = (88 : Word) := by decide
        have hp1 := sepConj_mono_left
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right h').1 hp').1)))))))) h hp
        simp only [evmMulModProductLayoutPre, signExtend12_64, se72, se80, se88] at hp1 ⊢
        xperm_hyp hp1)
      h_t0 hbody
    -- Rewrite the result word `BitVec.ofNat 256 (a·b mod n) = EvmWord.mulmod a b n`
    -- and the exit `base + 1816 + 344 = base + 2160`.
    have hne : n ≠ 0 := evmWord_ne_zero_of_toNat_pos hn0
    rw [← EvmWord.mulmod_of_ne_zero a b n hne] at hcomp
    have hexit2 : base + 1816 + 344 = base + 2160 := by
      rw [BitVec.add_assoc]; congr 1
    rw [hexit2] at hcomp
    exact hcomp
  case _h_absurd =>
    intro hp hQf
    obtain ⟨_, _, _, _, hQfL, _⟩ := hQf
    obtain ⟨_, _, _, _, _, r1⟩ := hQfL
    obtain ⟨_, _, _, _, _, r2⟩ := r1
    obtain ⟨_, _, _, _, _, r3⟩ := r2
    obtain ⟨_, _, _, _, _, r4⟩ := r3
    obtain ⟨_, _, _, _, _, r5⟩ := r4
    obtain ⟨_, _, _, _, _, r6⟩ := r5
    obtain ⟨_, _, _, _, _, r7⟩ := r6
    have horall : n.getLimbN 0 ||| n.getLimbN 1 ||| n.getLimbN 2 ||| n.getLimbN 3 = 0 :=
      ((sepConj_pure_right _).1 r7).2
    exact (evmWord_ne_zero_of_toNat_pos hn0) ((orAll_limbs_eq_zero_iff n).1 horall)

end EvmAsm.Evm64.MulMod.Compose
