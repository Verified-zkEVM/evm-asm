/-
  EvmAsm.Evm64.MulMod.Compose.ProductReduce

  Compose `product_layout ;; reduce512` into a single `cpsTripleWithin` over the
  full `evm_mulmod_program_code`: the N ≠ 0 body that computes the 512-bit
  product (`evm_mulmod_product_layout`, offset `base + 56`) and reduces it
  modulo `n` (`evm_mulmod_reduce512`, offset `base + 1816`).

  The two specs meet at the midpoint `(base + 56) + 1760 = base + 1816`. The
  only structural difference between `product_layout`'s output and
  `reduce512`'s input is the product window: `product_layout` exposes it as the
  eight explicit memory cells `sp - 160 .. sp - 104`, while `reduce512` consumes
  it as `limbChain (sp - 104) (fun i => productLimb a b (7 - i)) 8`. The merged
  bridge `limbChain_productLimb_eq` [A1] rewrites the `limbChain` window into the
  explicit cells, after which both intermediate assertions are permutations of
  the same `**` multiset and `xperm_hyp` closes the midpoint coercion.
-/

import EvmAsm.Evm64.MulMod.Compose.Reducer
import EvmAsm.Evm64.MulMod.Compose.ProductReduceBridge

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

set_option linter.unusedSimpArgs false in
/-- Compose the product-layout body with the 512-bit reducer into a single
    spec over `evm_mulmod_program_code`, covering the N ≠ 0 path from product
    construction through modular reduction. The product window emitted by
    `product_layout` is consumed by `reduce512` via `limbChain_productLimb_eq`
    instantiated at `limbs := fun i => productLimb a b (7 - i)`. -/
theorem evm_mulmod_product_reduce_evm_mulmod_spec_within
    (sp base : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word) :
    cpsTripleWithin (440 + (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1))
      (base + 56) ((base + 1816) + 344) (evm_mulmod_program_code base)
      ((evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
        ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
         (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
         (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old))) **
       ((.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
        regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20))
      (((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
        ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
        regOwn .x9 ** regOwn .x14) **
       ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (((.x5 ↦ᵣ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 3) **
          ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 0) **
          ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 1) **
          ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 2) **
          ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 3) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) (0 : EvmWord) 8) 3)) **
         (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
           regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
           regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
          limbChain (sp + signExtend12 (3992 : BitVec 12)) (fun i => productLimb a b (7 - i)) 8)))) := by
  -- Frame onto the product-layout spec the resources `reduce512` needs that
  -- `product_layout` does not touch (`F1`).
  have h1 := cpsTripleWithin_frameR
    ((.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
     ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
     ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
     ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
     ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
     regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20)
    (by pcFree)
    (evm_mulmod_product_layout_evm_mulmod_spec_within sp base a b n
      p0 p1 p2 p3 p4 p5 p6 p7
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
  -- Frame onto the reducer spec the resources `product_layout` produces but
  -- `reduce512` does not consume (`F2`).
  have h2 := cpsTripleWithin_frameL
    ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
     ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
     ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
     ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
     regOwn .x9 ** regOwn .x14)
    (by pcFree)
    (evm_mulmod_reduce512_evm_mulmod_spec_within sp base
      v16Old v18Old r0 r1 r2 r3 n (fun i => productLimb a b (7 - i)))
  -- Align the midpoint: `(base + 56) + 1760 = base + 1816`.
  have hmid : (base + 56) + 1760 = base + 1816 := by
    rw [BitVec.add_assoc]; congr 1
  rw [hmid] at h1
  -- Normalize the n-cell addresses `sp + signExtend12 N` (N ∈ {72,80,88}) to the
  -- plain-`Word` form `sp + N` used by `product_layout`'s output. `signExtend12 64`
  -- already has a `@[simp]` lemma; the other three reduce by `decide`.
  have se72 : signExtend12 (72 : BitVec 12) = (72 : Word) := by decide
  have se80 : signExtend12 (80 : BitVec 12) = (80 : Word) := by decide
  have se88 : signExtend12 (88 : BitVec 12) = (88 : Word) := by decide
  -- The intermediate assertions are permutations of the same multiset after
  -- rewriting the reducer's `limbChain` window into the explicit product cells.
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [evmMulModProductLayoutPost, evmMulModProductLayoutScratchPost,
        limbChain_productLimb_eq, signExtend12_64, se72, se80, se88] at hp ⊢
      xperm_hyp hp)
    h1 h2

end EvmAsm.Evm64.MulMod.Compose
