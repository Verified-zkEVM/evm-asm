/-
  EvmAsm.Evm64.MulMod.Compose.DispatchAll

  Unified top-level dispatch composition for the `evm_mulmod` program. Combines
  the two modulus arms — `N ≠ 0` (`Dispatch.lean`) and `N = 0`
  (`DispatchZero.lean`) — into a SINGLE specification whose only modulus
  hypothesis is `n.toNat ≤ 2^255`, covering both cases.

  The proof case-splits on `n = 0`:
  * `n = 0`: invoke `evm_mulmod_dispatch_zero_evm_mulmod_spec_within`, lift its
    small step bound to the program-wide bound, and weaken its (concrete) post
    to the common abstracted post `R`.
  * `n ≠ 0`: derive `0 < n.toNat`, invoke
    `evm_mulmod_dispatch_evm_mulmod_spec_within`, and weaken its post (with the
    `limbChain` product window unfolded to eight explicit cells) to `R`.

  The common post `R` keeps the result window (`sp + 64 .. sp + 88`), the
  argument windows, `x12`, and `x0` concrete (these are identical in both
  arms), and abstracts everything that differs between the arms to
  `memOwn`/`regOwn` ownership: the product scratch window
  (`sp + 96 .. sp + 152`), the modular accumulator window
  (`sp + 224 .. sp + 248`), and the scratch registers
  `x5 .. x11, x13 .. x20`.
-/

import EvmAsm.Evm64.MulMod.Compose.Dispatch
import EvmAsm.Evm64.MulMod.Compose.DispatchZero
import EvmAsm.Evm64.MulMod.Compose.ProductReduceBridge

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- Full `evm_mulmod` dispatch over BOTH modulus arms.

    Entry `base`, exit `base + 2152` (the program exit), step bound the larger
    (N ≠ 0) arm's bound. The precondition is the ambient `evm_mulmod` machine
    state (identical to both per-arm dispatch specs). The only modulus
    hypothesis is `n.toNat ≤ 2^255`.

    The post keeps the result window `sp + 64 .. sp + 88` (limbs of
    `EvmWord.mulmod a b n`), the argument windows, `x12 ↦ sp + 64`, and
    `x0 ↦ 0` concrete; the scratch registers and the product/accumulator
    windows — which differ between the two arms — are abstracted to ownership
    (`regOwn`/`memOwn`). -/
theorem evm_mulmod_dispatch_all_evm_mulmod_spec_within
    (sp base : Word) (a b n : EvmWord)
    (v5Old v6Old : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word)
    (hn : n.toNat ≤ 2 ^ 255) :
    cpsTripleWithin (8 + (440 + (6 + (2 + 64 * 64 + 2 + 1) * 8 + 8 + 1)))
      base (base + 2152) (evm_mulmod_program_code base)
      -- Ambient pre: identical to both per-arm dispatch PREs.
      (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v5Old) ** (.x5 ↦ᵣ v6Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n.getLimbN 0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n.getLimbN 1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n.getLimbN 2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n.getLimbN 3)) **
       ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
        ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ p0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ p1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ p2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7) **
        (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) ** (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) **
        (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) **
        (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) **
        ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ r3) **
        regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20))
      -- Common post `R`: result/args concrete; scratch abstracted to ownership.
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 3) **
       (sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
       ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
       ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
       (.x0 ↦ᵣ (0 : Word)) **
       memOwn (sp + signExtend12 (96 : BitVec 12)) **
       memOwn (sp + signExtend12 (104 : BitVec 12)) **
       memOwn (sp + signExtend12 (112 : BitVec 12)) **
       memOwn (sp + signExtend12 (120 : BitVec 12)) **
       memOwn (sp + signExtend12 (128 : BitVec 12)) **
       memOwn (sp + signExtend12 (136 : BitVec 12)) **
       memOwn (sp + signExtend12 (144 : BitVec 12)) **
       memOwn (sp + signExtend12 (152 : BitVec 12)) **
       memOwn (sp + signExtend12 (224 : BitVec 12)) **
       memOwn (sp + signExtend12 (232 : BitVec 12)) **
       memOwn (sp + signExtend12 (240 : BitVec 12)) **
       memOwn (sp + signExtend12 (248 : BitVec 12)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x9 **
       regOwn .x10 ** regOwn .x11 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
       regOwn .x16 ** regOwn .x17 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20) := by
  by_cases hz : n = 0
  · -- N = 0 arm: lift the step bound, weaken the (concrete) post to `R`.
    refine cpsTripleWithin_weaken (fun _ hp => hp) ?_
      (cpsTripleWithin_mono_nSteps (show (8 + (4 + 1 + 1)) ≤ _ by omega)
        (evm_mulmod_dispatch_zero_evm_mulmod_spec_within sp base a b n v5Old v6Old
          p0 p1 p2 p3 p4 p5 p6 p7 x7Old x8Old x9Old x10Old x11Old x13Old x14Old
          v16Old v18Old r0 r1 r2 r3 hz))
    intro h hp
    -- Weaken each abstract `↦ᵣ`/`↦ₘ` leaf of the zero-arm post to ownership,
    -- keeping the concrete leaves, producing a hypothesis in the zero-arm's
    -- native order; then permute to `R`.
    have hp' :
        (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 3)) **
         regOwn .x6 ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
         ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
         ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
         ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
         memOwn (sp + signExtend12 (96 : BitVec 12)) **
         memOwn (sp + signExtend12 (104 : BitVec 12)) **
         memOwn (sp + signExtend12 (112 : BitVec 12)) **
         memOwn (sp + signExtend12 (120 : BitVec 12)) **
         memOwn (sp + signExtend12 (128 : BitVec 12)) **
         memOwn (sp + signExtend12 (136 : BitVec 12)) **
         memOwn (sp + signExtend12 (144 : BitVec 12)) **
         memOwn (sp + signExtend12 (152 : BitVec 12)) **
         regOwn .x7 ** regOwn .x8 ** regOwn .x9 ** regOwn .x10 **
         regOwn .x11 ** regOwn .x13 ** regOwn .x14 ** regOwn .x16 ** regOwn .x18 **
         memOwn (sp + signExtend12 (224 : BitVec 12)) **
         memOwn (sp + signExtend12 (232 : BitVec 12)) **
         memOwn (sp + signExtend12 (240 : BitVec 12)) **
         memOwn (sp + signExtend12 (248 : BitVec 12)) **
         regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20) h := by
      refine sepConj_mono (fun _ hh => hh) ?_ h hp  -- head group concrete
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x6
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x5
      refine sepConj_mono (fun _ hh => hh) ?_  -- x0 concrete
      refine sepConj_mono (fun _ hh => hh) ?_  -- a0
      refine sepConj_mono (fun _ hh => hh) ?_  -- a1
      refine sepConj_mono (fun _ hh => hh) ?_  -- a2
      refine sepConj_mono (fun _ hh => hh) ?_  -- a3
      refine sepConj_mono (fun _ hh => hh) ?_  -- b0
      refine sepConj_mono (fun _ hh => hh) ?_  -- b1
      refine sepConj_mono (fun _ hh => hh) ?_  -- b2
      refine sepConj_mono (fun _ hh => hh) ?_  -- b3
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p0
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p1
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p2
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p3
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p4
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p5
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p6
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- p7
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x7
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x8
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x9
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x10
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x11
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x13
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x14
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x16
      refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x18
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- r0
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- r1
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- r2
      refine sepConj_mono (memIs_implies_memOwn) ?_  -- r3
      exact fun _ hh => hh  -- regOwn x15 ** regOwn x17 ** regOwn x19 ** regOwn x20
    xperm_hyp hp'
  · -- N ≠ 0 arm.
    have hn0 : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h | h
      · exact absurd (by rw [← BitVec.toNat_inj]; simpa using h) hz
      · exact h
    refine cpsTripleWithin_weaken (fun _ hp => hp) ?_
      (evm_mulmod_dispatch_evm_mulmod_spec_within sp base a b n v5Old v6Old
        p0 p1 p2 p3 p4 p5 p6 p7 x7Old x8Old x9Old x10Old x11Old x13Old x14Old
        v16Old v18Old r0 r1 r2 r3 hn0 hn)
    intro h hp
    -- Unfold the product window `limbChain` to eight explicit cells, then
    -- convert each abstract leaf to ownership.
    rw [limbChain_productLimb_eq] at hp
    -- Weaken each abstract leaf of the (rewritten) N ≠ 0 post to ownership,
    -- preserving the post's native tree shape; then permute to `R`.
    have hp' :
        -- G1 (a/b cells + regOwn x8/x9/x14, unchanged)
        (((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
          ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
          ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
          ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x14) **
         (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
         -- G3 (x5, accumulator window, result window)
         (regOwn .x5 **
          memOwn (sp + signExtend12 (224 : BitVec 12)) **
          memOwn (sp + signExtend12 (232 : BitVec 12)) **
          memOwn (sp + signExtend12 (240 : BitVec 12)) **
          memOwn (sp + signExtend12 (248 : BitVec 12)) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (EvmWord.mulmod a b n) 3)) **
         -- G4 registers
         ((regOwn .x15 ** (.x0 ↦ᵣ (0 : Word)) **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           regOwn .x13 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20 **
           regOwn .x16 ** regOwn .x18) **
          -- product window
          (memOwn (sp + signExtend12 (152 : BitVec 12)) **
           memOwn (sp + signExtend12 (144 : BitVec 12)) **
           memOwn (sp + signExtend12 (136 : BitVec 12)) **
           memOwn (sp + signExtend12 (128 : BitVec 12)) **
           memOwn (sp + signExtend12 (120 : BitVec 12)) **
           memOwn (sp + signExtend12 (112 : BitVec 12)) **
           memOwn (sp + signExtend12 (104 : BitVec 12)) **
           memOwn (sp + signExtend12 (96 : BitVec 12))))) h := by
      -- top: G1 ** (x12 ** (G3 ** (G4regs ** prod)))
      refine sepConj_mono ?_ ?_ h hp
      · -- G1: 8 concrete mem cells then regOwn x8/x9/x14 (already Own)
        refine sepConj_mono (fun _ hh => hh) ?_  -- a0
        refine sepConj_mono (fun _ hh => hh) ?_  -- a1
        refine sepConj_mono (fun _ hh => hh) ?_  -- a2
        refine sepConj_mono (fun _ hh => hh) ?_  -- a3
        refine sepConj_mono (fun _ hh => hh) ?_  -- b0
        refine sepConj_mono (fun _ hh => hh) ?_  -- b1
        refine sepConj_mono (fun _ hh => hh) ?_  -- b2
        refine sepConj_mono (fun _ hh => hh) ?_  -- b3
        exact fun _ hh => hh  -- regOwn x8 ** regOwn x9 ** regOwn x14
      · -- x12 ** (G3 ** (G4regs ** prod))
        refine sepConj_mono (fun _ hh => hh) ?_  -- x12 concrete
        refine sepConj_mono ?_ ?_  -- G3 ** (G4regs ** prod)
        · -- G3: x5 (→regOwn), 4 mem (→memOwn), 4 result cells (concrete)
          refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x5
          refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+224
          refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+232
          refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+240
          refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+248
          refine sepConj_mono (fun _ hh => hh) ?_  -- sp+64 result
          refine sepConj_mono (fun _ hh => hh) ?_  -- sp+72
          refine sepConj_mono (fun _ hh => hh) ?_  -- sp+80
          exact fun _ hh => hh  -- sp+88
        · -- G4regs ** prod
          refine sepConj_mono ?_ ?_  -- G4regs ** prod
          · -- G4regs: x15 (→regOwn), x0 (concrete), then 10 regOwn already-Own
            refine sepConj_mono (regIs_implies_regOwn _) ?_  -- x15
            refine sepConj_mono (fun _ hh => hh) ?_  -- x0 concrete
            exact fun _ hh => hh  -- regOwn x6..x18 chain (already Own)
          · -- product window: 8 mem cells → memOwn
            refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+152
            refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+144
            refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+136
            refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+128
            refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+120
            refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+112
            refine sepConj_mono (memIs_implies_memOwn) ?_  -- sp+104
            exact memIs_implies_memOwn  -- sp+96
    xperm_hyp hp'

end EvmAsm.Evm64.MulMod.Compose
