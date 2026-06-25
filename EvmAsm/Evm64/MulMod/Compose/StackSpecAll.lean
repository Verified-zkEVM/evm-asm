/-
  EvmAsm.Evm64.MulMod.Compose.StackSpecAll

  Stack-level lift of the UNIFIED `evm_mulmod` dispatch spec
  (`evm_mulmod_dispatch_all_evm_mulmod_spec_within`) over BOTH modulus arms.

  The unified dispatch presents the `a` / `b` / `n` argument words and the
  `EvmWord.mulmod a b n` result word as raw limb-level memory atoms. This file
  bundles those four-cell windows into `evmWordIs` predicates, mirroring
  `evm_mulmod_stack_spec_within_nonzero_small` (StackSpec.lean) but built on the
  all-`n` dispatch (`hn : n.toNat ≤ 2^255`, covering `n = 0` and `n ≠ 0`):
    * PRE: `evmWordIs sp a`, `evmWordIs (sp + 32) b`,
      `evmWordIs (sp + signExtend12 64) n`.
    * POST: `evmWordIs (sp + signExtend12 64) (EvmWord.mulmod a b n)`.
  Everything else — the product scratch window, the modular accumulator cells,
  the scratch registers, `x12` — is already abstracted to `memOwn`/`regOwn`
  ownership in the unified dispatch's post, so it simply frames through.

  Proved via `cpsTripleWithin_weaken`: the pre-impl callback unfolds the stated
  `evmWordIs` atoms into the dispatch's raw cells (normalizing the
  `signExtend12` offsets on the `n`-word to plain `sp + 64/72/80/88`) and the
  post-impl callback folds the dispatch's result cells back into the single
  `evmWordIs` result word.
-/

import EvmAsm.Evm64.MulMod.Compose.DispatchAll
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- Stack-level lift of `evm_mulmod_dispatch_all_evm_mulmod_spec_within` over
    BOTH modulus arms (`n.toNat ≤ 2^255`, covering `n = 0` and `n ≠ 0`).

    Identical entry/exit (`base` → `base + 2152`), step bound, and code
    requirement to the unified dispatch spec, but the `a` / `b` / `n` argument
    windows are presented as `evmWordIs` predicates rather than four raw limb
    cells each, and the result window is
    `evmWordIs (sp + signExtend12 64) (EvmWord.mulmod a b n)`. The product
    scratch, modular-accumulator cells, scratch registers and `x12` — already
    abstracted to `memOwn`/`regOwn` ownership in the dispatch's post — pass
    through unchanged as a scratch frame. -/
theorem evm_mulmod_stack_spec_within_small
    (sp base : Word) (a b n : EvmWord)
    (v5Old v6Old : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word)
    (hn : n.toNat ≤ 2 ^ 255) :
    cpsTripleWithin (8 + (440 + (6 + (2 + 64 * 64 + 2 + 1) * 8 + 8 + 1)))
      base (base + 2152) (evm_mulmod_program_code base)
      -- Ambient pre: `a`/`b`/`n` argument words as `evmWordIs`, scratch verbatim.
      (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v5Old) ** (.x5 ↦ᵣ v6Old) ** (.x0 ↦ᵣ 0) **
        evmWordIs (sp + signExtend12 (64 : BitVec 12)) n) **
       (evmWordIs sp a ** evmWordIs (sp + 32) b **
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
      -- Common post: result word as `evmWordIs`, everything else abstracted.
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       evmWordIs (sp + signExtend12 (64 : BitVec 12)) (EvmWord.mulmod a b n) **
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
  have se72 : signExtend12 (72 : BitVec 12) = (72 : Word) := by decide
  have se80 : signExtend12 (80 : BitVec 12) = (80 : Word) := by decide
  have se88 : signExtend12 (88 : BitVec 12) = (88 : Word) := by decide
  exact cpsTripleWithin_weaken
    (fun h hp => by
      -- Pre: unfold the three `evmWordIs` argument words into raw limb cells,
      -- normalizing the `n`-word's `signExtend12` offsets to `sp + 64/72/80/88`.
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl] at hp
      simp only [signExtend12_64] at hp
      rw [evmWordIs_sp64_limbs_eq sp n _ _ _ _ rfl rfl rfl rfl] at hp
      simp only [signExtend12_64, se72, se80, se88] at hp ⊢
      xperm_hyp hp)
    (fun h hq => by
      -- Post: fold the result cells back into `evmWordIs (sp + signExtend12 64)`.
      simp only [signExtend12_64, se72, se80, se88] at hq ⊢
      rw [evmWordIs_sp64_limbs_eq_right sp (EvmWord.mulmod a b n) _ _ _ _ _ rfl rfl rfl rfl] at hq
      xperm_hyp hq)
    (evm_mulmod_dispatch_all_evm_mulmod_spec_within sp base a b n v5Old v6Old
      p0 p1 p2 p3 p4 p5 p6 p7 x7Old x8Old x9Old x10Old x11Old x13Old x14Old
      v16Old v18Old r0 r1 r2 r3 hn)

end EvmAsm.Evm64.MulMod.Compose
