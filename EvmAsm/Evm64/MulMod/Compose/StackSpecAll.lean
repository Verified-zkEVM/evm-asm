/-
  EvmAsm.Evm64.MulMod.Compose.StackSpecAll

  Total (hypothesis-free, all-`n`) stack-level spec for `evm_mulmod`.

  Lifts `evm_mulmod_dispatch_all_evm_mulmod_spec_within` (the unconditional
  both-arms dispatch) to present the `a` / `b` / `n` argument words as
  `evmWordIs` predicates rather than four raw limb cells each. The result word
  is already exposed as `evmWordIs (sp + signExtend12 64) (EvmWord.mulmod a b n)`
  by the abstracted `evmMulModDispatchPost`.

  This is the headline MULMOD contract: for **every** modulus `n` (including
  `n = 0`, where `EvmWord.mulmod a b 0 = 0`, and `n > 2^255`, now that the
  reducer is carry-aware), running `evm_mulmod` from `base` reaches the program
  exit `base + 2160` leaving `(a · b) mod n` on the stack top.
-/

import EvmAsm.Evm64.MulMod.Compose.DispatchAll
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- Total stack-level MULMOD spec — **hypothesis-free, all `n`**.

    Entry `base`, exit `base + 2160` (the program exit), over
    `evm_mulmod_program_code base`. The `a` / `b` / `n` argument words are
    presented as `evmWordIs sp a`, `evmWordIs (sp + 32) b`,
    `evmWordIs (sp + signExtend12 64) n`; the scratch product window
    (`sp - 160 .. sp - 104`), modular-accumulator cells (`sp - 32 .. sp - 8`),
    and scratch registers (`x0, x5 .. x20`) pass through as a frame. On exit the
    stack top holds `evmWordIs (sp + signExtend12 64) (EvmWord.mulmod a b n)` and
    everything else is forgotten as `regOwn`/`memOwn` (`evmMulModDispatchPost`).

    Total: no `0 < n.toNat` and no `n ≤ 2^255` hypothesis — the carry-aware
    reducer computes `(a · b) mod n` for every `n`, and the `n = 0` arm yields
    `EvmWord.mulmod a b 0 = 0`. -/
theorem evm_mulmod_stack_spec_within
    (sp base : Word) (a b n : EvmWord)
    (v5Old v6Old : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word) :
    cpsTripleWithin (8 + (440 + (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1)))
      base (base + 2160) (evm_mulmod_program_code base)
      -- Ambient pre: `a`/`b`/`n` argument words as `evmWordIs`, scratch verbatim.
      (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v5Old) ** (.x5 ↦ᵣ v6Old) ** (.x0 ↦ᵣ 0) **
        evmWordIs (sp + signExtend12 (64 : BitVec 12)) n) **
       (evmWordIs sp a ** evmWordIs (sp + 32) b **
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
      (evmMulModDispatchPost sp a b n) := by
  have se72 : signExtend12 (72 : BitVec 12) = (72 : Word) := by decide
  have se80 : signExtend12 (80 : BitVec 12) = (80 : Word) := by decide
  have se88 : signExtend12 (88 : BitVec 12) = (88 : Word) := by decide
  refine cpsTripleWithin_weaken (fun h hp => by
      -- Pre: unfold the three `evmWordIs` argument words into raw limb cells,
      -- normalizing the `n`-word's `signExtend12` offsets to `sp + 64/72/80/88`,
      -- then permute into `evmMulModDispatchPre`.
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl] at hp
      simp only [signExtend12_64] at hp
      rw [evmWordIs_sp64_limbs_eq sp n _ _ _ _ rfl rfl rfl rfl] at hp
      unfold evmMulModDispatchPre
      simp only [signExtend12_64, se72, se80, se88]
      xperm_hyp hp)
    (fun _ hq => hq)
    (evm_mulmod_dispatch_all_evm_mulmod_spec_within sp base a b n v5Old v6Old
      p0 p1 p2 p3 p4 p5 p6 p7 x7Old x8Old x9Old x10Old x11Old x13Old x14Old
      v16Old v18Old r0 r1 r2 r3)

end EvmAsm.Evm64.MulMod.Compose
