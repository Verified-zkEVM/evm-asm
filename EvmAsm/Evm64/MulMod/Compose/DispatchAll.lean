/-
  EvmAsm.Evm64.MulMod.Compose.DispatchAll

  Top-level dispatch composition for the `evm_mulmod` program over **all**
  moduli `n` (no hypothesis). The two dispatch arms
  (`evm_mulmod_dispatch_evm_mulmod_spec_within`, `0 < n.toNat`, and
  `evm_mulmod_dispatch_zero_evm_mulmod_spec_within`, `n = 0`) are weakened to a
  common abstracted postcondition `evmMulModDispatchPost sp a b n` — the result
  word `EvmWord.mulmod a b n` at `sp + 64` stays precise, while every scratch
  register and clobbered stack cell is forgotten as `regOwn`/`memOwn`. A
  `by_cases n = 0` then combines the arms unconditionally.

  Both arms share the same entry `base`, exit `base + 2160` (the program exit),
  precondition (the ambient `evm_mulmod` machine state), and result word, so the
  merge needs no `n ≤ 2^255` restriction now that the reducer is carry-aware.
  The two arms have different step bounds; the smaller `n = 0` bound is widened
  to the larger `n ≠ 0` bound with `cpsTripleWithin_mono_nSteps`.
-/

import EvmAsm.Evm64.MulMod.Compose.Dispatch
import EvmAsm.Evm64.MulMod.Compose.DispatchZero
import EvmAsm.Evm64.MulMod.Compose.ProductReduceBridge
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- The ambient `evm_mulmod` machine state at program entry, shared by both
    dispatch arms. Verbatim copy of the dispatch arms' precondition. -/
@[irreducible]
def evmMulModDispatchPre (sp : Word) (a b n : EvmWord)
    (v5Old v6Old : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word) : Assertion :=
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v5Old) ** (.x5 ↦ᵣ v6Old) ** (.x0 ↦ᵣ 0) **
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
    regOwn .x15 ** regOwn .x17 ** regOwn .x19 ** regOwn .x20)

/-- Abstracted dispatch postcondition shared by both arms.

    The result word `EvmWord.mulmod a b n` sits at `sp + signExtend12 64` as a
    precise `evmWordIs`; `x12` advances to `sp + signExtend12 64`. Every other
    clobbered resource — the 16 scratch registers, the `a`/`b` argument window
    (`sp .. sp + 56`), the eight-cell product scratch window
    (`sp - 160 .. sp - 104`), and the modular accumulator window
    (`sp - 32 .. sp - 8`) — is forgotten as `regOwn`/`memOwn`.

    Bundled `@[irreducible]` so consumers see a handful of opaque atoms. -/
@[irreducible]
def evmMulModDispatchPost (sp : Word) (a b n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
  evmWordIs (sp + signExtend12 (64 : BitVec 12)) (EvmWord.mulmod a b n) **
  regOwn .x0 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 **
  regOwn .x9 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** regOwn .x18 ** regOwn .x19 **
  regOwn .x20 **
  memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** memOwn (sp + 24) **
  memOwn (sp + 32) ** memOwn (sp + 40) ** memOwn (sp + 48) ** memOwn (sp + 56) **
  memOwn (sp + signExtend12 (3936 : BitVec 12)) **
  memOwn (sp + signExtend12 (3944 : BitVec 12)) **
  memOwn (sp + signExtend12 (3952 : BitVec 12)) **
  memOwn (sp + signExtend12 (3960 : BitVec 12)) **
  memOwn (sp + signExtend12 (3968 : BitVec 12)) **
  memOwn (sp + signExtend12 (3976 : BitVec 12)) **
  memOwn (sp + signExtend12 (3984 : BitVec 12)) **
  memOwn (sp + signExtend12 (3992 : BitVec 12)) **
  memOwn (sp + signExtend12 (4064 : BitVec 12)) **
  memOwn (sp + signExtend12 (4072 : BitVec 12)) **
  memOwn (sp + signExtend12 (4080 : BitVec 12)) **
  memOwn (sp + signExtend12 (4088 : BitVec 12))

/-- Full `evm_mulmod` dispatch over **all** moduli `n` (no hypothesis).

    Entry `base`, exit `base + 2160` (the program exit). From the ambient
    machine state `evmMulModDispatchPre`, the program leaves
    `evmMulModDispatchPost`: the result word `EvmWord.mulmod a b n` at
    `sp + 64` as `evmWordIs` with everything else forgotten as scratch.
    Combines the `n ≠ 0` and `n = 0` arms by `by_cases n = 0`; total now that
    the reducer is carry-aware. -/
theorem evm_mulmod_dispatch_all_evm_mulmod_spec_within
    (sp base : Word) (a b n : EvmWord)
    (v5Old v6Old : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word) :
    cpsTripleWithin (8 + (440 + (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1)))
      base (base + 2160) (evm_mulmod_program_code base)
      (evmMulModDispatchPre sp a b n v5Old v6Old p0 p1 p2 p3 p4 p5 p6 p7
        x7Old x8Old x9Old x10Old x11Old x13Old x14Old v16Old v18Old r0 r1 r2 r3)
      (evmMulModDispatchPost sp a b n) := by
  have se72 : signExtend12 (72 : BitVec 12) = (72 : Word) := by decide
  have se80 : signExtend12 (80 : BitVec 12) = (80 : Word) := by decide
  have se88 : signExtend12 (88 : BitVec 12) = (88 : Word) := by decide
  by_cases hnz : n = 0
  · -- N = 0 arm: widen the small step bound up to the N ≠ 0 bound.
    have harm : cpsTripleWithin (8 + (440 + (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1)))
        base (base + 2160) (evm_mulmod_program_code base) _ _ :=
      cpsTripleWithin_mono_nSteps (by decide)
      (evm_mulmod_dispatch_zero_evm_mulmod_spec_within sp base a b n v5Old v6Old
        p0 p1 p2 p3 p4 p5 p6 p7 x7Old x8Old x9Old x10Old x11Old x13Old x14Old
        v16Old v18Old r0 r1 r2 r3 hnz)
    refine cpsTripleWithin_weaken (fun h hp => by
        unfold evmMulModDispatchPre at hp; xperm_hyp hp) ?_ harm
    intro h hq
    -- Fold the zeroed result cells into `evmWordIs (sp + 64) (mulmod a b n)`.
    simp only [signExtend12_64, se72, se80, se88] at hq
    rw [← evmWordIs_sp64_limbs_eq sp (EvmWord.mulmod a b n) _ _ _ _ rfl rfl rfl rfl] at hq
    -- Forget every concrete scratch register/cell (regIs → regOwn, memIs → memOwn)
    -- in native order; the trailing `regOwn x15/x17/x19/x20` pass through identity.
    replace hq := sepConj_mono_right (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn ((fun _ x => x)))))))))))))))))))))))))))))))))) h hq
    show evmMulModDispatchPost sp a b n h
    unfold evmMulModDispatchPost
    simp only [signExtend12_64]
    xperm_hyp hq
  · -- N ≠ 0 arm.
    have hn0 : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h | h
      · exact absurd (by rw [← BitVec.toNat_inj]; simpa using h) hnz
      · exact h
    have harm := evm_mulmod_dispatch_evm_mulmod_spec_within sp base a b n v5Old v6Old
      p0 p1 p2 p3 p4 p5 p6 p7 x7Old x8Old x9Old x10Old x11Old x13Old x14Old
      v16Old v18Old r0 r1 r2 r3 hn0
    refine cpsTripleWithin_weaken (fun h hp => by
        unfold evmMulModDispatchPre at hp; xperm_hyp hp) ?_ harm
    intro h hq
    -- Unfold the product `limbChain` window into eight explicit cells, then fold
    -- the result cells into `evmWordIs`.
    simp only [limbChain_productLimb_eq, signExtend12_64, se72, se80, se88] at hq
    rw [← evmWordIs_sp64_limbs_eq sp (EvmWord.mulmod a b n) _ _ _ _ rfl rfl rfl rfl] at hq
    -- Forget every concrete scratch register/cell, navigating the arm's nested
    -- post tree: G1 (a/b cells + regOwn x9,x14), x12, G2 (x5 + accum cells +
    -- evmWordIs), G3 (x15,x0 + regOwn …), G4 (product cells).
    replace hq := sepConj_mono
      (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn ((fun _ x => x))))))))))
      (sepConj_mono (fun _ x => x)
        (sepConj_mono
          (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn ((fun _ x => x)))))))
          (sepConj_mono
            (sepConj_mono (regIs_to_regOwn _ _) (sepConj_mono (regIs_to_regOwn _ _) ((fun _ x => x))))
            (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn (memIs_implies_memOwn))))))))))) h hq
    show evmMulModDispatchPost sp a b n h
    unfold evmMulModDispatchPost
    simp only [signExtend12_64]
    xperm_hyp hq

end EvmAsm.Evm64.MulMod.Compose
