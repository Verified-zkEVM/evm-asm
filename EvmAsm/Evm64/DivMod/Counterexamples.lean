/-
  EvmAsm.Evm64.DivMod.Counterexamples

  Kernel-checked regression pins for the two n4 call-addback counterexamples
  that motivated the div128 v4 migration.
-/

import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4
import EvmAsm.Evm64.DivMod.Spec.CallAddback
import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime
import EvmAsm.Evm64.DivMod.Spec.N2QuotientStackBridge
import EvmAsm.Evm64.DivMod.Spec.N3QuotientStackBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

namespace DivModCounterexamples

-- The executable DIV/MOD programs must keep the v4 div128 subroutine wired in.
theorem evm_div_uses_div128_v4 :
    evm_div =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) := rfl

theorem evm_mod_uses_div128_v4 :
    evm_mod =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_mod_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) := rfl

theorem evm_div_callable_uses_div128_v4 :
    evm_div_callable =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      cc_ret ;;
      divK_div128_v4) := rfl

theorem evm_mod_callable_uses_div128_v4 :
    evm_mod_callable =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_mod_epilogue 24 ;;
      divK_zeroPath ;;
      cc_ret ;;
      divK_div128_v4) := rfl

theorem evm_div_callable_v4_uses_div128_v4 :
    evm_div_callable_v4 =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      cc_ret ;;
      divK_div128_v4) := rfl

theorem evm_mod_callable_v4_uses_div128_v4 :
    evm_mod_callable_v4 =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_mod_epilogue 24 ;;
      divK_zeroPath ;;
      cc_ret ;;
      divK_div128_v4) := rfl

-- Counterexample A:
--   a3 = 2^63 + 2^33, a2 = a1 = a0 = 0
--   b3 = 1, b2 = 2^33 - 1, b1 = b0 = 0
--   q_true = 2^63 + 2^32 - 2
abbrev ceA_a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
abbrev ceA_b2 : Word := BitVec.ofNat 64 (2^33 - 1)
abbrev ceA_b3 : Word := BitVec.ofNat 64 1
abbrev ceA_b3Norm : Word := (ceA_b3 <<< 63) ||| (ceA_b2 >>> 1)
abbrev ceA_u4 : Word := ceA_a3 >>> 1
abbrev ceA_u3 : Word := ceA_a3 <<< 63
abbrev ceA_qTrue : Nat := 2^63 + 2^32 - 2
abbrev ceA_qHatV4 : Word := BitVec.ofNat 64 (ceA_qTrue + 1)
abbrev ceA_a : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => ceA_a3
abbrev ceA_b : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => 0 | 1 => 0 | 2 => ceA_b2 | 3 => ceA_b3

theorem div128Quot_v4_counterexampleA_exact :
    div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm = ceA_qHatV4 := by
  decide

theorem div128Quot_v4_counterexampleA_within_two_addbacks :
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat ≤ ceA_qTrue + 2 := by
  decide

/-- Counterexample A satisfies the v4 call/un21 guard used by the exact
    128/64 quotient route. The v4 trial quotient is exact for the normalized
    128/64 division, while still one above the full val256 quotient pinned by
    `ceA_qTrue`. -/
theorem div128Quot_v4_counterexampleA_floor_of_un21_lt_vTop :
    ceA_b3 ≠ 0 ∧
    (clzResult ceA_b3).1 ≠ 0 ∧
    isCallTrialN4 ceA_a3 ceA_b2 ceA_b3 ∧
    (divKTrialCallV4Un21 ceA_u4 ceA_u3 ceA_b3Norm).toNat < ceA_b3Norm.toNat ∧
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat =
      (ceA_u4.toNat * 2^64 + ceA_u3.toNat) / ceA_b3Norm.toNat ∧
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat = ceA_qTrue + 1 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide⟩
  · unfold isCallTrialN4
    decide
  · rw [← BitVec.lt_def]
    simp only [ceA_u4, ceA_u3, ceA_b3Norm, ceA_b3, ceA_b2, ceA_a3,
      divKTrialCallV4Un21, divKTrialCallV4Un1, divKTrialCallV4Q1dd,
      divKTrialCallV4Rhatdd, divKTrialCallV4DLo, divKTrialCallV4DHi,
      rv64_divu, signExtend12]
    decide

theorem n4CallAddbackBeqSemanticHolds_counterexampleA_v4 :
    n4CallAddbackBeqSemanticHolds ceA_a ceA_b := by
  rw [n4CallAddbackBeqSemantic_unfold]
  decide

/-- Counterexample A satisfies the runtime-only premise shape targeted by the
    final n=4 call-addback semantic discharger. -/
theorem ceA_runtime_only_premises :
    ceA_b.getLimbN 3 ≠ 0 ∧
    (clzResult (ceA_b.getLimbN 3)).1 ≠ 0 ∧
    isCallTrialN4Evm ceA_a ceA_b ∧
    isAddbackBorrowN4CallV4Evm ceA_a ceA_b ∧
    isAddbackCarry2NzN4CallV4Evm ceA_a ceA_b := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · rw [isCallTrialN4Evm_def]
    unfold isCallTrialN4
    decide
  · rw [isAddbackBorrowN4CallV4Evm_def,
        show ceA_a.getLimbN 0 = 0 from rfl, show ceA_a.getLimbN 1 = 0 from rfl,
        show ceA_a.getLimbN 2 = 0 from rfl,
        show ceA_a.getLimbN 3 = BitVec.ofNat 64 9223372045444710400 from rfl,
        show ceA_b.getLimbN 0 = 0 from rfl, show ceA_b.getLimbN 1 = 0 from rfl,
        show ceA_b.getLimbN 2 = BitVec.ofNat 64 8589934591 from rfl,
        show ceA_b.getLimbN 3 = 1 from rfl]
    simp only [isAddbackBorrowN4CallV4Ab, show (clzResult (1 : Word)).1 = 63#64 from by decide,
      signExtend12, loopBodyN4CallAddbackBorrowV4, divKTrialCallV4QHat, divKTrialCallV4Q1dd,
      divKTrialCallV4Q0dd, divKTrialCallV4Q0d, divKTrialCallV4Q0c, divKTrialCallV4Rhatdd,
      divKTrialCallV4Rhat2d, divKTrialCallV4Rhat2c, divKTrialCallV4Un21, divKTrialCallV4Un1,
      divKTrialCallV4Un0, divKTrialCallV4DHi, divKTrialCallV4DLo, div128Quot_phase2b_q0',
      mulsubN4_c3, mulsubN4, rv64_divu, rv64_mulhu]
    decide
  · rw [isAddbackCarry2NzN4CallV4Evm_def,
        show ceA_a.getLimbN 0 = 0 from rfl, show ceA_a.getLimbN 1 = 0 from rfl,
        show ceA_a.getLimbN 2 = 0 from rfl,
        show ceA_a.getLimbN 3 = BitVec.ofNat 64 9223372045444710400 from rfl,
        show ceA_b.getLimbN 0 = 0 from rfl, show ceA_b.getLimbN 1 = 0 from rfl,
        show ceA_b.getLimbN 2 = BitVec.ofNat 64 8589934591 from rfl,
        show ceA_b.getLimbN 3 = 1 from rfl]
    simp only [isAddbackCarry2NzN4CallV4Ab, show (clzResult (1 : Word)).1 = 63#64 from by decide,
      signExtend12, loopBodyN4CallAddbackCarry2NzV4, divKTrialCallV4QHat, divKTrialCallV4Q1dd,
      divKTrialCallV4Q0dd, divKTrialCallV4Q0d, divKTrialCallV4Q0c, divKTrialCallV4Rhatdd,
      divKTrialCallV4Rhat2d, divKTrialCallV4Rhat2c, divKTrialCallV4Un21, divKTrialCallV4Un1,
      divKTrialCallV4Un0, divKTrialCallV4DHi, divKTrialCallV4DLo, div128Quot_phase2b_q0',
      mulsubN4, addbackN4_carry, addbackN4, rv64_divu, rv64_mulhu]
    decide

/-- Counterexample A also satisfies the repaired semantic marker. This keeps the
    runtime-only target honest: the remaining work is proving the semantic
    marker directly, not routing through the stronger compact bounds package. -/
theorem ceA_n4CallAddbackBeqSemanticHoldsV4 :
    n4CallAddbackBeqSemanticHoldsV4 ceA_a ceA_b := by
  rw [n4CallAddbackBeqSemanticHoldsV4]
  decide

/-- Counterexample A satisfies the corrected-remainder half of the compact
    runtime-bounds package. -/
theorem ceA_n4CallAddbackBeqIterRNormVal_lt :
    n4CallAddbackBeqIterRNormVal ceA_a ceA_b < n4CallAddbackBeqBNormVal ceA_b := by
  rw [n4CallAddbackBeqIterRNormVal, n4CallAddbackBeqBNormVal]
  decide

/-- Counterexample A fails the compact qhat upper-bound conjunct. This is the
    precise part of the old runtime-bounds package that the repaired semantic
    route must not assume from runtime predicates alone. -/
theorem ceA_n4CallAddbackBeqQHat_compact_bound_false :
    ¬ ((n4CallAddbackBeqQHatV4 ceA_a ceA_b).toNat ≤
        n4CallAddbackBeqULoNormVal ceA_a ceA_b / n4CallAddbackBeqBNormVal ceA_b + 1) := by
  rw [n4CallAddbackBeqULoNormVal, n4CallAddbackBeqBNormVal]
  decide

/-- Counterexample A does not satisfy the current compact runtime-bounds package.
    Therefore the final runtime-only discharger cannot soundly close by deriving
    `n4CallAddbackBeqRuntimeBounds` from only the call/addback runtime predicates. -/
theorem ceA_n4CallAddbackBeqRuntimeBounds_false :
    ¬ n4CallAddbackBeqRuntimeBounds ceA_a ceA_b := by
  rw [n4CallAddbackBeqRuntimeBounds]
  decide

/-- The runtime-only premise shape alone is not enough to recover the compact
    runtime-bounds package used by older semantic bridges. -/
theorem runtime_only_premises_do_not_imply_runtime_bounds :
    ∃ a b : EvmWord,
      b.getLimbN 3 ≠ 0 ∧
      (clzResult (b.getLimbN 3)).1 ≠ 0 ∧
      isCallTrialN4Evm a b ∧
      isAddbackBorrowN4CallV4Evm a b ∧
      isAddbackCarry2NzN4CallV4Evm a b ∧
      ¬ n4CallAddbackBeqRuntimeBounds a b :=
  ⟨ceA_a, ceA_b,
    ceA_runtime_only_premises.1,
    ceA_runtime_only_premises.2.1,
    ceA_runtime_only_premises.2.2.1,
    ceA_runtime_only_premises.2.2.2.1,
    ceA_runtime_only_premises.2.2.2.2,
    ceA_n4CallAddbackBeqRuntimeBounds_false⟩

/-- Even adding the repaired semantic marker to the runtime-only premise shape does
    not recover the old compact runtime-bounds package. The repaired marker is
    therefore a replacement target, not a route back through that package. -/
theorem runtime_only_semantic_do_not_imply_runtime_bounds :
    ∃ a b : EvmWord,
      b.getLimbN 3 ≠ 0 ∧
      (clzResult (b.getLimbN 3)).1 ≠ 0 ∧
      isCallTrialN4Evm a b ∧
      isAddbackBorrowN4CallV4Evm a b ∧
      isAddbackCarry2NzN4CallV4Evm a b ∧
      n4CallAddbackBeqSemanticHoldsV4 a b ∧
      ¬ n4CallAddbackBeqRuntimeBounds a b :=
  ⟨ceA_a, ceA_b,
    ceA_runtime_only_premises.1,
    ceA_runtime_only_premises.2.1,
    ceA_runtime_only_premises.2.2.1,
    ceA_runtime_only_premises.2.2.2.1,
    ceA_runtime_only_premises.2.2.2.2,
    ceA_n4CallAddbackBeqSemanticHoldsV4,
    ceA_n4CallAddbackBeqRuntimeBounds_false⟩

/-- Per-counterexample regression pin: the executable DIV body is on the v4
    path, and the normalized trial quotient for counterexample A has the v4
    bounded-overshoot shape. -/
theorem evm_div_counterexampleA_v4_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm = ceA_qHatV4 ∧
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat ≤ ceA_qTrue + 2 := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor <;> decide

-- Counterexample B:
--   a3 = 2^64 - 2, a2 = a1 = a0 = 0
--   b3 = 1, b2 = 2^64 - 2, b1 = b0 = 0
--   q_true = floor(val256(a) / val256(b)) = 2^63 - 1
abbrev ceB_a3 : Word := BitVec.ofNat 64 (2^64 - 2)
abbrev ceB_b2 : Word := BitVec.ofNat 64 (2^64 - 2)
abbrev ceB_b3 : Word := BitVec.ofNat 64 1
abbrev ceB_b3Norm : Word := (ceB_b3 <<< 63) ||| (ceB_b2 >>> 1)
abbrev ceB_u4 : Word := ceB_a3 >>> 1
abbrev ceB_u3 : Word := ceB_a3 <<< 63
abbrev ceB_qTrue : Nat := 2^63 - 1
abbrev ceB_qHatV4 : Word := BitVec.ofNat 64 ceB_qTrue

theorem div128Quot_v4_counterexampleB_exact :
    div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm = ceB_qHatV4 := by
  decide

theorem div128Quot_v4_counterexampleB_within_two_addbacks :
    (div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm).toNat ≤ ceB_qTrue + 2 := by
  decide

/-- Per-counterexample regression pin: the executable DIV body is on the v4
    path, and the normalized trial quotient for counterexample B has the v4
    exact quotient shape. -/
theorem evm_div_counterexampleB_v4_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm = ceB_qHatV4 ∧
    (div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm).toNat ≤ ceB_qTrue + 2 := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor <;> decide

-- N1 universal-carry counterexample:
--   b0 = 2^63 - 1, b1 = b2 = b3 = 0, shift = 1
--   qHat = u0 = u1 = u2 = u3 = 2^64 - 1, uTop = 0
--
-- This does not exercise a reachable runtime state of the v4 program. It pins
-- the proof-shape failure: `Carry2NzAll` is too strong when quantified over
-- arbitrary qHat/u states, even for a normalized one-limb divisor.
abbrev ceN1CarryB0 : Word := BitVec.ofNat 64 (2^63 - 1)
abbrev ceN1CarryNormB0 : Word :=
  ceN1CarryB0 <<< (((clzResult ceN1CarryB0).1).toNat % 64)
abbrev ceN1CarryMaxWord : Word := BitVec.ofNat 64 (2^64 - 1)
abbrev ceN1CarryMs :=
  mulsubN4 ceN1CarryMaxWord ceN1CarryNormB0 0 0 0
    ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord
abbrev ceN1CarryAb :=
  addbackN4 ceN1CarryMs.1 ceN1CarryMs.2.1 ceN1CarryMs.2.2.1
    ceN1CarryMs.2.2.2.1 (0 - ceN1CarryMs.2.2.2.2)
    ceN1CarryNormB0 0 0 0

theorem ceN1Carry_norm_eq :
    ceN1CarryNormB0 = BitVec.ofNat 64 (2^64 - 2) := by
  decide

theorem ceN1Carry_first_carry_zero :
    addbackN4_carry ceN1CarryMs.1 ceN1CarryMs.2.1 ceN1CarryMs.2.2.1
      ceN1CarryMs.2.2.2.1 ceN1CarryNormB0 0 0 0 = 0 := by
  decide

theorem ceN1Carry_second_carry_zero :
    addbackN4_carry ceN1CarryAb.1 ceN1CarryAb.2.1 ceN1CarryAb.2.2.1
      ceN1CarryAb.2.2.2.1 ceN1CarryNormB0 0 0 0 = 0 := by
  decide

theorem ceN1Carry_isAddbackCarry2Nz_false :
    ¬ isAddbackCarry2Nz ceN1CarryMaxWord ceN1CarryNormB0 0 0 0
      ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord 0 := by
  intro h
  rw [isAddbackCarry2Nz] at h
  have h_second_ne := h ceN1Carry_first_carry_zero
  exact h_second_ne ceN1Carry_second_carry_zero

theorem ceN1Carry_Carry2NzAll_false :
    ¬ Carry2NzAll ceN1CarryNormB0 0 0 0 := by
  intro h
  exact ceN1Carry_isAddbackCarry2Nz_false
    (h ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord ceN1CarryMaxWord
      ceN1CarryMaxWord 0)

-- N2/N3 universal-carry counterexamples:
--
-- These pin the same proof-shape failure for the current `fullDivN2Carry2NzV4`
-- and `fullDivN3Carry2NzV4` packages. The bad states are arbitrary
-- `Carry2NzAll` witnesses, not known reachable runtime states.
abbrev ceN23CarryB0 : Word := BitVec.ofNat 64 (2^63 - 1)
abbrev ceN23CarryBTop : Word := BitVec.ofNat 64 (2^62)
abbrev ceN23CarryMaxWord : Word := BitVec.ofNat 64 (2^64 - 1)
abbrev ceN23CarryNormV0 : Word := BitVec.ofNat 64 (2^64 - 2)
abbrev ceN23CarryNormV1 : Word := BitVec.ofNat 64 (2^63)
abbrev ceN23CarryNormV2 : Word := BitVec.ofNat 64 (2^63)

theorem ceN2Carry_norm_eq :
    fullDivN2NormV ceN23CarryB0 ceN23CarryBTop 0 0 =
      (ceN23CarryNormV0, ceN23CarryNormV1, 0, 0) := by
  have hs : (fullDivN2Shift ceN23CarryBTop).toNat % 64 = 1 := by
    rw [fullDivN2Shift_unfold]; decide
  have ha : (fullDivN2AntiShift ceN23CarryBTop).toNat % 64 = 63 := by
    rw [fullDivN2AntiShift_unfold, fullDivN2Shift_unfold]; decide
  simp only [fullDivN2NormV, ceN23CarryB0, ceN23CarryBTop, ceN23CarryNormV0,
    ceN23CarryNormV1, hs, ha, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem ceN3Carry_norm_eq :
    fullDivN3NormV ceN23CarryB0 ceN23CarryBTop ceN23CarryBTop 0 =
      (ceN23CarryNormV0, ceN23CarryNormV1, ceN23CarryNormV2, 0) := by
  have hs : (fullDivN3Shift ceN23CarryBTop).toNat % 64 = 1 := by
    rw [fullDivN3Shift_unfold]; decide
  have ha : (fullDivN3AntiShift ceN23CarryBTop).toNat % 64 = 63 := by
    rw [fullDivN3AntiShift_unfold, fullDivN3Shift_unfold]; decide
  simp only [fullDivN3NormV, ceN23CarryB0, ceN23CarryBTop, ceN23CarryNormV0,
    ceN23CarryNormV1, ceN23CarryNormV2, hs, ha, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem ceN2Carry_isAddbackCarry2Nz_false :
    ¬ isAddbackCarry2Nz ceN23CarryMaxWord ceN23CarryNormV0 ceN23CarryNormV1 0 0
      ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord 0 := by
  intro h
  rw [isAddbackCarry2Nz] at h
  have h_second_ne := h (by decide)
  exact h_second_ne (by decide)

theorem ceN3Carry_isAddbackCarry2Nz_false :
    ¬ isAddbackCarry2Nz ceN23CarryMaxWord ceN23CarryNormV0 ceN23CarryNormV1
      ceN23CarryNormV2 0
      ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord 0 := by
  intro h
  rw [isAddbackCarry2Nz] at h
  have h_second_ne := h (by decide)
  exact h_second_ne (by decide)

theorem ceN2Carry_fullDivN2Carry2NzV4_false :
    ¬ fullDivN2Carry2NzV4 ceN23CarryB0 ceN23CarryBTop 0 0 := by
  intro h
  unfold fullDivN2Carry2NzV4 at h
  rw [ceN2Carry_norm_eq] at h
  exact ceN2Carry_isAddbackCarry2Nz_false
    (h ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord
      ceN23CarryMaxWord 0)

theorem ceN3Carry_fullDivN3Carry2NzV4_false :
    ¬ fullDivN3Carry2NzV4 ceN23CarryB0 ceN23CarryBTop ceN23CarryBTop 0 := by
  intro h
  unfold fullDivN3Carry2NzV4 at h
  rw [ceN3Carry_norm_eq] at h
  exact ceN3Carry_isAddbackCarry2Nz_false
    (h ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord ceN23CarryMaxWord
      ceN23CarryMaxWord 0)

-- A smaller diagnostic for the N1 max-path carry bridge:
--
--   v0 = u1 = 2^63, u0 = u2 = u3 = 0, qHat = 2^64 - 1.
--
-- This satisfies the normalized one-limb divisor shape and the selected max
-- branch condition `¬ BitVec.ult u1 v0`, but a zero first-addback carry does
-- not force the mulsub carry `c3` to be one.  Therefore the bridge introduced
-- by `isAddbackCarry2NzN1Max_of_not_ult_c3_one_of_carry_zero` still needs a
-- genuine reachable-path/remainder invariant; normalized shape plus branch
-- condition alone is not enough.
abbrev ceN1MaxLocalV0 : Word := BitVec.ofNat 64 (2^63)
abbrev ceN1MaxLocalU1 : Word := BitVec.ofNat 64 (2^63)
abbrev ceN1MaxLocalMs :=
  mulsubN4 ceN1CarryMaxWord ceN1MaxLocalV0 0 0 0
    0 ceN1MaxLocalU1 0 0

theorem ceN1MaxLocal_v0_normalized :
    2^63 ≤ ceN1MaxLocalV0.toNat := by
  decide

theorem ceN1MaxLocal_not_ult :
    ¬ BitVec.ult ceN1MaxLocalU1 ceN1MaxLocalV0 := by
  decide

theorem ceN1MaxLocal_first_carry_zero :
    addbackN4_carry ceN1MaxLocalMs.1 ceN1MaxLocalMs.2.1
      ceN1MaxLocalMs.2.2.1 ceN1MaxLocalMs.2.2.2.1
      ceN1MaxLocalV0 0 0 0 = 0 := by
  decide

theorem ceN1MaxLocal_mulsub_c3_zero :
    ceN1MaxLocalMs.2.2.2.2 = 0 := by
  decide

theorem ceN1MaxLocal_c3_one_of_carry_zero_false :
    ¬ (addbackN4_carry ceN1MaxLocalMs.1 ceN1MaxLocalMs.2.1
        ceN1MaxLocalMs.2.2.1 ceN1MaxLocalMs.2.2.2.1
        ceN1MaxLocalV0 0 0 0 = 0 →
      ceN1MaxLocalMs.2.2.2.2 = 1) := by
  intro h
  have hc3_one := h ceN1MaxLocal_first_carry_zero
  rw [ceN1MaxLocal_mulsub_c3_zero] at hc3_one
  contradiction

-- Reachable N1-shaped semantic regression using the same divisor shape as the
-- universal-carry counterexample above.
abbrev ceN1ShapeA : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ceN1CarryB0 | 1 => 0 | 2 => 0 | 3 => 0
abbrev ceN1ShapeB : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ceN1CarryB0 | 1 => 0 | 2 => 0 | 3 => 0
abbrev ceN1ShapeQuot : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0

theorem ceN1Shape_semantic_div_eq_one :
    EvmWord.div ceN1ShapeA ceN1ShapeB = ceN1ShapeQuot := by
  decide

/-- Pinned normalized divisor limbs for the N1 reachable shape.
    `ceN1CarryB0 = 2^63 - 1` normalizes by a shift of 1 to `2^64 - 2`. -/
theorem ceN1Shape_fullDivN1NormV_eq :
    fullDivN1NormV ceN1CarryB0 0 0 0 = (BitVec.ofNat 64 (2 ^ 64 - 2), 0, 0, 0) := by
  have hs : (fullDivN1Shift ceN1CarryB0).toNat % 64 = 1 := by
    rw [fullDivN1Shift_unfold]; decide
  have ha : (fullDivN1AntiShift ceN1CarryB0).toNat % 64 = 63 := by
    unfold fullDivN1AntiShift; rw [fullDivN1Shift_unfold]; decide
  simp only [fullDivN1NormV, ceN1CarryB0, hs, ha, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Pinned normalized dividend limbs for the N1 reachable shape. -/
theorem ceN1Shape_fullDivN1NormU_eq :
    fullDivN1NormU ceN1CarryB0 0 0 0 ceN1CarryB0 =
      (BitVec.ofNat 64 (2 ^ 64 - 2), 0, 0, 0, 0) := by
  have hs : (fullDivN1Shift ceN1CarryB0).toNat % 64 = 1 := by
    rw [fullDivN1Shift_unfold]; decide
  have ha : (fullDivN1AntiShift ceN1CarryB0).toNat % 64 = 63 := by
    unfold fullDivN1AntiShift; rw [fullDivN1Shift_unfold]; decide
  simp only [fullDivN1NormU, ceN1CarryB0, hs, ha, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- Each iteration of the N1 unified loop is pinned to its concrete six-tuple by
-- substituting the previously pinned tuples (`NormV`, `NormU`, and the prior
-- `Ri`) and unfolding exactly ONE iteration's arithmetic onto concrete
-- literals.  This keeps every `decide` small: only one division / mulsub /
-- addback step is symbolic at a time.  The unfold of the otherwise
-- `@[irreducible]` `iterN1Call` succeeds because it is named explicitly.

/-- Iteration 3 (top limb) of the N1 loop is zero on the reachable shape. -/
theorem ceN1Shape_fullDivN1R3_eq :
    fullDivN1R3 true ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 = (0, 0, 0, 0, 0, 0) := by
  unfold fullDivN1R3
  rw [ceN1Shape_fullDivN1NormV_eq, ceN1Shape_fullDivN1NormU_eq]
  unfold iterN1 iterN1Call iterWithDoubleAddback
  simp only [if_true, mulsubN4, addbackN4, addbackN4_carry, div128Quot,
    div128Quot_phase2b_q0', rv64_divu, rv64_mulhu, signExtend12, Prod.ext_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Iteration 2 of the N1 loop is zero on the reachable shape. -/
theorem ceN1Shape_fullDivN1R2_eq :
    fullDivN1R2 true true ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 = (0, 0, 0, 0, 0, 0) := by
  unfold fullDivN1R2
  rw [ceN1Shape_fullDivN1NormV_eq, ceN1Shape_fullDivN1NormU_eq, ceN1Shape_fullDivN1R3_eq]
  unfold iterN1 iterN1Call iterWithDoubleAddback
  simp only [if_true, mulsubN4, addbackN4, addbackN4_carry, div128Quot,
    div128Quot_phase2b_q0', rv64_divu, rv64_mulhu, signExtend12, Prod.ext_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Iteration 1 of the N1 loop is zero on the reachable shape. -/
theorem ceN1Shape_fullDivN1R1_eq :
    fullDivN1R1 true true true ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 = (0, 0, 0, 0, 0, 0) := by
  unfold fullDivN1R1
  rw [ceN1Shape_fullDivN1NormV_eq, ceN1Shape_fullDivN1NormU_eq, ceN1Shape_fullDivN1R2_eq]
  unfold iterN1 iterN1Call iterWithDoubleAddback
  simp only [if_true, mulsubN4, addbackN4, addbackN4_carry, div128Quot,
    div128Quot_phase2b_q0', rv64_divu, rv64_mulhu, signExtend12, Prod.ext_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Iteration 0 (low limb) of the N1 loop yields quotient limb 1. -/
theorem ceN1Shape_fullDivN1R0_eq :
    fullDivN1R0 true true true true ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 =
      (1, 0, 0, 0, 0, 0) := by
  unfold fullDivN1R0
  rw [ceN1Shape_fullDivN1NormV_eq, ceN1Shape_fullDivN1NormU_eq, ceN1Shape_fullDivN1R1_eq]
  unfold iterN1 iterN1Call iterWithDoubleAddback
  simp only [if_true, mulsubN4, addbackN4, addbackN4_carry, div128Quot,
    div128Quot_phase2b_q0', rv64_divu, rv64_mulhu, signExtend12, Prod.ext_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem ceN1Shape_fullDivN1QuotientWord_eq_semantic_div :
    fullDivN1QuotientWord true true true true
      ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 =
    EvmWord.div ceN1ShapeA ceN1ShapeB := by
  rw [ceN1Shape_semantic_div_eq_one]
  unfold fullDivN1QuotientWord
  rw [ceN1Shape_fullDivN1R0_eq, ceN1Shape_fullDivN1R1_eq, ceN1Shape_fullDivN1R2_eq,
    ceN1Shape_fullDivN1R3_eq]
  decide

theorem evm_div_ceN1Shape_v4_semantic_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    EvmWord.div ceN1ShapeA ceN1ShapeB = ceN1ShapeQuot ∧
    fullDivN1QuotientWord true true true true
      ceN1CarryB0 0 0 0 ceN1CarryB0 0 0 0 =
    EvmWord.div ceN1ShapeA ceN1ShapeB := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor
  · exact ceN1Shape_semantic_div_eq_one
  · exact ceN1Shape_fullDivN1QuotientWord_eq_semantic_div

-- ============================================================================
-- V4 div128Quot is NOT exact even in the normalized call regime
--
-- Pins that the v4 `div128Quot` overshoots the exact 128/64 floor on a
-- concrete input satisfying BOTH `vTop ≥ 2^63` (normalized) AND `uHi < vTop`
-- (call regime). So there is no "v4 is exact in the call regime" shortcut for
-- the n=1 lane: the v5 capped quotient (`div128Quot_v5 = floor`, proven in
-- `div128Quot_v5_eq_q_true`) is genuinely required. Kernel-checked (`decide`,
-- no `native_decide`).
-- ============================================================================

/-- Call-regime witness for the v4 `div128Quot` inexactness. -/
abbrev ceV4Div128CallUHi : Word := BitVec.ofNat 64 9570702615907497163
/-- Low limb of the v4 `div128Quot` call-regime witness. -/
abbrev ceV4Div128CallULo : Word := BitVec.ofNat 64 3560909652333379602
/-- Normalized divisor of the v4 `div128Quot` call-regime witness. -/
abbrev ceV4Div128CallVTop : Word := BitVec.ofNat 64 14276325073769090779

theorem ceV4Div128Call_vTop_normalized :
    ceV4Div128CallVTop.toNat ≥ 2^63 := by decide

theorem ceV4Div128Call_call_regime :
    ceV4Div128CallUHi.toNat < ceV4Div128CallVTop.toNat := by decide

/-- The v4 `div128Quot` is NOT the exact floor in the normalized call regime —
    motivating the v5 migration for the n=1 lane. -/
theorem ceV4Div128Call_div128Quot_ne_floor :
    (div128Quot ceV4Div128CallUHi ceV4Div128CallULo ceV4Div128CallVTop).toNat ≠
      (ceV4Div128CallUHi.toNat * 2^64 + ceV4Div128CallULo.toNat) /
        ceV4Div128CallVTop.toNat := by decide

end DivModCounterexamples

end EvmAsm.Evm64
