/-
  EvmAsm.Evm64.SMod.Compose.QuadMemBridges

  SMOD-shaped wrappers around the generic memory-quad to `evmWordIs` bridges.
-/

import EvmAsm.Evm64.SMod.AddrNorm
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64.SMod.Compose

/-- Bridge lemma: four dividend-slot memory atoms fold into a single
    `evmWordIs sp` atom. -/
theorem evmWordIs_eq_quadMem (sp : Word) (limbs : Fin 4 → Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) **
     ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limbs 1) **
     ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limbs 2) **
     ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limbs 3)) =
    evmWordIs sp (EvmWord.fromLimbs limbs) := by
  rw [EvmAsm.Evm64.SMod.AddrNorm.stackSlot0 sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot8 sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot16 sp,
    EvmAsm.Evm64.SMod.AddrNorm.stackSlot24 sp]
  exact (evmWordIs_fromLimbs (addr := sp) limbs).symm

/-- Divisor-slot companion to `evmWordIs_eq_quadMem`: four divisor-slot memory
    atoms fold into a single `evmWordIs (sp + 32)` atom. -/
theorem evmWordIs_eq_quadMem_sp32 (sp : Word) (limbs : Fin 4 → Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ limbs 0) **
     ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ limbs 1) **
     ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ limbs 2) **
     ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ limbs 3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs limbs) := by
  rw [EvmAsm.Evm64.SMod.AddrNorm.divisorBaseSlot0 sp,
    EvmAsm.Evm64.SMod.AddrNorm.divisorBaseSlot8 sp,
    EvmAsm.Evm64.SMod.AddrNorm.divisorBaseSlot16 sp,
    EvmAsm.Evm64.SMod.AddrNorm.divisorBaseSlot24 sp]
  exact (evmWordIs_fromLimbs (addr := sp + 32) limbs).symm

/-- Named-arguments specialization of `evmWordIs_eq_quadMem`. -/
theorem evmWordIs_eq_quadMem_named (sp s0 s1 s2 s3 : Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ s3)) =
    evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  rw [← evmWordIs_eq_quadMem sp
    (fun i : Fin 4 => match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)]

/-- Named-arguments specialization of `evmWordIs_eq_quadMem_sp32`. -/
theorem evmWordIs_eq_quadMem_sp32_named (sp s0 s1 s2 s3 : Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ s3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  rw [← evmWordIs_eq_quadMem_sp32 sp
    (fun i : Fin 4 => match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)]

/-- SMOD-post-shaped dividend bridge where slot 3 uses
    `evm_smodDividendTopLimbOff`. -/
theorem evmWordIs_eq_quadMem_smodDividend (sp s0 s1 s2 s3 : Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ s3)) =
    evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  unfold EvmAsm.Evm64.evm_smodDividendTopLimbOff
  exact evmWordIs_eq_quadMem_named sp s0 s1 s2 s3

/-- SMOD-post-shaped divisor bridge where slot 3 uses
    `evm_smodDivisorTopLimbOff`. -/
theorem evmWordIs_eq_quadMem_smodDivisor (sp s0 s1 s2 s3 : Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ s3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  unfold EvmAsm.Evm64.evm_smodDivisorTopLimbOff
  exact evmWordIs_eq_quadMem_sp32_named sp s0 s1 s2 s3

end EvmAsm.Evm64.SMod.Compose
