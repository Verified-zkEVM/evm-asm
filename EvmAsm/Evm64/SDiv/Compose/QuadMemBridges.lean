/-
  EvmAsm.Evm64.SDiv.Compose.QuadMemBridges

  SDIV-shaped wrappers around the generic memory-quad to `evmWordIs`
  bridges from `Compose/Base.lean`.
-/

module

public import EvmAsm.Evm64.SDiv.AddrNorm
public import EvmAsm.Evm64.Stack

@[expose] public section

namespace EvmAsm.Evm64.SDiv.Compose

/-- Bridge lemma: four `↦ₘ`-memory atoms at `sp + signExtend12 (0/8/16/24)`
    fold into a single `evmWordIs sp` atom holding `EvmWord.fromLimbs` of the
    four limbs. -/
theorem evmWordIs_eq_quadMem (sp : Word) (limbs : Fin 4 → Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) **
     ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limbs 1) **
     ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limbs 2) **
     ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limbs 3)) =
    evmWordIs sp (EvmWord.fromLimbs limbs) := by
  rw [EvmAsm.Evm64.SDiv.AddrNorm.stackSlot0 sp,
    EvmAsm.Evm64.SDiv.AddrNorm.stackSlot8 sp,
    EvmAsm.Evm64.SDiv.AddrNorm.stackSlot16 sp,
    EvmAsm.Evm64.SDiv.AddrNorm.stackSlot24 sp]
  exact (evmWordIs_fromLimbs (addr := sp) limbs).symm

/-- Divisor-slot companion to `evmWordIs_eq_quadMem`: four `↦ₘ`-memory atoms
    at `sp + signExtend12 (32/40/48/56)` fold into a single
    `evmWordIs (sp + 32)` atom. -/
theorem evmWordIs_eq_quadMem_sp32 (sp : Word) (limbs : Fin 4 → Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ limbs 0) **
     ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ limbs 1) **
     ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ limbs 2) **
     ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ limbs 3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs limbs) := by
  rw [EvmAsm.Evm64.SDiv.AddrNorm.divisorBaseSlot0 sp,
    EvmAsm.Evm64.SDiv.AddrNorm.divisorBaseSlot8 sp,
    EvmAsm.Evm64.SDiv.AddrNorm.divisorBaseSlot16 sp,
    EvmAsm.Evm64.SDiv.AddrNorm.divisorBaseSlot24 sp]
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

/-- SDIV-Post-shaped variant of `evmWordIs_eq_quadMem_named`: same dividend
    bridge but slot 3's offset is `signExtend12 evm_sdivDividendTopLimbOff`. -/
theorem evmWordIs_eq_quadMem_sdivDividend (sp s0 s1 s2 s3 : Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ s3)) =
    evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  unfold EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  exact evmWordIs_eq_quadMem_named sp s0 s1 s2 s3

/-- SDIV-Post-shaped variant of `evmWordIs_eq_quadMem_sp32_named`. -/
theorem evmWordIs_eq_quadMem_sdivDivisor (sp s0 s1 s2 s3 : Word) :
    (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ s3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  unfold EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  exact evmWordIs_eq_quadMem_sp32_named sp s0 s1 s2 s3

/-- Mid-tree variant of `evmWordIs_eq_quadMem_sdivDividend`: threads a
    remainder `Q` so callers can fold four dividend sum-memIs atoms into
    a single `evmWordIs sp` atom inside a longer sepConj chain. -/
theorem evmWordIs_eq_quadMem_sdivDividend_right
    (sp s0 s1 s2 s3 : Word) (Q : EvmAsm.Rv64.Assertion) :
    (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
       s3) **
     Q) =
    ((evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
        match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)) ** Q) := by
  rw [← evmWordIs_eq_quadMem_sdivDividend sp s0 s1 s2 s3]
  rw [EvmAsm.Rv64.sepConj_assoc', EvmAsm.Rv64.sepConj_assoc',
    EvmAsm.Rv64.sepConj_assoc']

/-- Mid-tree variant of `evmWordIs_eq_quadMem_sdivDivisor`. -/
theorem evmWordIs_eq_quadMem_sdivDivisor_right
    (sp s0 s1 s2 s3 : Word) (Q : EvmAsm.Rv64.Assertion) :
    (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ s0) **
     ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ s1) **
     ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ s2) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
       s3) **
     Q) =
    ((evmWordIs (sp + 32) (EvmWord.fromLimbs fun i : Fin 4 =>
        match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)) ** Q) := by
  rw [← evmWordIs_eq_quadMem_sdivDivisor sp s0 s1 s2 s3]
  rw [EvmAsm.Rv64.sepConj_assoc', EvmAsm.Rv64.sepConj_assoc',
    EvmAsm.Rv64.sepConj_assoc']

end EvmAsm.Evm64.SDiv.Compose
