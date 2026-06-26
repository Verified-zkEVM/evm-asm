/-
  EvmAsm.Evm64.MulMod.AddPartialSpecs

  Concrete product-layout add-partial cpsTriple specs that build on the
  per-limb MULMOD block specs.
-/

import EvmAsm.Evm64.MulMod.LimbSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Concrete add-partial calls with long carry suffixes
-- ============================================================================

/-- Product-layout call `evm_mulmod_product_add_partial 16 32 112 120 [3968, 3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_16_32_112_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 16) base (base + 60 + 64)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (16 : BitVec 12) (32 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3968, 3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (32 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))))) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p4 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b)))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (16 : BitVec 12) (32 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_128_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p4 p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 8 40 112 120 [3968, 3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_8_40_112_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 16) base (base + 60 + 64)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (8 : BitVec 12) (40 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3968, 3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (40 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))))) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p4 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b)))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (8 : BitVec 12) (40 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_128_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p4 p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 0 48 112 120 [3968, 3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_0_48_112_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 16) base (base + 60 + 64)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (0 : BitVec 12) (48 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3968, 3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (48 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))))) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p4 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModAddPartialHiCarry hi lo a b)))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (0 : BitVec 12) (48 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_128_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p4 p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 8 32 104 112 [3960, 3968, 3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_8_32_104_112_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 20) base (base + 60 + 80)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (8 : BitVec 12) (32 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3960, 3968, 3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (32 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       ((((((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))))))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b)))))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b)))))) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p3 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b))))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b))))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (8 : BitVec 12) (32 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_120_128_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p3 p4 p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    ((((((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 0 40 104 112 [3960, 3968, 3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_0_40_104_112_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 20) base (base + 60 + 80)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (0 : BitVec 12) (40 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3960, 3968, 3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (40 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       ((((((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))))))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b)))))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b)))))) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p3 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b))))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModAddPartialHiCarry hi lo a b))))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (0 : BitVec 12) (40 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_120_128_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p3 p4 p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    ((((((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 0 32 96 104 [3952, 3960, 3968, 3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_0_32_96_104_112_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 24) base (base + 60 + 96)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (0 : BitVec 12) (32 : BitVec 12) (3936 : BitVec 12) (3944 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3952, 3960, 3968, 3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (32 : BitVec 12) (3936 : BitVec 12) (3944 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((((((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))))))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (mulModAddPartialHiCarry hi lo a b))))))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (mulModAddPartialHiCarry hi lo a b))))))) **
        ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p2 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p3 (mulModCarryStepCarry p2 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (mulModAddPartialHiCarry hi lo a b))))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (mulModAddPartialHiCarry hi lo a b)))))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (mulModAddPartialHiCarry hi lo a b)))))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (0 : BitVec 12) (32 : BitVec 12) (3936 : BitVec 12) (3944 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_112_120_128_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p2 p3 p4 p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((((((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
        ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))))))
    (by pcFree) core
  seqFrame coreF carry



end EvmAsm.Evm64
