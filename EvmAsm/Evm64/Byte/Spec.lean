/-
  EvmAsm.Evm64.Byte.Spec

  Composed CPS specifications for the 256-bit EVM BYTE program (64-bit).

  Full program CodeReq, subsumption lemmas, and per-path composed specs.
  The BYTE program has 6 execution paths:
  1. zero_high: high index limbs nonzero → zero result
  2. zero_geq32: idx[0] >= 32 → zero result
  3. body_3: idx ∈ [24,31], extract from limb 0 at sp+32
  4. body_2: idx ∈ [16,23], extract from limb 1 at sp+40
  5. body_1: idx ∈ [8,15], extract from limb 2 at sp+48
  6. body_0: idx ∈ [0,7], extract from limb 3 at sp+56
-/

import EvmAsm.Evm64.Byte.LimbSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Full program CodeReq
-- ============================================================================

/-- Full BYTE program code as CodeReq.ofProg. -/
abbrev evm_byte_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base evm_byte

-- Program length verification
private theorem byte_phase_a_len : byte_phase_a.length = 9 := by native_decide
private theorem byte_phase_b_len : byte_phase_b.length = 5 := by native_decide
private theorem byte_phase_c_len : byte_phase_c.length = 5 := by native_decide
private theorem byte_body_3_len : byte_body_3.length = 4 := by native_decide
private theorem byte_body_2_len : byte_body_2.length = 4 := by native_decide
private theorem byte_body_1_len : byte_body_1.length = 4 := by native_decide
private theorem byte_body_0_len : byte_body_0.length = 3 := by native_decide
private theorem byte_store_len : byte_store.length = 6 := by native_decide
private theorem byte_zero_path_len : byte_zero_path.length = 5 := by native_decide
private theorem evm_byte_len : evm_byte.length = 45 := by native_decide

-- ============================================================================
-- CodeReq subsumption: each sub-phase code ⊆ evm_byte_code
-- ============================================================================

/-- Phase A code (9 instrs at offset 0) is subsumed by evm_byte_code. -/
private theorem byte_phase_a_sub (base : Addr) :
    ∀ a i, (byte_phase_a_code base) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_phase_a_code
  exact CodeReq.ofProg_mono_sub base base evm_byte byte_phase_a 0
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Phase B code (5 instrs at offset 36) is subsumed by evm_byte_code. -/
private theorem byte_phase_b_sub (base : Addr) :
    ∀ a i, (byte_phase_b_code (base + 36)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_phase_b_code
  exact CodeReq.ofProg_mono_sub base (base + 36) evm_byte byte_phase_b 9
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- body_3 code (4 instrs at offset 76) is subsumed by evm_byte_code. -/
private theorem byte_body_3_sub (base : Addr) :
    ∀ a i, (byte_body_3_code (base + 76)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_3_code
  exact CodeReq.ofProg_mono_sub base (base + 76) evm_byte byte_body_3 19
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- body_2 code (4 instrs at offset 92) is subsumed by evm_byte_code. -/
private theorem byte_body_2_sub (base : Addr) :
    ∀ a i, (byte_body_2_code (base + 92)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_2_code
  exact CodeReq.ofProg_mono_sub base (base + 92) evm_byte byte_body_2 23
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- body_1 code (4 instrs at offset 108) is subsumed by evm_byte_code. -/
private theorem byte_body_1_sub (base : Addr) :
    ∀ a i, (byte_body_1_code (base + 108)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_1_code
  exact CodeReq.ofProg_mono_sub base (base + 108) evm_byte byte_body_1 27
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- body_0 code (3 instrs at offset 124) is subsumed by evm_byte_code. -/
private theorem byte_body_0_sub (base : Addr) :
    ∀ a i, (byte_body_0_code (base + 124)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_0_code
  exact CodeReq.ofProg_mono_sub base (base + 124) evm_byte byte_body_0 31
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Store code (6 instrs at offset 136) is subsumed by evm_byte_code. -/
private theorem byte_store_sub (base : Addr) :
    ∀ a i, (byte_store_code (base + 136)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_store_code
  exact CodeReq.ofProg_mono_sub base (base + 136) evm_byte byte_store 34
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

/-- Zero path code (5 instrs at offset 160) is subsumed by evm_byte_code. -/
private theorem byte_zero_path_sub (base : Addr) :
    ∀ a i, (byte_zero_path_code (base + 160)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_zero_path_code
  exact CodeReq.ofProg_mono_sub base (base + 160) evm_byte byte_zero_path 40
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide)

-- ============================================================================
-- Per-path composed specs (limb-level)
-- ============================================================================

-- These specs compose the LimbSpec building blocks into full execution paths.
-- Each path goes from entry (base) to exit (base + 180).

-- TODO: The branch composition for full per-path specs requires composing
-- Phase A (with BNE/BEQ branches) + Phase B + Phase C (with BEQ cascade) + body_N + store.
-- This follows the DivMod cpsBranch composition pattern but is deferred to a follow-up PR.

-- For now, we provide the key subsumption lemmas and address arithmetic facts
-- that will be needed for the full composition.

-- Address arithmetic for JAL targets in the full program
private theorem signExtend21_48 : signExtend21 (48 : BitVec 21) = (48 : Word) := by native_decide
private theorem signExtend21_32 : signExtend21 (32 : BitVec 21) = (32 : Word) := by native_decide
private theorem signExtend21_16 : signExtend21 (16 : BitVec 21) = (16 : Word) := by native_decide
private theorem signExtend21_24 : signExtend21 (24 : BitVec 21) = (24 : Word) := by native_decide

private theorem byte_body_3_exit_eq (base : Addr) :
    (base + 76 + 12) + signExtend21 (48 : BitVec 21) = base + 136 := by
  rw [signExtend21_48]; bv_omega

private theorem byte_body_2_exit_eq (base : Addr) :
    (base + 92 + 12) + signExtend21 (32 : BitVec 21) = base + 136 := by
  rw [signExtend21_32]; bv_omega

private theorem byte_body_1_exit_eq (base : Addr) :
    (base + 108 + 12) + signExtend21 (16 : BitVec 21) = base + 136 := by
  rw [signExtend21_16]; bv_omega

private theorem byte_store_exit_eq (base : Addr) :
    (base + 136 + 20) + signExtend21 (24 : BitVec 21) = base + 180 := by
  rw [signExtend21_24]; bv_omega

end EvmAsm.Rv64
