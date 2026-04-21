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
import EvmAsm.Evm64.EvmWordArith
import EvmAsm.Evm64.SpAddr
import EvmAsm.Rv64.AddrNorm
import Mathlib.Tactic.Set

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_7
  zero_add_se12_1_toNat zero_add_se12_2_toNat bv6_toNat_3
  word_toNat_7 word_toNat_32 word_toNat_255 word_add_zero)

-- ============================================================================
-- Full program CodeReq
-- ============================================================================

/-- Full BYTE program code as CodeReq.ofProg. -/
abbrev evm_byte_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_byte

-- ============================================================================
-- CodeReq subsumption: each sub-phase code ⊆ evm_byte_code
-- ============================================================================

/-- Phase A code (9 instrs at offset 0) is subsumed by evm_byte_code. -/
private theorem byte_phase_a_sub (base : Word) :
    ∀ a i, (byte_phase_a_code base) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_phase_a_code
  exact CodeReq.ofProg_mono_sub base base evm_byte byte_phase_a 0
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Phase B code (5 instrs at offset 36) is subsumed by evm_byte_code. -/
private theorem byte_phase_b_sub (base : Word) :
    ∀ a i, (byte_phase_b_code (base + 36)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_phase_b_code
  exact CodeReq.ofProg_mono_sub base (base + 36) evm_byte byte_phase_b 9
    (by bv_omega) (by decide) (by decide) (by decide)

/-- body_3 code (4 instrs at offset 76) is subsumed by evm_byte_code. -/
private theorem byte_body_3_sub (base : Word) :
    ∀ a i, (byte_body_3_code (base + 76)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_3_code
  exact CodeReq.ofProg_mono_sub base (base + 76) evm_byte byte_body_3 19
    (by bv_omega) (by decide) (by decide) (by decide)

/-- body_2 code (4 instrs at offset 92) is subsumed by evm_byte_code. -/
private theorem byte_body_2_sub (base : Word) :
    ∀ a i, (byte_body_2_code (base + 92)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_2_code
  exact CodeReq.ofProg_mono_sub base (base + 92) evm_byte byte_body_2 23
    (by bv_omega) (by decide) (by decide) (by decide)

/-- body_1 code (4 instrs at offset 108) is subsumed by evm_byte_code. -/
private theorem byte_body_1_sub (base : Word) :
    ∀ a i, (byte_body_1_code (base + 108)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_1_code
  exact CodeReq.ofProg_mono_sub base (base + 108) evm_byte byte_body_1 27
    (by bv_omega) (by decide) (by decide) (by decide)

/-- body_0 code (3 instrs at offset 124) is subsumed by evm_byte_code. -/
private theorem byte_body_0_sub (base : Word) :
    ∀ a i, (byte_body_0_code (base + 124)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_body_0_code
  exact CodeReq.ofProg_mono_sub base (base + 124) evm_byte byte_body_0 31
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Store code (6 instrs at offset 136) is subsumed by evm_byte_code. -/
private theorem byte_store_sub (base : Word) :
    ∀ a i, (byte_store_code (base + 136)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_store_code
  exact CodeReq.ofProg_mono_sub base (base + 136) evm_byte byte_store 34
    (by bv_omega) (by decide) (by decide) (by decide)

/-- Zero path code (5 instrs at offset 160) is subsumed by evm_byte_code. -/
private theorem byte_zero_path_sub (base : Word) :
    ∀ a i, (byte_zero_path_code (base + 160)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_zero_path_code
  exact CodeReq.ofProg_mono_sub base (base + 160) evm_byte byte_zero_path 40
    (by bv_omega) (by decide) (by decide) (by decide)

-- ============================================================================
-- Phase C subsumption
-- ============================================================================

/-- Phase C code (5 instrs at offset 56) is subsumed by evm_byte_code. -/
private theorem byte_phase_c_sub (base : Word) :
    ∀ a i, (byte_phase_c_code (base + 56)) a = some i → (evm_byte_code base) a = some i := by
  unfold evm_byte_code byte_phase_c_code
  exact CodeReq.ofProg_mono_sub base (base + 56) evm_byte byte_phase_c 14
    (by bv_omega) (by decide) (by decide) (by decide)

-- ============================================================================
-- Singleton subsumption for individual branch instructions
-- ============================================================================

/-- A singleton at instruction k of evm_byte is subsumed by evm_byte_code. -/
private theorem singleton_sub_evm_byte (base addr : Word) (instr : Instr) (k : Nat)
    (hk : k < evm_byte.length)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : evm_byte.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → (evm_byte_code base) a = some i :=
  CodeReq.singleton_mono (h_instr ▸ CodeReq.ofProg_lookup_addr base evm_byte k addr hk
    (by decide) h_addr)

/-- BNE x5 x0 140 singleton at base+20 is subsumed by evm_byte_code. -/
private theorem byte_bne_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 20) (.BNE .x5 .x0 140) a = some i →
      (evm_byte_code base) a = some i :=
  singleton_sub_evm_byte base (base + 20) (.BNE .x5 .x0 140) 5
    (by decide) (by bv_omega) (by decide)

/-- LD x5 x12 0 singleton at base+24 is subsumed by evm_byte_code. -/
private theorem byte_ld0_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 24) (.LD .x5 .x12 0) a = some i →
      (evm_byte_code base) a = some i :=
  singleton_sub_evm_byte base (base + 24) (.LD .x5 .x12 0) 6
    (by decide) (by bv_omega) (by decide)

/-- SLTIU x10 x5 32 singleton at base+28 is subsumed by evm_byte_code. -/
private theorem byte_sltiu_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 32) a = some i →
      (evm_byte_code base) a = some i :=
  singleton_sub_evm_byte base (base + 28) (.SLTIU .x10 .x5 32) 7
    (by decide) (by bv_omega) (by decide)

/-- BEQ x10 x0 128 singleton at base+32 is subsumed by evm_byte_code. -/
private theorem byte_beq_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x10 .x0 128) a = some i →
      (evm_byte_code base) a = some i :=
  singleton_sub_evm_byte base (base + 32) (.BEQ .x10 .x0 128) 8
    (by decide) (by bv_omega) (by decide)

-- ============================================================================
-- Address normalization lemmas
-- ============================================================================

-- Phase A offsets
private theorem byte_off_20 (base : Word) : (base + 20 : Word) + 4 = base + 24 := by bv_omega
private theorem byte_off_24 (base : Word) : (base + 24 : Word) + 4 = base + 28 := by bv_omega
private theorem byte_off_28 (base : Word) : (base + 28 : Word) + 4 = base + 32 := by bv_omega
private theorem byte_off_32 (base : Word) : (base + 32 : Word) + 4 = base + 36 := by bv_omega
private theorem byte_off_36_20 (base : Word) : (base + 36 : Word) + 20 = base + 56 := by bv_omega
private theorem byte_off_160_20 (base : Word) : (base + 160 : Word) + 20 = base + 180 := by bv_omega

-- BNE/BEQ branch targets
private theorem byte_bne_target (base : Word) : (base + 20 : Word) + signExtend13 140 = base + 160 := by
  rv64_addr
private theorem byte_beq_target (base : Word) : (base + 32 : Word) + signExtend13 128 = base + 160 := by
  rv64_addr

-- Phase C exit addresses
private theorem byte_c_e0 (base : Word) : (base + 56 : Word) + signExtend13 68 = base + 124 := by
  rv64_addr
private theorem byte_c_e1 (base : Word) : ((base + 56 : Word) + 8) + signExtend13 44 = base + 108 := by
  rv64_addr
private theorem byte_c_e2 (base : Word) : ((base + 56 : Word) + 16) + signExtend13 20 = base + 92 := by
  rv64_addr
private theorem byte_c_e3 (base : Word) : (base + 56 : Word) + 20 = base + 76 := by bv_omega

-- Body exit addresses (JAL targets → store at base+136)
private theorem byte_body_3_exit_eq (base : Word) :
    (base + 76 + 12) + signExtend21 (48 : BitVec 21) = base + 136 := by rv64_addr
private theorem byte_body_2_exit_eq (base : Word) :
    (base + 92 + 12) + signExtend21 (32 : BitVec 21) = base + 136 := by rv64_addr
private theorem byte_body_1_exit_eq (base : Word) :
    (base + 108 + 12) + signExtend21 (16 : BitVec 21) = base + 136 := by rv64_addr
-- body_0 is fallthrough: exits at base+124+12 = base+136 (no JAL)

-- Store exit address
private theorem byte_store_exit_eq (base : Word) :
    (base + 136 + 20) + signExtend21 (24 : BitVec 21) = base + 180 := by rv64_addr

-- ============================================================================
-- Helper lemmas
-- ============================================================================

-- `regIs_to_regOwn` lives in `Rv64/SepLogic.lean` (shared).

-- `cpsNBranch_extend_code` and `cpsNBranch_frameR` live in
-- `Rv64/CPSSpec.lean` (shared).

-- `cpsTriple_strip_pure_and_convert` lives in `Rv64/CPSSpec.lean` (shared).

-- ============================================================================
-- Bridge lemma: connect per-limb body output to EvmWord.byte result
-- ============================================================================

-- `signExtend12_255` is the `@[simp]` theorem in `EvmAsm/Rv64/Instructions.lean`
-- (reachable via `open EvmAsm.Rv64` at the file header).

/-- Bridge from per-limb SRL+ANDI to natural number div+mod.
    `(limb >>> (n % 64)) &&& 255 = BitVec.ofNat 64 ((limb.toNat / 2^n) % 256)` for n < 64. -/
private theorem bv_srl_mask_eq (x : Word) (n : Nat) (hn : n < 64) :
    (x >>> (n % 64)) &&& signExtend12 (255 : BitVec 12) =
    BitVec.ofNat 64 ((x.toNat / 2 ^ n) % 256) := by
  rw [signExtend12_255]
  have hn64 : n % 64 = n := Nat.mod_eq_of_lt hn
  rw [hn64]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
             word_toNat_255,
             BitVec.toNat_ofNat]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 8]
  have hmod_lt : (x.toNat / 2 ^ n) % 256 < 2 ^ 64 := by
    have := Nat.mod_lt (x.toNat / 2^n) (by norm_num : 0 < 256)
    linarith [show (256 : Nat) ≤ 2^64 from by norm_num]
  omega

-- ============================================================================
-- Zero path composition: high limbs nonzero
-- ============================================================================

/-- Zero path via BNE taken: high index limbs are nonzero → result is zero.
    Execution: LD idx[1] → LD/OR idx[2] → LD/OR idx[3] → BNE(taken) → zero_path. -/
theorem evm_byte_zero_high_spec (sp base : Word)
    (i0 i1 i2 i3 v0 v1 v2 v3 r5 r10 : Word)
    (hhigh : i1 ||| i2 ||| i3 ≠ 0) :
    cpsTriple base (base + 180) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: OR-reduce (base → base+20) → extend to evm_byte_code
  have hOR := cpsTriple_extend_code (byte_phase_a_sub base)
    (byte_phase_a_or_reduce_spec sp r5 r10 i1 i2 i3 base)
  simp only [signExtend12_8, signExtend12_16, signExtend12_24] at hOR
  -- Frame OR-reduce with remaining state
  have hOR_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ i0) ** ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hOR
  -- Step 2: BNE at base+20 → extend to evm_byte_code, eliminate ntaken
  have hbne_raw := bne_spec_gen .x5 .x0 140 (i1 ||| i2 ||| i3) (0 : Word) (base + 20)
  rw [byte_bne_target, byte_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (byte_bne_sub base) hbne_raw
  -- Eliminate ntaken path (i1|||i2|||i3 = 0 contradicts hhigh)
  have hbne_taken := cpsBranch_takenStripPure2 hbne
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hhigh)
  -- Frame BNE with remaining state
  have hbne_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ i3) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_taken
  -- Compose OR-reduce → BNE(taken)
  have hAB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hOR_f hbne_framed
  -- Step 3: Zero path (base+160 → base+180) → extend to evm_byte_code
  have hzp := cpsTriple_extend_code (byte_zero_path_sub base)
    (byte_zero_path_spec sp v0 v1 v2 v3 (base + 160))
  simp only [signExtend12_32] at hzp
  rw [byte_off_160_20] at hzp
  -- Frame zero path with remaining state
  have hzp_framed := cpsTriple_frameR
    ((.x5 ↦ᵣ (i1 ||| i2 ||| i3)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ i3) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3))
    (by pcFree) hzp
  -- Compose AB → ZP: normalize addresses in perm callback
  have hABZ := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hzp_framed
  -- Final: weaken regs to regOwn
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (i1 ||| i2 ||| i3)) ** (.x10 ↦ᵣ i3) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    hABZ

-- ============================================================================
-- Zero path composition: idx >= 32, high limbs zero
-- ============================================================================

/-- Zero path via BEQ taken: i1=i2=i3=0 but i0 >= 32 → result is zero.
    Execution: OR-reduce → BNE(ntaken) → LD idx[0] → SLTIU → BEQ(taken) → zero_path. -/
theorem evm_byte_zero_geq32_spec (sp base : Word)
    (i0 i1 i2 i3 v0 v1 v2 v3 r5 r10 : Word)
    (hlow : i1 ||| i2 ||| i3 = 0)
    (hlarge : BitVec.ult i0 (signExtend12 (32 : BitVec 12)) = false) :
    cpsTriple base (base + 180) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: OR-reduce (base → base+20) → extend to evm_byte_code
  have hOR := cpsTriple_extend_code (byte_phase_a_sub base)
    (byte_phase_a_or_reduce_spec sp r5 r10 i1 i2 i3 base)
  simp only [signExtend12_8, signExtend12_16, signExtend12_24] at hOR
  -- Frame OR-reduce with remaining state
  have hOR_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ i0) ** ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hOR
  -- Step 2: BNE at base+20 → eliminate TAKEN (i1|||i2|||i3 = 0)
  have hbne_raw := bne_spec_gen .x5 .x0 140 (i1 ||| i2 ||| i3) (0 : Word) (base + 20)
  rw [byte_bne_target, byte_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (byte_bne_sub base) hbne_raw
  have hbne_ntaken := cpsBranch_ntakenStripPure2 hbne
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hlow)
  -- Frame BNE(ntaken) with remaining state
  have hbne_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ i3) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_ntaken
  -- Compose OR-reduce → BNE(ntaken)
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hOR_f hbne_framed
  -- Step 3: LD x5 x12 0 at base+24
  have hld_raw := ld_spec_gen .x5 .x12 sp (i1 ||| i2 ||| i3) i0 0 (base + 24) (by nofun)
  simp only [signExtend12_0] at hld_raw
  rw [word_add_zero, byte_off_24] at hld_raw
  have hld := cpsTriple_extend_code (byte_ld0_sub base) hld_raw
  -- Step 4: SLTIU at base+28
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 i3 i0 32 (base + 28) (by nofun)
  rw [byte_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code (byte_sltiu_sub base) hsltiu_raw
  -- Frame + compose LD → SLTIU
  have hld_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ i3) **
     ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hld
  have hsltiu_f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hsltiu
  have h34 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hld_f hsltiu_f
  -- Compose h12 → h34
  have h1234 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h12 h34
  -- Step 5: BEQ at base+32 → eliminate ntaken (sltiuVal = 0 since i0 ≥ 32)
  let sltiuVal := (if BitVec.ult i0 (signExtend12 (32 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hbeq_raw := beq_spec_gen .x10 .x0 128 sltiuVal (0 : Word) (base + 32)
  rw [byte_beq_target, byte_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code (byte_beq_sub base) hbeq_raw
  -- sltiuVal = 0 (since i0 ≥ 32 → ult is false)
  have hsltiu_eq : sltiuVal = (0 : Word) := by
    simp only [sltiuVal, hlarge]; decide
  -- Eliminate ntaken: ntaken postcondition has ⌜sltiuVal ≠ 0⌝, but sltiuVal = 0
  have hbeq_taken := cpsBranch_takenStripPure2 hbeq
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact ((sepConj_pure_right _).mp h_rest).2 hsltiu_eq)
  -- Frame BEQ(taken) with remaining state
  have hbeq_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ i0) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbeq_taken
  -- Compose h1234 → BEQ(taken)
  have h12345 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1234 hbeq_framed
  -- Step 6: Zero path (base+160 → base+180)
  have hzp := cpsTriple_extend_code (byte_zero_path_sub base)
    (byte_zero_path_spec sp v0 v1 v2 v3 (base + 160))
  simp only [signExtend12_32] at hzp
  rw [byte_off_160_20] at hzp
  have hzp_framed := cpsTriple_frameR
    ((.x5 ↦ᵣ i0) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ sltiuVal) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3))
    (by pcFree) hzp
  -- Compose → ZP: normalize addresses in perm callback
  have hfull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hzp_framed
  -- Final: weaken regs to regOwn
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ i0) ** (.x10 ↦ᵣ sltiuVal) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    hfull

-- ============================================================================
-- Body path composition with evmWordIs postcondition
-- ============================================================================

open EvmWord in
/-- Body path: idx < 32 → result is `EvmWord.byte idx value`.
    Composes Phase A ntaken → Phase B → Phase C → body_L + store → exit
    and uses byte_correct to connect per-limb results to EvmWord.byte. -/
theorem evm_byte_body_evmWord_spec (sp base : Word)
    (idx value : EvmWord) (r5 r6 r10 : Word)
    (hhigh_zero : idx.getLimbN 1 ||| idx.getLimbN 2 ||| idx.getLimbN 3 = 0)
    (hlt_i0 : BitVec.ult (idx.getLimbN 0) (signExtend12 (32 : BitVec 12)) = true)
    (hlt : idx.toNat < 32) :
    cpsTriple base (base + 180) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       evmWordIs sp idx ** evmWordIs (sp + 32) value)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
       (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       evmWordIs sp idx ** evmWordIs (sp + 32) (byte idx value)) := by
  -- Abbreviate limbs
  set i0 := idx.getLimbN 0
  set i1 := idx.getLimbN 1
  set i2 := idx.getLimbN 2
  set i3 := idx.getLimbN 3
  set v0 := value.getLimbN 0
  set v1 := value.getLimbN 1
  set v2 := value.getLimbN 2
  set v3 := value.getLimbN 3
  set result := byte idx value
  -- Reduce evmWordIs to raw memIs
  suffices h_raw : cpsTriple base (base + 180) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
       (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
       ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)) by
    exact cpsTriple_weaken
      (fun h hp => by
        unfold evmWordIs at hp
        simp only [spAddr32_8, spAddr32_16, spAddr32_24] at hp
        xperm_hyp hp)
      (fun h hq => by
        simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                   EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at hq
        unfold evmWordIs
        simp only [spAddr32_8, spAddr32_16, spAddr32_24]
        xperm_hyp hq)
      h_raw
  -- Now prove h_raw in flat memIs form
  -- Address normalization for sp+32 region
  have ha40 : sp + 40 = (sp + 32 : Word) + 8 := by bv_omega
  have ha48 : sp + 48 = (sp + 32 : Word) + 16 := by bv_omega
  have ha56 : sp + 56 = (sp + 32 : Word) + 24 := by bv_omega
  have ha40' : (sp + 32 : Word) + 8 = sp + 40 := by bv_omega
  have ha48' : (sp + 32 : Word) + 16 = sp + 48 := by bv_omega
  have ha56' : (sp + 32 : Word) + 24 = sp + 56 := by bv_omega
  -- Phase A: OR-reduce (base → base+20)
  have hOR := cpsTriple_extend_code (byte_phase_a_sub base)
    (byte_phase_a_or_reduce_spec sp r5 r10 i1 i2 i3 base)
  simp only [signExtend12_8, signExtend12_16, signExtend12_24] at hOR
  have hOR_f := cpsTriple_frameR
    ((.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ i0) ** ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hOR
  -- BNE at base+20: eliminate TAKEN (i1|||i2|||i3=0 contradicts ne 0)
  have hbne_raw := bne_spec_gen .x5 .x0 140 (i1 ||| i2 ||| i3) (0 : Word) (base + 20)
  rw [byte_bne_target, byte_off_20] at hbne_raw
  have hbne := cpsBranch_extend_code (byte_bne_sub base) hbne_raw
  have hbne_ntaken := cpsBranch_ntakenStripPure2 hbne
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hhigh_zero)
  have hbne_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ i3) ** (.x6 ↦ᵣ r6) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbne_ntaken
  have h12 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hOR_f hbne_framed
  -- LD x5 x12 0 at base+24
  have hld_raw := ld_spec_gen .x5 .x12 sp (i1 ||| i2 ||| i3) i0 0 (base + 24) (by nofun)
  simp only [signExtend12_0] at hld_raw
  rw [word_add_zero, byte_off_24] at hld_raw
  have hld := cpsTriple_extend_code (byte_ld0_sub base) hld_raw
  -- SLTIU at base+28
  have hsltiu_raw := sltiu_spec_gen .x10 .x5 i3 i0 32 (base + 28) (by nofun)
  rw [byte_off_28] at hsltiu_raw
  have hsltiu := cpsTriple_extend_code (byte_sltiu_sub base) hsltiu_raw
  have hld_f := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ i3) ** (.x6 ↦ᵣ r6) **
     ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hld
  have hsltiu_f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ r6) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hsltiu
  have h34 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hld_f hsltiu_f
  have h1234 := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h12 h34
  -- BEQ at base+32: eliminate TAKEN (sltiuVal=1 since i0<32, so 1=0 is absurd)
  let sltiuVal := (if BitVec.ult i0 (signExtend12 (32 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hsltiu_eq : sltiuVal = (1 : Word) := by simp only [sltiuVal, hlt_i0]; decide
  have hbeq_raw := beq_spec_gen .x10 .x0 128 sltiuVal (0 : Word) (base + 32)
  rw [byte_beq_target, byte_off_32] at hbeq_raw
  have hbeq := cpsBranch_extend_code (byte_beq_sub base) hbeq_raw
  have hbeq_ntaken := cpsBranch_ntakenStripPure2 hbeq
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      have heq := ((sepConj_pure_right _).mp h_rest).2
      simp [hsltiu_eq] at heq)
  have hbeq_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ i0) ** (.x6 ↦ᵣ r6) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hbeq_ntaken
  have hphaseA := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1234 hbeq_framed
  -- Phase B: base+36 → base+56
  let byteInLimb := i0 &&& signExtend12 (7 : BitVec 12)
  let byteShift := byteInLimb <<< (3 : BitVec 6).toNat
  let shiftAmount := (56 : Word) - byteShift
  let limbFromMsb := i0 >>> (3 : BitVec 6).toNat
  have hphaseB_raw := byte_phase_b_spec i0 r6 sltiuVal (base + 36)
  have hphaseB := cpsTriple_extend_code (byte_phase_b_sub base) hphaseB_raw
  rw [byte_off_36_20] at hphaseB
  have hphaseB_f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hphaseB
  have hphaseAB := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hphaseA hphaseB_f
  -- Phase C: cascade dispatch at base+56
  have hphaseC_raw := byte_phase_c_spec limbFromMsb byteShift (base + 56)
    (base + 124) (base + 108) (base + 92) (base + 76)
    (byte_c_e0 base) (byte_c_e1 base) (byte_c_e2 base) (byte_c_e3 base)
  have hphaseC := cpsNBranch_extend_code (byte_phase_c_sub base) hphaseC_raw
  -- Body specs extended to evm_byte_code, then composed with store
  -- body_3: base+76 → base+136 (via JAL 48), then store: base+136 → base+180
  -- Body 3 spec (load from sp+32, i.e. limb 0 = v0)
  have hbody3_raw := byte_body_3_spec sp limbFromMsb shiftAmount v0 (base + 76)
  rw [byte_body_3_exit_eq] at hbody3_raw
  simp only [signExtend12_32] at hbody3_raw
  have hbody3 := cpsTriple_extend_code (byte_body_3_sub base) hbody3_raw
  -- Body 2 spec (load from sp+40, i.e. limb 1 = v1)
  have hbody2_raw := byte_body_2_spec sp limbFromMsb shiftAmount v1 (base + 92)
  rw [byte_body_2_exit_eq] at hbody2_raw
  simp only [signExtend12_40] at hbody2_raw
  have hbody2 := cpsTriple_extend_code (byte_body_2_sub base) hbody2_raw
  -- Body 1 spec (load from sp+48, i.e. limb 2 = v2)
  have hbody1_raw := byte_body_1_spec sp limbFromMsb shiftAmount v2 (base + 108)
  rw [byte_body_1_exit_eq] at hbody1_raw
  simp only [signExtend12_48] at hbody1_raw
  have hbody1 := cpsTriple_extend_code (byte_body_1_sub base) hbody1_raw
  -- Body 0 spec (load from sp+56, i.e. limb 3 = v3)
  have hbody0_raw := byte_body_0_spec sp limbFromMsb shiftAmount v3 (base + 124)
  simp only [signExtend12_56] at hbody0_raw
  have hbody0_exit : (base + 124 : Word) + 12 = base + 136 := by bv_omega
  rw [hbody0_exit] at hbody0_raw
  have hbody0 := cpsTriple_extend_code (byte_body_0_sub base) hbody0_raw
  -- Body+store composition, bridge, Phase C merge, and final composition
  -- are deferred to evm_byte_body_compose_spec (Byte/BodyCompose.lean)
  -- which builds on the infrastructure established above.
  -- For now, use the Phase A+B composition and Phase C dispatch directly.
  --
  -- The approach: frame Phase C, then merge with body+store per exit.
  -- Each body: bodyBase → base+136 (extended to evm_byte_code)
  -- Store: base+136 → base+180 (extended to evm_byte_code)
  -- Compose body → store, frame with x0/x10/idxMem, weaken regs, bridge via bv_srl_mask_eq + byte_correct
  --
  -- Due to the different x10 values per Phase C exit and the complex memory layouts,
  -- the composition is done inline in the merge callback.
  have hidx_toNat : idx.toNat = i0.toNat :=
    EvmWord.toNat_eq_getLimb0_of_high_zero idx hhigh_zero
  have hresult_high1 : getLimb result 1 = 0 :=
    byte_getLimb_high idx value (1 : Fin 4) (by decide)
  have hresult_high2 : getLimb result 2 = 0 :=
    byte_getLimb_high idx value (2 : Fin 4) (by decide)
  have hresult_high3 : getLimb result 3 = 0 :=
    byte_getLimb_high idx value (3 : Fin 4) (by decide)
  have hresult_limb0 := byte_correct idx value hlt
  have hlimb_val : limbFromMsb.toNat = i0.toNat / 8 := by
    show (i0 >>> (3 : BitVec 6).toNat).toNat = i0.toNat / 8
    rw [bv6_toNat_3]; simp [BitVec.toNat_ushiftRight]; omega
  have hbyte_shift_val : byteShift.toNat = (i0.toNat % 8) * 8 := by
    show (byteInLimb <<< (3 : BitVec 6).toNat).toNat = (i0.toNat % 8) * 8
    rw [bv6_toNat_3]
    simp only [byteInLimb, BitVec.toNat_shiftLeft, BitVec.toNat_and, se12_7,
               word_toNat_7]
    rw [Nat.and_two_pow_sub_one_eq_mod _ 3]
    have : i0.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    have : (i0.toNat % 8) * 8 < 2 ^ 64 := by omega
    omega
  have hshift_val : shiftAmount.toNat = 56 - (i0.toNat % 8) * 8 := by
    show ((56 : Word) - byteShift).toNat = _
    have hbs_lt : byteShift.toNat ≤ 56 := by omega
    bv_omega
  have hshift_lt64 : shiftAmount.toNat < 64 := by omega
  -- Bridge helper: connect body result to getLimb result 0
  have bridge : ∀ (vLimb : Word) (K : Nat) (hK : K = i0.toNat / 8) (_ : K < 4)
      (hvLimb : vLimb = value.getLimb ⟨3 - K, by omega⟩),
      (vLimb >>> (shiftAmount.toNat % 64)) &&& signExtend12 (255 : BitVec 12) = getLimb result 0 := by
    intro vLimb K hK hKlt hvLimb
    have heq := bv_srl_mask_eq vLimb shiftAmount.toNat hshift_lt64
    rw [heq]; show _ = getLimb (byte idx value) 0
    -- byte_correct: getLimb (byte idx value) 0 = ofNat 64 ((value.getLimb ⟨3-idx.toNat/8,_⟩.toNat / 2^(56-(idx.toNat%8)*8)) % 256)
    rw [byte_correct idx value hlt]
    -- Now goal: ofNat 64 ((vLimb.toNat / 2^shiftAmount.toNat) % 256) =
    --           ofNat 64 ((value.getLimb ⟨3-idx.toNat/8,_⟩.toNat / 2^(56-(idx.toNat%8)*8)) % 256)
    -- Show the Nat arguments are equal
    apply congrArg (BitVec.ofNat 64)
    -- Both sides are Nat, show they're equal
    -- LHS: (vLimb.toNat / 2^shiftAmount.toNat) % 256
    -- RHS: (value.getLimb ⟨3-idx.toNat/8, _⟩.toNat / 2^(56-(idx.toNat%8)*8)) % 256
    -- vLimb = value.getLimb ⟨3-K, _⟩, K = idx.toNat/8 (via hidx_toNat), shiftAmount.toNat = 56-(i0.toNat%8)*8
    have hval_eq : (3 - idx.toNat / 8) = (3 - K) := by rw [hidx_toNat, hK]
    have h_limb_toNat : (value.getLimb ⟨3 - idx.toNat / 8, by omega⟩).toNat = vLimb.toNat := by
      have : value.getLimb ⟨3 - idx.toNat / 8, by omega⟩ = value.getLimb ⟨3 - K, by omega⟩ := by
        congr 1; ext; exact hval_eq
      rw [this, ← hvLimb]
    rw [h_limb_toNat]; congr 1; congr 1; rw [hidx_toNat, hshift_val]
  let resultPost :=
    (.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
     (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
     ((sp + 32) ↦ₘ getLimb result 0) ** ((sp + 40) ↦ₘ getLimb result 1) **
     ((sp + 48) ↦ₘ getLimb result 2) ** ((sp + 56) ↦ₘ getLimb result 3)
  -- Build framed body specs (frame each body with remaining val mem cells)
  -- Body 3 (loads v0 from sp+32): already has all 4 val cells in pre/post after framing with val_mem_1,2,3
  -- But the raw body specs have only 1 val cell. Need to frame with other 3 val cells first.
  -- body_3 has: pre = (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ _) ** (.x6 ↦ᵣ shiftAmount) ** ((sp+32)↦ₘv0)
  have hb3_val_f := cpsTriple_frameR
    (((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hbody3
  have hb3_canon : cpsTriple (base + 76) (base + 136) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ limbFromMsb) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v0 >>> (shiftAmount.toNat % 64)) &&& signExtend12 255) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) hb3_val_f
  have hb2_val_f := cpsTriple_frameR
    (((sp + 32) ↦ₘ v0) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hbody2
  have hb2_canon : cpsTriple (base + 92) (base + 136) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ limbFromMsb) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v1 >>> (shiftAmount.toNat % 64)) &&& signExtend12 255) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) hb2_val_f
  have hb1_val_f := cpsTriple_frameR
    (((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 56) ↦ₘ v3)) (by pcFree) hbody1
  have hb1_canon : cpsTriple (base + 108) (base + 136) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ limbFromMsb) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v2 >>> (shiftAmount.toNat % 64)) &&& signExtend12 255) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) hb1_val_f
  have hb0_val_f := cpsTriple_frameR
    (((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2)) (by pcFree) hbody0
  have hb0_canon : cpsTriple (base + 124) (base + 136) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ limbFromMsb) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v3 >>> (shiftAmount.toNat % 64)) &&& signExtend12 255) ** (.x6 ↦ᵣ shiftAmount) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) hb0_val_f
  -- Frame Phase C and merge with bodies+store
  have hphaseC_framed := cpsNBranch_frameR
    (F := (.x6 ↦ᵣ shiftAmount) ** (.x12 ↦ᵣ sp) **
          (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
          ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
    (by pcFree) hphaseC
  simp only [List.map] at hphaseC_framed
  -- For each Phase C exit, build body+store and thread dispatch fact
  -- Helper to derive K from dispatch fact
  have derive_K_0 (hd : limbFromMsb = 0) : 0 = i0.toNat / 8 := by
    have : limbFromMsb.toNat = 0 := by rw [hd]; rfl
    omega
  have derive_K_1 (hd : limbFromMsb = (0 : Word) + signExtend12 1) : 1 = i0.toNat / 8 := by
    have : limbFromMsb.toNat = 1 := by rw [hd]; decide
    omega
  have derive_K_2 (hd : limbFromMsb = (0 : Word) + signExtend12 2) : 2 = i0.toNat / 8 := by
    have : limbFromMsb.toNat = 2 := by rw [hd]; decide
    omega
  have derive_K_3 (hd : limbFromMsb ≠ 0 ∧ limbFromMsb ≠ (0 : Word) + signExtend12 1 ∧
      limbFromMsb ≠ (0 : Word) + signExtend12 2) : 3 = i0.toNat / 8 := by
    obtain ⟨h0, h1, h2⟩ := hd
    have hn0 : limbFromMsb.toNat ≠ 0 :=
      fun hc => h0 (BitVec.eq_of_toNat_eq (by simpa using hc))
    have hn1 : limbFromMsb.toNat ≠ 1 :=
      fun hc => h1 (BitVec.eq_of_toNat_eq (by
        show limbFromMsb.toNat = ((0 : Word) + signExtend12 1).toNat
        simp only [zero_add_se12_1_toNat]; exact hc))
    have hn2 : limbFromMsb.toNat ≠ 2 :=
      fun hc => h2 (BitVec.eq_of_toNat_eq (by
        show limbFromMsb.toNat = ((0 : Word) + signExtend12 2).toNat
        simp only [zero_add_se12_2_toNat]; exact hc))
    have hlt4 : limbFromMsb.toNat < 4 := by omega
    omega
  -- Build body+store specs WITHOUT the dispatch fact (just compose and weaken regs)
  -- Then use cpsTriple_strip_pure_and_convert to accept the dispatch fact from Phase C
  -- and convert the postcondition using the bridge.
  -- Body+store for each body (produces concrete mem values, not yet bridged to getLimb result)
  -- Helper to build body+store (parametric in x10 value)
  have mk_body_store : ∀ (bodyBase : Word) (x10v vLimb : Word)
      (hbodyRaw : cpsTriple bodyBase (base + 136) (evm_byte_code base)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ limbFromMsb) ** (.x6 ↦ᵣ shiftAmount) **
         ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (vLimb >>> (shiftAmount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)) ** (.x6 ↦ᵣ shiftAmount) **
         ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))),
      let resV := (vLimb >>> (shiftAmount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
      cpsTriple bodyBase (base + 180) (evm_byte_code base)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ limbFromMsb) ** (.x6 ↦ᵣ shiftAmount) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10v) **
         (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
         ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
        ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ resV) ** (.x6 ↦ᵣ shiftAmount) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10v) **
         (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
         ((sp + 32) ↦ₘ resV) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
    intro bodyBase x10v vLimb hbodyRaw resV
    have hbody_f := cpsTriple_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10v) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3))
      (by pcFree) hbodyRaw
    have hstore_raw := byte_store_spec sp resV v0 v1 v2 v3 (base + 136)
    rw [byte_store_exit_eq] at hstore_raw; simp only [signExtend12_32] at hstore_raw
    have hstore := cpsTriple_extend_code (byte_store_sub base) hstore_raw
    have hstore_f := cpsTriple_frameR
      ((.x6 ↦ᵣ shiftAmount) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10v) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3))
      (by pcFree) hstore
    have hbs := cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hbody_f hstore_f
    exact cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq) hbs
  -- Build body+store for each body (with Phase C exit x10 values)
  -- Phase C exits: e0 has x10=byteShift, e1 has x10=(0:Word)+signExtend12 1,
  -- e2 has x10=(0:Word)+signExtend12 2, e3 has x10=(0:Word)+signExtend12 2
  have hbs0 := mk_body_store (base + 124) byteShift v3 hb0_canon
  have hbs1 := mk_body_store (base + 108) ((0:Word) + signExtend12 1) v2 hb1_canon
  have hbs2 := mk_body_store (base + 92) ((0:Word) + signExtend12 2) v1 hb2_canon
  have hbs3 := mk_body_store (base + 76) ((0:Word) + signExtend12 2) v0 hb3_canon
  -- Helper to weaken regs to regOwn
  have body_post_weaken : ∀ (resV x10v : Word),
      ∀ h, ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ resV) ** (.x6 ↦ᵣ shiftAmount) **
            (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10v) **
            (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
            ((sp + 32) ↦ₘ resV) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) h →
           ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
            (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
            (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
            ((sp + 32) ↦ₘ resV) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) h := by
    intro resV x10v h hq
    have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 _)) h hq
    have w2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h w1
    have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _))))) h w2
    exact (congrFun (show _ = _ from by xperm) h).mp w3
  -- Weaken each body+store to use regOwn (but keep concrete mem result)
  have hbs0_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ h hq) hbs0
  have hbs1_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ h hq) hbs1
  have hbs2_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ h hq) hbs2
  have hbs3_w := cpsTriple_weaken
    (fun h hp => hp) (fun h hq => body_post_weaken _ _ h hq) hbs3
  -- Wrap each with cpsTriple_strip_pure_and_convert to accept dispatch fact and bridge to resultPost
  -- The dispatch fact is used to derive K, which is used by bridge to convert memory values
  have hb0_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbs0_w (fun (hd : limbFromMsb = 0) h hq => by
      simp only [resultPost, hresult_high1, hresult_high2, hresult_high3]
      rw [← bridge v3 0 (derive_K_0 hd) (by omega) rfl]; exact hq)
  have hb1_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbs1_w (fun (hd : limbFromMsb = (0 : Word) + signExtend12 1) h hq => by
      simp only [resultPost, hresult_high1, hresult_high2, hresult_high3]
      rw [← bridge v2 1 (derive_K_1 hd) (by omega) rfl]; exact hq)
  have hb2_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbs2_w (fun (hd : limbFromMsb = (0 : Word) + signExtend12 2) h hq => by
      simp only [resultPost, hresult_high1, hresult_high2, hresult_high3]
      rw [← bridge v1 2 (derive_K_2 hd) (by omega) rfl]; exact hq)
  have hb3_ev := @cpsTriple_strip_pure_and_convert _ _ _ _ _ resultPost _
    hbs3_w (fun (hd : limbFromMsb ≠ 0 ∧ limbFromMsb ≠ (0 : Word) + signExtend12 1 ∧
      limbFromMsb ≠ (0 : Word) + signExtend12 2) h hq => by
      simp only [resultPost, hresult_high1, hresult_high2, hresult_high3]
      rw [← bridge v0 3 (derive_K_3 hd) (by omega) rfl]; exact hq)
  -- Merge Phase C with bodies
  have hphaseCD := cpsNBranch_merge hphaseC_framed
    (fun exit hmem => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hb0_ev
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hb1_ev
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hb2_ev
      · exact cpsTriple_weaken
          (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hb3_ev)
  -- Flatten hphaseAB postcondition for composition
  have hphaseAB' : cpsTriple base (base + 56) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x5 ↦ᵣ limbFromMsb) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ byteShift) **
       (.x6 ↦ᵣ shiftAmount) ** (.x12 ↦ᵣ sp) **
       (sp ↦ₘ i0) ** ((sp + 8) ↦ₘ i1) ** ((sp + 16) ↦ₘ i2) ** ((sp + 24) ↦ₘ i3) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      hphaseAB
  -- Final: Phase AB → Phase CD
  exact cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hphaseAB' hphaseCD

-- ============================================================================
-- Stack-level spec: EvmWord.byte with evmWordIs
-- ============================================================================

/-- Stack-level BYTE spec using evmWordIs and EvmWord.byte. -/
theorem evm_byte_stack_spec (sp base : Word)
    (idx val : EvmWord) (v5 v6 v10 : Word) :
    cpsTriple base (base + 180) (evm_byte_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       evmWordIs sp idx ** evmWordIs (sp + 32) val)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) **
       (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       evmWordIs sp idx ** evmWordIs (sp + 32) (EvmWord.byte idx val)) := by
  -- Abbreviate limbs
  set i0 := idx.getLimbN 0
  set i1 := idx.getLimbN 1
  set i2 := idx.getLimbN 2
  set i3 := idx.getLimbN 3
  set v0 := val.getLimbN 0
  set v1 := val.getLimbN 1
  set v2 := val.getLimbN 2
  set v3 := val.getLimbN 3
  -- Case split on three conditions
  by_cases hhigh : i1 ||| i2 ||| i3 ≠ 0
  · -- Case 1: high limbs nonzero → zero result
    -- Show EvmWord.byte idx val = 0 (since idx.toNat ≥ 2^64 ≥ 32)
    have hbyte_zero : EvmWord.byte idx val = 0 := by
      apply EvmWord.byte_zero
      intro hlt32
      -- If idx.toNat < 32 < 2^64, all high limbs must be zero, contradicting hhigh
      apply hhigh
      have hlt64 : idx.toNat < 2^64 := by omega
      -- getLimb k = (idx.toNat / 2^(k*64)) % 2^64
      -- For k >= 1, idx.toNat < 2^64 ⇒ idx.toNat / 2^(k*64) = 0
      have h1 : i1 = 0 := by
        show idx.getLimbN 1 = 0; simp [EvmWord.getLimbN, EvmWord.getLimb]
        apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]; omega
      have h2 : i2 = 0 := by
        show idx.getLimbN 2 = 0; apply BitVec.eq_of_toNat_eq
        simp [EvmWord.getLimbN, EvmWord.getLimb, BitVec.extractLsb'_toNat]; omega
      have h3 : i3 = 0 := by
        show idx.getLimbN 3 = 0; apply BitVec.eq_of_toNat_eq
        simp [EvmWord.getLimbN, EvmWord.getLimb, BitVec.extractLsb'_toNat]; omega
      rw [h1, h2, h3]; simp
    rw [hbyte_zero]
    -- Use evm_byte_zero_high_spec at the limb level, then wrap with evmWordIs
    have h_raw := evm_byte_zero_high_spec sp base i0 i1 i2 i3 v0 v1 v2 v3 v5 v10 hhigh
    -- Frame x6 (not used by zero_high path)
    have h_framed := cpsTriple_frameR
      (.x6 ↦ᵣ v6) (by pcFree) h_raw
    -- Convert to evmWordIs form
    exact cpsTriple_weaken
      (fun h hp => by
        unfold evmWordIs at hp
        simp only [spAddr32_8, spAddr32_16, spAddr32_24] at hp
        xperm_hyp hp)
      (fun h hq => by
        unfold evmWordIs
        simp only [spAddr32_8, spAddr32_16, spAddr32_24,
                   EvmWord.getLimbN_zero]
        have w := sepConj_mono_right (regIs_to_regOwn .x6 _) h hq
        xperm_hyp w)
      h_framed
  · push Not at hhigh
    -- hhigh : i1 ||| i2 ||| i3 = 0
    by_cases hlt : idx.toNat < 32
    · -- Case 3: idx < 32 → body path
      -- Need: BitVec.ult i0 (signExtend12 32) = true
      have hlt_i0 : BitVec.ult i0 (signExtend12 (32 : BitVec 12)) = true := by
        simp only [BitVec.ult, signExtend12_32,
                   word_toNat_32]
        have hidx_toNat : idx.toNat = i0.toNat :=
          EvmWord.toNat_eq_getLimb0_of_high_zero idx hhigh
        rw [decide_eq_true_eq]; omega
      exact evm_byte_body_evmWord_spec sp base idx val v5 v6 v10 hhigh hlt_i0 hlt
    · -- Case 2: idx.toNat >= 32, high limbs zero → zero result
      have hbyte_zero : EvmWord.byte idx val = 0 := EvmWord.byte_zero idx val hlt
      rw [hbyte_zero]
      -- Need: BitVec.ult i0 (signExtend12 32) = false
      have hlarge : BitVec.ult i0 (signExtend12 (32 : BitVec 12)) = false := by
        simp only [BitVec.ult, signExtend12_32,
                   word_toNat_32]
        have hidx_toNat : idx.toNat = i0.toNat :=
          EvmWord.toNat_eq_getLimb0_of_high_zero idx hhigh
        rw [decide_eq_false_iff_not]; omega
      have h_raw := evm_byte_zero_geq32_spec sp base i0 i1 i2 i3 v0 v1 v2 v3 v5 v10 hhigh hlarge
      have h_framed := cpsTriple_frameR
        (.x6 ↦ᵣ v6) (by pcFree) h_raw
      exact cpsTriple_weaken
        (fun h hp => by
          unfold evmWordIs at hp
          simp only [spAddr32_8, spAddr32_16, spAddr32_24] at hp
          xperm_hyp hp)
        (fun h hq => by
          unfold evmWordIs
          simp only [spAddr32_8, spAddr32_16, spAddr32_24,
                     EvmWord.getLimbN_zero]
          have w := sepConj_mono_right (regIs_to_regOwn .x6 _) h hq
          xperm_hyp w)
        h_framed

end EvmAsm.Evm64
