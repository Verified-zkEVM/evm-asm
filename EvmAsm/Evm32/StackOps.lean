/-
  EvmAsm.Evm32.StackOps

  Verified 256-bit EVM stack manipulation opcodes:
  - POP (Phase 2.1): discard top of stack, sp += 32. 1 instruction.
  - PUSH0 (Phase 2.2): push 0 onto stack, sp -= 32. 9 instructions.
  - DUP1 (Phase 2.3): duplicate top of stack, sp -= 32. 17 instructions.
  - SWAP1 (Phase 2.4): swap top two stack items, sp unchanged. 32 instructions.
-/

import EvmAsm.Evm32.Stack
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.RunBlock
import EvmAsm.Rv32.Tactics.LiftSpec

open EvmAsm.Tactics

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| bv_omega)

@[simp] theorem signExtend12_neg32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by
  native_decide

@[simp] theorem EvmWord.getLimb_zero (i : Fin 8) : (0 : EvmWord).getLimb i = 0 := by
  have h : ∀ j : Fin 8, (0 : EvmWord).getLimb j = 0 := by native_decide
  exact h i

-- ============================================================================
-- Program definitions
-- ============================================================================

def evm_pop : Program := ADDI .x12 .x12 32

def evm_push0 : Program :=
  ADDI .x12 .x12 (-32) ;;
  SW .x12 .x0 0 ;; SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28

def evm_dup1 : Program :=
  ADDI .x12 .x12 (-32) ;;
  LW .x7 .x12 32 ;; SW .x12 .x7 0 ;;
  LW .x7 .x12 36 ;; SW .x12 .x7 4 ;;
  LW .x7 .x12 40 ;; SW .x12 .x7 8 ;;
  LW .x7 .x12 44 ;; SW .x12 .x7 12 ;;
  LW .x7 .x12 48 ;; SW .x12 .x7 16 ;;
  LW .x7 .x12 52 ;; SW .x12 .x7 20 ;;
  LW .x7 .x12 56 ;; SW .x12 .x7 24 ;;
  LW .x7 .x12 60 ;; SW .x12 .x7 28

def evm_swap1 : Program :=
  LW .x7 .x12 0  ;; LW .x6 .x12 32 ;; SW .x12 .x6 0  ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4  ;; LW .x6 .x12 36 ;; SW .x12 .x6 4  ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8  ;; LW .x6 .x12 40 ;; SW .x12 .x6 8  ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; SW .x12 .x6 12 ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; SW .x12 .x6 16 ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; SW .x12 .x6 20 ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; SW .x12 .x6 24 ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; SW .x12 .x6 28 ;; SW .x12 .x7 60

-- ============================================================================
-- POP spec (Phase 2.1)
-- ============================================================================

theorem evm_pop_spec (sp base : Addr) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ sp))
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ (sp + 32))) := by
  have h := addi_spec_gen_same .x12 sp 32 base (by nofun)
  simp only [signExtend12_32] at h; exact h

theorem evm_pop_stack_spec (sp base : Addr)
    (a : EvmWord) (rest : List EvmWord) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) :=
  cpsTriple_consequence base (base + 4) _ _ _ _
    (fun h hp => (sepConj_assoc _ _ _ h).mpr hp)
    (fun h hq => (sepConj_assoc _ _ _ h).mp hq)
    (cpsTriple_frame_left base (base + 4) _ _ _ (by pcFree) (evm_pop_spec sp base))

-- ============================================================================
-- PUSH0 spec (Phase 2.2)
-- ============================================================================
set_option maxHeartbeats 4800000 in
theorem evm_push0_spec (nsp base : Addr)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (hvalid : ValidMemRange nsp 8) :
    let code :=
      (base ↦ᵢ .ADDI .x12 .x12 (-32)) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
      ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
      ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
      ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
      ((base + 32) ↦ᵢ .SW .x12 .x0 28)
    cpsTriple base (base + 36)
      (code **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      (code **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  -- Compose ADDI + 8 SW x0 specs via runBlock
  have S0 := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at S0
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at S0
  have S1 := sw_x0_spec_gen .x12 nsp d0 0 (base + 4) (by validMem)
  have S2 := sw_x0_spec_gen .x12 nsp d1 4 (base + 8) (by validMem)
  have S3 := sw_x0_spec_gen .x12 nsp d2 8 (base + 12) (by validMem)
  have S4 := sw_x0_spec_gen .x12 nsp d3 12 (base + 16) (by validMem)
  have S5 := sw_x0_spec_gen .x12 nsp d4 16 (base + 20) (by validMem)
  have S6 := sw_x0_spec_gen .x12 nsp d5 20 (base + 24) (by validMem)
  have S7 := sw_x0_spec_gen .x12 nsp d6 24 (base + 28) (by validMem)
  have S8 := sw_x0_spec_gen .x12 nsp d7 28 (base + 32) (by validMem)
  runBlock S0 S1 S2 S3 S4 S5 S6 S7 S8

theorem evm_push0_stack_spec (nsp base : Addr)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 8) :
    cpsTriple base (base + 36)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
       ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
       ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
       ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       evmStackIs (nsp + 32) rest)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
       ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
       ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
       ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
       (.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_zero]; xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ (evmStackIs (nsp + 32) rest)
      (by exact pcFree_evmStackIs (nsp + 32) rest)
      (evm_push0_spec nsp base d0 d1 d2 d3 d4 d5 d6 d7 hvalid))

-- ============================================================================
-- DUP1 per-pair helper (Phase 2.3)
-- ============================================================================

/-- Two-instruction spec for DUP1: LW x7 from source, SW x7 to destination.
    Copies src_val from src address to dst address. -/
theorem dup1_pair_spec (sp : Addr)
    (off_src off_dst : BitVec 12) (src_val dst_old v7 : Word) (base : Addr)
    (hvalid_src : isValidMemAccess (sp + signExtend12 off_src) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 off_dst) = true) :
    let code := (base ↦ᵢ .LW .x7 .x12 off_src) ** ((base + 4) ↦ᵢ .SW .x12 .x7 off_dst)
    cpsTriple base (base + 8)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ dst_old))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ src_val) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ src_val)) := by
  runBlock

-- ============================================================================
-- DUP1 spec (Phase 2.3)
-- ============================================================================

set_option maxHeartbeats 6400000 in
theorem evm_dup1_spec (nsp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp 16) :
    let code :=
      (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
      ((base + 4) ↦ᵢ .LW .x7 .x12 32) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
      ((base + 12) ↦ᵢ .LW .x7 .x12 36) ** ((base + 16) ↦ᵢ .SW .x12 .x7 4) **
      ((base + 20) ↦ᵢ .LW .x7 .x12 40) ** ((base + 24) ↦ᵢ .SW .x12 .x7 8) **
      ((base + 28) ↦ᵢ .LW .x7 .x12 44) ** ((base + 32) ↦ᵢ .SW .x12 .x7 12) **
      ((base + 36) ↦ᵢ .LW .x7 .x12 48) ** ((base + 40) ↦ᵢ .SW .x12 .x7 16) **
      ((base + 44) ↦ᵢ .LW .x7 .x12 52) ** ((base + 48) ↦ᵢ .SW .x12 .x7 20) **
      ((base + 52) ↦ᵢ .LW .x7 .x12 56) ** ((base + 56) ↦ᵢ .SW .x12 .x7 24) **
      ((base + 60) ↦ᵢ .LW .x7 .x12 60) ** ((base + 64) ↦ᵢ .SW .x12 .x7 28)
    cpsTriple base (base + 68)
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
       ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
      (code **
       -- Registers + memory (copied)
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a7) **
       (nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) ** ((nsp + 12) ↦ₘ a3) **
       ((nsp + 16) ↦ₘ a4) ** ((nsp + 20) ↦ₘ a5) ** ((nsp + 24) ↦ₘ a6) ** ((nsp + 28) ↦ₘ a7) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
       ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7)) := by
  -- Compose ADDI + 8 dup1_pair_specs via runBlock
  have S0 := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at S0
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at S0
  have P0 := dup1_pair_spec nsp 32 0 a0 d0 v7 (base + 4) (by validMem) (by validMem)
  have P1 := dup1_pair_spec nsp 36 4 a1 d1 a0 (base + 12) (by validMem) (by validMem)
  have P2 := dup1_pair_spec nsp 40 8 a2 d2 a1 (base + 20) (by validMem) (by validMem)
  have P3 := dup1_pair_spec nsp 44 12 a3 d3 a2 (base + 28) (by validMem) (by validMem)
  have P4 := dup1_pair_spec nsp 48 16 a4 d4 a3 (base + 36) (by validMem) (by validMem)
  have P5 := dup1_pair_spec nsp 52 20 a5 d5 a4 (base + 44) (by validMem) (by validMem)
  have P6 := dup1_pair_spec nsp 56 24 a6 d6 a5 (base + 52) (by validMem) (by validMem)
  have P7 := dup1_pair_spec nsp 60 28 a7 d7 a6 (base + 60) (by validMem) (by validMem)
  runBlock S0 P0 P1 P2 P3 P4 P5 P6 P7

theorem evm_dup1_stack_spec (nsp base : Addr)
    (a : EvmWord) (d0 d1 d2 d3 d4 d5 d6 d7 : Word) (v7 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 16) :
    cpsTriple base (base + 68)
      (-- Code: ADDI then 8 LW/SW pairs
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .LW .x7 .x12 32) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LW .x7 .x12 36) ** ((base + 16) ↦ᵢ .SW .x12 .x7 4) **
       ((base + 20) ↦ᵢ .LW .x7 .x12 40) ** ((base + 24) ↦ᵢ .SW .x12 .x7 8) **
       ((base + 28) ↦ᵢ .LW .x7 .x12 44) ** ((base + 32) ↦ᵢ .SW .x12 .x7 12) **
       ((base + 36) ↦ᵢ .LW .x7 .x12 48) ** ((base + 40) ↦ᵢ .SW .x12 .x7 16) **
       ((base + 44) ↦ᵢ .LW .x7 .x12 52) ** ((base + 48) ↦ᵢ .SW .x12 .x7 20) **
       ((base + 52) ↦ᵢ .LW .x7 .x12 56) ** ((base + 56) ↦ᵢ .SW .x12 .x7 24) **
       ((base + 60) ↦ᵢ .LW .x7 .x12 60) ** ((base + 64) ↦ᵢ .SW .x12 .x7 28) **
       -- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       evmWordIs (nsp + 32) a ** evmStackIs (nsp + 64) rest)
      (-- Code (preserved)
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .LW .x7 .x12 32) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LW .x7 .x12 36) ** ((base + 16) ↦ᵢ .SW .x12 .x7 4) **
       ((base + 20) ↦ᵢ .LW .x7 .x12 40) ** ((base + 24) ↦ᵢ .SW .x12 .x7 8) **
       ((base + 28) ↦ᵢ .LW .x7 .x12 44) ** ((base + 32) ↦ᵢ .SW .x12 .x7 12) **
       ((base + 36) ↦ᵢ .LW .x7 .x12 48) ** ((base + 40) ↦ᵢ .SW .x12 .x7 16) **
       ((base + 44) ↦ᵢ .LW .x7 .x12 52) ** ((base + 48) ↦ᵢ .SW .x12 .x7 20) **
       ((base + 52) ↦ᵢ .LW .x7 .x12 56) ** ((base + 56) ↦ᵢ .SW .x12 .x7 24) **
       ((base + 60) ↦ᵢ .LW .x7 .x12 60) ** ((base + 64) ↦ᵢ .SW .x12 .x7 28) **
       -- Results
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a.getLimb 7) **
       evmWordIs nsp a ** evmWordIs (nsp + 32) a ** evmStackIs (nsp + 64) rest) := by
  -- Derive from evm_dup1_spec with evmStackIs as frame
  have h_main := cpsTriple_frame_left _ _ _ _
    (evmStackIs (nsp + 64) rest) (by pcFree)
    (evm_dup1_spec nsp base
      (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
      (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
      d0 d1 d2 d3 d4 d5 d6 d7 v7 hvalid)
  liftSpec h_main

-- ============================================================================
-- SWAP1 per-limb helper (Phase 2.4)
-- ============================================================================

/-- Four-instruction spec for SWAP1: loads a from off_a into x7, b from off_b into x6,
    writes b to off_a, writes a to off_b. Net effect: swaps the two memory cells. -/
theorem swap1_limb_spec (sp : Addr)
    (off_a off_b : BitVec 12) (a b v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let code :=
      (base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SW .x12 .x6 off_a) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a) ** (mem_b ↦ₘ b))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ b) **
       (mem_a ↦ₘ b) ** (mem_b ↦ₘ a)) := by
  runBlock

-- ============================================================================
-- SWAP1 spec (Phase 2.4)
-- ============================================================================

set_option maxHeartbeats 6400000 in
theorem evm_swap1_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    let code :=
      (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
      ((base + 8) ↦ᵢ .SW .x12 .x6 0) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
      ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
      ((base + 24) ↦ᵢ .SW .x12 .x6 4) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
      ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
      ((base + 40) ↦ᵢ .SW .x12 .x6 8) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
      ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
      ((base + 56) ↦ᵢ .SW .x12 .x6 12) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
      ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
      ((base + 72) ↦ᵢ .SW .x12 .x6 16) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
      ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
      ((base + 88) ↦ᵢ .SW .x12 .x6 20) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
      ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
      ((base + 104) ↦ᵢ .SW .x12 .x6 24) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
      ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
      ((base + 120) ↦ᵢ .SW .x12 .x6 28) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60)
    cpsTriple base (base + 128)
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (code **
       -- Registers + memory (swapped)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) ** ((sp + 12) ↦ₘ b3) **
       ((sp + 16) ↦ₘ b4) ** ((sp + 20) ↦ₘ b5) ** ((sp + 24) ↦ₘ b6) ** ((sp + 28) ↦ₘ b7) **
       ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** ((sp + 44) ↦ₘ a3) **
       ((sp + 48) ↦ₘ a4) ** ((sp + 52) ↦ₘ a5) ** ((sp + 56) ↦ₘ a6) ** ((sp + 60) ↦ₘ a7)) := by
  -- Compose 8 swap1_limb_specs via runBlock
  have L0 := swap1_limb_spec sp 0 32 a0 b0 v7 v6 base (by validMem) (by validMem)
  have L1 := swap1_limb_spec sp 4 36 a1 b1 a0 b0 (base + 16) (by validMem) (by validMem)
  have L2 := swap1_limb_spec sp 8 40 a2 b2 a1 b1 (base + 32) (by validMem) (by validMem)
  have L3 := swap1_limb_spec sp 12 44 a3 b3 a2 b2 (base + 48) (by validMem) (by validMem)
  have L4 := swap1_limb_spec sp 16 48 a4 b4 a3 b3 (base + 64) (by validMem) (by validMem)
  have L5 := swap1_limb_spec sp 20 52 a5 b5 a4 b4 (base + 80) (by validMem) (by validMem)
  have L6 := swap1_limb_spec sp 24 56 a6 b6 a5 b5 (base + 96) (by validMem) (by validMem)
  have L7 := swap1_limb_spec sp 28 60 a7 b7 a6 b6 (base + 112) (by validMem) (by validMem)
  runBlock L0 L1 L2 L3 L4 L5 L6 L7

set_option maxHeartbeats 3200000 in
theorem evm_swap1_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 128)
      (-- Limb 0 code
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 0) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 4) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 8) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 12) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 16) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 20) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 24) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 28) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b ** evmStackIs (sp + 64) rest)
      (-- Same code (preserved)
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 0) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 4) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 8) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 12) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 16) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 20) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 24) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 28) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a.getLimb 7) ** (.x6 ↦ᵣ b.getLimb 7) **
       evmWordIs sp b ** evmWordIs (sp + 32) a ** evmStackIs (sp + 64) rest) := by
  have h_main := cpsTriple_frame_left _ _ _ _
    (evmStackIs (sp + 64) rest)
    (by exact pcFree_evmStackIs (sp + 64) rest)
    (evm_swap1_spec sp base
      (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
      (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
      (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
      (b.getLimb 4) (b.getLimb 5) (b.getLimb 6) (b.getLimb 7)
      v7 v6 hvalid)
  liftSpec h_main

-- ============================================================================
-- Phase 2.5: Generic DUP (n : Nat) and SWAP (n : Nat)
-- ============================================================================

/-- Sign-extend a small non-negative 12-bit value to 32 bits.
    The MSB is clear when m < 2^11 = 2048, so signExtend = zeroExtend = identity. -/
theorem signExtend12_ofNat_small (m : Nat) (hm : m < 2048) :
    signExtend12 (BitVec.ofNat 12 m) = BitVec.ofNat 32 m := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

-- ============================================================================
-- Generic DUP program definition
-- ============================================================================

/-- One limb pair for DUP: LW x7 from source offset, SW x7 to destination offset. -/
private def dup_one_limb (n i : Nat) : Program :=
  LW .x7 .x12 (BitVec.ofNat 12 (n * 32 + i * 4)) ;;
  SW .x12 .x7 (BitVec.ofNat 12 (i * 4))

/-- Generic DUPn program (1-indexed): push copy of nth stack element on top.
    n=1 copies the top, n=2 copies the second element, etc.
    Uses 17 instructions: 1 ADDI + 8 × (LW + SW). -/
def evm_dup (n : Nat) : Program :=
  ADDI .x12 .x12 (-32) ;;
  dup_one_limb n 0 ;; dup_one_limb n 1 ;; dup_one_limb n 2 ;; dup_one_limb n 3 ;;
  dup_one_limb n 4 ;; dup_one_limb n 5 ;; dup_one_limb n 6 ;; dup_one_limb n 7

@[simp] theorem evm_dup_length (n : Nat) : (evm_dup n).length = 17 := by
  simp [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]

private theorem evm_dup_getElem_0 (n : Nat) :
    (show List Instr from evm_dup n)[0]? = some (Instr.ADDI .x12 .x12 (-32)) := by
  simp only [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]; rfl

private theorem evm_dup_getElem_lw (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_dup n)[2 * i + 1]? = some (Instr.LW .x7 .x12 (BitVec.ofNat 12 (n * 32 + i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]; rfl)

private theorem evm_dup_getElem_sw (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_dup n)[2 * i + 2]? = some (Instr.SW .x12 .x7 (BitVec.ofNat 12 (i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]; rfl)

-- ============================================================================
-- evmStackIs split lemma
-- ============================================================================

/-- Split evmStackIs at position k: extract the kth element (0-indexed). -/
theorem evmStackIs_split_at (sp : Addr) (stack : List EvmWord) (k : Nat)
    (hk : k < stack.length) :
    evmStackIs sp stack =
      (evmStackIs sp (stack.take k) **
       evmWordIs (sp + BitVec.ofNat 32 (k * 32)) (stack[k]'hk) **
       evmStackIs (sp + BitVec.ofNat 32 ((k + 1) * 32)) (stack.drop (k + 1))) := by
  induction k generalizing sp stack with
  | zero =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      simp only [Nat.zero_mul, List.take_zero,
                 List.drop_succ_cons, List.drop_zero, List.getElem_cons_zero,
                 evmStackIs_cons, evmStackIs_nil, sepConj_emp_left', BitVec.add_zero]
      congr 1
  | succ k ih =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      have hk' : k < vs.length := by simp at hk; omega
      have a1 : sp + (32 : Addr) + BitVec.ofNat 32 (k * 32) =
                sp + BitVec.ofNat 32 ((k + 1) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have a2 : sp + (32 : Addr) + BitVec.ofNat 32 ((k + 1) * 32) =
                sp + BitVec.ofNat 32 ((k + 2) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [evmStackIs_cons, ih (sp + 32) vs hk', a1, a2]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ]
      simp only [evmStackIs_cons, sepConj_assoc']

-- ============================================================================
-- Low-level DUP spec (explicit memory cells)
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Generic DUPn spec (low level): copies 8 limbs from src (at nsp+n*32) to dst (at nsp).
    Requires 1 ≤ n ≤ 16 (valid EVM DUP range). -/
theorem evm_dup_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    cpsTriple base (base + 68)
      (-- Code: ADDI then 8 LW/SW pairs
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
       ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
       ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
       ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
       ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
       ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
       ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
       ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
       ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
       ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
       ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
       ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
       ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
       ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
       ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
       ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
       -- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp+4) ↦ₘ d1) ** ((nsp+8) ↦ₘ d2) ** ((nsp+12) ↦ₘ d3) **
       ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
       ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
       ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
       ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
       ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
       ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
       ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
      (-- Same code (preserved)
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
       ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
       ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
       ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
       ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
       ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
       ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
       ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
       ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
       ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
       ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
       ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
       ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
       ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
       ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
       ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
       -- Registers + memory (copied)
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ s7) **
       (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
       ((nsp+16) ↦ₘ s4) ** ((nsp+20) ↦ₘ s5) ** ((nsp+24) ↦ₘ s6) ** ((nsp+28) ↦ₘ s7) **
       ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
       ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
       ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
       ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
       ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
       ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7)) := by
  -- ADDI result normalization
  have h_addi : (nsp + 32 : Word) + signExtend12 (-32 : BitVec 12) = nsp := by
    simp only [signExtend12_neg32]; bv_omega
  -- signExtend12 for source offsets (generic via signExtend12_ofNat_small)
  have hse_s0 : signExtend12 (BitVec.ofNat 12 (n*32)) = BitVec.ofNat 32 (n*32) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+4)) = BitVec.ofNat 32 (n*32+4) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 32 (n*32+8) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+12)) = BitVec.ofNat 32 (n*32+12) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s4 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 32 (n*32+16) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s5 : signExtend12 (BitVec.ofNat 12 (n*32+20)) = BitVec.ofNat 32 (n*32+20) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s6 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 32 (n*32+24) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s7 : signExtend12 (BitVec.ofNat 12 (n*32+28)) = BitVec.ofNat 32 (n*32+28) :=
    signExtend12_ofNat_small _ (by omega)
  -- Memory address normalization for dst offsets (use signExtend12_ofNat_small)
  have hse_d0  : signExtend12 (BitVec.ofNat 12 0)  = BitVec.ofNat 32 0  := signExtend12_ofNat_small _ (by omega)
  have hse_d4  : signExtend12 (BitVec.ofNat 12 4)  = BitVec.ofNat 32 4  := signExtend12_ofNat_small _ (by omega)
  have hse_d8  : signExtend12 (BitVec.ofNat 12 8)  = BitVec.ofNat 32 8  := signExtend12_ofNat_small _ (by omega)
  have hse_d12 : signExtend12 (BitVec.ofNat 12 12) = BitVec.ofNat 32 12 := signExtend12_ofNat_small _ (by omega)
  have hse_d16 : signExtend12 (BitVec.ofNat 12 16) = BitVec.ofNat 32 16 := signExtend12_ofNat_small _ (by omega)
  have hse_d20 : signExtend12 (BitVec.ofNat 12 20) = BitVec.ofNat 32 20 := signExtend12_ofNat_small _ (by omega)
  have hse_d24 : signExtend12 (BitVec.ofNat 12 24) = BitVec.ofNat 32 24 := signExtend12_ofNat_small _ (by omega)
  have hse_d28 : signExtend12 (BitVec.ofNat 12 28) = BitVec.ofNat 32 28 := signExtend12_ofNat_small _ (by omega)
  have hm0 : nsp + signExtend12 (BitVec.ofNat 12 0) = nsp := by rw [hse_d0]; bv_omega
  have hm4 : nsp + signExtend12 (BitVec.ofNat 12 4) = nsp + 4 := by rw [hse_d4]; bv_omega
  have hm8 : nsp + signExtend12 (BitVec.ofNat 12 8) = nsp + 8 := by rw [hse_d8]; bv_omega
  have hm12 : nsp + signExtend12 (BitVec.ofNat 12 12) = nsp + 12 := by rw [hse_d12]; bv_omega
  have hm16 : nsp + signExtend12 (BitVec.ofNat 12 16) = nsp + 16 := by rw [hse_d16]; bv_omega
  have hm20 : nsp + signExtend12 (BitVec.ofNat 12 20) = nsp + 20 := by rw [hse_d20]; bv_omega
  have hm24 : nsp + signExtend12 (BitVec.ofNat 12 24) = nsp + 24 := by rw [hse_d24]; bv_omega
  have hm28 : nsp + signExtend12 (BitVec.ofNat 12 28) = nsp + 28 := by rw [hse_d28]; bv_omega
  -- Memory validity from ValidMemRange for dst locations (indices 0..7)
  have hv0 : isValidMemAccess nsp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (nsp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (nsp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (nsp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (nsp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (nsp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (nsp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (nsp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Memory validity from ValidMemRange for src locations (indices n*8..n*8+7)
  have hvs0 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32)) = true := by
    have := hvalid.get (i := n*8) (by omega)
    rwa [show 4 * (n * 8) = n * 32 from by omega] at this
  have hvs4 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+4)) = true := by
    have := hvalid.get (i := n*8+1) (by omega)
    rwa [show 4 * (n * 8 + 1) = n * 32 + 4 from by omega] at this
  have hvs8 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+8)) = true := by
    have := hvalid.get (i := n*8+2) (by omega)
    rwa [show 4 * (n * 8 + 2) = n * 32 + 8 from by omega] at this
  have hvs12 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+12)) = true := by
    have := hvalid.get (i := n*8+3) (by omega)
    rwa [show 4 * (n * 8 + 3) = n * 32 + 12 from by omega] at this
  have hvs16 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+16)) = true := by
    have := hvalid.get (i := n*8+4) (by omega)
    rwa [show 4 * (n * 8 + 4) = n * 32 + 16 from by omega] at this
  have hvs20 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+20)) = true := by
    have := hvalid.get (i := n*8+5) (by omega)
    rwa [show 4 * (n * 8 + 5) = n * 32 + 20 from by omega] at this
  have hvs24 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+24)) = true := by
    have := hvalid.get (i := n*8+6) (by omega)
    rwa [show 4 * (n * 8 + 6) = n * 32 + 24 from by omega] at this
  have hvs28 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+28)) = true := by
    have := hvalid.get (i := n*8+7) (by omega)
    rwa [show 4 * (n * 8 + 7) = n * 32 + 28 from by omega] at this
  -- Step 1: ADDI x12 x12 (-32) at base
  have sA_raw := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  rw [h_addi] at sA_raw
  have sA := cpsTriple_frame_left _ _ _ _
    (((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (.x7 ↦ᵣ v7) **
     (nsp ↦ₘ d0) ** ((nsp+4) ↦ₘ d1) ** ((nsp+8) ↦ₘ d2) ** ((nsp+12) ↦ₘ d3) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) sA_raw
  clear sA_raw
  -- Step 2: Pair 0 - LW from nsp + n*32, SW to nsp
  have P0_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32)) (BitVec.ofNat 12 0) s0 d0 v7 (base + 4)
    (by rw [hse_s0]; exact hvs0) (by rw [hm0]; exact hv0)
  rw [hse_s0, signExtend12_ofNat_small 0 (by omega)] at P0_raw
  rw [show nsp + BitVec.ofNat 32 0 = nsp from by bv_omega] at P0_raw
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_addr,
      show (base + 4 : Addr) + 8 = base + 12 from by bv_addr] at P0_raw
  have P0 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     ((nsp+4) ↦ₘ d1) ** ((nsp+8) ↦ₘ d2) ** ((nsp+12) ↦ₘ d3) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P0_raw
  clear P0_raw
  have sAP0 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sA P0
  clear sA P0
  -- Step 3: Pair 1 - LW from nsp + n*32+4, SW to nsp+4
  have P1_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+4)) (BitVec.ofNat 12 4) s1 d1 s0 (base + 12)
    (by rw [hse_s1]; exact hvs4) (by rw [hm4]; exact hv4)
  rw [hse_s1, signExtend12_ofNat_small 4 (by omega)] at P1_raw
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_addr,
      show (base + 12 : Addr) + 8 = base + 20 from by bv_addr] at P1_raw
  have P1 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) **
     ((nsp+8) ↦ₘ d2) ** ((nsp+12) ↦ₘ d3) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P1_raw
  clear P1_raw
  have sAP01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP0 P1
  clear sAP0 P1
  -- Step 4: Pair 2 - LW from nsp + n*32+8, SW to nsp+8
  have P2_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+8)) (BitVec.ofNat 12 8) s2 d2 s1 (base + 20)
    (by rw [hse_s2]; exact hvs8) (by rw [hm8]; exact hv8)
  rw [hse_s2, signExtend12_ofNat_small 8 (by omega)] at P2_raw
  rw [show (base + 20 : Addr) + 4 = base + 24 from by bv_addr,
      show (base + 20 : Addr) + 8 = base + 28 from by bv_addr] at P2_raw
  have P2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) **
     ((nsp+12) ↦ₘ d3) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P2_raw
  clear P2_raw
  have sAP012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP01 P2
  clear sAP01 P2
  -- Step 5: Pair 3 - LW from nsp + n*32+12, SW to nsp+12
  have P3_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+12)) (BitVec.ofNat 12 12) s3 d3 s2 (base + 28)
    (by rw [hse_s3]; exact hvs12) (by rw [hm12]; exact hv12)
  rw [hse_s3, signExtend12_ofNat_small 12 (by omega)] at P3_raw
  rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_addr,
      show (base + 28 : Addr) + 8 = base + 36 from by bv_addr] at P3_raw
  have P3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P3_raw
  clear P3_raw
  have sAP0123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP012 P3
  clear sAP012 P3
  -- Step 6: Pair 4 - LW from nsp + n*32+16, SW to nsp+16
  have P4_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+16)) (BitVec.ofNat 12 16) s4 d4 s3 (base + 36)
    (by rw [hse_s4]; exact hvs16) (by rw [hm16]; exact hv16)
  rw [hse_s4, signExtend12_ofNat_small 16 (by omega)] at P4_raw
  rw [show (base + 36 : Addr) + 4 = base + 40 from by bv_addr,
      show (base + 36 : Addr) + 8 = base + 44 from by bv_addr] at P4_raw
  have P4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P4_raw
  clear P4_raw
  have sAP01234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP0123 P4
  clear sAP0123 P4
  -- Step 7: Pair 5 - LW from nsp + n*32+20, SW to nsp+20
  have P5_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+20)) (BitVec.ofNat 12 20) s5 d5 s4 (base + 44)
    (by rw [hse_s5]; exact hvs20) (by rw [hm20]; exact hv20)
  rw [hse_s5, signExtend12_ofNat_small 20 (by omega)] at P5_raw
  rw [show (base + 44 : Addr) + 4 = base + 48 from by bv_addr,
      show (base + 44 : Addr) + 8 = base + 52 from by bv_addr] at P5_raw
  have P5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+16) ↦ₘ s4) **
     ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P5_raw
  clear P5_raw
  have sAP012345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP01234 P5
  clear sAP01234 P5
  -- Step 8: Pair 6 - LW from nsp + n*32+24, SW to nsp+24
  have P6_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+24)) (BitVec.ofNat 12 24) s6 d6 s5 (base + 52)
    (by rw [hse_s6]; exact hvs24) (by rw [hm24]; exact hv24)
  rw [hse_s6, signExtend12_ofNat_small 24 (by omega)] at P6_raw
  rw [show (base + 52 : Addr) + 4 = base + 56 from by bv_addr,
      show (base + 52 : Addr) + 8 = base + 60 from by bv_addr] at P6_raw
  have P6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+16) ↦ₘ s4) ** ((nsp+20) ↦ₘ s5) **
     ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P6_raw
  clear P6_raw
  have sAP0123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP012345 P6
  clear sAP012345 P6
  -- Step 9: Pair 7 - LW from nsp + n*32+28, SW to nsp+28
  have P7_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+28)) (BitVec.ofNat 12 28) s7 d7 s6 (base + 60)
    (by rw [hse_s7]; exact hvs28) (by rw [hm28]; exact hv28)
  rw [hse_s7, signExtend12_ofNat_small 28 (by omega)] at P7_raw
  rw [show (base + 60 : Addr) + 4 = base + 64 from by bv_addr,
      show (base + 60 : Addr) + 8 = base + 68 from by bv_addr] at P7_raw
  have P7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+16) ↦ₘ s4) ** ((nsp+20) ↦ₘ s5) ** ((nsp+24) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6))
    (by pcFree) P7_raw
  clear P7_raw
  -- Final composition and permutation to match goal
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) sAP0123456 P7)

-- ============================================================================
-- Stack-level DUP spec
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- DUPn spec at evmWordIs level: copies the nth stack element (0-indexed: element n-1)
    from evmStackIs to a new top position, leaving the rest unchanged. -/
theorem evm_dup_evmword_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (src dst : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    cpsTriple base (base + 68)
      (-- Code
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
       ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
       ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
       ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
       ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
       ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
       ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
       ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
       ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
       ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
       ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
       ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
       ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
       ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
       ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
       ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
       -- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp dst **
       evmWordIs (nsp + BitVec.ofNat 32 (n * 32)) src)
      (-- Same code (preserved)
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
       ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
       ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
       ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
       ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
       ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
       ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
       ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
       ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
       ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
       ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
       ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
       ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
       ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
       ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
       ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
       -- Results
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ src.getLimb 7) **
       evmWordIs nsp src **
       evmWordIs (nsp + BitVec.ofNat 32 (n * 32)) src) := by
  -- Address normalizations for evmWordIs (nsp + BitVec.ofNat 32 (n*32))
  have haddr4  : (nsp + BitVec.ofNat 32 (n*32) : Addr) + 4  = nsp + BitVec.ofNat 32 (n*32+4)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr8  : (nsp + BitVec.ofNat 32 (n*32) : Addr) + 8  = nsp + BitVec.ofNat 32 (n*32+8)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr12 : (nsp + BitVec.ofNat 32 (n*32) : Addr) + 12 = nsp + BitVec.ofNat 32 (n*32+12) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr16 : (nsp + BitVec.ofNat 32 (n*32) : Addr) + 16 = nsp + BitVec.ofNat 32 (n*32+16) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr20 : (nsp + BitVec.ofNat 32 (n*32) : Addr) + 20 = nsp + BitVec.ofNat 32 (n*32+20) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr24 : (nsp + BitVec.ofNat 32 (n*32) : Addr) + 24 = nsp + BitVec.ofNat 32 (n*32+24) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr28 : (nsp + BitVec.ofNat 32 (n*32) : Addr) + 28 = nsp + BitVec.ofNat 32 (n*32+28) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Derive from evm_dup_spec
  have h_main := evm_dup_spec nsp base n hn1 hn16
    (src.getLimb 0) (src.getLimb 1) (src.getLimb 2) (src.getLimb 3)
    (src.getLimb 4) (src.getLimb 5) (src.getLimb 6) (src.getLimb 7)
    (dst.getLimb 0) (dst.getLimb 1) (dst.getLimb 2) (dst.getLimb 3)
    (dst.getLimb 4) (dst.getLimb 5) (dst.getLimb 6) (dst.getLimb 7)
    v7 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by
      simp only [evmWordIs, haddr4, haddr8, haddr12, haddr16, haddr20, haddr24, haddr28] at hp
      xperm_hyp hp)
    (fun _ hq => by
      simp only [evmWordIs, haddr4, haddr8, haddr12, haddr16, haddr20, haddr24, haddr28]
      xperm_hyp hq)
    h_main

set_option maxHeartbeats 3200000 in
/-- DUPn stack spec: copies the (n-1)-th element (0-indexed) from the stack
    to a new top, leaving the stack unchanged. -/
theorem evm_dup_stack_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n ≤ stack.length)
    (d : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    let vn := stack[n - 1]'(by omega)
    cpsTriple base (base + 68)
      (-- Code
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
       ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
       ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
       ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
       ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
       ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
       ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
       ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
       ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
       ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
       ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
       ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
       ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
       ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
       ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
       ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
       -- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp d **
       evmStackIs (nsp + 32) stack)
      (-- Same code (preserved)
       (base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
       ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
       ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
       ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
       ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
       ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
       ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
       ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
       ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
       ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
       ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
       ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
       ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
       ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
       ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
       ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
       -- Results
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ vn.getLimb 7) **
       evmWordIs nsp vn **
       evmStackIs (nsp + 32) stack) := by
  intro vn
  -- Split evmStackIs (nsp + 32) stack at position (n-1) to extract the target element
  have hk : n - 1 < stack.length := by omega
  have hsplit := evmStackIs_split_at (nsp + 32) stack (n - 1) hk
  -- Address normalizations
  have haddr_src : (nsp + 32 : Addr) + BitVec.ofNat 32 ((n - 1) * 32) =
      nsp + BitVec.ofNat 32 (n * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr_rest : (nsp + 32 : Addr) + BitVec.ofNat 32 (((n - 1) + 1) * 32) =
      nsp + BitVec.ofNat 32 (n * 32 + 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [haddr_src, haddr_rest, show n - 1 + 1 = n from by omega] at hsplit
  -- Frame the evm_dup_evmword_spec with the stack prefix and suffix
  have h_main := cpsTriple_frame_left _ _ _ _
    (evmStackIs (nsp + 32) (stack.take (n - 1)) **
     evmStackIs (nsp + BitVec.ofNat 32 (n * 32 + 32)) (stack.drop n))
    (by pcFree)
    (evm_dup_evmword_spec nsp base n hn1 hn16 vn d v7 hvalid)
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by rw [hsplit] at hp; xperm_hyp hp)
    (fun _ hq => by rw [hsplit]; xperm_hyp hq)
    h_main

-- ============================================================================
-- Generic SWAP program definition
-- ============================================================================

/-- One limb quad for SWAP: LW x7 from top, LW x6 from nth, SW x6 to top, SW x7 to nth. -/
private def swap_one_limb (n i : Nat) : Program :=
  LW .x7 .x12 (BitVec.ofNat 12 (i * 4)) ;;
  LW .x6 .x12 (BitVec.ofNat 12 (n * 32 + i * 4)) ;;
  SW .x12 .x6 (BitVec.ofNat 12 (i * 4)) ;;
  SW .x12 .x7 (BitVec.ofNat 12 (n * 32 + i * 4))

/-- Generic SWAPn program (1-indexed): swap the top element with the nth stack element.
    n=1 swaps top with 2nd, n=2 swaps top with 3rd, etc.
    Uses 32 instructions: 8 × (LW + LW + SW + SW). -/
def evm_swap (n : Nat) : Program :=
  swap_one_limb n 0 ;; swap_one_limb n 1 ;; swap_one_limb n 2 ;; swap_one_limb n 3 ;;
  swap_one_limb n 4 ;; swap_one_limb n 5 ;; swap_one_limb n 6 ;; swap_one_limb n 7

@[simp] theorem evm_swap_length (n : Nat) : (evm_swap n).length = 32 := by
  simp [evm_swap, swap_one_limb, LW, SW, single, seq]

private theorem evm_swap_getElem_lw1 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 0]? = some (Instr.LW .x7 .x12 (BitVec.ofNat 12 (i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

private theorem evm_swap_getElem_lw2 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 1]? = some (Instr.LW .x6 .x12 (BitVec.ofNat 12 (n * 32 + i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

private theorem evm_swap_getElem_sw1 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 2]? = some (Instr.SW .x12 .x6 (BitVec.ofNat 12 (i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

private theorem evm_swap_getElem_sw2 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 3]? = some (Instr.SW .x12 .x7 (BitVec.ofNat 12 (n * 32 + i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

-- ============================================================================
-- Low-level SWAP spec (explicit memory cells)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Generic SWAPn spec (low level): swaps 8 limbs at sp (top) with 8 limbs at sp+n*32 (nth).
    Requires 1 ≤ n ≤ 16 (valid EVM SWAP range). -/
theorem evm_swap_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    cpsTriple base (base + 128)
      (-- Limb 0 code
       (base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
       ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
       ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
       -- Limb 1 code
       ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
       ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
       ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
       -- Limb 2 code
       ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
       ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
       ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
       -- Limb 3 code
       ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
       ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
       ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
       -- Limb 4 code
       ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
       ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
       ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
       -- Limb 5 code
       ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
       ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
       ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
       -- Limb 6 code
       ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
       ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
       ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
       -- Limb 7 code
       ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
       ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
       ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp+4) ↦ₘ a1) ** ((sp+8) ↦ₘ a2) ** ((sp+12) ↦ₘ a3) **
       ((sp+16) ↦ₘ a4) ** ((sp+20) ↦ₘ a5) ** ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
       ((sp + BitVec.ofNat 32 (n*32))    ↦ₘ b0) **
       ((sp + BitVec.ofNat 32 (n*32+4))  ↦ₘ b1) **
       ((sp + BitVec.ofNat 32 (n*32+8))  ↦ₘ b2) **
       ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ b3) **
       ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ b4) **
       ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ b5) **
       ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
       ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
      (-- Same code (preserved)
       (base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
       ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
       ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
       ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
       ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
       ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
       ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
       ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
       ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
       ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
       ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
       ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
       ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
       ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
       ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
       ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
       ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
       -- Registers + memory (swapped)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) ** ((sp+8) ↦ₘ b2) ** ((sp+12) ↦ₘ b3) **
       ((sp+16) ↦ₘ b4) ** ((sp+20) ↦ₘ b5) ** ((sp+24) ↦ₘ b6) ** ((sp+28) ↦ₘ b7) **
       ((sp + BitVec.ofNat 32 (n*32))    ↦ₘ a0) **
       ((sp + BitVec.ofNat 32 (n*32+4))  ↦ₘ a1) **
       ((sp + BitVec.ofNat 32 (n*32+8))  ↦ₘ a2) **
       ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ a3) **
       ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ a4) **
       ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ a5) **
       ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ a6) **
       ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ a7)) := by
  -- signExtend12 for n-dependent source offsets
  have hse_s0 : signExtend12 (BitVec.ofNat 12 (n*32)) = BitVec.ofNat 32 (n*32) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+4)) = BitVec.ofNat 32 (n*32+4) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 32 (n*32+8) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+12)) = BitVec.ofNat 32 (n*32+12) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s4 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 32 (n*32+16) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s5 : signExtend12 (BitVec.ofNat 12 (n*32+20)) = BitVec.ofNat 32 (n*32+20) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s6 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 32 (n*32+24) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s7 : signExtend12 (BitVec.ofNat 12 (n*32+28)) = BitVec.ofNat 32 (n*32+28) :=
    signExtend12_ofNat_small _ (by omega)
  -- signExtend12 for destination offsets (0,4,...,28)
  have hse_d0  : signExtend12 (BitVec.ofNat 12 0)  = BitVec.ofNat 32 0  := signExtend12_ofNat_small _ (by omega)
  have hse_d4  : signExtend12 (BitVec.ofNat 12 4)  = BitVec.ofNat 32 4  := signExtend12_ofNat_small _ (by omega)
  have hse_d8  : signExtend12 (BitVec.ofNat 12 8)  = BitVec.ofNat 32 8  := signExtend12_ofNat_small _ (by omega)
  have hse_d12 : signExtend12 (BitVec.ofNat 12 12) = BitVec.ofNat 32 12 := signExtend12_ofNat_small _ (by omega)
  have hse_d16 : signExtend12 (BitVec.ofNat 12 16) = BitVec.ofNat 32 16 := signExtend12_ofNat_small _ (by omega)
  have hse_d20 : signExtend12 (BitVec.ofNat 12 20) = BitVec.ofNat 32 20 := signExtend12_ofNat_small _ (by omega)
  have hse_d24 : signExtend12 (BitVec.ofNat 12 24) = BitVec.ofNat 32 24 := signExtend12_ofNat_small _ (by omega)
  have hse_d28 : signExtend12 (BitVec.ofNat 12 28) = BitVec.ofNat 32 28 := signExtend12_ofNat_small _ (by omega)
  -- Memory address normalizations for destination offsets
  have hm0  : sp + signExtend12 (BitVec.ofNat 12 0)  = sp      := by rw [hse_d0]; bv_omega
  have hm4  : sp + signExtend12 (BitVec.ofNat 12 4)  = sp + 4  := by rw [hse_d4]; bv_omega
  have hm8  : sp + signExtend12 (BitVec.ofNat 12 8)  = sp + 8  := by rw [hse_d8]; bv_omega
  have hm12 : sp + signExtend12 (BitVec.ofNat 12 12) = sp + 12 := by rw [hse_d12]; bv_omega
  have hm16 : sp + signExtend12 (BitVec.ofNat 12 16) = sp + 16 := by rw [hse_d16]; bv_omega
  have hm20 : sp + signExtend12 (BitVec.ofNat 12 20) = sp + 20 := by rw [hse_d20]; bv_omega
  have hm24 : sp + signExtend12 (BitVec.ofNat 12 24) = sp + 24 := by rw [hse_d24]; bv_omega
  have hm28 : sp + signExtend12 (BitVec.ofNat 12 28) = sp + 28 := by rw [hse_d28]; bv_omega
  -- Memory validity for destination locations (indices 0..7)
  have hv0  : isValidMemAccess sp       = true := by have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4  : isValidMemAccess (sp + 4)  = true := by have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8  : isValidMemAccess (sp + 8)  = true := by have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by have := hvalid.get (i := 7) (by omega); simpa using this
  -- Memory validity for source locations (indices n*8..n*8+7)
  have hvs0  : isValidMemAccess (sp + BitVec.ofNat 32 (n*32))     = true := by
    have := hvalid.get (i := n*8) (by omega); rwa [show 4 * (n * 8) = n * 32 from by omega] at this
  have hvs4  : isValidMemAccess (sp + BitVec.ofNat 32 (n*32+4))   = true := by
    have := hvalid.get (i := n*8+1) (by omega); rwa [show 4 * (n * 8 + 1) = n * 32 + 4 from by omega] at this
  have hvs8  : isValidMemAccess (sp + BitVec.ofNat 32 (n*32+8))   = true := by
    have := hvalid.get (i := n*8+2) (by omega); rwa [show 4 * (n * 8 + 2) = n * 32 + 8 from by omega] at this
  have hvs12 : isValidMemAccess (sp + BitVec.ofNat 32 (n*32+12))  = true := by
    have := hvalid.get (i := n*8+3) (by omega); rwa [show 4 * (n * 8 + 3) = n * 32 + 12 from by omega] at this
  have hvs16 : isValidMemAccess (sp + BitVec.ofNat 32 (n*32+16))  = true := by
    have := hvalid.get (i := n*8+4) (by omega); rwa [show 4 * (n * 8 + 4) = n * 32 + 16 from by omega] at this
  have hvs20 : isValidMemAccess (sp + BitVec.ofNat 32 (n*32+20))  = true := by
    have := hvalid.get (i := n*8+5) (by omega); rwa [show 4 * (n * 8 + 5) = n * 32 + 20 from by omega] at this
  have hvs24 : isValidMemAccess (sp + BitVec.ofNat 32 (n*32+24))  = true := by
    have := hvalid.get (i := n*8+6) (by omega); rwa [show 4 * (n * 8 + 6) = n * 32 + 24 from by omega] at this
  have hvs28 : isValidMemAccess (sp + BitVec.ofNat 32 (n*32+28))  = true := by
    have := hvalid.get (i := n*8+7) (by omega); rwa [show 4 * (n * 8 + 7) = n * 32 + 28 from by omega] at this
  -- Memory validity via signExtend12 for swap1_limb_spec
  have hvm_d0  : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 0))  = true := by rw [hm0]; exact hv0
  have hvm_d4  : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 4))  = true := by rw [hm4]; exact hv4
  have hvm_d8  : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 8))  = true := by rw [hm8]; exact hv8
  have hvm_d12 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 12)) = true := by rw [hm12]; exact hv12
  have hvm_d16 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 16)) = true := by rw [hm16]; exact hv16
  have hvm_d20 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 20)) = true := by rw [hm20]; exact hv20
  have hvm_d24 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 24)) = true := by rw [hm24]; exact hv24
  have hvm_d28 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 28)) = true := by rw [hm28]; exact hv28
  have hvm_s0  : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32)))    = true := by rw [hse_s0]; exact hvs0
  have hvm_s4  : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+4)))  = true := by rw [hse_s1]; exact hvs4
  have hvm_s8  : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+8)))  = true := by rw [hse_s2]; exact hvs8
  have hvm_s12 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+12))) = true := by rw [hse_s3]; exact hvs12
  have hvm_s16 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+16))) = true := by rw [hse_s4]; exact hvs16
  have hvm_s20 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+20))) = true := by rw [hse_s5]; exact hvs20
  have hvm_s24 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+24))) = true := by rw [hse_s6]; exact hvs24
  have hvm_s28 : isValidMemAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+28))) = true := by rw [hse_s7]; exact hvs28
  -- Limb 0: swap at base, offsets (BitVec.ofNat 12 0) and (BitVec.ofNat 12 (n*32))
  have L0_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 0) (BitVec.ofNat 12 (n*32))
    a0 b0 v7 v6 base hvm_d0 hvm_s0
  rw [hm0, hse_s0] at L0_raw
  have L0 := cpsTriple_frame_left _ _ _ _
    (((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
     ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
     ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
     ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
     ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
     ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
     ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
     ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
     ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
     ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
     ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
     ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
     ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
     ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
     ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
     ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
     ((sp+4) ↦ₘ a1) ** ((sp+8) ↦ₘ a2) ** ((sp+12) ↦ₘ a3) **
     ((sp+16) ↦ₘ a4) ** ((sp+20) ↦ₘ a5) ** ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
     ((sp + BitVec.ofNat 32 (n*32+4))  ↦ₘ b1) **
     ((sp + BitVec.ofNat 32 (n*32+8))  ↦ₘ b2) **
     ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ b3) **
     ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ b4) **
     ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ b5) **
     ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
     ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
    (by pcFree) L0_raw
  clear L0_raw
  -- Limb 1: swap at base+16, offsets 4 and n*32+4
  have L1_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 4) (BitVec.ofNat 12 (n*32+4))
    a1 b1 a0 b0 (base + 16) hvm_d4 hvm_s4
  rw [hm4, hse_s1] at L1_raw
  rw [show (base + 16 : Addr) + 4 = base + 20 from by bv_omega,
      show (base + 16 : Addr) + 8 = base + 24 from by bv_omega,
      show (base + 16 : Addr) + 12 = base + 28 from by bv_omega,
      show (base + 16 : Addr) + 16 = base + 32 from by bv_omega] at L1_raw
  have L1 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
     ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
     ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
     ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
     ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
     ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
     ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
     ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
     ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
     ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
     ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
     ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
     ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
     ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
     ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
     ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
     (sp ↦ₘ b0) ** ((sp + BitVec.ofNat 32 (n*32)) ↦ₘ a0) **
     ((sp+8) ↦ₘ a2) ** ((sp+12) ↦ₘ a3) **
     ((sp+16) ↦ₘ a4) ** ((sp+20) ↦ₘ a5) ** ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
     ((sp + BitVec.ofNat 32 (n*32+8))  ↦ₘ b2) **
     ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ b3) **
     ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ b4) **
     ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ b5) **
     ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
     ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
    (by pcFree) L1_raw
  clear L1_raw
  have L01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L0 L1
  clear L0 L1
  -- Limb 2: swap at base+32, offsets 8 and n*32+8
  have L2_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 8) (BitVec.ofNat 12 (n*32+8))
    a2 b2 a1 b1 (base + 32) hvm_d8 hvm_s8
  rw [hm8, hse_s2] at L2_raw
  rw [show (base + 32 : Addr) + 4 = base + 36 from by bv_omega,
      show (base + 32 : Addr) + 8 = base + 40 from by bv_omega,
      show (base + 32 : Addr) + 12 = base + 44 from by bv_omega,
      show (base + 32 : Addr) + 16 = base + 48 from by bv_omega] at L2_raw
  have L2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
     ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
     ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
     ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
     ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
     ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
     ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
     ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
     ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
     ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
     ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
     ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
     ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
     ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
     ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
     ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
     (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) **
     ((sp + BitVec.ofNat 32 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 32 (n*32+4)) ↦ₘ a1) **
     ((sp+12) ↦ₘ a3) **
     ((sp+16) ↦ₘ a4) ** ((sp+20) ↦ₘ a5) ** ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
     ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ b3) **
     ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ b4) **
     ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ b5) **
     ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
     ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
    (by pcFree) L2_raw
  clear L2_raw
  have L012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L01 L2
  clear L01 L2
  -- Limb 3: swap at base+48, offsets 12 and n*32+12
  have L3_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 12) (BitVec.ofNat 12 (n*32+12))
    a3 b3 a2 b2 (base + 48) hvm_d12 hvm_s12
  rw [hm12, hse_s3] at L3_raw
  rw [show (base + 48 : Addr) + 4 = base + 52 from by bv_omega,
      show (base + 48 : Addr) + 8 = base + 56 from by bv_omega,
      show (base + 48 : Addr) + 12 = base + 60 from by bv_omega,
      show (base + 48 : Addr) + 16 = base + 64 from by bv_omega] at L3_raw
  have L3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
     ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
     ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
     ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
     ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
     ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
     ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
     ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
     ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
     ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
     ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
     ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
     ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
     ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
     ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
     ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
     (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) ** ((sp+8) ↦ₘ b2) **
     ((sp + BitVec.ofNat 32 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 32 (n*32+4)) ↦ₘ a1) ** ((sp + BitVec.ofNat 32 (n*32+8)) ↦ₘ a2) **
     ((sp+16) ↦ₘ a4) ** ((sp+20) ↦ₘ a5) ** ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
     ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ b4) **
     ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ b5) **
     ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
     ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
    (by pcFree) L3_raw
  clear L3_raw
  have L0123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L012 L3
  clear L012 L3
  -- Limb 4: swap at base+64, offsets 16 and n*32+16
  have L4_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 16) (BitVec.ofNat 12 (n*32+16))
    a4 b4 a3 b3 (base + 64) hvm_d16 hvm_s16
  rw [hm16, hse_s4] at L4_raw
  rw [show (base + 64 : Addr) + 4 = base + 68 from by bv_omega,
      show (base + 64 : Addr) + 8 = base + 72 from by bv_omega,
      show (base + 64 : Addr) + 12 = base + 76 from by bv_omega,
      show (base + 64 : Addr) + 16 = base + 80 from by bv_omega] at L4_raw
  have L4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
     ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
     ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
     ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
     ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
     ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
     ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
     ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
     ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
     ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
     ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
     ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
     ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
     ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
     ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
     ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
     (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) ** ((sp+8) ↦ₘ b2) ** ((sp+12) ↦ₘ b3) **
     ((sp + BitVec.ofNat 32 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 32 (n*32+4)) ↦ₘ a1) **
     ((sp + BitVec.ofNat 32 (n*32+8)) ↦ₘ a2) ** ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ a3) **
     ((sp+20) ↦ₘ a5) ** ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
     ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ b5) **
     ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
     ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
    (by pcFree) L4_raw
  clear L4_raw
  have L01234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L0123 L4
  clear L0123 L4
  -- Limb 5: swap at base+80, offsets 20 and n*32+20
  have L5_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 20) (BitVec.ofNat 12 (n*32+20))
    a5 b5 a4 b4 (base + 80) hvm_d20 hvm_s20
  rw [hm20, hse_s5] at L5_raw
  rw [show (base + 80 : Addr) + 4 = base + 84 from by bv_omega,
      show (base + 80 : Addr) + 8 = base + 88 from by bv_omega,
      show (base + 80 : Addr) + 12 = base + 92 from by bv_omega,
      show (base + 80 : Addr) + 16 = base + 96 from by bv_omega] at L5_raw
  have L5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
     ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
     ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
     ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
     ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
     ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
     ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
     ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
     ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
     ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
     ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
     ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
     ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
     ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
     ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
     ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
     (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) ** ((sp+8) ↦ₘ b2) ** ((sp+12) ↦ₘ b3) ** ((sp+16) ↦ₘ b4) **
     ((sp + BitVec.ofNat 32 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 32 (n*32+4)) ↦ₘ a1) **
     ((sp + BitVec.ofNat 32 (n*32+8)) ↦ₘ a2) ** ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ a3) **
     ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ a4) **
     ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
     ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
     ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
    (by pcFree) L5_raw
  clear L5_raw
  have L012345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L01234 L5
  clear L01234 L5
  -- Limb 6: swap at base+96, offsets 24 and n*32+24
  have L6_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 24) (BitVec.ofNat 12 (n*32+24))
    a6 b6 a5 b5 (base + 96) hvm_d24 hvm_s24
  rw [hm24, hse_s6] at L6_raw
  rw [show (base + 96 : Addr) + 4 = base + 100 from by bv_omega,
      show (base + 96 : Addr) + 8 = base + 104 from by bv_omega,
      show (base + 96 : Addr) + 12 = base + 108 from by bv_omega,
      show (base + 96 : Addr) + 16 = base + 112 from by bv_omega] at L6_raw
  have L6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
     ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
     ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
     ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
     ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
     ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
     ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
     ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
     ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
     ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
     ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
     ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
     ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
     ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
     ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
     ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
     (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) ** ((sp+8) ↦ₘ b2) ** ((sp+12) ↦ₘ b3) **
     ((sp+16) ↦ₘ b4) ** ((sp+20) ↦ₘ b5) **
     ((sp + BitVec.ofNat 32 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 32 (n*32+4)) ↦ₘ a1) **
     ((sp + BitVec.ofNat 32 (n*32+8)) ↦ₘ a2) ** ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ a3) **
     ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ a4) ** ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ a5) **
     ((sp+28) ↦ₘ a7) **
     ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
    (by pcFree) L6_raw
  clear L6_raw
  have L0123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L012345 L6
  clear L012345 L6
  -- Limb 7: swap at base+112, offsets 28 and n*32+28
  have L7_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 28) (BitVec.ofNat 12 (n*32+28))
    a7 b7 a6 b6 (base + 112) hvm_d28 hvm_s28
  rw [hm28, hse_s7] at L7_raw
  rw [show (base + 112 : Addr) + 4 = base + 116 from by bv_omega,
      show (base + 112 : Addr) + 8 = base + 120 from by bv_omega,
      show (base + 112 : Addr) + 12 = base + 124 from by bv_omega,
      show (base + 112 : Addr) + 16 = base + 128 from by bv_omega] at L7_raw
  have L7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
     ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
     ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
     ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
     ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
     ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
     ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
     ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
     ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
     ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
     ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
     ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
     ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
     ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
     ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
     ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
     (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) ** ((sp+8) ↦ₘ b2) ** ((sp+12) ↦ₘ b3) **
     ((sp+16) ↦ₘ b4) ** ((sp+20) ↦ₘ b5) ** ((sp+24) ↦ₘ b6) **
     ((sp + BitVec.ofNat 32 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 32 (n*32+4)) ↦ₘ a1) **
     ((sp + BitVec.ofNat 32 (n*32+8)) ↦ₘ a2) ** ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ a3) **
     ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ a4) ** ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ a5) **
     ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ a6))
    (by pcFree) L7_raw
  clear L7_raw
  -- Final composition and permutation to match goal
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) L0123456 L7)

-- ============================================================================
-- Stack-level SWAP spec
-- ============================================================================

/-- SWAPn spec at evmWordIs level: swaps the top and nth stack elements. -/
theorem evm_swap_evmword_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (top nth : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    cpsTriple base (base + 128)
      (-- Code
       (base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
       ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
       ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
       ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
       ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
       ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
       ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
       ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
       ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
       ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
       ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
       ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
       ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
       ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
       ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
       ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
       ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
       -- Registers + data
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp top **
       evmWordIs (sp + BitVec.ofNat 32 (n * 32)) nth)
      (-- Code (preserved)
       (base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
       ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
       ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
       ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
       ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
       ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
       ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
       ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
       ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
       ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
       ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
       ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
       ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
       ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
       ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
       ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
       ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
       -- Registers + data (swapped)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 7) ** (.x6 ↦ᵣ nth.getLimb 7) **
       evmWordIs sp nth **
       evmWordIs (sp + BitVec.ofNat 32 (n * 32)) top) := by
  -- Address normalizations for evmWordIs (sp + BitVec.ofNat 32 (n * 32))
  have ha4  : (sp + BitVec.ofNat 32 (n * 32) : Addr) + 4  = sp + BitVec.ofNat 32 (n*32+4)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha8  : (sp + BitVec.ofNat 32 (n * 32) : Addr) + 8  = sp + BitVec.ofNat 32 (n*32+8)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha12 : (sp + BitVec.ofNat 32 (n * 32) : Addr) + 12 = sp + BitVec.ofNat 32 (n*32+12) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha16 : (sp + BitVec.ofNat 32 (n * 32) : Addr) + 16 = sp + BitVec.ofNat 32 (n*32+16) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha20 : (sp + BitVec.ofNat 32 (n * 32) : Addr) + 20 = sp + BitVec.ofNat 32 (n*32+20) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha24 : (sp + BitVec.ofNat 32 (n * 32) : Addr) + 24 = sp + BitVec.ofNat 32 (n*32+24) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha28 : (sp + BitVec.ofNat 32 (n * 32) : Addr) + 28 = sp + BitVec.ofNat 32 (n*32+28) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs, ha4, ha8, ha12, ha16, ha20, ha24, ha28] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, ha4, ha8, ha12, ha16, ha20, ha24, ha28]
      xperm_hyp hq)
    (evm_swap_spec sp base n hn1 hn16
      (top.getLimb 0) (top.getLimb 1) (top.getLimb 2) (top.getLimb 3)
      (top.getLimb 4) (top.getLimb 5) (top.getLimb 6) (top.getLimb 7)
      (nth.getLimb 0) (nth.getLimb 1) (nth.getLimb 2) (nth.getLimb 3)
      (nth.getLimb 4) (nth.getLimb 5) (nth.getLimb 6) (nth.getLimb 7)
      v7 v6 hvalid)

/-- SWAPn stack spec: swaps top with the nth element (1-indexed) of the stack. -/
theorem evm_swap_stack_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n + 1 ≤ stack.length)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    let top := stack[0]'(by omega)
    let nth := stack[n]'(by omega)
    cpsTriple base (base + 128)
      (-- Code
       (base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
       ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
       ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
       ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
       ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
       ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
       ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
       ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
       ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
       ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
       ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
       ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
       ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
       ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
       ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
       ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
       ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
       -- Registers + data
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmStackIs sp stack)
      (-- Code (preserved)
       (base ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 0)) **
       ((base + 4) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32))) **
       ((base + 8) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 0)) **
       ((base + 12) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32))) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 4)) **
       ((base + 20) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 24) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 4)) **
       ((base + 28) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 8)) **
       ((base + 36) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 40) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 8)) **
       ((base + 44) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 12)) **
       ((base + 52) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 56) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 12)) **
       ((base + 60) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 16)) **
       ((base + 68) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 72) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 16)) **
       ((base + 76) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 20)) **
       ((base + 84) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 88) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 20)) **
       ((base + 92) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 24)) **
       ((base + 100) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 104) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 24)) **
       ((base + 108) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 28)) **
       ((base + 116) ↦ᵢ .LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))) **
       ((base + 120) ↦ᵢ .SW .x12 .x6 (BitVec.ofNat 12 28)) **
       ((base + 124) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))) **
       -- Registers + data (swapped)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 7) ** (.x6 ↦ᵣ nth.getLimb 7) **
       evmWordIs sp nth **
       evmStackIs (sp + 32) ((stack.drop 1).take (n - 1)) **
       evmWordIs (sp + BitVec.ofNat 32 (n * 32)) top **
       evmStackIs (sp + BitVec.ofNat 32 ((n + 1) * 32)) ((stack.drop 1).drop n)) := by
  intro top nth
  -- Split evmStackIs sp stack at position 0 to extract the top element
  have hk0 : 0 < stack.length := by omega
  have hsplit0 := evmStackIs_split_at sp stack 0 hk0
  -- Split the tail (stack.drop 1) at position (n-1) to extract the nth element
  have htail_len : n - 1 < (stack.drop 1).length := by simp; omega
  have hsplit1 := evmStackIs_split_at (sp + 32) (stack.drop 1) (n - 1) htail_len
  -- Address normalizations
  have haddr_src : (sp + 32 : Addr) + BitVec.ofNat 32 ((n - 1) * 32) =
      sp + BitVec.ofNat 32 (n * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr_rest : (sp + 32 : Addr) + BitVec.ofNat 32 (((n - 1) + 1) * 32) =
      sp + BitVec.ofNat 32 ((n + 1) * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Simplify the element access: (stack.drop 1)[n-1] = stack[n]
  have helem : (stack.drop 1)[n - 1]'htail_len = stack[n]'(by omega) := by
    simp; congr 1; omega
  rw [haddr_src, haddr_rest, show (n - 1) + 1 = n from by omega, helem] at hsplit1
  -- Frame the evm_swap_evmword_spec with the middle and rest stacks
  have h_main := cpsTriple_frame_left _ _ _ _
    (evmStackIs (sp + 32) ((stack.drop 1).take (n - 1)) **
     evmStackIs (sp + BitVec.ofNat 32 ((n + 1) * 32)) ((stack.drop 1).drop n))
    (by pcFree)
    (evm_swap_evmword_spec sp base n hn1 hn16 top nth v7 v6 hvalid)
  have haddr32 : (sp + BitVec.ofNat 32 (1 * 32) : Addr) = sp + 32 := by bv_omega
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      rw [hsplit0] at hp
      simp only [Nat.zero_mul, List.take_zero, evmStackIs_nil, sepConj_emp_left',
                  BitVec.add_zero, haddr32] at hp
      rw [hsplit1] at hp
      xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_main

end EvmAsm
