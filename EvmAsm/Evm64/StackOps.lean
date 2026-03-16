/-
  EvmAsm.Evm64.StackOps

  Verified 256-bit EVM stack manipulation opcodes (RV64):
  - POP: discard top of stack, sp += 32. 1 instruction.
  - PUSH0: push 0 onto stack, sp -= 32. 5 instructions.
  - DUP1: duplicate top of stack, sp -= 32. 9 instructions.
  - SWAP1: swap top two stack items, sp unchanged. 16 instructions.
  - DUP1-16 (generic): evm_dup n, 9 instructions. Proved for 1 ≤ n ≤ 16.
  - SWAP1-16 (generic): evm_swap n, 16 instructions. Proved for 1 ≤ n ≤ 16.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

@[simp] theorem EvmWord.getLimb_zero (i : Fin 4) : (0 : EvmWord).getLimb i = 0 := by
  have h : ∀ j : Fin 4, (0 : EvmWord).getLimb j = 0 := by native_decide
  exact h i

@[simp] theorem signExtend12_neg32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by
  native_decide

-- ============================================================================
-- Program definitions
-- ============================================================================

def evm_pop : Program := ADDI .x12 .x12 32

def evm_push0 : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

def evm_dup1 : Program :=
  ADDI .x12 .x12 (-32) ;;
  LD .x7 .x12 32 ;; SD .x12 .x7 0 ;;
  LD .x7 .x12 40 ;; SD .x12 .x7 8 ;;
  LD .x7 .x12 48 ;; SD .x12 .x7 16 ;;
  LD .x7 .x12 56 ;; SD .x12 .x7 24

def evm_swap1 : Program :=
  LD .x7 .x12 0  ;; LD .x6 .x12 32 ;; SD .x12 .x6 0  ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8  ;; LD .x6 .x12 40 ;; SD .x12 .x6 8  ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; SD .x12 .x6 16 ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; SD .x12 .x6 24 ;; SD .x12 .x7 56

-- ============================================================================
-- POP spec
-- ============================================================================

theorem evm_pop_spec (sp base : Addr) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI .x12 .x12 32))
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + 32)) := by
  have h := addi_spec_gen_same .x12 sp 32 base (by nofun)
  simp only [signExtend12_32] at h; exact h

theorem evm_pop_stack_spec (sp base : Addr)
    (a : EvmWord) (rest : List EvmWord) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI .x12 .x12 32))
      ((.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) :=
  cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => (sepConj_assoc _ _ _ h).mpr hp)
    (fun h hq => (sepConj_assoc _ _ _ h).mp hq)
    (cpsTriple_frame_left _ _ _ _ _ (evmWordIs sp a ** evmStackIs (sp + 32) rest) (by pcFree) (evm_pop_spec sp base))

-- ============================================================================
-- PUSH0 spec
-- ============================================================================

/-- CodeReq for the 256-bit EVM PUSH0 operation. 5 instructions. -/
abbrev evm_push0_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 (-32)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x0 0))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x0 8))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x0 16))
   (CodeReq.singleton (base + 16) (.SD .x12 .x0 24)))))

set_option maxHeartbeats 6400000 in
theorem evm_push0_spec (nsp base : Addr)
    (d0 d1 d2 d3 : Word)
    (hvalid : ValidMemRange nsp 4) :
    let code := evm_push0_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have LADDI := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  have L0 := sd_x0_spec_gen .x12 nsp d0 0 (base + 4) (by validMem)
  have L1 := sd_x0_spec_gen .x12 nsp d1 8 (base + 8) (by validMem)
  have L2 := sd_x0_spec_gen .x12 nsp d2 16 (base + 12) (by validMem)
  have L3 := sd_x0_spec_gen .x12 nsp d3 24 (base + 16) (by validMem)
  runBlock LADDI L0 L1 L2 L3

theorem evm_push0_stack_spec (nsp base : Addr)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 4) :
    let code := evm_push0_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmStackIs (nsp + 32) rest)
      ((.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) :=
  cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_zero]; xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (evmStackIs (nsp + 32) rest)
      (by exact pcFree_evmStackIs (nsp + 32) rest)
      (evm_push0_spec nsp base d0 d1 d2 d3 hvalid))

-- ============================================================================
-- DUP1 per-pair helper
-- ============================================================================

/-- Two-instruction spec for DUP1: LD x7 from source, SD x7 to destination.
    Copies src_val from src address to dst address. -/
theorem dup1_pair_spec (sp : Addr)
    (off_src off_dst : BitVec 12) (src_val dst_old v7 : Word) (base : Addr)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 off_src) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 off_dst) = true) :
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_src))
       (CodeReq.singleton (base + 4) (.SD .x12 .x7 off_dst))
    cpsTriple base (base + 8) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ src_val) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ src_val)) := by
  runBlock

-- ============================================================================
-- DUP1 spec
-- ============================================================================

/-- CodeReq for the 256-bit EVM DUP1 operation. 9 instructions. -/
abbrev evm_dup1_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 (-32)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x7 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x7 0))
  (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x7 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SD .x12 .x7 8))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x7 16))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 56))
   (CodeReq.singleton (base + 32) (.SD .x12 .x7 24)))))))))

set_option maxHeartbeats 6400000 in
theorem evm_dup1_spec (nsp base : Addr)
    (a0 a1 a2 a3 d0 d1 d2 d3 : Word) (v7 : Word)
    (hvalid : ValidMemRange nsp 8) :
    let code := evm_dup1_code base
    cpsTriple base (base + 36) code
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 40) ↦ₘ a1) ** ((nsp + 48) ↦ₘ a2) ** ((nsp + 56) ↦ₘ a3))
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a3) **
       (nsp ↦ₘ a0) ** ((nsp + 8) ↦ₘ a1) ** ((nsp + 16) ↦ₘ a2) ** ((nsp + 24) ↦ₘ a3) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 40) ↦ₘ a1) ** ((nsp + 48) ↦ₘ a2) ** ((nsp + 56) ↦ₘ a3)) := by
  have LADDI := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  have P0 := dup1_pair_spec nsp 32 0 a0 d0 v7 (base + 4) (by validMem) (by validMem)
  have P1 := dup1_pair_spec nsp 40 8 a1 d1 a0 (base + 12) (by validMem) (by validMem)
  have P2 := dup1_pair_spec nsp 48 16 a2 d2 a1 (base + 20) (by validMem) (by validMem)
  have P3 := dup1_pair_spec nsp 56 24 a3 d3 a2 (base + 28) (by validMem) (by validMem)
  runBlock LADDI P0 P1 P2 P3

set_option maxHeartbeats 6400000 in
theorem evm_dup1_stack_spec (nsp base : Addr)
    (a : EvmWord) (d0 d1 d2 d3 : Word) (v7 : Word)
    (hvalid : ValidMemRange nsp 8) :
    let code := evm_dup1_code base
    cpsTriple base (base + 36) code
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmWordIs (nsp + 32) a)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a.getLimb 3) **
       evmWordIs nsp a ** evmWordIs (nsp + 32) a) := by
  have h_main := evm_dup1_spec nsp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3) d0 d1 d2 d3 v7 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have : (nsp : Addr) + 32 + 8 = nsp + 40 := by bv_omega
      have : (nsp : Addr) + 32 + 16 = nsp + 48 := by bv_omega
      have : (nsp : Addr) + 32 + 24 = nsp + 56 := by bv_omega
      rw [‹nsp + 32 + 8 = nsp + 40›, ‹nsp + 32 + 16 = nsp + 48›, ‹nsp + 32 + 24 = nsp + 56›] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      have : (nsp : Addr) + 32 + 8 = nsp + 40 := by bv_omega
      have : (nsp : Addr) + 32 + 16 = nsp + 48 := by bv_omega
      have : (nsp : Addr) + 32 + 24 = nsp + 56 := by bv_omega
      rw [‹nsp + 32 + 8 = nsp + 40›, ‹nsp + 32 + 16 = nsp + 48›, ‹nsp + 32 + 24 = nsp + 56›]
      xperm_hyp hq)
    h_main

-- ============================================================================
-- SWAP1 per-limb helper
-- ============================================================================

/-- Four-instruction spec for SWAP1 per-limb: LD x7 from A, LD x6 from B,
    SD x6 to A, SD x7 to B. Swaps values at offsets off_a and off_b. -/
theorem swap1_limb_spec (sp : Addr)
    (off_a off_b : BitVec 12) (a_val b_val v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x6 off_a))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + signExtend12 off_a) ↦ₘ a_val) ** ((sp + signExtend12 off_b) ↦ₘ b_val))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a_val) ** (.x6 ↦ᵣ b_val) **
       ((sp + signExtend12 off_a) ↦ₘ b_val) ** ((sp + signExtend12 off_b) ↦ₘ a_val)) := by
  runBlock

-- ============================================================================
-- SWAP1 spec
-- ============================================================================

/-- CodeReq for the 256-bit EVM SWAP1 operation. 16 instructions. -/
abbrev evm_swap1_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x6 0))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x7 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x7 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x6 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x6 8))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SD .x12 .x7 40))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LD .x7 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x6 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SD .x12 .x6 16))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SD .x12 .x7 48))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x7 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 52) (.LD .x6 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 24))
   (CodeReq.singleton (base + 60) (.SD .x12 .x7 56))))))))))))))))

set_option maxHeartbeats 6400000 in
theorem evm_swap1_spec (sp base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_swap1_code base
    cpsTriple base (base + 64) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ a0) ** ((sp + 40) ↦ₘ a1) ** ((sp + 48) ↦ₘ a2) ** ((sp + 56) ↦ₘ a3)) := by
  have L0 := swap1_limb_spec sp 0 32 a0 b0 v7 v6 base (by validMem) (by validMem)
  have L1 := swap1_limb_spec sp 8 40 a1 b1 a0 b0 (base + 16) (by validMem) (by validMem)
  have L2 := swap1_limb_spec sp 16 48 a2 b2 a1 b1 (base + 32) (by validMem) (by validMem)
  have L3 := swap1_limb_spec sp 24 56 a3 b3 a2 b2 (base + 48) (by validMem) (by validMem)
  runBlock L0 L1 L2 L3

set_option maxHeartbeats 6400000 in
theorem evm_swap1_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_swap1_code base
    cpsTriple base (base + 64) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a.getLimb 3) ** (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp b ** evmWordIs (sp + 32) a) := by
  have h_main := evm_swap1_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    v7 v6 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›]
      xperm_hyp hq)
    h_main

-- ============================================================================
-- signExtend12_ofNat_small (needed for generic DUP/SWAP)
-- ============================================================================

/-- Sign-extend a small non-negative 12-bit value to 64 bits.
    The MSB is clear when m < 2^11 = 2048, so signExtend = zeroExtend = identity. -/
theorem signExtend12_ofNat_small (m : Nat) (hm : m < 2048) :
    signExtend12 (BitVec.ofNat 12 m) = BitVec.ofNat 64 m := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

-- ============================================================================
-- evmStackIs_split_at
-- ============================================================================

/-- Split evmStackIs at position k: extract the kth element (0-indexed). -/
theorem evmStackIs_split_at (sp : Addr) (stack : List EvmWord) (k : Nat)
    (hk : k < stack.length) :
    evmStackIs sp stack =
      (evmStackIs sp (stack.take k) **
       evmWordIs (sp + BitVec.ofNat 64 (k * 32)) (stack[k]'hk) **
       evmStackIs (sp + BitVec.ofNat 64 ((k + 1) * 32)) (stack.drop (k + 1))) := by
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
      have a1 : sp + (32 : Addr) + BitVec.ofNat 64 (k * 32) =
                sp + BitVec.ofNat 64 ((k + 1) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have a2 : sp + (32 : Addr) + BitVec.ofNat 64 ((k + 1) * 32) =
                sp + BitVec.ofNat 64 ((k + 2) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [evmStackIs_cons, ih (sp + 32) vs hk', a1, a2]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ]
      simp only [evmStackIs_cons, sepConj_assoc']

-- ============================================================================
-- Generic DUP program definition
-- ============================================================================

/-- One limb pair for DUP: LD x7 from source offset, SD x7 to destination offset. -/
private def dup_one_limb (n i : Nat) : Program :=
  LD .x7 .x12 (BitVec.ofNat 12 (n * 32 + i * 8)) ;;
  SD .x12 .x7 (BitVec.ofNat 12 (i * 8))

/-- Generic DUPn program (1-indexed): push copy of nth stack element on top.
    n=1 copies the top, n=2 copies the second element, etc.
    Uses 9 instructions: 1 ADDI + 4 × (LD + SD). -/
def evm_dup (n : Nat) : Program :=
  ADDI .x12 .x12 (-32) ;;
  dup_one_limb n 0 ;; dup_one_limb n 1 ;; dup_one_limb n 2 ;; dup_one_limb n 3

-- ============================================================================
-- Generic SWAP program definition
-- ============================================================================

/-- One limb quad for SWAP: LD x7 from top, LD x6 from nth, SD x6 to top, SD x7 to nth. -/
private def swap_one_limb (n i : Nat) : Program :=
  LD .x7 .x12 (BitVec.ofNat 12 (i * 8)) ;;
  LD .x6 .x12 (BitVec.ofNat 12 (n * 32 + i * 8)) ;;
  SD .x12 .x6 (BitVec.ofNat 12 (i * 8)) ;;
  SD .x12 .x7 (BitVec.ofNat 12 (n * 32 + i * 8))

/-- Generic SWAPn program (1-indexed): swap the top element with the nth stack element.
    n=1 swaps top with 2nd, n=2 swaps top with 3rd, etc.
    Uses 16 instructions: 4 × (LD + LD + SD + SD). -/
def evm_swap (n : Nat) : Program :=
  swap_one_limb n 0 ;; swap_one_limb n 1 ;; swap_one_limb n 2 ;; swap_one_limb n 3

-- ============================================================================
-- Low-level generic DUP spec
-- ============================================================================

/-- CodeReq for generic DUPn: 9 instructions (1 ADDI + 4 LD/SD pairs). -/
abbrev evm_dup_code (base : Addr) (n : Nat) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 (-32)))
  (CodeReq.union (CodeReq.singleton (base + 4)  (.LD .x7 .x12 (BitVec.ofNat 12 (n*32))))
  (CodeReq.union (CodeReq.singleton (base + 8)  (.SD .x12 .x7 (BitVec.ofNat 12 0)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+8))))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SD .x12 .x7 (BitVec.ofNat 12 8)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+16))))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x7 (BitVec.ofNat 12 16)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+24))))
   (CodeReq.singleton (base + 32) (.SD .x12 .x7 (BitVec.ofNat 12 24))))))))))

set_option maxHeartbeats 6400000 in
/-- Generic DUPn spec (low level): copies 4 dword limbs from src (at nsp+n*32) to dst (at nsp).
    Requires 1 ≤ n ≤ 16 (valid EVM DUP range). -/
theorem evm_dup_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (s0 s1 s2 s3 : Word)
    (d0 d1 d2 d3 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 4)) :
    let cr := evm_dup_code base n
    cpsTriple base (base + 36) cr
      (-- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp+8) ↦ₘ d1) ** ((nsp+16) ↦ₘ d2) ** ((nsp+24) ↦ₘ d3) **
       ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
       ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
      (-- Registers + memory (copied)
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ s3) **
       (nsp ↦ₘ s0) ** ((nsp+8) ↦ₘ s1) ** ((nsp+16) ↦ₘ s2) ** ((nsp+24) ↦ₘ s3) **
       ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
       ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3)) := by
  -- ADDI result normalization
  have h_addi : (nsp + 32 : Word) + signExtend12 (-32 : BitVec 12) = nsp := by
    simp only [signExtend12_neg32]; bv_omega
  -- signExtend12 for source offsets (generic via signExtend12_ofNat_small)
  have hse_s0 : signExtend12 (BitVec.ofNat 12 (n*32)) = BitVec.ofNat 64 (n*32) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 64 (n*32+8) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 64 (n*32+16) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 64 (n*32+24) :=
    signExtend12_ofNat_small _ (by omega)
  -- signExtend12 for destination offsets
  have hse_d0  : signExtend12 (BitVec.ofNat 12 0)  = BitVec.ofNat 64 0  := signExtend12_ofNat_small _ (by omega)
  have hse_d8  : signExtend12 (BitVec.ofNat 12 8)  = BitVec.ofNat 64 8  := signExtend12_ofNat_small _ (by omega)
  have hse_d16 : signExtend12 (BitVec.ofNat 12 16) = BitVec.ofNat 64 16 := signExtend12_ofNat_small _ (by omega)
  have hse_d24 : signExtend12 (BitVec.ofNat 12 24) = BitVec.ofNat 64 24 := signExtend12_ofNat_small _ (by omega)
  have hm0  : nsp + signExtend12 (BitVec.ofNat 12 0)  = nsp      := by rw [hse_d0]; bv_omega
  have hm8  : nsp + signExtend12 (BitVec.ofNat 12 8)  = nsp + 8  := by rw [hse_d8]; bv_omega
  have hm16 : nsp + signExtend12 (BitVec.ofNat 12 16) = nsp + 16 := by rw [hse_d16]; bv_omega
  have hm24 : nsp + signExtend12 (BitVec.ofNat 12 24) = nsp + 24 := by rw [hse_d24]; bv_omega
  -- Memory validity from ValidMemRange for dst locations (indices 0..3)
  have hv0  : isValidDwordAccess nsp       = true := by have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8  : isValidDwordAccess (nsp + 8)  = true := by have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (nsp + 16) = true := by have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (nsp + 24) = true := by have := hvalid.get (i := 3) (by omega); simpa using this
  -- Memory validity from ValidMemRange for src locations (indices n*4..n*4+3)
  have hvs0 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32)) = true := by
    have := hvalid.get (i := n*4) (by omega); rwa [show 8 * (n * 4) = n * 32 from by omega] at this
  have hvs8 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32+8)) = true := by
    have := hvalid.get (i := n*4+1) (by omega); rwa [show 8 * (n * 4 + 1) = n * 32 + 8 from by omega] at this
  have hvs16 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32+16)) = true := by
    have := hvalid.get (i := n*4+2) (by omega); rwa [show 8 * (n * 4 + 2) = n * 32 + 16 from by omega] at this
  have hvs24 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32+24)) = true := by
    have := hvalid.get (i := n*4+3) (by omega); rwa [show 8 * (n * 4 + 3) = n * 32 + 24 from by omega] at this
  -- Step 1: ADDI x12 x12 (-32) at base
  have sA_raw := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  rw [h_addi] at sA_raw
  have sA := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ v7) **
     (nsp ↦ₘ d0) ** ((nsp+8) ↦ₘ d1) ** ((nsp+16) ↦ₘ d2) ** ((nsp+24) ↦ₘ d3) **
     ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
     ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
    (by pcFree) sA_raw
  clear sA_raw
  -- Step 2: Pair 0 - LD from nsp + n*32, SD to nsp
  have P0_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32)) (BitVec.ofNat 12 0) s0 d0 v7 (base + 4)
    (by rw [hse_s0]; exact hvs0) (by rw [hm0]; exact hv0)
  rw [hse_s0, signExtend12_ofNat_small 0 (by omega)] at P0_raw
  rw [show nsp + BitVec.ofNat 64 0 = nsp from by bv_omega] at P0_raw
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega,
      show (base + 4 : Addr) + 8 = base + 12 from by bv_omega] at P0_raw
  have P0 := cpsTriple_frame_left _ _ _ _ _
    (((nsp+8) ↦ₘ d1) ** ((nsp+16) ↦ₘ d2) ** ((nsp+24) ↦ₘ d3) **
     ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
     ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
    (by pcFree) P0_raw
  clear P0_raw
  have sAP0 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sA P0
  clear sA P0
  -- Step 3: Pair 1 - LD from nsp + n*32+8, SD to nsp+8
  have P1_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+8)) (BitVec.ofNat 12 8) s1 d1 s0 (base + 12)
    (by rw [hse_s1]; exact hvs8) (by rw [hm8]; exact hv8)
  rw [hse_s1, signExtend12_ofNat_small 8 (by omega)] at P1_raw
  rw [show nsp + BitVec.ofNat 64 8 = nsp + 8 from by bv_omega] at P1_raw
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega,
      show (base + 12 : Addr) + 8 = base + 20 from by bv_omega] at P1_raw
  have P1 := cpsTriple_frame_left _ _ _ _ _
    ((nsp ↦ₘ s0) **
     ((nsp+16) ↦ₘ d2) ** ((nsp+24) ↦ₘ d3) **
     ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
     ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
    (by pcFree) P1_raw
  clear P1_raw
  have sAP01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP0 P1
  clear sAP0 P1
  -- Step 4: Pair 2 - LD from nsp + n*32+16, SD to nsp+16
  have P2_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+16)) (BitVec.ofNat 12 16) s2 d2 s1 (base + 20)
    (by rw [hse_s2]; exact hvs16) (by rw [hm16]; exact hv16)
  rw [hse_s2, signExtend12_ofNat_small 16 (by omega)] at P2_raw
  rw [show nsp + BitVec.ofNat 64 16 = nsp + 16 from by bv_omega] at P2_raw
  rw [show (base + 20 : Addr) + 4 = base + 24 from by bv_omega,
      show (base + 20 : Addr) + 8 = base + 28 from by bv_omega] at P2_raw
  have P2 := cpsTriple_frame_left _ _ _ _ _
    ((nsp ↦ₘ s0) ** ((nsp+8) ↦ₘ s1) **
     ((nsp+24) ↦ₘ d3) **
     ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
    (by pcFree) P2_raw
  clear P2_raw
  have sAP012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP01 P2
  clear sAP01 P2
  -- Step 5: Pair 3 - LD from nsp + n*32+24, SD to nsp+24
  have P3_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+24)) (BitVec.ofNat 12 24) s3 d3 s2 (base + 28)
    (by rw [hse_s3]; exact hvs24) (by rw [hm24]; exact hv24)
  rw [hse_s3, signExtend12_ofNat_small 24 (by omega)] at P3_raw
  rw [show nsp + BitVec.ofNat 64 24 = nsp + 24 from by bv_omega] at P3_raw
  rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_omega,
      show (base + 28 : Addr) + 8 = base + 36 from by bv_omega] at P3_raw
  have P3 := cpsTriple_frame_left _ _ _ _ _
    ((nsp ↦ₘ s0) ** ((nsp+8) ↦ₘ s1) ** ((nsp+16) ↦ₘ s2) **
     ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2))
    (by pcFree) P3_raw
  clear P3_raw
  -- Final composition and permutation to match goal
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) sAP012 P3)

-- ============================================================================
-- EvmWord-level DUP spec
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- DUPn spec at evmWordIs level: copies the nth stack element to new top position. -/
theorem evm_dup_evmword_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (src dst : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 4)) :
    let cr := evm_dup_code base n
    cpsTriple base (base + 36) cr
      (-- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp dst **
       evmWordIs (nsp + BitVec.ofNat 64 (n * 32)) src)
      (-- Results
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ src.getLimb 3) **
       evmWordIs nsp src **
       evmWordIs (nsp + BitVec.ofNat 64 (n * 32)) src) := by
  -- Address normalizations for evmWordIs (nsp + BitVec.ofNat 64 (n*32))
  have haddr8  : (nsp + BitVec.ofNat 64 (n * 32) : Addr) + 8  = nsp + BitVec.ofNat 64 (n*32+8)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr16 : (nsp + BitVec.ofNat 64 (n * 32) : Addr) + 16 = nsp + BitVec.ofNat 64 (n*32+16) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr24 : (nsp + BitVec.ofNat 64 (n * 32) : Addr) + 24 = nsp + BitVec.ofNat 64 (n*32+24) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Derive from evm_dup_spec
  have h_main := evm_dup_spec nsp base n hn1 hn16
    (src.getLimb 0) (src.getLimb 1) (src.getLimb 2) (src.getLimb 3)
    (dst.getLimb 0) (dst.getLimb 1) (dst.getLimb 2) (dst.getLimb 3)
    v7 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun _ hp => by
      simp only [evmWordIs, haddr8, haddr16, haddr24] at hp
      xperm_hyp hp)
    (fun _ hq => by
      simp only [evmWordIs, haddr8, haddr16, haddr24]
      xperm_hyp hq)
    h_main

-- ============================================================================
-- Stack-level DUP spec
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- DUPn stack spec: copies the (n-1)-th element (0-indexed) from the stack
    to a new top position, leaving the rest unchanged. -/
theorem evm_dup_stack_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n ≤ stack.length)
    (d : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 4)) :
    let vn := stack[n - 1]'(by omega)
    let cr := evm_dup_code base n
    cpsTriple base (base + 36) cr
      (-- Registers + memory
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp d **
       evmStackIs (nsp + 32) stack)
      (-- Results
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ vn.getLimb 3) **
       evmWordIs nsp vn **
       evmStackIs (nsp + 32) stack) := by
  intro vn
  -- Split evmStackIs (nsp + 32) stack at position (n-1) to extract the target element
  have hk : n - 1 < stack.length := by omega
  have hsplit := evmStackIs_split_at (nsp + 32) stack (n - 1) hk
  -- Address normalizations
  have haddr_src : (nsp + 32 : Addr) + BitVec.ofNat 64 ((n - 1) * 32) =
      nsp + BitVec.ofNat 64 (n * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr_rest : (nsp + 32 : Addr) + BitVec.ofNat 64 (((n - 1) + 1) * 32) =
      nsp + BitVec.ofNat 64 (n * 32 + 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [haddr_src, haddr_rest, show n - 1 + 1 = n from by omega] at hsplit
  -- Frame the evm_dup_evmword_spec with the stack prefix and suffix
  have h_main := cpsTriple_frame_left _ _ _ _ _
    (evmStackIs (nsp + 32) (stack.take (n - 1)) **
     evmStackIs (nsp + BitVec.ofNat 64 (n * 32 + 32)) (stack.drop n))
    (by pcFree)
    (evm_dup_evmword_spec nsp base n hn1 hn16 vn d v7 hvalid)
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun _ hp => by rw [hsplit] at hp; xperm_hyp hp)
    (fun _ hq => by rw [hsplit]; xperm_hyp hq)
    h_main

-- ============================================================================
-- Low-level generic SWAP spec
-- ============================================================================

/-- CodeReq for generic SWAPn: 16 instructions (4 limb quads). -/
abbrev evm_swap_code (base : Addr) (n : Nat) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 (BitVec.ofNat 12 0)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32))))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x6 (BitVec.ofNat 12 0)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32))))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x7 .x12 (BitVec.ofNat 12 8)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+8))))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x6 (BitVec.ofNat 12 8)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+8))))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LD .x7 .x12 (BitVec.ofNat 12 16)))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+16))))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SD .x12 .x6 (BitVec.ofNat 12 16)))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+16))))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x7 .x12 (BitVec.ofNat 12 24)))
  (CodeReq.union (CodeReq.singleton (base + 52) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+24))))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (BitVec.ofNat 12 24)))
   (CodeReq.singleton (base + 60) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+24))))))))))))))))))))

set_option maxHeartbeats 3200000 in
/-- Generic SWAPn spec (low level): swaps 4 dword limbs at sp (top) with 4 at sp+n*32 (nth).
    Requires 1 ≤ n ≤ 16 (valid EVM SWAP range). -/
theorem evm_swap_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 4)) :
    let cr := evm_swap_code base n
    cpsTriple base (base + 64) cr
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp+8) ↦ₘ a1) ** ((sp+16) ↦ₘ a2) ** ((sp+24) ↦ₘ a3) **
       ((sp + BitVec.ofNat 64 (n*32))    ↦ₘ b0) **
       ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ b1) **
       ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ b2) **
       ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ b3))
      (-- Registers + memory (swapped)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ b0) ** ((sp+8) ↦ₘ b1) ** ((sp+16) ↦ₘ b2) ** ((sp+24) ↦ₘ b3) **
       ((sp + BitVec.ofNat 64 (n*32))    ↦ₘ a0) **
       ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ a1) **
       ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ a2) **
       ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ a3)) := by
  -- signExtend12 for n-dependent source offsets
  have hse_s0 : signExtend12 (BitVec.ofNat 12 (n*32)) = BitVec.ofNat 64 (n*32) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 64 (n*32+8) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 64 (n*32+16) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 64 (n*32+24) :=
    signExtend12_ofNat_small _ (by omega)
  -- signExtend12 for destination offsets (0,8,16,24)
  have hse_d0  : signExtend12 (BitVec.ofNat 12 0)  = BitVec.ofNat 64 0  := signExtend12_ofNat_small _ (by omega)
  have hse_d8  : signExtend12 (BitVec.ofNat 12 8)  = BitVec.ofNat 64 8  := signExtend12_ofNat_small _ (by omega)
  have hse_d16 : signExtend12 (BitVec.ofNat 12 16) = BitVec.ofNat 64 16 := signExtend12_ofNat_small _ (by omega)
  have hse_d24 : signExtend12 (BitVec.ofNat 12 24) = BitVec.ofNat 64 24 := signExtend12_ofNat_small _ (by omega)
  -- Memory address normalizations
  have hm0  : sp + signExtend12 (BitVec.ofNat 12 0)  = sp      := by rw [hse_d0]; bv_omega
  have hm8  : sp + signExtend12 (BitVec.ofNat 12 8)  = sp + 8  := by rw [hse_d8]; bv_omega
  have hm16 : sp + signExtend12 (BitVec.ofNat 12 16) = sp + 16 := by rw [hse_d16]; bv_omega
  have hm24 : sp + signExtend12 (BitVec.ofNat 12 24) = sp + 24 := by rw [hse_d24]; bv_omega
  -- Memory validity for destination locations (indices 0..3)
  have hv0  : isValidDwordAccess sp       = true := by have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8  : isValidDwordAccess (sp + 8)  = true := by have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + 16) = true := by have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + 24) = true := by have := hvalid.get (i := 3) (by omega); simpa using this
  -- Memory validity for source locations
  have hvs0  : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32))     = true := by
    have := hvalid.get (i := n*4) (by omega); rwa [show 8 * (n * 4) = n * 32 from by omega] at this
  have hvs8  : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32+8))   = true := by
    have := hvalid.get (i := n*4+1) (by omega); rwa [show 8 * (n * 4 + 1) = n * 32 + 8 from by omega] at this
  have hvs16 : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32+16))  = true := by
    have := hvalid.get (i := n*4+2) (by omega); rwa [show 8 * (n * 4 + 2) = n * 32 + 16 from by omega] at this
  have hvs24 : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32+24))  = true := by
    have := hvalid.get (i := n*4+3) (by omega); rwa [show 8 * (n * 4 + 3) = n * 32 + 24 from by omega] at this
  -- Memory validity via signExtend12 for swap1_limb_spec
  have hvm_d0  : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 0))  = true := by rw [hm0]; exact hv0
  have hvm_d8  : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 8))  = true := by rw [hm8]; exact hv8
  have hvm_d16 : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 16)) = true := by rw [hm16]; exact hv16
  have hvm_d24 : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 24)) = true := by rw [hm24]; exact hv24
  have hvm_s0  : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32)))    = true := by rw [hse_s0]; exact hvs0
  have hvm_s8  : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+8)))  = true := by rw [hse_s1]; exact hvs8
  have hvm_s16 : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+16))) = true := by rw [hse_s2]; exact hvs16
  have hvm_s24 : isValidDwordAccess (sp + signExtend12 (BitVec.ofNat 12 (n*32+24))) = true := by rw [hse_s3]; exact hvs24
  -- Limb 0: swap at base, offsets 0 and n*32
  have L0_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 0) (BitVec.ofNat 12 (n*32))
    a0 b0 v7 v6 base hvm_d0 hvm_s0
  rw [hm0, hse_s0] at L0_raw
  have L0 := cpsTriple_frame_left _ _ _ _ _
    (((sp+8) ↦ₘ a1) ** ((sp+16) ↦ₘ a2) ** ((sp+24) ↦ₘ a3) **
     ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ b1) **
     ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ b2) **
     ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ b3))
    (by pcFree) L0_raw
  clear L0_raw
  -- Limb 1: swap at base+16, offsets 8 and n*32+8
  have L1_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 8) (BitVec.ofNat 12 (n*32+8))
    a1 b1 a0 b0 (base + 16) hvm_d8 hvm_s8
  rw [hm8, hse_s1] at L1_raw
  rw [show (base + 16 : Addr) + 4 = base + 20 from by bv_omega,
      show (base + 16 : Addr) + 8 = base + 24 from by bv_omega,
      show (base + 16 : Addr) + 12 = base + 28 from by bv_omega,
      show (base + 16 : Addr) + 16 = base + 32 from by bv_omega] at L1_raw
  have L1 := cpsTriple_frame_left _ _ _ _ _
    ((sp ↦ₘ b0) ** ((sp + BitVec.ofNat 64 (n*32)) ↦ₘ a0) **
     ((sp+16) ↦ₘ a2) ** ((sp+24) ↦ₘ a3) **
     ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ b2) **
     ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ b3))
    (by pcFree) L1_raw
  clear L1_raw
  have L01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L0 L1
  clear L0 L1
  -- Limb 2: swap at base+32, offsets 16 and n*32+16
  have L2_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 16) (BitVec.ofNat 12 (n*32+16))
    a2 b2 a1 b1 (base + 32) hvm_d16 hvm_s16
  rw [hm16, hse_s2] at L2_raw
  rw [show (base + 32 : Addr) + 4 = base + 36 from by bv_omega,
      show (base + 32 : Addr) + 8 = base + 40 from by bv_omega,
      show (base + 32 : Addr) + 12 = base + 44 from by bv_omega,
      show (base + 32 : Addr) + 16 = base + 48 from by bv_omega] at L2_raw
  have L2 := cpsTriple_frame_left _ _ _ _ _
    ((sp ↦ₘ b0) ** ((sp+8) ↦ₘ b1) **
     ((sp + BitVec.ofNat 64 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 64 (n*32+8)) ↦ₘ a1) **
     ((sp+24) ↦ₘ a3) **
     ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ b3))
    (by pcFree) L2_raw
  clear L2_raw
  have L012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L01 L2
  clear L01 L2
  -- Limb 3: swap at base+48, offsets 24 and n*32+24
  have L3_raw := swap1_limb_spec sp
    (BitVec.ofNat 12 24) (BitVec.ofNat 12 (n*32+24))
    a3 b3 a2 b2 (base + 48) hvm_d24 hvm_s24
  rw [hm24, hse_s3] at L3_raw
  rw [show (base + 48 : Addr) + 4 = base + 52 from by bv_omega,
      show (base + 48 : Addr) + 8 = base + 56 from by bv_omega,
      show (base + 48 : Addr) + 12 = base + 60 from by bv_omega,
      show (base + 48 : Addr) + 16 = base + 64 from by bv_omega] at L3_raw
  have L3 := cpsTriple_frame_left _ _ _ _ _
    ((sp ↦ₘ b0) ** ((sp+8) ↦ₘ b1) ** ((sp+16) ↦ₘ b2) **
     ((sp + BitVec.ofNat 64 (n*32)) ↦ₘ a0) ** ((sp + BitVec.ofNat 64 (n*32+8)) ↦ₘ a1) **
     ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ a2))
    (by pcFree) L3_raw
  clear L3_raw
  -- Final composition and permutation to match goal
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) L012 L3)

-- ============================================================================
-- EvmWord-level SWAP spec
-- ============================================================================

/-- SWAPn spec at evmWordIs level: swaps the top and nth stack elements. -/
theorem evm_swap_evmword_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (top nth : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 4)) :
    let cr := evm_swap_code base n
    cpsTriple base (base + 64) cr
      (-- Registers + data
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp top **
       evmWordIs (sp + BitVec.ofNat 64 (n * 32)) nth)
      (-- Registers + data (swapped)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 3) ** (.x6 ↦ᵣ nth.getLimb 3) **
       evmWordIs sp nth **
       evmWordIs (sp + BitVec.ofNat 64 (n * 32)) top) := by
  -- Address normalizations
  have ha8  : (sp + BitVec.ofNat 64 (n * 32) : Addr) + 8  = sp + BitVec.ofNat 64 (n*32+8)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha16 : (sp + BitVec.ofNat 64 (n * 32) : Addr) + 16 = sp + BitVec.ofNat 64 (n*32+16) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha24 : (sp + BitVec.ofNat 64 (n * 32) : Addr) + 24 = sp + BitVec.ofNat 64 (n*32+24) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs, ha8, ha16, ha24] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, ha8, ha16, ha24]
      xperm_hyp hq)
    (evm_swap_spec sp base n hn1 hn16
      (top.getLimb 0) (top.getLimb 1) (top.getLimb 2) (top.getLimb 3)
      (nth.getLimb 0) (nth.getLimb 1) (nth.getLimb 2) (nth.getLimb 3)
      v7 v6 hvalid)

-- ============================================================================
-- Stack-level SWAP spec
-- ============================================================================

/-- SWAPn stack spec: swaps top with the nth element (1-indexed) of the stack. -/
theorem evm_swap_stack_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n + 1 ≤ stack.length)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 4)) :
    let top := stack[0]'(by omega)
    let nth := stack[n]'(by omega)
    let cr := evm_swap_code base n
    cpsTriple base (base + 64) cr
      (-- Registers + data
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmStackIs sp stack)
      (-- Registers + data (swapped)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 3) ** (.x6 ↦ᵣ nth.getLimb 3) **
       evmWordIs sp nth **
       evmStackIs (sp + 32) ((stack.drop 1).take (n - 1)) **
       evmWordIs (sp + BitVec.ofNat 64 (n * 32)) top **
       evmStackIs (sp + BitVec.ofNat 64 ((n + 1) * 32)) ((stack.drop 1).drop n)) := by
  intro top nth
  -- Split evmStackIs sp stack at position 0 to extract the top element
  have hk0 : 0 < stack.length := by omega
  have hsplit0 := evmStackIs_split_at sp stack 0 hk0
  -- Split the tail (stack.drop 1) at position (n-1) to extract the nth element
  have htail_len : n - 1 < (stack.drop 1).length := by simp; omega
  have hsplit1 := evmStackIs_split_at (sp + 32) (stack.drop 1) (n - 1) htail_len
  -- Address normalizations
  have haddr_src : (sp + 32 : Addr) + BitVec.ofNat 64 ((n - 1) * 32) =
      sp + BitVec.ofNat 64 (n * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr_rest : (sp + 32 : Addr) + BitVec.ofNat 64 (((n - 1) + 1) * 32) =
      sp + BitVec.ofNat 64 ((n + 1) * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Simplify the element access: (stack.drop 1)[n-1] = stack[n]
  have helem : (stack.drop 1)[n - 1]'htail_len = stack[n]'(by omega) := by
    simp; congr 1; omega
  rw [haddr_src, haddr_rest, show (n - 1) + 1 = n from by omega, helem] at hsplit1
  -- Frame the evm_swap_evmword_spec with the middle and rest stacks
  have h_main := cpsTriple_frame_left _ _ _ _ _
    (evmStackIs (sp + 32) ((stack.drop 1).take (n - 1)) **
     evmStackIs (sp + BitVec.ofNat 64 ((n + 1) * 32)) ((stack.drop 1).drop n))
    (by pcFree)
    (evm_swap_evmword_spec sp base n hn1 hn16 top nth v7 v6 hvalid)
  have haddr32 : (sp + BitVec.ofNat 64 (1 * 32) : Addr) = sp + 32 := by bv_omega
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      rw [hsplit0] at hp
      simp only [Nat.zero_mul, List.take_zero, evmStackIs_nil, sepConj_emp_left',
                  BitVec.add_zero, haddr32] at hp
      rw [hsplit1] at hp
      xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_main

end EvmAsm.Rv64
