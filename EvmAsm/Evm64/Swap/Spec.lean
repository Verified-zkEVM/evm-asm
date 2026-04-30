/-
  EvmAsm.Evm64.Swap.Spec

  256-bit EVM SWAP1-16 specs.
-/

import EvmAsm.Evm64.Swap.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Per-limb helper
-- ============================================================================

/-- Four-instruction spec for SWAP per-limb: LD x7 from A, LD x6 from B,
    SD x6 to A, SD x7 to B. Swaps values at offsets off_a and off_b. -/
theorem swap_limb_spec_within (sp : Word)
    (off_a off_b : BitVec 12) (aVal bVal v7 v6 : Word) (base : Word) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.singleton base (.LD .x7 .x12 off_a) |>.union
        (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b) |>.union
        (CodeReq.singleton (base + 8) (.SD .x12 .x6 off_a) |>.union
         (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b)))))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + signExtend12 off_a) ↦ₘ aVal) ** ((sp + signExtend12 off_b) ↦ₘ bVal))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ aVal) ** (.x6 ↦ᵣ bVal) **
       ((sp + signExtend12 off_a) ↦ₘ bVal) ** ((sp + signExtend12 off_b) ↦ₘ aVal)) := by
  have L0 := ld_spec_gen_within .x7 .x12 sp v7 aVal off_a base (by nofun)
  have L1 := ld_spec_gen_within .x6 .x12 sp v6 bVal off_b (base + 4) (by nofun)
  have S0 := sd_spec_gen_within .x12 .x6 sp bVal aVal off_a (base + 8)
  have S1 := sd_spec_gen_within .x12 .x7 sp aVal bVal off_b (base + 12)
  runBlock L0 L1 S0 S1


-- ============================================================================
-- Low-level generic SWAP spec
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Generic SWAPn spec (low level): swaps 4 dword limbs at sp (top) with 4 at sp+n*32 (nth).
    Requires 1 ≤ n ≤ 16 (valid EVM SWAP range). -/
theorem evm_swap_spec_within (sp base : Word)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (v7 v6 : Word) :
    cpsTripleWithin 16 base (base + 64) (evm_swap_code base n)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp+8) ↦ₘ a1) ** ((sp+16) ↦ₘ a2) ** ((sp+24) ↦ₘ a3) **
       ((sp + BitVec.ofNat 64 (n*32))    ↦ₘ b0) **
       ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ b1) **
       ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ b2) **
       ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ b0) ** ((sp+8) ↦ₘ b1) ** ((sp+16) ↦ₘ b2) ** ((sp+24) ↦ₘ b3) **
       ((sp + BitVec.ofNat 64 (n*32))    ↦ₘ a0) **
       ((sp + BitVec.ofNat 64 (n*32+8))  ↦ₘ a1) **
       ((sp + BitVec.ofNat 64 (n*32+16)) ↦ₘ a2) **
       ((sp + BitVec.ofNat 64 (n*32+24)) ↦ₘ a3)) := by
  -- signExtend12 normalizations for n-dependent source offsets
  have hse_s0 : signExtend12 (BitVec.ofNat 12 (n*32)) = BitVec.ofNat 64 (n*32) :=
    signExtend12_ofNat_small (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 64 (n*32+8) :=
    signExtend12_ofNat_small (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 64 (n*32+16) :=
    signExtend12_ofNat_small (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 64 (n*32+24) :=
    signExtend12_ofNat_small (by omega)
  -- signExtend12 normalizations for destination offsets (0,8,16,24)
  have hm0  : sp + signExtend12 (BitVec.ofNat 12 0)  = sp      := by
    rw [signExtend12_ofNat_small (by omega)]; bv_omega
  have hm8  : sp + signExtend12 (BitVec.ofNat 12 8)  = sp + 8  := by
    rw [signExtend12_ofNat_small (by omega)]; bv_omega
  have hm16 : sp + signExtend12 (BitVec.ofNat 12 16) = sp + 16 := by
    rw [signExtend12_ofNat_small (by omega)]; bv_omega
  have hm24 : sp + signExtend12 (BitVec.ofNat 12 24) = sp + 24 := by
    rw [signExtend12_ofNat_small (by omega)]; bv_omega
  -- Limb 0 swap
  have L0 := swap_limb_spec_within sp
    (BitVec.ofNat 12 0) (BitVec.ofNat 12 (n*32))
    a0 b0 v7 v6 base
  rw [hm0, hse_s0] at L0
  -- Limb 1 swap
  have L1 := swap_limb_spec_within sp
    (BitVec.ofNat 12 8) (BitVec.ofNat 12 (n*32+8))
    a1 b1 a0 b0 (base + 16)
  rw [hm8, hse_s1] at L1
  -- Limb 2 swap
  have L2 := swap_limb_spec_within sp
    (BitVec.ofNat 12 16) (BitVec.ofNat 12 (n*32+16))
    a2 b2 a1 b1 (base + 32)
  rw [hm16, hse_s2] at L2
  -- Limb 3 swap
  have L3 := swap_limb_spec_within sp
    (BitVec.ofNat 12 24) (BitVec.ofNat 12 (n*32+24))
    a3 b3 a2 b2 (base + 48)
  rw [hm24, hse_s3] at L3
  runBlock L0 L1 L2 L3


-- ============================================================================
-- EvmWord-level SWAP spec
-- ============================================================================

/-- SWAPn spec at evmWordIs level: swaps the top and nth stack elements. -/
theorem evm_swap_evmword_spec_within (sp base : Word)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (top nth : EvmWord) (v7 v6 : Word) :
    cpsTripleWithin 16 base (base + 64) (evm_swap_code base n)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp top **
       evmWordIs (sp + BitVec.ofNat 64 (n * 32)) nth)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimbN 3) ** (.x6 ↦ᵣ nth.getLimbN 3) **
       evmWordIs sp nth **
       evmWordIs (sp + BitVec.ofNat 64 (n * 32)) top) := by
  -- Address normalizations
  have ha8  : (sp + BitVec.ofNat 64 (n * 32) : Word) + 8  = sp + BitVec.ofNat 64 (n*32+8)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha16 : (sp + BitVec.ofNat 64 (n * 32) : Word) + 16 = sp + BitVec.ofNat 64 (n*32+16) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ha24 : (sp + BitVec.ofNat 64 (n * 32) : Word) + 24 = sp + BitVec.ofNat 64 (n*32+24) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact cpsTripleWithin_weaken
    (fun h hp => by
      simp only [evmWordIs, ha8, ha16, ha24] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, ha8, ha16, ha24]
      xperm_hyp hq)
    (evm_swap_spec_within sp base n hn1 hn16
      (top.getLimbN 0) (top.getLimbN 1) (top.getLimbN 2) (top.getLimbN 3)
      (nth.getLimbN 0) (nth.getLimbN 1) (nth.getLimbN 2) (nth.getLimbN 3)
      v7 v6)


-- ============================================================================
-- Stack-level SWAP spec
-- ============================================================================

/-- SWAPn stack spec: swaps top with the nth element (1-indexed) of the stack. -/
theorem evm_swap_stack_spec_within (sp base : Word)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n + 1 ≤ stack.length)
    (v7 v6 : Word) :
    let top := stack[0]'(by omega)
    let nth := stack[n]'(by omega)
    cpsTripleWithin 16 base (base + 64) (evm_swap_code base n)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmStackIs sp stack)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimbN 3) ** (.x6 ↦ᵣ nth.getLimbN 3) **
       evmWordIs sp nth **
       evmStackIs (sp + 32) ((stack.drop 1).take (n - 1)) **
       evmWordIs (sp + BitVec.ofNat 64 (n * 32)) top **
       evmStackIs (sp + BitVec.ofNat 64 ((n + 1) * 32)) ((stack.drop 1).drop n)) := by
  intro top nth
  -- Split evmStackIs sp stack at position 0 to extract top
  have hk0 : 0 < stack.length := by omega
  have hsplit0 := evmStackIs_split_at sp stack 0 hk0
  -- Split the tail at position (n-1) to extract nth
  have htail_len : n - 1 < (stack.drop 1).length := by simp; omega
  have hsplit1 := evmStackIs_split_at (sp + 32) (stack.drop 1) (n - 1) htail_len
  -- Address normalizations
  have haddr_src : (sp + 32 : Word) + BitVec.ofNat 64 ((n - 1) * 32) =
      sp + BitVec.ofNat 64 (n * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr_rest : (sp + 32 : Word) + BitVec.ofNat 64 (((n - 1) + 1) * 32) =
      sp + BitVec.ofNat 64 ((n + 1) * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Simplify element access
  have helem : (stack.drop 1)[n - 1]'htail_len = stack[n]'(by omega) := by
    simp; congr 1; omega
  rw [haddr_src, haddr_rest, show (n - 1) + 1 = n from by omega, helem] at hsplit1
  -- Frame the swap spec with middle and rest stacks
  have h_main := cpsTripleWithin_frameR
    (evmStackIs (sp + 32) ((stack.drop 1).take (n - 1)) **
     evmStackIs (sp + BitVec.ofNat 64 ((n + 1) * 32)) ((stack.drop 1).drop n))
    (by pcFree)
    (evm_swap_evmword_spec_within sp base n hn1 hn16 top nth v7 v6)
  have haddr32 : (sp + BitVec.ofNat 64 (1 * 32) : Word) = sp + 32 := by bv_omega
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [hsplit0] at hp
      simp only [Nat.zero_mul, List.take_zero, evmStackIs_nil, sepConj_emp_left',
                  BitVec.add_zero, haddr32] at hp
      rw [hsplit1] at hp
      xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_main


end EvmAsm.Evm64
