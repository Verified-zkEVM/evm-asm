/-
  EvmAsm.Evm64.Swap

  256-bit EVM SWAP1-16: generic swap of top with nth stack element.
  16 instructions (4 × (LD + LD + SD + SD)).
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Program definitions
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
-- Per-limb helper
-- ============================================================================

/-- Four-instruction spec for SWAP per-limb: LD x7 from A, LD x6 from B,
    SD x6 to A, SD x7 to B. Swaps values at offsets off_a and off_b. -/
theorem swap_limb_spec (sp : Addr)
    (off_a off_b : BitVec 12) (a_val b_val v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    cpsTriple base (base + 16)
      (CodeReq.singleton base (.LD .x7 .x12 off_a) |>.union
        (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b) |>.union
        (CodeReq.singleton (base + 8) (.SD .x12 .x6 off_a) |>.union
         (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b)))))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + signExtend12 off_a) ↦ₘ a_val) ** ((sp + signExtend12 off_b) ↦ₘ b_val))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a_val) ** (.x6 ↦ᵣ b_val) **
       ((sp + signExtend12 off_a) ↦ₘ b_val) ** ((sp + signExtend12 off_b) ↦ₘ a_val)) := by
  runBlock

-- ============================================================================
-- CodeReq for generic SWAP (explicit union chain)
-- ============================================================================

/-- CodeReq for generic SWAPn: 16 instructions = 64 bytes.
    Built as an explicit union chain because symbolic n prevents ofProg reduction. -/
abbrev evm_swap_code (base : Addr) (n : Nat) : CodeReq :=
  -- Limb 0
  CodeReq.singleton base (.LD .x7 .x12 (BitVec.ofNat 12 0))
  |>.union (CodeReq.singleton (base + 4)  (.LD .x6 .x12 (BitVec.ofNat 12 (n*32))))
  |>.union (CodeReq.singleton (base + 8)  (.SD .x12 .x6 (BitVec.ofNat 12 0)))
  |>.union (CodeReq.singleton (base + 12) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32))))
  -- Limb 1
  |>.union (CodeReq.singleton (base + 16) (.LD .x7 .x12 (BitVec.ofNat 12 8)))
  |>.union (CodeReq.singleton (base + 20) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+8))))
  |>.union (CodeReq.singleton (base + 24) (.SD .x12 .x6 (BitVec.ofNat 12 8)))
  |>.union (CodeReq.singleton (base + 28) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+8))))
  -- Limb 2
  |>.union (CodeReq.singleton (base + 32) (.LD .x7 .x12 (BitVec.ofNat 12 16)))
  |>.union (CodeReq.singleton (base + 36) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+16))))
  |>.union (CodeReq.singleton (base + 40) (.SD .x12 .x6 (BitVec.ofNat 12 16)))
  |>.union (CodeReq.singleton (base + 44) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+16))))
  -- Limb 3
  |>.union (CodeReq.singleton (base + 48) (.LD .x7 .x12 (BitVec.ofNat 12 24)))
  |>.union (CodeReq.singleton (base + 52) (.LD .x6 .x12 (BitVec.ofNat 12 (n*32+24))))
  |>.union (CodeReq.singleton (base + 56) (.SD .x12 .x6 (BitVec.ofNat 12 24)))
  |>.union (CodeReq.singleton (base + 60) (.SD .x12 .x7 (BitVec.ofNat 12 (n*32+24))))

-- ============================================================================
-- Low-level generic SWAP spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Generic SWAPn spec (low level): swaps 4 dword limbs at sp (top) with 4 at sp+n*32 (nth).
    Requires 1 ≤ n ≤ 16 (valid EVM SWAP range). -/
theorem evm_swap_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (a0 a1 a2 a3 : Word)
    (b0 b1 b2 b3 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 4)) :
    cpsTriple base (base + 64) (evm_swap_code base n)
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
    signExtend12_ofNat_small _ (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 64 (n*32+8) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 64 (n*32+16) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 64 (n*32+24) :=
    signExtend12_ofNat_small _ (by omega)
  -- signExtend12 normalizations for destination offsets (0,8,16,24)
  have hm0  : sp + signExtend12 (BitVec.ofNat 12 0)  = sp      := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  have hm8  : sp + signExtend12 (BitVec.ofNat 12 8)  = sp + 8  := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  have hm16 : sp + signExtend12 (BitVec.ofNat 12 16) = sp + 16 := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  have hm24 : sp + signExtend12 (BitVec.ofNat 12 24) = sp + 24 := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  -- Memory validity for destination locations (indices 0..3)
  have hv0  : isValidDwordAccess sp       = true := by have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8  : isValidDwordAccess (sp + 8)  = true := by have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + 16) = true := by have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + 24) = true := by have := hvalid.get (i := 3) (by omega); simpa using this
  -- Memory validity for source locations (indices n*4..n*4+3)
  have hvs0 : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32)) = true := by
    have := hvalid.get (i := n*4) (by omega); rwa [show 8 * (n * 4) = n * 32 from by omega] at this
  have hvs8 : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32+8)) = true := by
    have := hvalid.get (i := n*4+1) (by omega); rwa [show 8 * (n * 4 + 1) = n * 32 + 8 from by omega] at this
  have hvs16 : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32+16)) = true := by
    have := hvalid.get (i := n*4+2) (by omega); rwa [show 8 * (n * 4 + 2) = n * 32 + 16 from by omega] at this
  have hvs24 : isValidDwordAccess (sp + BitVec.ofNat 64 (n*32+24)) = true := by
    have := hvalid.get (i := n*4+3) (by omega); rwa [show 8 * (n * 4 + 3) = n * 32 + 24 from by omega] at this
  -- Limb 0 swap
  have L0 := swap_limb_spec sp
    (BitVec.ofNat 12 0) (BitVec.ofNat 12 (n*32))
    a0 b0 v7 v6 base (by rw [hm0]; exact hv0) (by rw [hse_s0]; exact hvs0)
  rw [hm0, hse_s0] at L0
  -- Limb 1 swap
  have L1 := swap_limb_spec sp
    (BitVec.ofNat 12 8) (BitVec.ofNat 12 (n*32+8))
    a1 b1 a0 b0 (base + 16) (by rw [hm8]; exact hv8) (by rw [hse_s1]; exact hvs8)
  rw [hm8, hse_s1] at L1
  -- Limb 2 swap
  have L2 := swap_limb_spec sp
    (BitVec.ofNat 12 16) (BitVec.ofNat 12 (n*32+16))
    a2 b2 a1 b1 (base + 32) (by rw [hm16]; exact hv16) (by rw [hse_s2]; exact hvs16)
  rw [hm16, hse_s2] at L2
  -- Limb 3 swap
  have L3 := swap_limb_spec sp
    (BitVec.ofNat 12 24) (BitVec.ofNat 12 (n*32+24))
    a3 b3 a2 b2 (base + 48) (by rw [hm24]; exact hv24) (by rw [hse_s3]; exact hvs24)
  rw [hm24, hse_s3] at L3
  runBlock L0 L1 L2 L3

-- ============================================================================
-- EvmWord-level SWAP spec
-- ============================================================================

/-- SWAPn spec at evmWordIs level: swaps the top and nth stack elements. -/
theorem evm_swap_evmword_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (top nth : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 4)) :
    cpsTriple base (base + 64) (evm_swap_code base n)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp top **
       evmWordIs (sp + BitVec.ofNat 64 (n * 32)) nth)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 3) ** (.x6 ↦ᵣ nth.getLimb 3) **
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
    cpsTriple base (base + 64) (evm_swap_code base n)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmStackIs sp stack)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 3) ** (.x6 ↦ᵣ nth.getLimb 3) **
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
  have haddr_src : (sp + 32 : Addr) + BitVec.ofNat 64 ((n - 1) * 32) =
      sp + BitVec.ofNat 64 (n * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr_rest : (sp + 32 : Addr) + BitVec.ofNat 64 (((n - 1) + 1) * 32) =
      sp + BitVec.ofNat 64 ((n + 1) * 32) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Simplify element access
  have helem : (stack.drop 1)[n - 1]'htail_len = stack[n]'(by omega) := by
    simp; congr 1; omega
  rw [haddr_src, haddr_rest, show (n - 1) + 1 = n from by omega, helem] at hsplit1
  -- Frame the swap spec with middle and rest stacks
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
