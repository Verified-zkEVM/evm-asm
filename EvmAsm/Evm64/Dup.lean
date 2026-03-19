/-
  EvmAsm.Evm64.Dup

  256-bit EVM DUP1-16: generic duplication of nth stack element.
  9 instructions (1 ADDI + 4 × (LD + SD)).
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
-- Per-limb helper
-- ============================================================================

/-- Two-instruction spec for DUP: LD x7 from source, SD x7 to destination.
    Copies src_val from src address to dst address. -/
theorem dup_pair_spec (sp : Addr)
    (off_src off_dst : BitVec 12) (src_val dst_old v7 : Word) (base : Addr)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 off_src) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 off_dst) = true) :
    cpsTriple base (base + 8)
      (CodeReq.singleton base (.LD .x7 .x12 off_src) |>.union
        (CodeReq.singleton (base + 4) (.SD .x12 .x7 off_dst)))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ src_val) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ src_val)) := by
  runBlock

-- ============================================================================
-- CodeReq for generic DUP (explicit union chain, not ofProg)
-- ============================================================================

/-- CodeReq for generic DUPn: 9 instructions = 36 bytes.
    Built as an explicit union chain because symbolic n prevents ofProg reduction. -/
abbrev evm_dup_code (base : Addr) (n : Nat) : CodeReq :=
  CodeReq.singleton base (.ADDI .x12 .x12 (-32))
  |>.union (CodeReq.singleton (base + 4)  (.LD .x7 .x12 (BitVec.ofNat 12 (n*32))))
  |>.union (CodeReq.singleton (base + 8)  (.SD .x12 .x7 (BitVec.ofNat 12 0)))
  |>.union (CodeReq.singleton (base + 12) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+8))))
  |>.union (CodeReq.singleton (base + 16) (.SD .x12 .x7 (BitVec.ofNat 12 8)))
  |>.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+16))))
  |>.union (CodeReq.singleton (base + 24) (.SD .x12 .x7 (BitVec.ofNat 12 16)))
  |>.union (CodeReq.singleton (base + 28) (.LD .x7 .x12 (BitVec.ofNat 12 (n*32+24))))
  |>.union (CodeReq.singleton (base + 32) (.SD .x12 .x7 (BitVec.ofNat 12 24)))

-- ============================================================================
-- Low-level generic DUP spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Generic DUPn spec (low level): copies 4 dword limbs from src (at nsp+n*32) to dst (at nsp).
    Requires 1 ≤ n ≤ 16 (valid EVM DUP range). -/
theorem evm_dup_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (s0 s1 s2 s3 : Word)
    (d0 d1 d2 d3 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 4)) :
    cpsTriple base (base + 36) (evm_dup_code base n)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp+8) ↦ₘ d1) ** ((nsp+16) ↦ₘ d2) ** ((nsp+24) ↦ₘ d3) **
       ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
       ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3))
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ s3) **
       (nsp ↦ₘ s0) ** ((nsp+8) ↦ₘ s1) ** ((nsp+16) ↦ₘ s2) ** ((nsp+24) ↦ₘ s3) **
       ((nsp + BitVec.ofNat 64 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 64 (n*32+8))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 64 (n*32+16)) ↦ₘ s2) **
       ((nsp + BitVec.ofNat 64 (n*32+24)) ↦ₘ s3)) := by
  -- signExtend12 normalizations for source offsets
  have hse_s0 : signExtend12 (BitVec.ofNat 12 (n*32)) = BitVec.ofNat 64 (n*32) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 64 (n*32+8) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 64 (n*32+16) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 64 (n*32+24) :=
    signExtend12_ofNat_small _ (by omega)
  -- signExtend12 normalizations for destination offsets
  have hm0  : nsp + signExtend12 (BitVec.ofNat 12 0)  = nsp      := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  have hm8  : nsp + signExtend12 (BitVec.ofNat 12 8)  = nsp + 8  := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  have hm16 : nsp + signExtend12 (BitVec.ofNat 12 16) = nsp + 16 := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  have hm24 : nsp + signExtend12 (BitVec.ofNat 12 24) = nsp + 24 := by
    rw [signExtend12_ofNat_small _ (by omega)]; bv_omega
  -- Memory validity from ValidMemRange for dst locations
  have hv0  : isValidDwordAccess nsp       = true := by have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8  : isValidDwordAccess (nsp + 8)  = true := by have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (nsp + 16) = true := by have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (nsp + 24) = true := by have := hvalid.get (i := 3) (by omega); simpa using this
  -- Memory validity from ValidMemRange for src locations
  have hvs0 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32)) = true := by
    have := hvalid.get (i := n*4) (by omega); rwa [show 8 * (n * 4) = n * 32 from by omega] at this
  have hvs8 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32+8)) = true := by
    have := hvalid.get (i := n*4+1) (by omega); rwa [show 8 * (n * 4 + 1) = n * 32 + 8 from by omega] at this
  have hvs16 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32+16)) = true := by
    have := hvalid.get (i := n*4+2) (by omega); rwa [show 8 * (n * 4 + 2) = n * 32 + 16 from by omega] at this
  have hvs24 : isValidDwordAccess (nsp + BitVec.ofNat 64 (n*32+24)) = true := by
    have := hvalid.get (i := n*4+3) (by omega); rwa [show 8 * (n * 4 + 3) = n * 32 + 24 from by omega] at this
  -- ADDI spec
  have sA := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at sA
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at sA
  -- Pair specs (LD + SD for each limb)
  have P0 := dup_pair_spec nsp
    (BitVec.ofNat 12 (n*32)) (BitVec.ofNat 12 0) s0 d0 v7 (base + 4)
    (by rw [hse_s0]; exact hvs0) (by rw [hm0]; exact hv0)
  rw [hse_s0, hm0] at P0
  have P1 := dup_pair_spec nsp
    (BitVec.ofNat 12 (n*32+8)) (BitVec.ofNat 12 8) s1 d1 s0 (base + 12)
    (by rw [hse_s1]; exact hvs8) (by rw [hm8]; exact hv8)
  rw [hse_s1, hm8] at P1
  have P2 := dup_pair_spec nsp
    (BitVec.ofNat 12 (n*32+16)) (BitVec.ofNat 12 16) s2 d2 s1 (base + 20)
    (by rw [hse_s2]; exact hvs16) (by rw [hm16]; exact hv16)
  rw [hse_s2, hm16] at P2
  have P3 := dup_pair_spec nsp
    (BitVec.ofNat 12 (n*32+24)) (BitVec.ofNat 12 24) s3 d3 s2 (base + 28)
    (by rw [hse_s3]; exact hvs24) (by rw [hm24]; exact hv24)
  rw [hse_s3, hm24] at P3
  runBlock sA P0 P1 P2 P3

-- ============================================================================
-- EvmWord-level DUP spec
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- DUPn spec at evmWordIs level: copies the nth stack element to new top position. -/
theorem evm_dup_evmword_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (src dst : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 4)) :
    cpsTriple base (base + 36) (evm_dup_code base n)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp dst **
       evmWordIs (nsp + BitVec.ofNat 64 (n * 32)) src)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ src.getLimb 3) **
       evmWordIs nsp src **
       evmWordIs (nsp + BitVec.ofNat 64 (n * 32)) src) := by
  -- Address normalizations for evmWordIs (nsp + BitVec.ofNat 64 (n*32))
  have haddr8  : (nsp + BitVec.ofNat 64 (n*32) : Addr) + 8  = nsp + BitVec.ofNat 64 (n*32+8)  := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr16 : (nsp + BitVec.ofNat 64 (n*32) : Addr) + 16 = nsp + BitVec.ofNat 64 (n*32+16) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr24 : (nsp + BitVec.ofNat 64 (n*32) : Addr) + 24 = nsp + BitVec.ofNat 64 (n*32+24) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
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
    cpsTriple base (base + 36) (evm_dup_code base n)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp d **
       evmStackIs (nsp + 32) stack)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ vn.getLimb 3) **
       evmWordIs nsp vn **
       evmStackIs (nsp + 32) stack) := by
  intro vn
  -- Split evmStackIs at position (n-1) to extract the target element
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

end EvmAsm.Rv64
