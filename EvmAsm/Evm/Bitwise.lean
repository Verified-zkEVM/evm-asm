/-
  EvmAsm.Evm.Bitwise

  256-bit EVM bitwise operations (AND, OR, XOR, NOT) as RISC-V programs.
  Each operates on 8 little-endian 32-bit limbs stored in memory.
-/

import EvmAsm.Evm.Stack
import EvmAsm.CPSSpec
import EvmAsm.SyscallSpecs
import EvmAsm.Tactics.XSimp

open EvmAsm.Tactics

namespace EvmAsm

-- ============================================================================
-- Program Definitions
-- ============================================================================

/-- 256-bit EVM AND: binary, pops 2, pushes 1.
    For each of 8 limbs: load A[i] and B[i], AND them, store to B[i].
    Then advance sp by 32. -/
def evm_and : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM OR. -/
def evm_or : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM XOR. -/
def evm_xor : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM NOT: unary (pop 1, push 1, sp unchanged).
    For each limb: load, XOR with -1 (complement), store back. -/
def evm_not : Program :=
  LW .x7 .x12 0 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 0 ;;
  LW .x7 .x12 4 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 4 ;;
  LW .x7 .x12 8 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 8 ;;
  LW .x7 .x12 12 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 12 ;;
  LW .x7 .x12 16 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 16 ;;
  LW .x7 .x12 20 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 20 ;;
  LW .x7 .x12 24 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 24 ;;
  LW .x7 .x12 28 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 28

-- ============================================================================
-- Per-limb Specs: Binary Bitwise
-- ============================================================================

/-- Per-limb AND spec (4 instructions: LW x7, LW x6, AND x7 x7 x6, SW x12 x7).
    Loads A[i] and B[i], computes AND, stores result at B[i]'s location. -/
theorem and_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb &&& b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb &&& b_limb))) := by
  -- Address normalization
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  have ha3 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  -- Step 1: LW x7 x12 off_a at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .LW .x6 .x12 off_b) ** ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x6 ↦ᵣ v6) **
     ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (by pcFree) (lw_spec_gen .x7 .x12 sp v7 a_limb off_a base (by nofun) hvalid_a)
  -- Step 2: LW x6 x12 off_b at base+4
  have s2_raw := lw_spec_gen .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hvalid_b
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x7 ↦ᵣ a_limb) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2
  clear s1 s2 s2_raw
  -- Step 3: AND x7 x7 x6 at base+8
  have s3_raw := and_spec_gen_rd_eq_rs1 .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun)
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x12 ↦ᵣ sp) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (by pcFree) s3_raw
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3
  clear s12 s3 s3_raw
  -- Step 4: SW x12 x7 off_b at base+12
  have s4_raw := sw_spec_gen .x12 .x7 sp (a_limb &&& b_limb) b_limb off_b (base + 12) hvalid_b
  rw [ha3] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** (.x6 ↦ᵣ b_limb) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (by pcFree) s4_raw
  -- Compose all and permute to match spec
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s123 s4)

/-- Per-limb OR spec (4 instructions: LW x7, LW x6, OR x7 x7 x6, SW x12 x7). -/
theorem or_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ||| b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ||| b_limb))) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  have ha3 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .LW .x6 .x12 off_b) ** ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x6 ↦ᵣ v6) **
     ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (by pcFree) (lw_spec_gen .x7 .x12 sp v7 a_limb off_a base (by nofun) hvalid_a)
  have s2_raw := lw_spec_gen .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hvalid_b
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x7 ↦ᵣ a_limb) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2
  clear s1 s2 s2_raw
  have s3_raw := or_spec_gen_rd_eq_rs1 .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun)
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x12 ↦ᵣ sp) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (by pcFree) s3_raw
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3
  clear s12 s3 s3_raw
  have s4_raw := sw_spec_gen .x12 .x7 sp (a_limb ||| b_limb) b_limb off_b (base + 12) hvalid_b
  rw [ha3] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
     ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) ** (.x6 ↦ᵣ b_limb) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (by pcFree) s4_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s123 s4)

/-- Per-limb XOR spec (4 instructions: LW x7, LW x6, XOR x7 x7 x6, SW x12 x7). -/
theorem xor_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ^^^ b_limb))) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  have ha3 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .LW .x6 .x12 off_b) ** ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x6 ↦ᵣ v6) **
     ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (by pcFree) (lw_spec_gen .x7 .x12 sp v7 a_limb off_a base (by nofun) hvalid_a)
  have s2_raw := lw_spec_gen .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hvalid_b
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x7 ↦ᵣ a_limb) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2
  clear s1 s2 s2_raw
  have s3_raw := xor_spec_gen_rd_eq_rs1 .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun)
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
     ((base + 12) ↦ᵢ .SW .x12 .x7 off_b) ** (.x12 ↦ᵣ sp) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (by pcFree) s3_raw
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3
  clear s12 s3 s3_raw
  have s4_raw := sw_spec_gen .x12 .x7 sp (a_limb ^^^ b_limb) b_limb off_b (base + 12) hvalid_b
  rw [ha3] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
     ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** (.x6 ↦ᵣ b_limb) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (by pcFree) s4_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s123 s4)

/-- Per-limb NOT spec (3 instructions: LW x7, XORI x7 x7 (-1), SW x12 x7).
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec (off : BitVec 12)
    (sp limb v7 : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    cpsTriple base (base + 12)
      ((base ↦ᵢ .LW .x7 .x12 off) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) **
       ((base + 8) ↦ᵢ .SW .x12 .x7 off) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((base ↦ᵢ .LW .x7 .x12 off) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) **
       ((base + 8) ↦ᵢ .SW .x12 .x7 off) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  -- Step 1: LW x7 x12 off at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 8) ↦ᵢ .SW .x12 .x7 off))
    (by pcFree) (lw_spec_gen .x7 .x12 sp v7 limb off base (by nofun) hvalid)
  -- Step 2: XORI x7 x7 (-1) at base+4
  have s2_raw := xori_spec_gen_same .x7 limb (-1) (base + 4) (by nofun)
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off) ** ((base + 8) ↦ᵢ .SW .x12 .x7 off) **
     (.x12 ↦ᵣ sp) ** ((sp + signExtend12 off) ↦ₘ limb))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2
  clear s1 s2 s2_raw
  -- Step 3: SW x12 x7 off at base+8
  have s3_raw := sw_spec_gen .x12 .x7 sp (limb ^^^ signExtend12 (-1)) limb off (base + 8) hvalid
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 off) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)))
    (by pcFree) s3_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s12 s3)

-- ============================================================================
-- Helpers
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Individual limb canonicalizers
-- Each lifts a 5-conjunct per-limb spec to the full 19-conjunct canonical form.
-- Only 2 sep_perm calls per theorem, well within heartbeat limits.
-- ============================================================================

private theorem bw_limb0 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ b0))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ op a0 b0))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ op a0 b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb1 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ b1))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ op a1 b1))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ op a1 b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb2 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ b2))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ op a2 b2))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ op a2 b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb3 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ b3))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ op a3 b3))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ op a3 b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb4 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ b4))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a4 b4) ** (.x6 ↦ᵣ b4) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ op a4 b4))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a4 b4) ** (.x6 ↦ᵣ b4) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ op a4 b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb5 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ b5))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a5 b5) ** (.x6 ↦ᵣ b5) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ op a5 b5))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a5 b5) ** (.x6 ↦ᵣ b5) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ op a5 b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb6 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ b6))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a6 b6) ** (.x6 ↦ᵣ b6) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ op a6 b6))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a6 b6) ** (.x6 ↦ᵣ b6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ op a6 b6) ** ((sp + 60) ↦ₘ b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb7 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ op a7 b7))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ op a7 b7)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

-- ============================================================================
-- ADDI canonicalizer: changes x12 from sp to sp+32, no sep_perm needed
-- ============================================================================

private theorem bw_addi (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTriple (base + 128) (base + 132)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have ha : (base + 128 : Addr) + 4 = base + 132 := by bv_omega
  have s_raw := addi_spec_gen_same .x12 sp 32 (base + 128) (by nofun)
  rw [ha] at s_raw
  simp only [signExtend12_32] at s_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (pcFree_sepConj hF (by pcFree)) s_raw)

-- ============================================================================
-- Address recasting helpers for cpsTriple
-- ============================================================================

private theorem cpsTriple_addr_eq {P Q : Assertion}
    {s1 s2 e1 e2 : Addr} (hs : s1 = s2) (he : e1 = e2)
    (h : cpsTriple s1 e1 P Q) :
    cpsTriple s2 e2 P Q := by
  subst hs; subst he; exact h

-- ============================================================================
-- Full binary bitwise spec: composes 8 limb canonicalizers + ADDI.
-- Takes an abstract pcFree assertion F (representing instruction memory) and
-- 8 per-limb hypotheses, each with F and the two relevant memory cells.
-- Uses ValidMemRange for clean validity hypotheses.
-- ============================================================================

set_option maxHeartbeats 12800000 in
theorem binary_bitwise_spec (sp base : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L0 : cpsTriple base (base + 16)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ b0))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ op a0 b0)))
    (L1 : cpsTriple (base + 16) (base + 32)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ b1))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ op a1 b1)))
    (L2 : cpsTriple (base + 32) (base + 48)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ b2))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ op a2 b2)))
    (L3 : cpsTriple (base + 48) (base + 64)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ b3))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ op a3 b3)))
    (L4 : cpsTriple (base + 64) (base + 80)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ b4))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a4 b4) ** (.x6 ↦ᵣ b4) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ op a4 b4)))
    (L5 : cpsTriple (base + 80) (base + 96)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a4 b4) ** (.x6 ↦ᵣ b4) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ b5))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a5 b5) ** (.x6 ↦ᵣ b5) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ op a5 b5)))
    (L6 : cpsTriple (base + 96) (base + 112)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a5 b5) ** (.x6 ↦ᵣ b5) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ b6))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a6 b6) ** (.x6 ↦ᵣ b6) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ op a6 b6)))
    (L7 : cpsTriple (base + 112) (base + 128)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a6 b6) ** (.x6 ↦ᵣ b6) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ b7))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ op a7 b7)))
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 132)
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ op a0 b0) ** ((sp + 36) ↦ₘ op a1 b1) ** ((sp + 40) ↦ₘ op a2 b2) ** ((sp + 44) ↦ₘ op a3 b3) **
       ((sp + 48) ↦ₘ op a4 b4) ** ((sp + 52) ↦ₘ op a5 b5) ** ((sp + 56) ↦ₘ op a6 b6) ** ((sp + 60) ↦ₘ op a7 b7)) := by
  -- G bundles F with ADDI instrAt for bw_limb helpers
  let G := F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)
  have hG : G.pcFree := pcFree_sepConj hF (by pcFree)
  -- Convert L hypotheses from flat exit addresses to (base_k + 16) form
  -- using cpsTriple_addr_eq which only touches the address parameters, not assertions
  have L1' := cpsTriple_addr_eq (rfl : (base + 16 : Addr) = base + 16)
    (by bv_omega : (base + 32 : Addr) = (base + 16) + 16) L1
  have L2' := cpsTriple_addr_eq (by bv_omega : (base + 32 : Addr) = (base + 32))
    (by bv_omega : (base + 48 : Addr) = (base + 32) + 16) L2
  have L3' := cpsTriple_addr_eq (rfl : (base + 48 : Addr) = base + 48)
    (by bv_omega : (base + 64 : Addr) = (base + 48) + 16) L3
  have L4' := cpsTriple_addr_eq (rfl : (base + 64 : Addr) = base + 64)
    (by bv_omega : (base + 80 : Addr) = (base + 64) + 16) L4
  have L5' := cpsTriple_addr_eq (rfl : (base + 80 : Addr) = base + 80)
    (by bv_omega : (base + 96 : Addr) = (base + 80) + 16) L5
  have L6' := cpsTriple_addr_eq (rfl : (base + 96 : Addr) = base + 96)
    (by bv_omega : (base + 112 : Addr) = (base + 96) + 16) L6
  have L7' := cpsTriple_addr_eq (rfl : (base + 112 : Addr) = base + 112)
    (by bv_omega : (base + 128 : Addr) = (base + 112) + 16) L7
  clear L1 L2 L3 L4 L5 L6 L7
  -- Expand each limb to full 16-mem level using bw_limb helpers
  have S0 := bw_limb0 sp base op a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 G hG L0
  have S1 := bw_limb1 sp (base + 16) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) b1 b2 b3 b4 b5 b6 b7 (op a0 b0) b0 G hG L1'
  -- S0 exit is (base + 16), S1 entry is (base + 16): ok
  -- S1 exit is ((base + 16) + 16), need to convert to (base + 32) for next composition
  have S01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S0 S1
  clear S0 S1 L0 L1'
  -- S01: cpsTriple base ((base + 16) + 16) ... need to rewrite exit to (base + 32)
  have S01' := cpsTriple_addr_eq (rfl) (by bv_omega : ((base + 16 : Addr) + 16) = base + 32) S01
  clear S01
  have S2 := bw_limb2 sp (base + 32) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) b2 b3 b4 b5 b6 b7 (op a1 b1) b1 G hG L2'
  have S012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S01' S2
  clear S01' S2 L2'
  have S012' := cpsTriple_addr_eq (rfl) (by bv_omega : ((base + 32 : Addr) + 16) = base + 48) S012
  clear S012
  have S3 := bw_limb3 sp (base + 48) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) b3 b4 b5 b6 b7 (op a2 b2) b2 G hG L3'
  have S0123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S012' S3
  clear S012' S3 L3'
  have S0123' := cpsTriple_addr_eq (rfl) (by bv_omega : ((base + 48 : Addr) + 16) = base + 64) S0123
  clear S0123
  have S4 := bw_limb4 sp (base + 64) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) b4 b5 b6 b7 (op a3 b3) b3 G hG L4'
  have S01234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S0123' S4
  clear S0123' S4 L4'
  have S01234' := cpsTriple_addr_eq (rfl) (by bv_omega : ((base + 64 : Addr) + 16) = base + 80) S01234
  clear S01234
  have S5 := bw_limb5 sp (base + 80) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) b5 b6 b7 (op a4 b4) b4 G hG L5'
  have S012345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S01234' S5
  clear S01234' S5 L5'
  have S012345' := cpsTriple_addr_eq (rfl) (by bv_omega : ((base + 80 : Addr) + 16) = base + 96) S012345
  clear S012345
  have S6 := bw_limb6 sp (base + 96) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) (op a5 b5) b6 b7 (op a5 b5) b5 G hG L6'
  have S0123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S012345' S6
  clear S012345' S6 L6'
  have S0123456' := cpsTriple_addr_eq (rfl) (by bv_omega : ((base + 96 : Addr) + 16) = base + 112) S0123456
  clear S0123456
  have S7 := bw_limb7 sp (base + 112) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) (op a5 b5) (op a6 b6) b7 (op a6 b6) b6 G hG L7'
  have S01234567 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S0123456' S7
  clear S0123456' S7 L7'
  have S01234567' := cpsTriple_addr_eq (rfl) (by bv_omega : ((base + 112 : Addr) + 16) = base + 128) S01234567
  clear S01234567
  -- ADDI step: bw_addi uses F (without ADDI instrAt), it adds ADDI explicitly
  have Saddi := bw_addi sp base a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) (op a5 b5) (op a6 b6) (op a7 b7)
    (op a7 b7) b7 F hF
  -- Compose limbs with ADDI; xperm_hyp handles G = F ** ADDI_instrAt
  exact cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S01234567' Saddi

end EvmAsm
