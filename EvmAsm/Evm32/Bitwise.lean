/-
  EvmAsm.Evm32.Bitwise

  256-bit EVM bitwise operations (AND, OR, XOR, NOT) as RISC-V programs.
  Each operates on 8 little-endian 32-bit limbs stored in memory.
-/

import EvmAsm.Evm32.Stack
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.RunBlock

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
  single (.ADDI .x12 .x12 32)

/-- 256-bit EVM OR: binary, pops 2, pushes 1. -/
def evm_or : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  single (.ADDI .x12 .x12 32)

/-- 256-bit EVM XOR: binary, pops 2, pushes 1. -/
def evm_xor : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  single (.ADDI .x12 .x12 32)

/-- 256-bit EVM NOT: unary, pops 1, pushes 1.
    For each of 8 limbs: load, XOR with -1, store back. -/
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
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SW .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb &&& b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb &&& b_limb))) := by
  runBlock

/-- Per-limb OR spec (4 instructions: LW x7, LW x6, OR x7 x7 x6, SW x12 x7). -/
theorem or_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SW .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ||| b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ||| b_limb))) := by
  runBlock

/-- Per-limb XOR spec (4 instructions: LW x7, LW x6, XOR x7 x7 x6, SW x12 x7). -/
theorem xor_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.XOR .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SW .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ^^^ b_limb))) := by
  runBlock

/-- Per-limb NOT spec (3 instructions: LW x7, XORI x7 x7 (-1), SW x12 x7).
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec (off : BitVec 12)
    (sp limb v7 : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.XORI .x7 .x7 (-1)))
       (CodeReq.singleton (base + 8) (.SW .x12 .x7 off)))
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  have S0 := lw_spec_gen .x7 .x12 sp v7 limb off base (by nofun) hvalid
  have S1 := xori_spec_gen_same .x7 limb (-1) (base + 4) (by nofun)
  have S2 := sw_spec_gen .x12 .x7 sp (limb ^^^ signExtend12 (-1)) limb off (base + 8) hvalid
  generalize limb ^^^ signExtend12 (-1 : BitVec 12) = c at S1 S2 ⊢
  runBlock S0 S1 S2

end EvmAsm
