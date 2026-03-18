/-
  EvmAsm.Evm64.Bitwise

  256-bit EVM bitwise operations (AND, OR, XOR, NOT) as RV64 programs.
  Each operates on 4 little-endian 64-bit limbs stored in memory.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Program Definitions
-- ============================================================================

/-- 256-bit EVM AND: binary, pops 2, pushes 1.
    For each of 4 limbs: load A[i] and B[i], AND them, store to B[i].
    Then advance sp by 32. -/
def evm_and : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM OR. -/
def evm_or : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM XOR. -/
def evm_xor : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM NOT: unary (pop 1, push 1, sp unchanged).
    For each limb: load, XOR with -1 (complement), store back. -/
def evm_not : Program :=
  LD .x7 .x12 0 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 0 ;;
  LD .x7 .x12 8 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 8 ;;
  LD .x7 .x12 16 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 16 ;;
  LD .x7 .x12 24 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 24

-- ============================================================================
-- Per-limb Specs: Binary Bitwise
-- ============================================================================

/-- Per-limb AND spec (4 instructions: LD x7, LD x6, AND x7 x7 x6, SD x12 x7).
    Loads A[i] and B[i], computes AND, stores result at B[i]'s location. -/
theorem and_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb &&& b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb &&& b_limb))) := by
  runBlock

/-- Per-limb OR spec (4 instructions: LD x7, LD x6, OR x7 x7 x6, SD x12 x7). -/
theorem or_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ||| b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ||| b_limb))) := by
  runBlock

/-- Per-limb XOR spec (4 instructions: LD x7, LD x6, XOR x7 x7 x6, SD x12 x7). -/
theorem xor_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.XOR .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ^^^ b_limb))) := by
  runBlock

/-- Per-limb NOT spec (3 instructions: LD x7, XORI x7 x7 (-1), SD x12 x7).
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec (off : BitVec 12)
    (sp limb v7 : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off))
      (CodeReq.union (CodeReq.singleton (base + 4) (.XORI .x7 .x7 (-1)))
       (CodeReq.singleton (base + 8) (.SD .x12 .x7 off)))
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  runBlock

end EvmAsm.Rv64
