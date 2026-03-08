/-
  EvmAsm.Evm64.Comparison

  256-bit EVM comparison operations (ISZERO, LT, GT, EQ, SLT, SGT) as RV64 programs.
  ISZERO: unary, OR all 4 limbs, SLTIU to boolean, store result.
  LT/GT: binary, multi-limb subtraction tracking only the borrow.
  SLT/SGT: binary, signed compare MSB limb, then unsigned borrow for lower limbs.
  EQ: binary, XOR-OR accumulation, SLTIU to boolean.

  Per-limb specs are defined here; full composition specs are in
  IsZero.lean, Lt.lean, Gt.lean, Eq.lean, Slt.lean, Sgt.lean
  (which can build in parallel).
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

/-- 256-bit EVM ISZERO: unary (pop 1, push 1, sp unchanged).
    OR all 4 limbs into x7, then SLTIU x7, x7, 1 (x7 = x7 == 0 ? 1 : 0).
    Store 256-bit result: limb[0] = x7, limbs[1-3] = 0 (via x0).
    12 instructions total. -/
def evm_iszero : Program :=
  -- OR reduction: load limb 0, then load & OR limbs 1-3 (7 instructions)
  LD .x7 .x12 0 ;;
  LD .x6 .x12 8  ;; single (.OR .x7 .x7 .x6) ;;
  LD .x6 .x12 16 ;; single (.OR .x7 .x7 .x6) ;;
  LD .x6 .x12 24 ;; single (.OR .x7 .x7 .x6) ;;
  -- Convert to boolean (1 instruction)
  single (.SLTIU .x7 .x7 1) ;;
  -- Store 256-bit result: limb[0] = x7, limbs[1-3] = 0 (4 instructions)
  SD .x12 .x7 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

/-- 256-bit EVM LT: binary (pop 2, push 1, sp += 32).
    Computes a < b by tracking borrow across multi-limb subtraction.
    Final borrow = 1 iff a < b. Store boolean result as 256-bit value.
    26 instructions total. -/
def evm_lt : Program :=
  -- Limb 0 (3 instructions): borrow detection only
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limb 1 (6 instructions): borrow propagation
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2 (6 instructions)
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 3 (6 instructions)
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- sp adjustment + store 256-bit result (5 instructions)
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

/-- 256-bit EVM GT: binary (pop 2, push 1, sp += 32).
    GT(a, b) = LT(b, a): swap load order vs evm_lt.
    26 instructions total. -/
def evm_gt : Program :=
  -- Limb 0 (3 instructions): load b into x7, a into x6
  LD .x7 .x12 32 ;; LD .x6 .x12 0 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limb 1 (6 instructions)
  LD .x7 .x12 40 ;; LD .x6 .x12 8 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2 (6 instructions)
  LD .x7 .x12 48 ;; LD .x6 .x12 16 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 3 (6 instructions)
  LD .x7 .x12 56 ;; LD .x6 .x12 24 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- sp adjustment + store 256-bit result (5 instructions)
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

/-- 256-bit EVM SLT (Signed Less Than): binary (pop 2, push 1, sp += 32).
    Compare MSB limbs (limb 3) with signed RV64 SLT instruction.
    If MSB limbs equal, fall through to unsigned borrow chain on limbs 0-2.
    25 instructions total. -/
def evm_slt : Program :=
  -- Phase 1: Load MSB limbs and branch (3 instructions)
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;;
  single (.BEQ .x7 .x6 12) ;;
  -- MSB differ path (2 instructions): signed compare + jump to store
  single (.SLT .x5 .x7 .x6) ;; single (.JAL .x0 64) ;;
  -- Lower compare path: 3-limb unsigned borrow chain (15 instructions)
  -- Limb 0 (3 instructions)
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limb 1 (6 instructions)
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2 (6 instructions)
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Store phase (5 instructions)
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

/-- 256-bit EVM SGT (Signed Greater Than): binary (pop 2, push 1, sp += 32).
    SGT(a, b) = SLT(b, a): swap load order vs evm_slt.
    25 instructions total. -/
def evm_sgt : Program :=
  -- Phase 1: Load MSB limbs (swapped) and branch (3 instructions)
  LD .x7 .x12 56 ;; LD .x6 .x12 24 ;;
  single (.BEQ .x7 .x6 12) ;;
  -- MSB differ path (2 instructions): signed compare + jump to store
  single (.SLT .x5 .x7 .x6) ;; single (.JAL .x0 64) ;;
  -- Lower compare path: 3-limb unsigned borrow chain (swapped, 15 instructions)
  -- Limb 0 (3 instructions)
  LD .x7 .x12 32 ;; LD .x6 .x12 0 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limb 1 (6 instructions)
  LD .x7 .x12 40 ;; LD .x6 .x12 8 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2 (6 instructions)
  LD .x7 .x12 48 ;; LD .x6 .x12 16 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Store phase (5 instructions)
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

/-- 256-bit EVM EQ: binary (pop 2, push 1, sp += 32).
    XOR each limb pair, OR-reduce all XORs, SLTIU to boolean.
    21 instructions total. -/
def evm_eq : Program :=
  -- Limb 0 (3 instructions): XOR
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;;
  -- Limb 1 (4 instructions): XOR + OR-accumulate
  LD .x6 .x12 8 ;; LD .x5 .x12 40 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 2 (4 instructions)
  LD .x6 .x12 16 ;; LD .x5 .x12 48 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 3 (4 instructions)
  LD .x6 .x12 24 ;; LD .x5 .x12 56 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Convert to boolean + sp adjustment + store (6 instructions)
  single (.SLTIU .x7 .x7 1) ;;
  ADDI .x12 .x12 32 ;;
  SD .x12 .x7 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

-- ============================================================================
-- Per-limb Specs: LT (borrow propagation without storing results)
-- ============================================================================

/-- LT limb 0 spec (3 instructions): LD, LD, SLTU.
    Computes initial borrow = (a < b ? 1 : 0). Does NOT modify memory. -/
theorem lt_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let code :=
      (base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SLTU .x5 .x7 .x6)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a_limb) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- LT carry limb spec (6 instructions): LD, LD, SLTU, SUB, SLTU, OR.
    Propagates borrow without storing result. Memory is NOT modified. -/
theorem lt_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let borrow_out := borrow1 ||| borrow2
    let code :=
      (base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .SLTU .x11 .x7 .x6) ** ((base + 12) ↦ᵢ .SUB .x7 .x7 .x6) **
      ((base + 16) ↦ᵢ .SLTU .x6 .x7 .x5) ** ((base + 20) ↦ᵢ .OR .x5 .x11 .x6)
    cpsTriple base (base + 24)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: EQ (XOR + OR accumulation)
-- ============================================================================

/-- EQ limb 0 spec (3 instructions): LD x7, LD x6, XOR x7 x7 x6. -/
theorem eq_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let code :=
      (base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
      ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- EQ OR-limb spec (4 instructions): LD x6, LD x5, XOR x6 x6 x5, OR x7 x7 x6. -/
theorem eq_or_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v6 v5 acc : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let xor_k := a_limb ^^^ b_limb
    let code :=
      (base ↦ᵢ .LD .x6 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x5 .x12 off_b) **
      ((base + 8) ↦ᵢ .XOR .x6 .x6 .x5) ** ((base + 12) ↦ᵢ .OR .x7 .x7 .x6)
    cpsTriple base (base + 16)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (acc ||| xor_k)) ** (.x6 ↦ᵣ xor_k) ** (.x5 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: ISZERO (OR reduction)
-- ============================================================================

/-- ISZERO OR-limb spec (2 instructions): LD x6, OR x7 x7 x6.
    Loads a limb and OR-accumulates into x7. -/
theorem iszero_or_limb_spec (off : BitVec 12)
    (sp a_limb v6 acc : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    let code :=
      (base ↦ᵢ .LD .x6 .x12 off) ** ((base + 4) ↦ᵢ .OR .x7 .x7 .x6)
    cpsTriple base (base + 8)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) **
       (mem ↦ₘ a_limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (acc ||| a_limb)) ** (.x6 ↦ᵣ a_limb) **
       (mem ↦ₘ a_limb)) := by
  runBlock

-- ============================================================================
-- BEQ helper specs (single-path, for SLT/SGT composition)
-- ============================================================================

/-- BEQ when values are equal: always taken (jump to PC + signExtend13 offset).
    BEQ only modifies PC; all pcFree assertions are preserved. -/
theorem beq_eq_spec (rs1 rs2 : Reg) (offset : BitVec 13)
    (v : Word) (base : Addr) :
    cpsTriple base (base + signExtend13 offset)
      ((base ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v))
      ((base ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v)) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs1 : s.getReg rs1 = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hrs2 : s.getReg rs2 = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
    simp [execInstrBr, hrs1, hrs2]
  refine ⟨1, s.setPC (s.pc + signExtend13 offset), ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_sepConj (pcFree_regIs _ _) (pcFree_regIs _ _))) hR) _ _ hPR

/-- BEQ when values are not equal: never taken (fall through to PC + 4).
    BEQ only modifies PC; all pcFree assertions are preserved. -/
theorem beq_ne_spec (rs1 rs2 : Reg) (offset : BitVec 13)
    (v1 v2 : Word) (hne : v1 ≠ v2) (base : Addr) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((base ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) := by
  intro R hR s hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + 4) := by
    simp [execInstrBr, hrs1, hrs2, bne_iff_ne, hne]
  refine ⟨1, s.setPC (s.pc + 4), ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_sepConj (pcFree_regIs _ _) (pcFree_regIs _ _))) hR) _ _ hPR

-- ============================================================================
-- Per-limb Specs: SLT (MSB load + signed comparison)
-- ============================================================================

/-- SLT MSB load spec (2 instructions): LD x7, LD x6.
    Loads the MSB limbs (limb 3) of both operands into x7 and x6. -/
theorem slt_msb_load_spec (off_a off_b : BitVec 12)
    (sp a3 b3 v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let code :=
      (base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b)
    cpsTriple base (base + 8)
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a3) ** (mem_b ↦ₘ b3))
      (code **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
       (mem_a ↦ₘ a3) ** (mem_b ↦ₘ b3)) := by
  runBlock

end EvmAsm.Rv64
