/-
  EvmAsm.Evm64.Exp.LimbSpec

  Per-block / per-limb cpsTriple specs for EXP sub-blocks (square block,
  conditional-multiply block, iter body, loop, prologue, epilogue).

  Slice 4a (beads evm-asm-w5of) lands `exp_bit_test_block_spec_within`.
  Subsequent slices (evm-asm-mtj3 family) will add `exp_square_block_spec`
  and `exp_cond_mul_block_spec`. Per `OPCODE_TEMPLATE.md`, each sub-block
  gets exactly one cpsTriple lemma.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.Exp.LimbSpecBase

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (ADDI Assertion CodeReq LD SD addi_spec_gen_same_within
  addi_spec_gen_within andi_spec_gen_within beq_spec_within bne_spec_gen_within
  cpsBranchWithin cpsBranchWithin_extend_code cpsBranchWithin_frameR
  cpsBranchWithin_ntakenPath cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
  cpsBranchWithin_takenPath cpsBranchWithin_takenStripPure2 cpsBranchWithin_weaken
  cpsTripleWithin cpsTripleWithin_extend_code cpsTripleWithin_frameR
  cpsTripleWithin_mono_nSteps cpsTripleWithin_seq_perm_same_cr cpsTripleWithin_seq_same_cr
  cpsTripleWithin_seq_cpsBranchWithin_with_perm cpsTripleWithin_weaken
  generic_sd_spec_within jal_spec_within ld_spec_gen_within seq sepConj_pure_right
  signExtend12 signExtend13 signExtend21 single slli_spec_gen_same_within
  srli_spec_gen_same_within srli_spec_gen_within)

/-- The word assembled from the four accumulator limbs copied out by
    `exp_epilogue`. Limbs are little-endian, matching `evmWordIs`. -/
def expResultWord (r0 r1 r2 r3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun
    | ⟨0, _⟩ => r0
    | ⟨1, _⟩ => r1
    | ⟨2, _⟩ => r2
    | ⟨3, _⟩ => r3)

theorem expResultWord_getLimbN_0 (r0 r1 r2 r3 : Word) :
    (expResultWord r0 r1 r2 r3).getLimbN 0 = r0 := by
  unfold expResultWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

theorem expResultWord_getLimbN_1 (r0 r1 r2 r3 : Word) :
    (expResultWord r0 r1 r2 r3).getLimbN 1 = r1 := by
  unfold expResultWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

theorem expResultWord_getLimbN_2 (r0 r1 r2 r3 : Word) :
    (expResultWord r0 r1 r2 r3).getLimbN 2 = r2 := by
  unfold expResultWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

theorem expResultWord_getLimbN_3 (r0 r1 r2 r3 : Word) :
    (expResultWord r0 r1 r2 r3).getLimbN 3 = r3 := by
  unfold expResultWord
  rw [EvmWord.getLimbN_lt _ _ (by decide), EvmWord.getLimb_fromLimbs]

theorem expResultWord_getLimbN_4 (r0 r1 r2 r3 : Word) :
    (expResultWord r0 r1 r2 r3).getLimbN 4 = 0 := by
  simp [EvmWord.getLimbN]

/-- Repacking the four concrete limbs of an EVM word with `expResultWord`
    returns the original word. -/
theorem expResultWord_getLimbN_self (r : EvmWord) :
    expResultWord (r.getLimbN 0) (r.getLimbN 1) (r.getLimbN 2) (r.getLimbN 3) = r := by
  apply EvmWord.eq_iff_limbs.mpr
  intro i
  fin_cases i <;> unfold expResultWord <;> rw [EvmWord.getLimb_fromLimbs] <;> rfl

/-- The four limbs written by `exp_epilogue` fold to the assembled EXP result
    word in the output stack slot at `evmSp + 32`. -/
theorem exp_epilogue_result_word
    (evmSp r0 r1 r2 r3 : Word) :
    (((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) =
    evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3) := by
  have h32 : (evmSp + signExtend12 (32 : BitVec 12) : Word) = evmSp + 32 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h40 : (evmSp + signExtend12 (40 : BitVec 12) : Word) = evmSp + 40 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h48 : (evmSp + signExtend12 (48 : BitVec 12) : Word) = evmSp + 48 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h56 : (evmSp + signExtend12 (56 : BitVec 12) : Word) = evmSp + 56 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  rw [h32, h40, h48, h56]
  exact (evmWordIs_sp32_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
    (expResultWord_getLimbN_0 r0 r1 r2 r3)
    (expResultWord_getLimbN_1 r0 r1 r2 r3)
    (expResultWord_getLimbN_2 r0 r1 r2 r3)
    (expResultWord_getLimbN_3 r0 r1 r2 r3)).symm

/-- Right-associated variant of `exp_epilogue_result_word` for composition
    postconditions with a framed remainder. -/
theorem exp_epilogue_result_word_right
    (evmSp r0 r1 r2 r3 : Word) (Q : Assertion) :
    (((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) ** Q) =
    (evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3) ** Q) := by
  have h32 : (evmSp + signExtend12 (32 : BitVec 12) : Word) = evmSp + 32 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h40 : (evmSp + signExtend12 (40 : BitVec 12) : Word) = evmSp + 40 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h48 : (evmSp + signExtend12 (48 : BitVec 12) : Word) = evmSp + 48 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h56 : (evmSp + signExtend12 (56 : BitVec 12) : Word) = evmSp + 56 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  rw [h32, h40, h48, h56]
  exact evmWordIs_sp32_limbs_eq_right evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3 Q
    (expResultWord_getLimbN_0 r0 r1 r2 r3)
    (expResultWord_getLimbN_1 r0 r1 r2 r3)
    (expResultWord_getLimbN_2 r0 r1 r2 r3)
    (expResultWord_getLimbN_3 r0 r1 r2 r3)

/-- Consumer-facing epilogue spec with the copied result limbs folded into the
    stack-word assertion used by later EXP composition proofs. -/
theorem exp_epilogue_word_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 base (base + 36) (CodeReq.ofProg base exp_epilogue)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by
      rw [← exp_epilogue_result_word evmSp r0 r1 r2 r3]
      xperm_hyp hq)
    (exp_epilogue_ofProg_spec_within sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

-- ============================================================================
-- Section: exp_loop_marshal_factor1 (8 instructions, slice 4-marshal-factor1
-- / evm-asm-do8x6)
-- ============================================================================
--
-- `exp_loop_marshal_factor1` (defined in `Exp/Program.lean`) copies the four
-- limbs of the running accumulator `result` from the local scratch frame at
-- `sp + 0..+24` into the LP64 MUL factor-1 slot at `x12 + 0..+24`:
--
--     LD .x5 .x2 0  ;; SD .x12 .x5 0  ;;
--     LD .x5 .x2 8  ;; SD .x12 .x5 8  ;;
--     LD .x5 .x2 16 ;; SD .x12 .x5 16 ;;
--     LD .x5 .x2 24 ;; SD .x12 .x5 24
--
-- Mirrors `exp_epilogue_spec_within`'s LD/SD chain (Section above), only
-- without the trailing `ADDI .x12 .x12 32` and with destination offsets
-- 0..24 rather than 32..56.

def exp_loop_marshal_factor1_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x5 .x2 0)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x5 0)).union
      ((CodeReq.singleton (base + 8) (.LD .x5 .x2 8)).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x5 8)).union
          ((CodeReq.singleton (base + 16) (.LD .x5 .x2 16)).union
            ((CodeReq.singleton (base + 20) (.SD .x12 .x5 16)).union
              ((CodeReq.singleton (base + 24) (.LD .x5 .x2 24)).union
                (CodeReq.singleton (base + 28) (.SD .x12 .x5 24))))))))

theorem exp_loop_marshal_factor1_code_eq_ofProg (base : Word) :
    exp_loop_marshal_factor1_code base =
      CodeReq.ofProg base exp_loop_marshal_factor1 := by
  unfold exp_loop_marshal_factor1_code exp_loop_marshal_factor1 LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x2 0, .SD .x12 .x5 0, .LD .x5 .x2 8,
     .SD .x12 .x5 8, .LD .x5 .x2 16, .SD .x12 .x5 16,
     .LD .x5 .x2 24, .SD .x12 .x5 24]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem exp_loop_marshal_factor1_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 base (base + 32) (exp_loop_marshal_factor1_code base)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) := by
  unfold exp_loop_marshal_factor1_code
  have hLd0 := ld_spec_gen_within .x5 .x2 sp tOld r0
    (0 : BitVec 12) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x5 evmSp r0 d0
    (0 : BitVec 12) (base + 4)
  have hLd1 := ld_spec_gen_within .x5 .x2 sp r0 r1
    (8 : BitVec 12) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x12 .x5 evmSp r1 d1
    (8 : BitVec 12) (base + 12)
  have hLd2 := ld_spec_gen_within .x5 .x2 sp r1 r2
    (16 : BitVec 12) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x12 .x5 evmSp r2 d2
    (16 : BitVec 12) (base + 20)
  have hLd3 := ld_spec_gen_within .x5 .x2 sp r2 r3
    (24 : BitVec 12) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x12 .x5 evmSp r3 d3
    (24 : BitVec 12) (base + 28)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3

theorem exp_loop_marshal_factor1_ofProg_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 base (base + 32)
      (CodeReq.ofProg base exp_loop_marshal_factor1)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) := by
  rw [← exp_loop_marshal_factor1_code_eq_ofProg]
  exact exp_loop_marshal_factor1_spec_within sp evmSp tOld
    r0 r1 r2 r3 d0 d1 d2 d3 base

-- ============================================================================
-- Section: exp_loop_marshal_result_to_factor2 (8 instructions, slice
-- evm-asm-koybi — sub-slice of evm-asm-mtj3 / #92)
-- ============================================================================
--
-- `exp_loop_marshal_result_to_factor2` (defined in `Exp/Program.lean`) copies
-- the four limbs of the running accumulator `result` from the local scratch
-- frame at `sp + 0..+24` into the LP64 MUL factor-2 slot at
-- `x12 + 32..+56`, used by the squaring-marshal where factor1 = factor2 =
-- result:
--
--     LD .x5 .x2 0  ;; SD .x12 .x5 32 ;;
--     LD .x5 .x2 8  ;; SD .x12 .x5 40 ;;
--     LD .x5 .x2 16 ;; SD .x12 .x5 48 ;;
--     LD .x5 .x2 24 ;; SD .x12 .x5 56
--
-- Identical structure to `exp_epilogue_spec_within` minus the trailing
-- `ADDI .x12 .x12 32`.

def exp_loop_marshal_result_to_factor2_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x5 .x2 0)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x5 32)).union
      ((CodeReq.singleton (base + 8) (.LD .x5 .x2 8)).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x5 40)).union
          ((CodeReq.singleton (base + 16) (.LD .x5 .x2 16)).union
            ((CodeReq.singleton (base + 20) (.SD .x12 .x5 48)).union
              ((CodeReq.singleton (base + 24) (.LD .x5 .x2 24)).union
                (CodeReq.singleton (base + 28) (.SD .x12 .x5 56))))))))

theorem exp_loop_marshal_result_to_factor2_code_eq_ofProg (base : Word) :
    exp_loop_marshal_result_to_factor2_code base =
      CodeReq.ofProg base exp_loop_marshal_result_to_factor2 := by
  unfold exp_loop_marshal_result_to_factor2_code
    exp_loop_marshal_result_to_factor2 LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x2 0, .SD .x12 .x5 32, .LD .x5 .x2 8,
     .SD .x12 .x5 40, .LD .x5 .x2 16, .SD .x12 .x5 48,
     .LD .x5 .x2 24, .SD .x12 .x5 56]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem exp_loop_marshal_result_to_factor2_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 base (base + 32)
      (exp_loop_marshal_result_to_factor2_code base)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) := by
  unfold exp_loop_marshal_result_to_factor2_code
  have hLd0 := ld_spec_gen_within .x5 .x2 sp tOld r0
    (0 : BitVec 12) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x5 evmSp r0 d0
    (32 : BitVec 12) (base + 4)
  have hLd1 := ld_spec_gen_within .x5 .x2 sp r0 r1
    (8 : BitVec 12) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x12 .x5 evmSp r1 d1
    (40 : BitVec 12) (base + 12)
  have hLd2 := ld_spec_gen_within .x5 .x2 sp r1 r2
    (16 : BitVec 12) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x12 .x5 evmSp r2 d2
    (48 : BitVec 12) (base + 20)
  have hLd3 := ld_spec_gen_within .x5 .x2 sp r2 r3
    (24 : BitVec 12) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x12 .x5 evmSp r3 d3
    (56 : BitVec 12) (base + 28)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3

theorem exp_loop_marshal_result_to_factor2_ofProg_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 base (base + 32)
      (CodeReq.ofProg base exp_loop_marshal_result_to_factor2)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) := by
  rw [← exp_loop_marshal_result_to_factor2_code_eq_ofProg]
  exact exp_loop_marshal_result_to_factor2_spec_within sp evmSp tOld
    r0 r1 r2 r3 d0 d1 d2 d3 base

-- ============================================================================
-- Section: exp_loop_marshal_a_to_factor2 (8 instructions, slice
-- evm-asm-bipgq — sub-slice of evm-asm-mtj3 / #92)
-- ============================================================================
--
-- `exp_loop_marshal_a_to_factor2` (defined in `Exp/Program.lean`) copies the
-- four limbs of the base value `a` from the EVM-stack window at
-- `x12 + -64..-40` (immediately below the squaring/cond-mul scratch) into the
-- LP64 MUL factor-2 slot at `x12 + 32..+56`, used by the cond-mul taken-branch
-- path where factor1 = result and factor2 = base `a`:
--
--     LD .x5 .x12 -64 ;; SD .x12 .x5 32 ;;
--     LD .x5 .x12 -56 ;; SD .x12 .x5 40 ;;
--     LD .x5 .x12 -48 ;; SD .x12 .x5 48 ;;
--     LD .x5 .x12 -40 ;; SD .x12 .x5 56
--
-- Sibling of `exp_loop_marshal_result_to_factor2_spec_within` (which sources
-- from `sp + 0..24`) — this variant sources from the EVM-stack base `a` slot
-- so the per-iteration `factor2` is the base, not the running accumulator.

def exp_loop_marshal_a_to_factor2_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x5 .x12 (-64))).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x5 32)).union
      ((CodeReq.singleton (base + 8) (.LD .x5 .x12 (-56))).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x5 40)).union
          ((CodeReq.singleton (base + 16) (.LD .x5 .x12 (-48))).union
            ((CodeReq.singleton (base + 20) (.SD .x12 .x5 48)).union
              ((CodeReq.singleton (base + 24) (.LD .x5 .x12 (-40))).union
                (CodeReq.singleton (base + 28) (.SD .x12 .x5 56))))))))

theorem exp_loop_marshal_a_to_factor2_code_eq_ofProg (base : Word) :
    exp_loop_marshal_a_to_factor2_code base =
      CodeReq.ofProg base exp_loop_marshal_a_to_factor2 := by
  unfold exp_loop_marshal_a_to_factor2_code
    exp_loop_marshal_a_to_factor2 LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x12 (-64), .SD .x12 .x5 32, .LD .x5 .x12 (-56),
     .SD .x12 .x5 40, .LD .x5 .x12 (-48), .SD .x12 .x5 48,
     .LD .x5 .x12 (-40), .SD .x12 .x5 56]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem exp_loop_marshal_a_to_factor2_spec_within
    (evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 base (base + 32)
      (exp_loop_marshal_a_to_factor2_code base)
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) := by
  unfold exp_loop_marshal_a_to_factor2_code
  have hLd0 := ld_spec_gen_within .x5 .x12 evmSp tOld a0
    ((-64) : BitVec 12) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x5 evmSp a0 d0
    (32 : BitVec 12) (base + 4)
  have hLd1 := ld_spec_gen_within .x5 .x12 evmSp a0 a1
    ((-56) : BitVec 12) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x12 .x5 evmSp a1 d1
    (40 : BitVec 12) (base + 12)
  have hLd2 := ld_spec_gen_within .x5 .x12 evmSp a1 a2
    ((-48) : BitVec 12) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x12 .x5 evmSp a2 d2
    (48 : BitVec 12) (base + 20)
  have hLd3 := ld_spec_gen_within .x5 .x12 evmSp a2 a3
    ((-40) : BitVec 12) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x12 .x5 evmSp a3 d3
    (56 : BitVec 12) (base + 28)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3

theorem exp_loop_marshal_a_to_factor2_ofProg_spec_within
    (evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 base (base + 32)
      (CodeReq.ofProg base exp_loop_marshal_a_to_factor2)
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) := by
  rw [← exp_loop_marshal_a_to_factor2_code_eq_ofProg]
  exact exp_loop_marshal_a_to_factor2_spec_within evmSp tOld
    a0 a1 a2 a3 d0 d1 d2 d3 base

-- ============================================================================
-- Section: exp_loop_un_marshal_and_restore (9 instructions, slice
-- evm-asm-9vqmo — sub-slice of evm-asm-mtj3 / #92)
-- ============================================================================
--
-- `exp_loop_un_marshal_and_restore` (defined in `Exp/Program.lean`) copies the
-- four limbs of MUL's output from the LP64 result slot at `x12 + 0..+24`
-- back into the local scratch frame at `sp + 0..+24`, then issues
-- `ADDI .x12 .x12 (-32)` to undo the pre-call `ADDI .x12 .x12 32` pointer
-- advance:
--
--     LD .x5 .x12 0  ;; SD .x2 .x5 0  ;;
--     LD .x5 .x12 8  ;; SD .x2 .x5 8  ;;
--     LD .x5 .x12 16 ;; SD .x2 .x5 16 ;;
--     LD .x5 .x12 24 ;; SD .x2 .x5 24 ;;
--     ADDI .x12 .x12 (-32)
--
-- Mirrors `exp_epilogue_spec_within` with the LD/SD source/destination
-- registers swapped (factor1/result marshalling reads x2→x12; un_marshal
-- reads x12→x2) and a negative pointer-restore offset.

def exp_loop_un_marshal_and_restore_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x5 .x12 0)).union
    ((CodeReq.singleton (base + 4) (.SD .x2 .x5 0)).union
      ((CodeReq.singleton (base + 8) (.LD .x5 .x12 8)).union
        ((CodeReq.singleton (base + 12) (.SD .x2 .x5 8)).union
          ((CodeReq.singleton (base + 16) (.LD .x5 .x12 16)).union
            ((CodeReq.singleton (base + 20) (.SD .x2 .x5 16)).union
              ((CodeReq.singleton (base + 24) (.LD .x5 .x12 24)).union
                ((CodeReq.singleton (base + 28) (.SD .x2 .x5 24)).union
                  (CodeReq.singleton (base + 32) (.ADDI .x12 .x12 (-32))))))))))

theorem exp_loop_un_marshal_and_restore_code_eq_ofProg (base : Word) :
    exp_loop_un_marshal_and_restore_code base =
      CodeReq.ofProg base exp_loop_un_marshal_and_restore := by
  unfold exp_loop_un_marshal_and_restore_code
    exp_loop_un_marshal_and_restore LD SD ADDI single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x12 0, .SD .x2 .x5 0, .LD .x5 .x12 8,
     .SD .x2 .x5 8, .LD .x5 .x12 16, .SD .x2 .x5 16,
     .LD .x5 .x12 24, .SD .x2 .x5 24, .ADDI .x12 .x12 (-32)]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem exp_loop_un_marshal_and_restore_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 base (base + 36)
      (exp_loop_un_marshal_and_restore_code base)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) := by
  unfold exp_loop_un_marshal_and_restore_code
  have hLd0 := ld_spec_gen_within .x5 .x12 evmSp tOld d0
    (0 : BitVec 12) base (by decide)
  have hSd0 := generic_sd_spec_within .x2 .x5 sp d0 r0
    (0 : BitVec 12) (base + 4)
  have hLd1 := ld_spec_gen_within .x5 .x12 evmSp d0 d1
    (8 : BitVec 12) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x2 .x5 sp d1 r1
    (8 : BitVec 12) (base + 12)
  have hLd2 := ld_spec_gen_within .x5 .x12 evmSp d1 d2
    (16 : BitVec 12) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x2 .x5 sp d2 r2
    (16 : BitVec 12) (base + 20)
  have hLd3 := ld_spec_gen_within .x5 .x12 evmSp d2 d3
    (24 : BitVec 12) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x2 .x5 sp d3 r3
    (24 : BitVec 12) (base + 28)
  have hAddSp := addi_spec_gen_same_within .x12 evmSp
    (-32 : BitVec 12) (base + 32) (by decide)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3 hAddSp

theorem exp_loop_un_marshal_and_restore_ofProg_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 base (base + 36)
      (CodeReq.ofProg base exp_loop_un_marshal_and_restore)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) := by
  rw [← exp_loop_un_marshal_and_restore_code_eq_ofProg]
  exact exp_loop_un_marshal_and_restore_spec_within sp evmSp tOld
    r0 r1 r2 r3 d0 d1 d2 d3 base

-- ============================================================================
-- exp_prologue_fixed code + spec (10 instructions: GH #92, evm-asm-w5mk x5-fix)
--
-- Proves that exp_prologue_fixed correctly initializes:
--   x9 = 256, x5 = 1 (temp), accumulator = {1,0,0,0} at sp+0..24,
--   x6 = 64 (per-limb counter), x16 = evmSp+48 (next limb pointer),
--   x19 = exponent.getLimbN 3 (MSB exponent cursor loaded from evmSp+56)
-- ============================================================================

def exp_prologue_fixed_code (base : Word) : CodeReq :=
  CodeReq.ofProg base exp_prologue_fixed

/-- Spec for `exp_prologue_fixed` against `CodeReq.ofProg base exp_prologue_fixed`.
    Requires the exponent's MSB limb (at `evmSp + 56`) to be accessible.
    The exponent cursor `x19` is loaded from `evmSp + 56 = exponentWord.getLimbN 3`
    and the limb pointer `x16` is initialized to `evmSp + 48` for the next reload.
    Refs: GH #92, bead evm-asm-w5mk. -/
theorem exp_prologue_fixed_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 : Word)
    (base : Word) :
    cpsTripleWithin 10 base (base + 40) (exp_prologue_fixed_code base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
       (.x19 ↦ᵣ expLimb3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) := by
  have hCounter := addi_spec_gen_within .x9 .x0 cOld (0:Word) (256:BitVec 12) base (by decide)
  have hOne := addi_spec_gen_within .x5 .x0 tOld (0:Word) (1:BitVec 12) (base+4) (by decide)
  have hSd0 := generic_sd_spec_within .x2 .x5 sp (0+signExtend12 1) m0 (0:BitVec 12) (base+8)
  have hSd1 := generic_sd_spec_within .x2 .x0 sp (0:Word) m1 (8:BitVec 12) (base+12)
  have hSd2 := generic_sd_spec_within .x2 .x0 sp (0:Word) m2 (16:BitVec 12) (base+16)
  have hSd3 := generic_sd_spec_within .x2 .x0 sp (0:Word) m3 (24:BitVec 12) (base+20)
  have hC6 := addi_spec_gen_within .x20 .x0 c6Old (0:Word) (64:BitVec 12) (base+24) (by decide)
  have hLP := addi_spec_gen_within .x16 .x12 c16Old evmSp (56:BitVec 12) (base+28) (by decide)
  have hLd := ld_spec_gen_within .x19 .x16 (evmSp+signExtend12 56) c19Old expLimb3 (0:BitVec 12) (base+32) (by decide)
  have hAP := addi_spec_gen_same_within .x16 (evmSp+signExtend12 56) (-8:BitVec 12) (base+36) (by decide)
  runBlock hCounter hOne hSd0 hSd1 hSd2 hSd3 hC6 hLP hLd hAP

-- ============================================================================
-- exp_msb_bit_test_block_fixed specs (GH #92, bead evm-asm-w5mk)
-- Two paths: skip (BNE taken, x6≠0) and reload (BNE not-taken, x6=0).
-- These specs are proved below; the code abbreviation is defined first.
-- ============================================================================

abbrev exp_msb_bit_test_block_fixed_code (base : Word) : CodeReq :=
  CodeReq.ofProg base exp_msb_bit_test_block_fixed

/-- Lift the fixed bit-test block's leading `SRLI` to the full block code. -/
theorem exp_msb_bit_test_block_fixed_srli_spec_within (c10 e : Word) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (exp_msb_bit_test_block_fixed_code base)
      ((.x19 ↦ᵣ e) ** (.x10 ↦ᵣ c10))
      ((.x19 ↦ᵣ e) ** (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat))) := by
  have h := srli_spec_gen_within .x10 .x19 c10 e 63 base (by decide)
  have hext := cpsTripleWithin_extend_code (h := h)
    (hmono := CodeReq.ofProg_mono_sub base base exp_msb_bit_test_block_fixed
      [.SRLI .x10 .x19 63] 0 (by bv_omega) (by decide) (by decide) (by decide))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hext

/-- Lift the fixed bit-test block's `SLLI` step to the full block code. -/
theorem exp_msb_bit_test_block_fixed_slli_spec_within (e : Word) (base : Word) :
    cpsTripleWithin 1 (base + 4) (base + 8)
      (exp_msb_bit_test_block_fixed_code base)
      (.x19 ↦ᵣ e)
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) := by
  have h := slli_spec_gen_same_within .x19 e 1 (base + 4) (by decide)
  have hext := cpsTripleWithin_extend_code (h := h)
    (hmono := CodeReq.ofProg_mono_sub base (base + 4) exp_msb_bit_test_block_fixed
      [.SLLI .x19 .x19 1] 1 (by bv_omega) (by decide) (by decide) (by decide))
  have haddr : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [haddr] at hext; exact hext

/-- Lift the fixed bit-test block's counter decrement to the full block code. -/
theorem exp_msb_bit_test_block_fixed_decrement_spec_within (c6 : Word) (base : Word) :
    cpsTripleWithin 1 (base + 8) (base + 12)
      (exp_msb_bit_test_block_fixed_code base)
      (.x20 ↦ᵣ c6)
      (.x20 ↦ᵣ (c6 + signExtend12 (-1 : BitVec 12))) := by
  have h := addi_spec_gen_same_within .x20 c6 (-1 : BitVec 12) (base + 8) (by decide)
  have hext := cpsTripleWithin_extend_code (h := h)
    (hmono := CodeReq.ofProg_mono_sub base (base + 8) exp_msb_bit_test_block_fixed
      [.ADDI .x20 .x20 (-1)] 2 (by bv_omega) (by decide) (by decide) (by decide))
  have haddr : (base + 8 : Word) + 4 = base + 12 := by bv_addr
  rw [haddr] at hext; exact hext

-- ============================================================================
-- exp_msb_bit_test_block_fixed two-path specs (GH #92, bead evm-asm-w5mk)
-- ============================================================================

/-- BNE spec (instruction 4 of fixed block) lifted to the full fixed code.
    Used by both skip and reload path proofs. -/
theorem exp_msb_bit_test_block_fixed_bne_spec_within (c6_new : Word) (base : Word) :
    cpsBranchWithin 1 (base + 12)
      (exp_msb_bit_test_block_fixed_code base)
      ((.x20 ↦ᵣ c6_new) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 12 + signExtend13 (16 : BitVec 13))
        ((.x20 ↦ᵣ c6_new) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c6_new ≠ 0⌝)
      (base + 12 + 4)
        ((.x20 ↦ᵣ c6_new) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c6_new = 0⌝) :=
  cpsBranchWithin_extend_code
    (h := bne_spec_gen_within .x20 .x0 (16 : BitVec 13) c6_new (0 : Word) (base + 12))
    (hmono := CodeReq.ofProg_mono_sub base (base + 12) exp_msb_bit_test_block_fixed
      [.BNE .x20 .x0 16] 3 (by bv_omega) (by decide) (by decide) (by decide))

/-- Skip path of the fixed bit-test block: BNE is taken because x6-1 ≠ 0.
    Exits at base+28 after 4 instructions. x19 shifted, x10 = MSB of old x19,
    x6 decremented. -/
theorem exp_msb_bit_test_block_fixed_skip_spec_within
    (e c6 c10 : Word) (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin 4 base (base + 28)
      (exp_msb_bit_test_block_fixed_code base)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ c10) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ c6 + signExtend12 (-1 : BitVec 12)) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6 + signExtend12 (-1 : BitVec 12) ≠ 0⌝ **
       (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat))) := by
  let c6_new := c6 + signExtend12 (-1 : BitVec 12)
  -- Compose 3 instructions with explicit intermediate types
  have hSR_f := cpsTripleWithin_frameR ((.x20 ↦ᵣ c6) ** (.x0 ↦ᵣ (0:Word)))
    (by pcFree) (exp_msb_bit_test_block_fixed_srli_spec_within c10 e base)
  have hSL_f := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x20 ↦ᵣ c6) ** (.x0 ↦ᵣ (0:Word)))
    (by pcFree) (exp_msb_bit_test_block_fixed_slli_spec_within e base)
  have hAD_f := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ (e <<< (1:BitVec 6).toNat)) ** (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) **
     (.x0 ↦ᵣ (0:Word)))
    (by pcFree) (exp_msb_bit_test_block_fixed_decrement_spec_within c6 base)
  have h3_seq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hSR_f hSL_f) hAD_f
  have h3 : cpsTripleWithin 3 base (base + 12) (exp_msb_bit_test_block_fixed_code base)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ c10) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x19 ↦ᵣ (e <<< (1:BitVec 6).toNat)) ** (.x20 ↦ᵣ c6_new) **
       (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x0 ↦ᵣ (0:Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h3_seq
  have hBNE_f := cpsBranchWithin_frameR
    ((.x19 ↦ᵣ (e <<< (1:BitVec 6).toNat)) ** (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)))
    (by pcFree) (exp_msb_bit_test_block_fixed_bne_spec_within c6_new base)
  have hBNE_t := cpsBranchWithin_takenPath hBNE_f (fun _ hQf => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, heq⟩⟩⟩, _⟩ := hQf
    exact hc6 heq)
  have haddr : (base + 12 : Word) + signExtend13 (16 : BitVec 13) = base + 28 := by
    simp only [EvmAsm.Rv64.signExtend13, BitVec.reduceSignExtend]; bv_omega
  rw [haddr] at hBNE_t
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      simp only [show c6_new = c6 + signExtend12 (-1:BitVec 12) from rfl] at hp
      xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h3 hBNE_t)

/-- Reload path of the fixed bit-test block: BNE not taken because x6-1 = 0.
    All 7 instructions. Exits at base+28. Loads next exponent limb. -/
theorem exp_msb_bit_test_block_fixed_reload_spec_within
    (e c6 c10 ptr nextLimb : Word) (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    cpsTripleWithin 7 base (base + 28)
      (exp_msb_bit_test_block_fixed_code base)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ c10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      ((.x19 ↦ᵣ nextLimb) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
       (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) := by
  let c6_new := c6 + signExtend12 (-1 : BitVec 12)
  have hSR_f := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ c6) ** (.x0 ↦ᵣ (0:Word)) ** (.x16 ↦ᵣ ptr) **
     ((ptr + signExtend12 0) ↦ₘ nextLimb))
    (by pcFree) (exp_msb_bit_test_block_fixed_srli_spec_within c10 e base)
  have hSL_f := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x20 ↦ᵣ c6) ** (.x0 ↦ᵣ (0:Word)) **
     (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 0) ↦ₘ nextLimb))
    (by pcFree) (exp_msb_bit_test_block_fixed_slli_spec_within e base)
  have hAD_f := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ (e <<< (1:BitVec 6).toNat)) ** (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) **
     (.x0 ↦ᵣ (0:Word)) ** (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 0) ↦ₘ nextLimb))
    (by pcFree) (exp_msb_bit_test_block_fixed_decrement_spec_within c6 base)
  have h3_seq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hSR_f hSL_f) hAD_f
  have h3 : cpsTripleWithin 3 base (base+12) (exp_msb_bit_test_block_fixed_code base)
      ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ c10) ** (.x0 ↦ᵣ (0:Word)) **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 0) ↦ₘ nextLimb))
      ((.x19 ↦ᵣ (e <<< (1:BitVec 6).toNat)) ** (.x20 ↦ᵣ c6_new) **
       (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x0 ↦ᵣ (0:Word)) **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 0) ↦ₘ nextLimb)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h3_seq
  have hBNE_f := cpsBranchWithin_frameR
    ((.x19 ↦ᵣ (e <<< (1:BitVec 6).toNat)) ** (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) **
     (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0:BitVec 12)) ↦ₘ nextLimb))
    (by pcFree) (exp_msb_bit_test_block_fixed_bne_spec_within c6_new base)
  have hBNE_nt := cpsBranchWithin_ntakenPath hBNE_f (fun _ hQt => by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hne⟩⟩⟩, _⟩ := hQt
    exact hne hc6)
  have haddr16 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [haddr16] at hBNE_nt
  -- LD x19 x16 0 at base+16
  have hLd := cpsTripleWithin_extend_code
    (h := ld_spec_gen_within .x19 .x16 ptr (e <<< (1:BitVec 6).toNat)
      nextLimb (0:BitVec 12) (base+16) (by decide))
    (hmono := CodeReq.ofProg_mono_sub base (base+16) exp_msb_bit_test_block_fixed
      [.LD .x19 .x16 0] 4 (by bv_omega) (by decide) (by decide) (by decide))
  -- ADDI x16 x16 -8 at base+20
  have hAP := cpsTripleWithin_extend_code
    (h := addi_spec_gen_same_within .x16 ptr (-8:BitVec 12) (base+20) (by decide))
    (hmono := CodeReq.ofProg_mono_sub base (base+20) exp_msb_bit_test_block_fixed
      [.ADDI .x16 .x16 (-8)] 5 (by bv_omega) (by decide) (by decide) (by decide))
  -- ADDI x6 x0 64 at base+24
  have hC6 := cpsTripleWithin_extend_code
    (h := addi_spec_gen_within .x20 .x0 c6_new (0:Word) (64:BitVec 12) (base+24) (by decide))
    (hmono := CodeReq.ofProg_mono_sub base (base+24) exp_msb_bit_test_block_fixed
      [.ADDI .x20 .x0 64] 6 (by bv_omega) (by decide) (by decide) (by decide))
  have e1 : (base+16:Word)+4=base+20 := by bv_addr
  have e2 : (base+20:Word)+4=base+24 := by bv_addr
  have e3 : (base+24:Word)+4=base+28 := by bv_addr
  rw [e1] at hLd; rw [e2] at hAP; rw [e3] at hC6
  -- Compose last 3 instructions
  -- Build h3b with explicit type to force elaboration
  have hLd_f := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x20 ↦ᵣ c6_new) ** (.x0 ↦ᵣ (0:Word)) **
     ⌜c6_new = 0⌝)
    (by pcFree) hLd
  have hAP_f := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ nextLimb) ** (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x20 ↦ᵣ c6_new) **
     (.x0 ↦ᵣ (0:Word)) ** ⌜c6_new = 0⌝ ** ((ptr + signExtend12 0) ↦ₘ nextLimb))
    (by pcFree) hAP
  have hC6_f := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ nextLimb) ** (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) **
     ⌜c6_new = 0⌝ ** (.x16 ↦ᵣ (ptr + signExtend12 (-8:BitVec 12))) **
     ((ptr + signExtend12 0) ↦ₘ nextLimb))
    (by pcFree) hC6
  have h3b_seq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hLd_f hAP_f) hC6_f
  have h3b : cpsTripleWithin 3 (base+16) (base+28) (exp_msb_bit_test_block_fixed_code base)
      ((.x19 ↦ᵣ (e <<< (1:BitVec 6).toNat)) ** (.x20 ↦ᵣ c6_new) **
       (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x0 ↦ᵣ (0:Word)) **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 0) ↦ₘ nextLimb) ** ⌜c6_new = 0⌝)
      ((.x19 ↦ᵣ nextLimb) **
       (.x20 ↦ᵣ ((0:Word) + signExtend12 (64:BitVec 12))) **
       (.x10 ↦ᵣ (e >>> (63:BitVec 6).toNat)) ** (.x0 ↦ᵣ (0:Word)) **
       ⌜c6_new = 0⌝ **
       (.x16 ↦ᵣ (ptr + signExtend12 (-8:BitVec 12))) **
       ((ptr + signExtend12 0) ↦ₘ nextLimb)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) h3b_seq
  exact cpsTripleWithin_mono_nSteps (by norm_num)
    (cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by
        simp only [show c6_new = c6 + signExtend12 (-1:BitVec 12) from rfl] at hp
        xperm_hyp hp)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
          h3 hBNE_nt)
        h3b))

end EvmAsm.Evm64
