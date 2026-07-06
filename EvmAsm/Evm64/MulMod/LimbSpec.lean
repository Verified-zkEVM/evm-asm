/-
  EvmAsm.Evm64.MulMod.LimbSpec

  Per-block / per-limb cpsTriple specs for MULMOD sub-blocks (operand
  widening, callable-divide JAL, result narrowing).

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Per
  `OPCODE_TEMPLATE.md`, each sub-block will get exactly one cpsTriple
  lemma once the Compose layer pins the layout.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Evm64.MulMod.ProductAlgebra
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev evm_mulmod_reduce_zero_path_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.SD .x12 .x0 64)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x0 72)).union
      ((CodeReq.singleton (base + 8) (.SD .x12 .x0 80)).union
        (CodeReq.singleton (base + 12) (.SD .x12 .x0 88))))

theorem evm_mulmod_reduce_zero_path_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce_zero_path_code base =
      CodeReq.ofProg base evm_mulmod_reduce_zero_path := by
  unfold evm_mulmod_reduce_zero_path_code evm_mulmod_reduce_zero_path SD single seq
  change _ = CodeReq.ofProg base
    [.SD .x12 .x0 64, .SD .x12 .x0 72, .SD .x12 .x0 80, .SD .x12 .x0 88]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  bv_addr

theorem evm_mulmod_reduce_zero_path_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    let code := evm_mulmod_reduce_zero_path_code base
    cpsTripleWithin 4 base (base + 16) code
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (0 : Word))) := by
  unfold evm_mulmod_reduce_zero_path_code
  have hSd0 := generic_sd_x0_spec_within .x12 sp m0
    (64 : BitVec 12) base
  have hSd1 := generic_sd_x0_spec_within .x12 sp m1
    (72 : BitVec 12) (base + 4)
  have hSd2 := generic_sd_x0_spec_within .x12 sp m2
    (80 : BitVec 12) (base + 8)
  have hSd3 := generic_sd_x0_spec_within .x12 sp m3
    (88 : BitVec 12) (base + 12)
  runBlock hSd0 hSd1 hSd2 hSd3

theorem evm_mulmod_reduce_zero_path_ofProg_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base evm_mulmod_reduce_zero_path)
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (0 : Word))) := by
  rw [← evm_mulmod_reduce_zero_path_code_eq_ofProg]
  exact evm_mulmod_reduce_zero_path_spec_within sp m0 m1 m2 m3 base

abbrev evm_mulmod_epilogue_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_epilogue

theorem evm_mulmod_epilogue_spec_within
    (sp : Word) (base : Word) :
    let code := evm_mulmod_epilogue_code base
    cpsTripleWithin 1 base (base + 4) code
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base evm_mulmod_epilogue) _ _
  rw [show CodeReq.ofProg base evm_mulmod_epilogue =
      CodeReq.singleton base (.ADDI .x12 .x12 64) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_same_within .x12 sp 64 base (by nofun)

abbrev evm_mulmod_zero_path_skip_nonzero_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_zero_path_skip_nonzero

theorem evm_mulmod_zero_path_skip_nonzero_spec_within
    (base : Word) :
    let code := evm_mulmod_zero_path_skip_nonzero_code base
    cpsTripleWithin 1 base (base + signExtend21 (2108 : BitVec 21)) code
      empAssertion
      empAssertion := by
  show cpsTripleWithin 1 base (base + signExtend21 (2108 : BitVec 21))
    (CodeReq.ofProg base evm_mulmod_zero_path_skip_nonzero) _ _
  rw [show CodeReq.ofProg base evm_mulmod_zero_path_skip_nonzero =
      CodeReq.singleton base (.JAL .x0 2108) from CodeReq.ofProg_singleton]
  exact jal_x0_spec_gen_within 2108 base

abbrev evm_mulmod_nonzero_or_zero_prefix_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_nonzero_or_zero_prefix

theorem evm_mulmod_nonzero_or_zero_prefix_code_eq_unfold
    (base : Word) :
    evm_mulmod_nonzero_or_zero_prefix_code base =
      (CodeReq.singleton base (.LD .x6 .x12 64)).union
        ((CodeReq.singleton (base + 4) (.LD .x5 .x12 72)).union
          ((CodeReq.singleton (base + 8) (.OR .x6 .x6 .x5)).union
            ((CodeReq.singleton (base + 12) (.LD .x5 .x12 80)).union
              ((CodeReq.singleton (base + 16) (.OR .x6 .x6 .x5)).union
                ((CodeReq.singleton (base + 20) (.LD .x5 .x12 88)).union
                  ((CodeReq.singleton (base + 24) (.OR .x6 .x6 .x5)).union
                    (CodeReq.singleton (base + 28)
                      (.BNE .x6 .x0 (28 : BitVec 13))))))))) := by
  unfold evm_mulmod_nonzero_or_zero_prefix_code evm_mulmod_nonzero_or_zero_prefix
    LD OR' BNE single seq
  change CodeReq.ofProg base
    [.LD .x6 .x12 64, .LD .x5 .x12 72, .OR .x6 .x6 .x5,
     .LD .x5 .x12 80, .OR .x6 .x6 .x5,
     .LD .x5 .x12 88, .OR .x6 .x6 .x5,
     .BNE .x6 .x0 (28 : BitVec 13)] = _
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem evm_mulmod_nonzero_or_zero_prefix_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word) (base : Word) :
    let orAll := n0 ||| n1 ||| n2 ||| n3
    let code := evm_mulmod_nonzero_or_zero_prefix_code base
    cpsBranchWithin 8 base code
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3))
      ((base + 28) + signExtend13 (28 : BitVec 13))
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll ≠ 0⌝)
      (base + 32)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll = 0⌝) := by
  intro orAll code
  have hOrFold :
      cpsTripleWithin 7 base (base + 28) code
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3))
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3)) := by
    have L0 := ld_spec_gen_within .x6 .x12 sp v6Old n0
      (64 : BitVec 12) base (by nofun)
    have L1 := ld_spec_gen_within .x5 .x12 sp v5Old n1
      (72 : BitVec 12) (base + 4) (by nofun)
    have O1 := or_spec_gen_rd_eq_rs1_within .x6 .x5 n0 n1
      (base + 8) (by nofun)
    have L2 := ld_spec_gen_within .x5 .x12 sp n1 n2
      (80 : BitVec 12) (base + 12) (by nofun)
    have O2 := or_spec_gen_rd_eq_rs1_within .x6 .x5 (n0 ||| n1) n2
      (base + 16) (by nofun)
    have L3 := ld_spec_gen_within .x5 .x12 sp n2 n3
      (88 : BitVec 12) (base + 20) (by nofun)
    have O3 := or_spec_gen_rd_eq_rs1_within .x6 .x5 (n0 ||| n1 ||| n2) n3
      (base + 24) (by nofun)
    runBlock L0 L1 O1 L2 O2 L3 O3
  have hBneRaw := bne_spec_gen_within .x6 .x0 (28 : BitVec 13) orAll (0 : Word)
    (base + 28)
  have hBneExt : cpsBranchWithin 1 (base + 28) code
      ((.x6 ↦ᵣ orAll) ** (.x0 ↦ᵣ 0))
      ((base + 28) + signExtend13 (28 : BitVec 13))
        ((.x6 ↦ᵣ orAll) ** (.x0 ↦ᵣ 0) ** ⌜orAll ≠ (0 : Word)⌝)
      ((base + 28) + 4)
        ((.x6 ↦ᵣ orAll) ** (.x0 ↦ᵣ 0) ** ⌜orAll = (0 : Word)⌝) :=
    cpsBranchWithin_extend_code (h := hBneRaw) (hmono := by
      intro a i hsing
      show code a = some i
      rw [show code = evm_mulmod_nonzero_or_zero_prefix_code base from rfl,
        evm_mulmod_nonzero_or_zero_prefix_code_eq_unfold]
      simp only [CodeReq.singleton] at hsing
      split at hsing
      · rename_i ha
        rw [beq_iff_eq] at ha
        subst ha
        simp only [CodeReq.union, CodeReq.singleton]
        have h1 : (base + 28 : Word) ≠ base := by bv_omega
        have h2 : (base + 28 : Word) ≠ base + 4 := by bv_omega
        have h3 : (base + 28 : Word) ≠ base + 8 := by bv_omega
        have h4 : (base + 28 : Word) ≠ base + 12 := by bv_omega
        have h5 : (base + 28 : Word) ≠ base + 16 := by bv_omega
        have h6 : (base + 28 : Word) ≠ base + 20 := by bv_omega
        have h7 : (base + 28 : Word) ≠ base + 24 := by bv_omega
        simp at hsing ⊢
        exact hsing
      · simp at hsing)
  have hBneFramed := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) **
     ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3))
    (by pcFree) hBneExt
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hOrFold hBneFramed
  have h_addr_eq : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  rw [h_addr_eq] at composed
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- evm_mulmod_product_zero
-- ============================================================================

abbrev evm_mulmod_product_zero_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_product_zero

/-- Folded postcondition for `evm_mulmod_product_zero`.

    The block preserves the three input stack words `[a, b, N]` at `sp+0..88`
    and clears the eight-limb product window at `sp+96..152`. -/
@[irreducible]
def evmMulModProductZeroPost (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
  ((sp + 56) ↦ₘ b3) **
  ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
  ((sp + 88) ↦ₘ n3) **
  ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ (0 : Word))

theorem evmMulModProductZeroPost_unfold (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word) :
    evmMulModProductZeroPost sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 =
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
       ((sp + 56) ↦ₘ b3) **
       ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
       ((sp + 88) ↦ₘ n3) **
       ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ (0 : Word))) := by
  delta evmMulModProductZeroPost; rfl

/-- Zero the eight-limb MULMOD product window while preserving the input stack
    cells. -/
theorem evm_mulmod_product_zero_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 8 base (base + 32) (evm_mulmod_product_zero_code base)
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
       ((sp + 56) ↦ₘ b3) **
       ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
       ((sp + 88) ↦ₘ n3) **
       ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ p0) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ p1) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      (evmMulModProductZeroPost sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3) := by
  simp only [evmMulModProductZeroPost_unfold]
  have I0 := sd_x0_spec_gen_within .x12 sp p0 3936 base
  have I1 := sd_x0_spec_gen_within .x12 sp p1 3944 (base + 4)
  have I2 := sd_x0_spec_gen_within .x12 sp p2 3952 (base + 8)
  have I3 := sd_x0_spec_gen_within .x12 sp p3 3960 (base + 12)
  have I4 := sd_x0_spec_gen_within .x12 sp p4 3968 (base + 16)
  have I5 := sd_x0_spec_gen_within .x12 sp p5 3976 (base + 20)
  have I6 := sd_x0_spec_gen_within .x12 sp p6 3984 (base + 24)
  have I7 := sd_x0_spec_gen_within .x12 sp p7 3992 (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

-- ============================================================================
-- evm_mulmod_product_layout
-- ============================================================================

abbrev evm_mulmod_product_layout_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_product_layout

/-- Folded precondition for `evm_mulmod_product_layout`.

    The layout preserves the three input stack words `[a, b, n]` and may
    overwrite the eight-limb product window at `sp+96..152`. -/
@[irreducible]
def evmMulModProductLayoutPre (sp : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
  ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
  ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
  ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
  ((sp + 64) ↦ₘ n.getLimbN 0) ** ((sp + 72) ↦ₘ n.getLimbN 1) **
  ((sp + 80) ↦ₘ n.getLimbN 2) ** ((sp + 88) ↦ₘ n.getLimbN 3) **
  ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ p0) **
  ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ p1) **
  ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
  ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
  ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
  ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
  ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
  ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)

/-- Folded public postcondition for `evm_mulmod_product_layout`.

    The first four product-window limbs are the low 256 bits of `a * b`; the
    last four are the high 256 bits of the full 512-bit product. -/
@[irreducible]
def evmMulModProductLayoutPost (sp : Word) (a b n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
  ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
  ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
  ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
  ((sp + 64) ↦ₘ n.getLimbN 0) ** ((sp + 72) ↦ₘ n.getLimbN 1) **
  ((sp + 80) ↦ₘ n.getLimbN 2) ** ((sp + 88) ↦ₘ n.getLimbN 3) **
  ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ (a * b).getLimbN 0) **
  ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ (a * b).getLimbN 1) **
  ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ (a * b).getLimbN 2) **
  ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ (a * b).getLimbN 3) **
  ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 0) **
  ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 1) **
  ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 2) **
  ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 3)

theorem evmMulModProductLayoutPre_unfold (sp : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word) :
    evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 =
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
       ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
       ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
       ((sp + 64) ↦ₘ n.getLimbN 0) ** ((sp + 72) ↦ₘ n.getLimbN 1) **
       ((sp + 80) ↦ₘ n.getLimbN 2) ** ((sp + 88) ↦ₘ n.getLimbN 3) **
       ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ p0) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ p1) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)) := by
  delta evmMulModProductLayoutPre; rfl

theorem evmMulModProductLayoutPost_unfold (sp : Word) (a b n : EvmWord) :
    evmMulModProductLayoutPost sp a b n =
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
       ((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
       ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
       ((sp + 64) ↦ₘ n.getLimbN 0) ** ((sp + 72) ↦ₘ n.getLimbN 1) **
       ((sp + 80) ↦ₘ n.getLimbN 2) ** ((sp + 88) ↦ₘ n.getLimbN 3) **
       ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ (a * b).getLimbN 0) **
       ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ (a * b).getLimbN 1) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ (a * b).getLimbN 2) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ (a * b).getLimbN 3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 0) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 1) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 2) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 3)) := by
  delta evmMulModProductLayoutPost; rfl

-- ============================================================================
-- evm_mulmod_product_propagate_carry
-- ============================================================================

abbrev evm_mulmod_product_propagate_carry_code (base : Word) (offsets : List (BitVec 12)) :
    CodeReq :=
  CodeReq.ofProg base (evm_mulmod_product_propagate_carry offsets)

/-- One product-window carry propagation step: add incoming carry to a limb,
    store the updated limb, and leave the overflow carry in `x10`. -/
def mulModCarryStepValue (limb carry : Word) : Word :=
  limb + carry

/-- Carry-out from `mulModCarryStepValue`. -/
def mulModCarryStepCarry (limb carry : Word) : Word :=
  if BitVec.ult (limb + carry) carry then (1 : Word) else 0


-- ============================================================================
-- evm_mulmod_product_add_partial effect helpers
-- ============================================================================

/-- Low 64 bits of the selected 64x64 partial product. -/
def mulModAddPartialLoProduct (a b : Word) : Word :=
  a * b

/-- High 64 bits of the selected 64x64 partial product. -/
def mulModAddPartialHiProduct (a b : Word) : Word :=
  rv64_mulhu a b

/-- Updated low product-window limb after adding the low partial product. -/
def mulModAddPartialLoValue (lo a b : Word) : Word :=
  lo + mulModAddPartialLoProduct a b

/-- Carry from the low-limb partial-product addition. -/
def mulModAddPartialLoCarry (lo a b : Word) : Word :=
  if BitVec.ult (mulModAddPartialLoValue lo a b) (mulModAddPartialLoProduct a b) then
    (1 : Word)
  else
    0

/-- High-limb value after adding only the high partial product. -/
def mulModAddPartialHiBaseValue (hi a b : Word) : Word :=
  hi + mulModAddPartialHiProduct a b

/-- Carry from adding only the high partial product into the high limb. -/
def mulModAddPartialHiBaseCarry (hi a b : Word) : Word :=
  if BitVec.ult (mulModAddPartialHiBaseValue hi a b) (mulModAddPartialHiProduct a b) then
    (1 : Word)
  else
    0

/-- Final high-limb value after adding the low-limb carry. -/
def mulModAddPartialHiValue (hi lo a b : Word) : Word :=
  mulModAddPartialHiBaseValue hi a b + mulModAddPartialLoCarry lo a b

/-- Carry from adding the low-limb carry into the high limb. -/
def mulModAddPartialHiCarryFromLo (hi lo a b : Word) : Word :=
  if BitVec.ult (mulModAddPartialHiValue hi lo a b) (mulModAddPartialLoCarry lo a b) then
    (1 : Word)
  else
    0

/-- Carry that must be propagated past `hiOff` after one partial product. -/
def mulModAddPartialHiCarry (hi lo a b : Word) : Word :=
  mulModAddPartialHiBaseCarry hi a b ||| mulModAddPartialHiCarryFromLo hi lo a b

/-- Folded precondition fragment for the core add-partial block before its
    carry-tail call. It names the two selected input limbs and the two product
    limbs directly modified by the core block. -/
@[irreducible]
def evmMulModAddPartialCorePre (sp : Word)
    (aOff bOff loOff hiOff : BitVec 12) (a b lo hi : Word) : Assertion :=
  (.x12 ↦ᵣ sp) **
  ((sp + signExtend12 aOff) ↦ₘ a) **
  ((sp + signExtend12 bOff) ↦ₘ b) **
  ((sp + signExtend12 loOff) ↦ₘ lo) **
  ((sp + signExtend12 hiOff) ↦ₘ hi)

/-- Folded postcondition fragment after the core add-partial block has updated
    `loOff` and `hiOff`, before any carry-tail propagation. -/
@[irreducible]
def evmMulModAddPartialCorePost (sp : Word)
    (aOff bOff loOff hiOff : BitVec 12) (a b lo hi : Word) : Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ a) **
  (.x6 ↦ᵣ b) **
  (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
  (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
  (.x9 ↦ᵣ hi) **
  (.x10 ↦ᵣ mulModAddPartialHiCarry hi lo a b) **
  (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
  (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
  (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
  ((sp + signExtend12 aOff) ↦ₘ a) **
  ((sp + signExtend12 bOff) ↦ₘ b) **
  ((sp + signExtend12 loOff) ↦ₘ mulModAddPartialLoValue lo a b) **
  ((sp + signExtend12 hiOff) ↦ₘ mulModAddPartialHiValue hi lo a b)

@[irreducible]
def evmMulModAddPartialCoreFullPre (sp : Word)
    (aOff bOff loOff hiOff : BitVec 12) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    Assertion :=
  (.x12 ↦ᵣ sp) **
  (.x5 ↦ᵣ x5Old) **
  (.x6 ↦ᵣ x6Old) **
  (.x7 ↦ᵣ x7Old) **
  (.x8 ↦ᵣ x8Old) **
  (.x9 ↦ᵣ x9Old) **
  (.x10 ↦ᵣ x10Old) **
  (.x11 ↦ᵣ x11Old) **
  (.x13 ↦ᵣ x13Old) **
  (.x14 ↦ᵣ x14Old) **
  ((sp + signExtend12 aOff) ↦ₘ a) **
  ((sp + signExtend12 bOff) ↦ₘ b) **
  ((sp + signExtend12 loOff) ↦ₘ lo) **
  ((sp + signExtend12 hiOff) ↦ₘ hi)

abbrev evm_mulmod_product_add_partial_core_finish_code (base : Word)
    (aOff bOff loOff hiOff : BitVec 12) : CodeReq :=
  CodeReq.ofProg base
    (LD .x5 .x12 aOff ;;
     LD .x6 .x12 bOff ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 loOff ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 loOff ;;
     LD .x9 .x12 hiOff ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 hiOff)

/-- Core `evm_mulmod_product_add_partial` block through the high-limb store,
    leaving the merged carry ready for the carry-tail suffix. -/
theorem evm_mulmod_product_add_partial_core_finish_spec_within
    (sp base : Word) (aOff bOff loOff hiOff : BitVec 12)
    (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 base (base + 60)
      (evm_mulmod_product_add_partial_core_finish_code base aOff bOff loOff hiOff)
      (evmMulModAddPartialCoreFullPre sp aOff bOff loOff hiOff a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp aOff bOff loOff hiOff a b lo hi) := by
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct
  unfold mulModAddPartialLoProduct
  have I0 := ld_spec_gen_within .x5 .x12 sp x5Old a aOff base (by nofun)
  have I1 := ld_spec_gen_within .x6 .x12 sp x6Old b bOff (base + 4) (by nofun)
  have I2 := mul_spec_gen_within .x7 .x5 .x6 x7Old a b (base + 8) (by nofun)
  have I3 := mulhu_spec_gen_within .x8 .x5 .x6 x8Old a b (base + 12) (by nofun)
  have I4 := ld_spec_gen_within .x9 .x12 sp x9Old lo loOff (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x7 lo (a * b) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_within .x10 .x9 .x7 x10Old (lo + a * b) (a * b)
    (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (lo + a * b) lo loOff (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (lo + a * b) hi hiOff (base + 32) (by nofun)
  have I9 := add_spec_gen_within .x11 .x9 .x8 hi (rv64_mulhu a b) x11Old
    (base + 36) (by nofun)
  have I10 := sltu_spec_gen_within .x13 .x11 .x8 x13Old (hi + rv64_mulhu a b)
    (rv64_mulhu a b) (base + 40) (by nofun)
  have I11 := add_spec_gen_rd_eq_rs1_within .x11 .x10 (hi + rv64_mulhu a b)
    (if BitVec.ult (lo + a * b) (a * b) then 1 else 0) (base + 44) (by nofun)
  have I12 := sltu_spec_gen_within .x14 .x11 .x10 x14Old
    ((hi + rv64_mulhu a b) + if BitVec.ult (lo + a * b) (a * b) then 1 else 0)
    (if BitVec.ult (lo + a * b) (a * b) then 1 else 0) (base + 48) (by nofun)
  have I13 := or_spec_gen_within .x10 .x13 .x14
    (if BitVec.ult (lo + a * b) (a * b) then 1 else 0)
    (if BitVec.ult (hi + rv64_mulhu a b) (rv64_mulhu a b) then 1 else 0)
    (if BitVec.ult
      ((hi + rv64_mulhu a b) + if BitVec.ult (lo + a * b) (a * b) then 1 else 0)
      (if BitVec.ult (lo + a * b) (a * b) then 1 else 0) then 1 else 0)
    (base + 52) (by nofun)
  have I14 := sd_spec_gen_within .x12 .x11 sp
    ((hi + rv64_mulhu a b) + if BitVec.ult (lo + a * b) (a * b) then 1 else 0)
    hi hiOff (base + 56)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14

/-- Final product partial with no carry-tail suffix. This is the last
    `evm_mulmod_product_add_partial` call in the 4x4 schoolbook product layout. -/
theorem evm_mulmod_product_add_partial_144_152_nil_spec_within
    (sp base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 base (base + 60)
      (CodeReq.ofProg base
        (evm_mulmod_product_add_partial
          (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) []))
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi) := by
  change cpsTripleWithin 15 base (base + 60)
      (evm_mulmod_product_add_partial_core_finish_code base
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12))
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi)
  exact evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old

abbrev evm_mulmod_product_add_partial_finish_code (base : Word) (hiOff : BitVec 12) : CodeReq :=
  CodeReq.ofProg base (OR' .x10 .x13 .x14 ;; SD .x12 .x11 hiOff)

/-- Combined suffix for `evm_mulmod_product_add_partial`: merge the two
    high-limb carry flags, then store the already-computed high-limb value. -/
theorem evm_mulmod_product_add_partial_finish_spec_within (sp base : Word)
    (hiOff : BitVec 12) (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 base (base + 8)
      (evm_mulmod_product_add_partial_finish_code base hiOff)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) ** ((sp + signExtend12 hiOff) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) ** ((sp + signExtend12 hiOff) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) := by
  have I0 := or_spec_gen_within .x10 .x13 .x14 loCarry hiBaseCarry hiCarryFromLo
    (base + 0) (by nofun)
  have I1 := sd_spec_gen_within .x12 .x11 sp hiVal hiOld hiOff (base + 4)
  runBlock I0 I1

/-- Empty carry propagation is a no-op. -/
theorem evm_mulmod_product_propagate_carry_nil_spec_within (base sp carry v9 : Word) :
    cpsTripleWithin 0 base base (evm_mulmod_product_propagate_carry_code base [])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9)) := by
  show cpsTripleWithin 0 base base CodeReq.empty
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9))
  exact cpsTripleWithin_refl (fun _ hp => hp)

/-- Single-limb carry propagation. This is the reusable step used to build the
    concrete carry-offset list specs for `evm_mulmod_product_add_partial`. -/
theorem evm_mulmod_product_propagate_carry_one_spec_within (sp base : Word)
    (off : BitVec 12) (carry limb v9 : Word) :
    cpsTripleWithin 4 base (base + 16)
      (evm_mulmod_product_propagate_carry_code base [off])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 off) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry limb carry) **
       (.x9 ↦ᵣ mulModCarryStepValue limb carry) **
       ((sp + signExtend12 off) ↦ₘ mulModCarryStepValue limb carry)) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 limb off base (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 limb carry (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (limb + carry) carry (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (limb + carry) limb off (base + 12)
  runBlock I0 I1 I2 I3

/-- Product-layout call `evm_mulmod_product_add_partial 24 48 136 144 [3992]`. -/
theorem evm_mulmod_product_add_partial_24_48_136_144_152_spec_within
    (sp base : Word) (a b lo hi p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 4) base (base + 60 + 16)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (24 : BitVec 12) (48 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3992]))
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (48 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModAddPartialHiCarry hi lo a b)) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModAddPartialHiCarry hi lo a b))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (24 : BitVec 12) (48 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_one_spec_within sp (base + 60)
    (3992 : BitVec 12) (mulModAddPartialHiCarry hi lo a b) p7 hi
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 16 56 136 144 [3992]`. -/
theorem evm_mulmod_product_add_partial_16_56_136_144_152_spec_within
    (sp base : Word) (a b lo hi p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 4) base (base + 60 + 16)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (16 : BitVec 12) (56 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3992]))
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (56 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModAddPartialHiCarry hi lo a b)) **
        (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7 (mulModAddPartialHiCarry hi lo a b))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (16 : BitVec 12) (56 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_one_spec_within sp (base + 60)
    (3992 : BitVec 12) (mulModAddPartialHiCarry hi lo a b) p7 hi
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)
    (by pcFree) core
  seqFrame coreF carry

-- ============================================================================
-- Concrete carry-propagation suffixes used by evm_mulmod_product_layout
-- ============================================================================

/-- Concrete carry propagation over product offsets 144, 152. -/
theorem evm_mulmod_product_propagate_carry_144_152_spec_within
    (sp base carry v9 p6 p7 : Word) :
    cpsTripleWithin 8 base (base + 32)
      (evm_mulmod_product_propagate_carry_code base [3984, 3992])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (carry))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (carry))) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (carry)) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (carry)))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p6 3984 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p6 + (carry)) p6 3984 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p6 + (carry)) p7 3992 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (carry)) (carry) then 1 else 0)) p7 3992 (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

/-- Concrete carry propagation over product offsets 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_136_144_152_spec_within
    (sp base carry v9 p5 p6 p7 : Word) :
    cpsTripleWithin 12 base (base + 48)
      (evm_mulmod_product_propagate_carry_code base [3976, 3984, 3992])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (carry)))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (carry)))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (carry)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (carry))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (carry))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p5 3976 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p5 + (carry)) p5 3976 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p5 + (carry)) p6 3984 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) p6 3984 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) p7 3992 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p5 + (carry)) (carry) then 1 else 0) then 1 else 0)) p7 3992 (base + 44)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11

/-- Concrete carry propagation over product offsets 128, 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_128_136_144_152_spec_within
    (sp base carry v9 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 16 base (base + 64)
      (evm_mulmod_product_propagate_carry_code base [3968, 3976, 3984, 3992])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry))))) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 (carry)) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (mulModCarryStepCarry p4 (carry))) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry)))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (carry)))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p4 3968 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p4 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p4 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p4 + (carry)) p4 3968 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p4 + (carry)) p5 3976 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) p5 3976 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) p6 3984 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) p6 3984 (base + 44)
  have I12 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) p7 3992 (base + 48) (by nofun)
  have I13 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 52) (by nofun)
  have I14 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 56) (by nofun)
  have I15 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p4 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p7 3992 (base + 60)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15

/-- Concrete carry propagation over product offsets 120, 128, 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_120_128_136_144_152_spec_within
    (sp base carry v9 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 20 base (base + 80)
      (evm_mulmod_product_propagate_carry_code base [3960, 3968, 3976, 3984, 3992])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry)))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry)))))) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModCarryStepValue p3 (carry)) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 (mulModCarryStepCarry p3 (carry))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry)))) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry))))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (carry))))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p3 3960 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p3 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p3 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p3 + (carry)) p3 3960 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p3 + (carry)) p4 3968 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p4 (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) p4 3968 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) p5 3976 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) p5 3976 (base + 44)
  have I12 := ld_spec_gen_within .x9 .x12 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) p6 3984 (base + 48) (by nofun)
  have I13 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 52) (by nofun)
  have I14 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 56) (by nofun)
  have I15 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p6 3984 (base + 60)
  have I16 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p7 3992 (base + 64) (by nofun)
  have I17 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 68) (by nofun)
  have I18 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 72) (by nofun)
  have I19 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p3 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p7 3992 (base + 76)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19

/-- Concrete carry propagation over product offsets 112, 120, 128, 136, 144, 152. -/
theorem evm_mulmod_product_propagate_carry_112_120_128_136_144_152_spec_within
    (sp base carry v9 p2 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 24 base (base + 96)
      (evm_mulmod_product_propagate_carry_code base [3952, 3960, 3968, 3976, 3984, 3992])
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry))))))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry))))))) **
       ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ mulModCarryStepValue p2 (carry)) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModCarryStepValue p3 (mulModCarryStepCarry p2 (carry))) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModCarryStepValue p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry)))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry))))) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry)))))) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 (mulModCarryStepCarry p4 (mulModCarryStepCarry p3 (mulModCarryStepCarry p2 (carry)))))))) := by
  unfold mulModCarryStepValue mulModCarryStepCarry
  have I0 := ld_spec_gen_within .x9 .x12 sp v9 p2 3952 (base + 0) (by nofun)
  have I1 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p2 (carry) (base + 4) (by nofun)
  have I2 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p2 + (carry)) (carry) (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x9 sp (p2 + (carry)) p2 3952 (base + 12)
  have I4 := ld_spec_gen_within .x9 .x12 sp (p2 + (carry)) p3 3960 (base + 16) (by nofun)
  have I5 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p3 (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) (base + 20) (by nofun)
  have I6 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x9 sp (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) p3 3960 (base + 28)
  have I8 := ld_spec_gen_within .x9 .x12 sp (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) p4 3968 (base + 32) (by nofun)
  have I9 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p4 (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 36) (by nofun)
  have I10 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) (base + 40) (by nofun)
  have I11 := sd_spec_gen_within .x12 .x9 sp (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) p4 3968 (base + 44)
  have I12 := ld_spec_gen_within .x9 .x12 sp (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) p5 3976 (base + 48) (by nofun)
  have I13 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p5 (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 52) (by nofun)
  have I14 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) (base + 56) (by nofun)
  have I15 := sd_spec_gen_within .x12 .x9 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p5 3976 (base + 60)
  have I16 := ld_spec_gen_within .x9 .x12 sp (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) p6 3984 (base + 64) (by nofun)
  have I17 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p6 (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 68) (by nofun)
  have I18 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 72) (by nofun)
  have I19 := sd_spec_gen_within .x12 .x9 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p6 3984 (base + 76)
  have I20 := ld_spec_gen_within .x9 .x12 sp (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p7 3992 (base + 80) (by nofun)
  have I21 := add_spec_gen_rd_eq_rs1_within .x9 .x10 p7 (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 84) (by nofun)
  have I22 := sltu_spec_gen_rd_eq_rs2_within .x10 .x9 (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) (base + 88) (by nofun)
  have I23 := sd_spec_gen_within .x12 .x9 sp (p7 + (if BitVec.ult (p6 + (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p5 + (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0)) (if BitVec.ult (p4 + (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0)) (if BitVec.ult (p3 + (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0)) (if BitVec.ult (p2 + (carry)) (carry) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0) then 1 else 0)) p7 3992 (base + 92)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I23



-- ============================================================================
-- Concrete add-partial calls with multi-limb carry suffixes
-- ============================================================================

/-- Product-layout call `evm_mulmod_product_add_partial 24 40 128 136 [3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_24_40_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 8) base (base + 60 + 32)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (24 : BitVec 12) (40 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (40 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7
            (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b)))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (24 : BitVec 12) (40 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
      ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 16 48 128 136 [3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_16_48_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 8) base (base + 60 + 32)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (16 : BitVec 12) (48 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (48 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7
            (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b)))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (16 : BitVec 12) (48 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
      ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 8 56 128 136 [3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_8_56_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 8) base (base + 60 + 32)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (8 : BitVec 12) (56 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (56 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7
            (mulModCarryStepCarry p6 (mulModAddPartialHiCarry hi lo a b)))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (8 : BitVec 12) (56 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
      ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 24 32 120 128 [3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_24_32_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 12) base (base + 60 + 48)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (24 : BitVec 12) (32 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (32 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7
            (mulModCarryStepCarry p6
              (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (24 : BitVec 12) (32 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
      ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
      ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 16 40 120 128 [3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_16_40_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 12) base (base + 60 + 48)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (16 : BitVec 12) (40 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (40 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7
            (mulModCarryStepCarry p6
              (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (16 : BitVec 12) (40 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
      ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
      ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 8 48 120 128 [3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_8_48_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 12) base (base + 60 + 48)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (8 : BitVec 12) (48 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (48 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7
            (mulModCarryStepCarry p6
              (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (8 : BitVec 12) (48 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
      ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
      ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
    (by pcFree) core
  seqFrame coreF carry

/-- Product-layout call `evm_mulmod_product_add_partial 0 56 120 128 [3976, 3984, 3992]`. -/
theorem evm_mulmod_product_add_partial_0_56_120_128_136_144_152_spec_within
    (sp base : Word) (a b lo hi p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (15 + 12) base (base + 60 + 48)
      ((evm_mulmod_product_add_partial_core_finish_code base
          (0 : BitVec 12) (56 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code (base + 60) [3976, 3984, 3992]))
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (56 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old **
       (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b)))) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p5 (mulModAddPartialHiCarry hi lo a b)) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p6
            (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
          mulModCarryStepValue p7
            (mulModCarryStepCarry p6
              (mulModCarryStepCarry p5 (mulModAddPartialHiCarry hi lo a b))))) **
       (.x5 ↦ᵣ a) **
       (.x6 ↦ᵣ b) **
       (.x7 ↦ᵣ mulModAddPartialLoProduct a b) **
       (.x8 ↦ᵣ mulModAddPartialHiProduct a b) **
       (.x11 ↦ᵣ mulModAddPartialHiValue hi lo a b) **
       (.x13 ↦ᵣ mulModAddPartialHiBaseCarry hi a b) **
       (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo hi lo a b) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ a) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ b) **
       ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ mulModAddPartialLoValue lo a b) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ mulModAddPartialHiValue hi lo a b)) := by
  have core := evm_mulmod_product_add_partial_core_finish_spec_within sp base
    (0 : BitVec 12) (56 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  have carry := evm_mulmod_product_propagate_carry_136_144_152_spec_within sp (base + 60)
    (mulModAddPartialHiCarry hi lo a b) hi p5 p6 p7
  unfold evmMulModAddPartialCoreFullPre evmMulModAddPartialCorePost at core
  unfold evmMulModAddPartialCoreFullPre
  unfold mulModCarryStepValue mulModCarryStepCarry at carry ⊢
  unfold mulModAddPartialHiCarry mulModAddPartialHiCarryFromLo at core carry ⊢
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseCarry at core carry ⊢
  unfold mulModAddPartialHiBaseValue mulModAddPartialLoCarry at core carry ⊢
  unfold mulModAddPartialLoValue mulModAddPartialHiProduct at core carry ⊢
  unfold mulModAddPartialLoProduct at core carry ⊢
  have coreF := cpsTripleWithin_frameR
    (((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
      ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
      ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
    (by pcFree) core
  seqFrame coreF carry

-- ============================================================================
-- evm_mulmod_reduce512_init
-- ============================================================================

abbrev evm_mulmod_reduce512_init_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_reduce512_init

/-- Initialize the 512-bit reduction accumulator: clear the four remainder
    limbs, point `x16` at the high product limb, and set the outer limb counter
    in `x18` to 8. -/
theorem evm_mulmod_reduce512_init_spec_within (sp base : Word)
    (v16Old v18Old r0 r1 r2 r3 : Word) :
    cpsTripleWithin 6 base (base + 24) (evm_mulmod_reduce512_init_code base)
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3))
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ (sp + signExtend12 (3992 : BitVec 12))) **
       (.x18 ↦ᵣ (signExtend12 (8 : BitVec 12))) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ (0 : Word))) := by
  have I0 := sd_x0_spec_gen_within .x12 sp r0 4064 base
  have I1 := sd_x0_spec_gen_within .x12 sp r1 4072 (base + 4)
  have I2 := sd_x0_spec_gen_within .x12 sp r2 4080 (base + 8)
  have I3 := sd_x0_spec_gen_within .x12 sp r3 4088 (base + 12)
  have I4 := addi_spec_gen_within .x16 .x12 v16Old sp 3992 (base + 16) (by nofun)
  have I5 := addi_x0_spec_gen_within .x18 v18Old 8 (base + 20) (by nofun)
  runBlock I0 I1 I2 I3 I4 I5


-- ============================================================================
-- evm_mulmod_reduce512_write_result
-- ============================================================================

abbrev evm_mulmod_reduce512_write_result_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_reduce512_write_result

/-- Copy the finalized 256-bit remainder from the reducer accumulator window
    into the EVM result slots. -/
theorem evm_mulmod_reduce512_write_result_spec_within (sp base : Word)
    (v5Old r0 r1 r2 r3 m0 m1 m2 m3 : Word) :
    cpsTripleWithin 8 base (base + 32) (evm_mulmod_reduce512_write_result_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5Old) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ r3)) := by
  have I0 := ld_spec_gen_within .x5 .x12 sp v5Old r0 4064 base (by nofun)
  have I1 := sd_spec_gen_within .x12 .x5 sp r0 m0 64 (base + 4)
  have I2 := ld_spec_gen_within .x5 .x12 sp r0 r1 4072 (base + 8) (by nofun)
  have I3 := sd_spec_gen_within .x12 .x5 sp r1 m1 72 (base + 12)
  have I4 := ld_spec_gen_within .x5 .x12 sp r1 r2 4080 (base + 16) (by nofun)
  have I5 := sd_spec_gen_within .x12 .x5 sp r2 m2 80 (base + 20)
  have I6 := ld_spec_gen_within .x5 .x12 sp r2 r3 4088 (base + 24) (by nofun)
  have I7 := sd_spec_gen_within .x12 .x5 sp r3 m3 88 (base + 28)
  runBlock I0 I1 I2 I3 I4 I5 I6 I7

end EvmAsm.Evm64
