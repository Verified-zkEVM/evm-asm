/-
  EvmAsm.Evm64.AddMod.Compose.ZeroBranch

  Composition for the explicit ADDMOD `N = 0` phase-2 branch: the
  OR-fold/BEQ test followed by the zero-store path. This is a foundation
  slice for the total ADDMOD runtime, which must branch on zero modulus
  before choosing between low-sum and carry-aware reduction.
-/

import EvmAsm.Evm64.AddMod.LimbSpec

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Code bundle for the ADDMOD phase-2 `N = 0` test followed by the zero-store
    path. The branch offset is fixed to `4`, so the taken BEQ target at
    `base + 28` is the zero-store block at `base + 32`. -/
abbrev evm_addmod_phase2_n_zero_test_zero_path_code (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
     evm_addmod_phase2_zero_path)

theorem evm_addmod_phase2_n_zero_test_zero_path_code_eq_ofProg
    (base : Word) :
    evm_addmod_phase2_n_zero_test_zero_path_code base =
      CodeReq.ofProg base
        (evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
         evm_addmod_phase2_zero_path) := rfl

/-- On the ADDMOD `N = 0` branch, the phase-2 zero-test dispatches to the
    zero-store path and writes the result word as zero. The fall-through branch
    is eliminated by the explicit `n0 ||| n1 ||| n2 ||| n3 = 0` hypothesis. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word)
    (base : Word)
    (hZero : n0 ||| n1 ||| n2 ||| n3 = (0 : Word)) :
    cpsTripleWithin (8 + 4) base (base + 48)
      (evm_addmod_phase2_n_zero_test_zero_path_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (n0 ||| n1 ||| n2 ||| n3)) **
       (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  let orAll := n0 ||| n1 ||| n2 ||| n3
  have hTestRaw :=
    evm_addmod_phase2_n_zero_test_spec_within sp v5Old v6Old n0 n1 n2 n3
      base (4 : BitVec 13)
  have hTarget : (base + 28 : Word) + signExtend13 (4 : BitVec 13) = base + 32 := by
    bv_addr
  rw [hTarget] at hTestRaw
  have hTest :
      cpsBranchWithin 8 base (evm_addmod_phase2_n_zero_test_zero_path_code base)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
        (base + 32)
          ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
           ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
           ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
           ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
           ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
           ⌜orAll = 0⌝)
        (base + 32)
          ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
           ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
           ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
           ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
           ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
           ⌜orAll ≠ 0⌝) :=
    cpsBranchWithin_extend_code (h := hTestRaw) (hmono := by
      unfold evm_addmod_phase2_n_zero_test_zero_path_code
      exact CodeReq.ofProg_mono_append_left base
        (evm_addmod_phase2_n_zero_test (4 : BitVec 13))
        evm_addmod_phase2_zero_path)
  have hTakenRaw := cpsBranchWithin_takenPath hTest (fun hp hQf => by
    have hQfNorm :
        (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
          ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) **
          ⌜orAll ≠ 0⌝) hp := by
      xperm_hyp hQf
    exact ((sepConj_pure_right hp).mp hQfNorm).2 hZero)
  have hTaken :
      cpsTripleWithin 8 base (base + 32)
        (evm_addmod_phase2_n_zero_test_zero_path_code base)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) :=
    cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        have hpNorm :
            (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
              ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
              ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
              ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
              ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3)) **
              ⌜orAll = 0⌝) h := by
          xperm_hyp hp
        exact ((sepConj_pure_right h).mp hpNorm).1)
      hTakenRaw
  have hZeroPathRaw :=
    evm_addmod_phase2_zero_path_spec_within sp n0 n1 n2 n3 (base + 32)
  rw [show (base + 32 : Word) + 16 = base + 48 by bv_addr] at hZeroPathRaw
  have hZeroPath :
      cpsTripleWithin 4 (base + 32) (base + 48)
        (evm_addmod_phase2_n_zero_test_zero_path_code base)
        ((.x12 ↦ᵣ sp) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
        ((.x12 ↦ᵣ sp) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) :=
    cpsTripleWithin_extend_code (h := hZeroPathRaw) (hmono := by
      rw [evm_addmod_phase2_zero_path_code_eq_ofProg] at *
      unfold evm_addmod_phase2_n_zero_test_zero_path_code
      convert CodeReq.ofProg_mono_append_right base
        (evm_addmod_phase2_n_zero_test (4 : BitVec 13))
        evm_addmod_phase2_zero_path (by
          rw [List.length_append, evm_addmod_phase2_n_zero_test_length,
            evm_addmod_phase2_zero_path_length]
          norm_num) using 1)
  have hZeroPathFramed := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0))
    (by pcFree) hZeroPath
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hTaken hZeroPathFramed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hSeq

/-- `ofProg` surface for the ADDMOD `N = 0` phase-2 test plus zero-store path. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_ofProg_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word)
    (base : Word)
    (hZero : n0 ||| n1 ||| n2 ||| n3 = (0 : Word)) :
    cpsTripleWithin (8 + 4) base (base + 48)
      (CodeReq.ofProg base
        (evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
         evm_addmod_phase2_zero_path))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (n0 ||| n1 ||| n2 ||| n3)) **
       (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  rw [← evm_addmod_phase2_n_zero_test_zero_path_code_eq_ofProg]
  exact evm_addmod_phase2_n_zero_test_zero_path_spec_within
    sp v5Old v6Old n0 n1 n2 n3 base hZero

/-- Code bundle for the ADDMOD phase-2 zero-modulus test, zero-store path, and
    shared epilogue. The epilogue starts at base + 48. -/
abbrev evm_addmod_phase2_n_zero_test_zero_path_epilogue_code (base : Word) : CodeReq :=
  CodeReq.ofProg base
    ((evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
      evm_addmod_phase2_zero_path) ;;
     evm_addmod_epilogue)

theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_code_eq_ofProg
    (base : Word) :
    evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base =
      CodeReq.ofProg base
        ((evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
          evm_addmod_phase2_zero_path) ;;
         evm_addmod_epilogue) := rfl

/-- ADDMOD phase-2 zero-modulus path through the shared epilogue. This
    composes the explicit zero-modulus branch with the final stack-pointer
    advance. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word)
    (base : Word)
    (hZero : n0 ||| n1 ||| n2 ||| n3 = (0 : Word)) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (n0 ||| n1 ||| n2 ||| n3)) **
       (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  let prefixProg := evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
    evm_addmod_phase2_zero_path
  let orAll := n0 ||| n1 ||| n2 ||| n3
  have hPrefixRaw :=
    evm_addmod_phase2_n_zero_test_zero_path_ofProg_spec_within
      sp v5Old v6Old n0 n1 n2 n3 base hZero
  have hPrefix :
      cpsTripleWithin (8 + 4) base (base + 48)
        (evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) **
         (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) :=
    cpsTripleWithin_extend_code (h := hPrefixRaw) (hmono := by
      unfold evm_addmod_phase2_n_zero_test_zero_path_epilogue_code
      exact CodeReq.ofProg_mono_append_left base prefixProg evm_addmod_epilogue)
  have hEpilogueRaw := evm_addmod_epilogue_spec_within sp (base + 48)
  rw [show (base + 48 : Word) + 4 = base + 52 by bv_addr] at hEpilogueRaw
  have hEpilogue :
      cpsTripleWithin 1 (base + 48) (base + 52)
        (evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base)
        (.x12 ↦ᵣ sp)
        (.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) :=
    cpsTripleWithin_extend_code (h := hEpilogueRaw) (hmono := by
      unfold evm_addmod_phase2_n_zero_test_zero_path_epilogue_code
      convert CodeReq.ofProg_mono_append_right base prefixProg evm_addmod_epilogue (by
        unfold prefixProg evm_addmod_phase2_n_zero_test evm_addmod_phase2_zero_path
          evm_addmod_epilogue LD OR' SD ADDI single seq
        decide) using 1)
  have hEpilogueFramed := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word)))
    (by pcFree) hEpilogue
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPrefix hEpilogueFramed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hSeq

/-- Word-shaped surface for the ADDMOD zero-modulus phase-2 path through
    epilogue. This folds the four zero result limbs into the stack word slot
    consumed by the later stack-level ADDMOD composition. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_word_spec_within
    (sp v5Old v6Old base : Word) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmWordIs (sp + 32) (0 : EvmWord))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmWordIs (sp + 32) (0 : EvmWord)) := by
  have hRaw :=
    evm_addmod_phase2_n_zero_test_zero_path_epilogue_spec_within
      sp v5Old v6Old 0 0 0 0 base (by simp)
  have hOrZero : ((0 : Word) ||| 0 ||| 0 ||| 0) = (0 : Word) := by decide
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp (0 : EvmWord) 0 0 0 0
        (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
        (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3)] at hp
      simp only [signExtend12_32, signExtend12_40, signExtend12_48,
        signExtend12_56] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp (0 : EvmWord) 0 0 0 0
        (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
        (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3)]
      simp only [signExtend12_32, signExtend12_40, signExtend12_48,
        signExtend12_56] at hp ⊢
      rw [hOrZero] at hp
      xperm_hyp hp)
    hRaw

/-- Stack-tail surface for the ADDMOD zero-modulus phase-2 path through
    epilogue. The explicit zero branch preserves the caller tail and leaves the
    final live stack headed by the zero result word. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_stack_tail_spec_within
    (sp v5Old v6Old base : Word) (rest : List EvmWord) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest)) := by
  have hCore :=
    evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_word_spec_within
      sp v5Old v6Old base
  have hFramed := cpsTripleWithin_frameR (evmStackIs (sp + 64) rest)
    (by pcFree) hCore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_cons] at hp
      simp only [show (sp + 32 + 32 : Word) = sp + 64 from by bv_omega] at hp
      xperm_hyp hp)
    (fun _ hp => by
      rw [evmStackIs_cons]
      simp only [show (sp + 32 + 32 : Word) = sp + 64 from by bv_omega]
      xperm_hyp hp)
    hFramed

/-- The ADDMOD zero-test OR-fold of a modulus word is zero iff the modulus
    word itself is zero. -/
theorem addmod_orAll_limbs_eq_zero_iff (N : EvmWord) :
    (N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 =
      (0 : Word)) ↔ N = 0 := by
  rw [EvmWord.eq_zero_iff_limbs, EvmWord.getLimb_as_getLimbN_0,
      EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
      EvmWord.getLimb_as_getLimbN_3]
  constructor
  · intro h
    have h12 := EvmAsm.Evm64.EvmWord.bv_or_eq_zero
      (show (N.getLimbN 0 ||| N.getLimbN 1) |||
          (N.getLimbN 2 ||| N.getLimbN 3) = 0 by
        rw [← h]; ac_rfl)
    exact ⟨(EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.1).1,
           (EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.1).2,
           (EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.2).1,
           (EvmAsm.Evm64.EvmWord.bv_or_eq_zero h12.2).2⟩
  · rintro ⟨h0, h1, h2, h3⟩
    rw [h0, h1, h2, h3]
    simp

/-- The ADDMOD zero-test OR-fold of a modulus word is nonzero iff the modulus
    word itself is nonzero. -/
theorem addmod_orAll_limbs_ne_zero_iff (N : EvmWord) :
    (N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 ≠
      (0 : Word)) ↔ N ≠ 0 := by
  constructor
  · intro h_or hN
    exact h_or ((addmod_orAll_limbs_eq_zero_iff N).mpr hN)
  · intro hN h_or
    exact hN ((addmod_orAll_limbs_eq_zero_iff N).mp h_or)

/-- Stack-tail surface for the ADDMOD zero-modulus phase-2 path through
    epilogue with the zero modulus supplied as a hypothesis. This is the form
    branch composition usually has after extracting the zero-test guard. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_n_zero_stack_tail_spec_within
    (sp v5Old v6Old base : Word) (N : EvmWord) (rest : List EvmWord)
    (hN : N = (0 : EvmWord)) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) (N :: rest))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest)) := by
  subst N
  exact evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_stack_tail_spec_within
    sp v5Old v6Old base rest

/-- Stack-tail surface for the ADDMOD zero-modulus phase-2 path through
    epilogue with the zero-test OR-fold supplied directly. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_or_zero_stack_tail_spec_within
    (sp v5Old v6Old base : Word) (N : EvmWord) (rest : List EvmWord)
    (hOr : N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 =
      (0 : Word)) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (evm_addmod_phase2_n_zero_test_zero_path_epilogue_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) (N :: rest))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest)) := by
  exact evm_addmod_phase2_n_zero_test_zero_path_epilogue_n_zero_stack_tail_spec_within
    sp v5Old v6Old base N rest ((addmod_orAll_limbs_eq_zero_iff N).mp hOr)

/-- `ofProg` surface for the word-shaped ADDMOD zero-modulus phase-2 path
    through epilogue. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_word_ofProg_spec_within
    (sp v5Old v6Old base : Word) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (CodeReq.ofProg base
        ((evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
          evm_addmod_phase2_zero_path) ;;
         evm_addmod_epilogue))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmWordIs (sp + 32) (0 : EvmWord))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmWordIs (sp + 32) (0 : EvmWord)) := by
  rw [← evm_addmod_phase2_n_zero_test_zero_path_epilogue_code_eq_ofProg]
  exact evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_word_spec_within
    sp v5Old v6Old base

/-- `ofProg` surface for the stack-tail ADDMOD zero-modulus phase-2 path
    through epilogue. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_stack_tail_ofProg_spec_within
    (sp v5Old v6Old base : Word) (rest : List EvmWord) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (CodeReq.ofProg base
        ((evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
          evm_addmod_phase2_zero_path) ;;
         evm_addmod_epilogue))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest)) := by
  rw [← evm_addmod_phase2_n_zero_test_zero_path_epilogue_code_eq_ofProg]
  exact evm_addmod_phase2_n_zero_test_zero_path_epilogue_zero_stack_tail_spec_within
    sp v5Old v6Old base rest

/-- `ofProg` surface for the hypothesis-driven stack-tail ADDMOD
    zero-modulus phase-2 path through epilogue. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_n_zero_stack_tail_ofProg_spec_within
    (sp v5Old v6Old base : Word) (N : EvmWord) (rest : List EvmWord)
    (hN : N = (0 : EvmWord)) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (CodeReq.ofProg base
        ((evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
          evm_addmod_phase2_zero_path) ;;
         evm_addmod_epilogue))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) (N :: rest))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest)) := by
  rw [← evm_addmod_phase2_n_zero_test_zero_path_epilogue_code_eq_ofProg]
  exact evm_addmod_phase2_n_zero_test_zero_path_epilogue_n_zero_stack_tail_spec_within
    sp v5Old v6Old base N rest hN

/-- `ofProg` surface for the stack-tail ADDMOD zero-modulus phase-2 path
    through epilogue with the zero-test OR-fold supplied directly. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_or_zero_stack_tail_ofProg_spec_within
    (sp v5Old v6Old base : Word) (N : EvmWord) (rest : List EvmWord)
    (hOr : N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 =
      (0 : Word)) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (CodeReq.ofProg base
        ((evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
          evm_addmod_phase2_zero_path) ;;
         evm_addmod_epilogue))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) (N :: rest))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ 0) **
       evmStackIs (sp + 32) ((0 : EvmWord) :: rest)) := by
  rw [← evm_addmod_phase2_n_zero_test_zero_path_epilogue_code_eq_ofProg]
  exact evm_addmod_phase2_n_zero_test_zero_path_epilogue_or_zero_stack_tail_spec_within
    sp v5Old v6Old base N rest hOr

/-- ofProg surface for the ADDMOD zero-modulus phase-2 path through epilogue. -/
theorem evm_addmod_phase2_n_zero_test_zero_path_epilogue_ofProg_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word)
    (base : Word)
    (hZero : n0 ||| n1 ||| n2 ||| n3 = (0 : Word)) :
    cpsTripleWithin (8 + 4 + 1) base (base + 52)
      (CodeReq.ofProg base
        ((evm_addmod_phase2_n_zero_test (4 : BitVec 13) ;;
          evm_addmod_phase2_zero_path) ;;
         evm_addmod_epilogue))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ (sp + signExtend12 (32 : BitVec 12))) **
       (.x6 ↦ᵣ (n0 ||| n1 ||| n2 ||| n3)) **
       (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ (0 : Word))) := by
  rw [← evm_addmod_phase2_n_zero_test_zero_path_epilogue_code_eq_ofProg]
  exact evm_addmod_phase2_n_zero_test_zero_path_epilogue_spec_within
    sp v5Old v6Old n0 n1 n2 n3 base hZero

end EvmAsm.Evm64.AddMod.Compose
