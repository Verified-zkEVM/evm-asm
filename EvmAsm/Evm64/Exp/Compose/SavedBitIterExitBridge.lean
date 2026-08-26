/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterExitBridge

  Exit bridge theorems: from the final-iteration exit post-condition
  (`expTwoMulIterExitPost 0 ...`) plus an "exponent frame" atom
  (`evmWordIs (evmSp + signExtend12 (-32)) exponentWord`), prove
  `(expTwoMulLoopExitFullStackPreFrame ... ** leftover_regs) ps`.

  Architecture:
  - `expTwoMulIterExitPost` owns: x9, x0, x18, x2, x12, x5, x1,
    regOwn{x6,x7,x10,x11}, sp[0..24], LP64[0..24](memOwn),
    LP64[32..56], LP64[-64..-40](=evmSp_orig[0..24])
  - The exponent frame owns: LP64[-32..-8] (= evmSp_orig[32..56])
  - `expTwoMulLoopExitFullStackPreFrame` with `rest = [expResultWord w0..w3, squarW/rwW]`
    claims: x9, x0, x12, x2, x5, sp[0..24], LP64[-64..-40],
    LP64[-32..-8], LP64[0..24](=w0..w3), LP64[32..56]
  - Leftover (not in FullStackPreFrame): x18, x1, regOwn{x6,x7,x10,x11}

  The combined assertion (FullStackPreFrame ** leftover) covers ALL atoms
  in the hypothesis, making the proof a sep_perm repartitioning.

  Bead: evm-asm-w5mk.1.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

-- Address arithmetic: evmSp - 64 + N expressed as evmSp + M for concrete N
-- Used in goal normalization after rw [show evmSp - 64 = evmSp + 18446744073709551552]
private theorem addr_stack_neg64_add64 (_ : Word) :
    (18446744073709551552 : Word) + 64 = 0 := by decide
private theorem addr_stack_neg32_add32 (_ : Word) :
    (18446744073709551584 : Word) + 32 = 0 := by decide

theorem expTwoMulIterCondExitPost_to_FullStackPreFrame
    {bit sp evmSp base a0 a1 a2 a3 : Word} {rwW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterCondPost 0 bit sp evmSp base a0 a1 a2 a3 rwW ((0 : Word) = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
          (rwW.getLimbN 3)
          (rwW.getLimbN 0) (rwW.getLimbN 1) (rwW.getLimbN 2) (rwW.getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3, rwW]
          ((0 : Word) = 0) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x1 ↦ᵣ ((base + 152) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  rw [expTwoMulIterCondPost_unfold, expTwoMulIterCondRest_unfold,
      expTwoMulIterCondFrame_unfold] at h
  simp only [evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32,
             EvmAsm.Rv64.AddrNorm.word_add_zero] at h
  simp only [BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide] at h
  rw [pure_true_eq_emp] at h
  simp only [sepConj_emp_right'] at h
  -- Extract bit≠0
  have hbitne : bit ≠ 0 := by
    obtain ⟨_, _, _, _, h_A, _⟩ := h
    obtain ⟨_, _, _, _, _, h_cf⟩ := h_A
    obtain ⟨_, _, _, _, _, hpure⟩ := h_cf
    exact hpure.2
  rw [show (⌜bit ≠ 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hbitne⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  -- Navigate via obtain
  obtain ⟨ps_cond, ps_ef, hd_ef, hu_ef, h_cond, h_ef⟩ := h
  obtain ⟨ps_body, ps_x18, hd_x18, hu_x18, h_body, h_x18⟩ := h_cond
  obtain ⟨ps_x9x0, ps_cr, hd_cr, hu_cr, h_x9x0, h_cr⟩ := h_body
  obtain ⟨ps_x2, ps_r1, hd1, hu1, h_x2, h_r1⟩ := h_cr
  obtain ⟨ps_x12, ps_r2, hd2, hu2, h_x12, h_r2⟩ := h_r1
  obtain ⟨ps_x5, ps_r3, hd3, hu3, h_x5, h_r3⟩ := h_r2
  obtain ⟨ps_a0, ps_r4, hd4, hu4, h_a0, h_r4⟩ := h_r3
  obtain ⟨ps_a1, ps_r5, hd5, hu5, h_a1, h_r5⟩ := h_r4
  obtain ⟨ps_a2, ps_r6, hd6, hu6, h_a2, h_r6⟩ := h_r5
  obtain ⟨ps_a3, ps_r7, hd7, hu7, h_a3, h_r7⟩ := h_r6
  obtain ⟨ps_sp, ps_r8, hd8, hu8, h_sp, h_r8⟩ := h_r7
  obtain ⟨ps_e32, ps_r9, hd9, hu9, h_e32, h_r9⟩ := h_r8
  obtain ⟨ps_x6, ps_r10, hd10, hu10, h_x6, h_r10⟩ := h_r9
  obtain ⟨ps_x7, ps_r11, hd11, hu11, h_x7, h_r11⟩ := h_r10
  obtain ⟨ps_x10, ps_r12, hd12, hu12, h_x10, h_r12⟩ := h_r11
  obtain ⟨ps_x11, ps_r13, hd13, hu13, h_x11, h_r13⟩ := h_r12
  obtain ⟨w0, h_w0_chain⟩ := sepConj_choose_memOwn h_r13
  obtain ⟨ps_w0, ps_r14, hd_w0, hu_w0, h_w0, h_r14⟩ := h_w0_chain
  obtain ⟨w1, h_w1_chain⟩ := sepConj_choose_memOwn h_r14
  obtain ⟨ps_w1, ps_r15, hd_w1, hu_w1, h_w1, h_r15⟩ := h_w1_chain
  obtain ⟨w2, h_w2_chain⟩ := sepConj_choose_memOwn h_r15
  obtain ⟨ps_w2, ps_r16, hd_w2, hu_w2, h_w2, h_r16⟩ := h_w2_chain
  obtain ⟨w3, h_w3_chain⟩ := sepConj_choose_memOwn h_r16
  obtain ⟨ps_w3, ps_x1, hd_w3, hu_w3, h_w3, h_x1⟩ := h_w3_chain
  obtain ⟨ps_ex0, ps_ef1, hd_ex0, hu_ex0, h_ex0, h_ef1⟩ := h_ef
  obtain ⟨ps_ex1, ps_ef2, hd_ex1, hu_ex1, h_ex1, h_ef2⟩ := h_ef1
  obtain ⟨ps_ex2, ps_ex3, hd_ex23, hu_ex23, h_ex2, h_ex3⟩ := h_ef2
  refine ⟨w0, w1, w2, w3, ?_⟩
  rw [expTwoMulLoopExitFullStackPreFrame_unfold, expTwoMulLoopExitControl_unfold]
  rw [show (evmSp - 64 : Word) = evmSp + 18446744073709551552 from by bv_omega]
  simp only [evmWordIs, evmStackIs,
             signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
             signExtend12_64,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc,
             expResultWord_getLimbN_0, expResultWord_getLimbN_1,
             expResultWord_getLimbN_2, expResultWord_getLimbN_3,
             show (18446744073709551552:Word) + 8 = 18446744073709551560 from by decide,
             show (18446744073709551552:Word) + 16 = 18446744073709551568 from by decide,
             show (18446744073709551552:Word) + 24 = 18446744073709551576 from by decide,
             show (18446744073709551552:Word) + 32 = 18446744073709551584 from by decide,
             show (18446744073709551552:Word) + 64 = 0 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide,
             show (18446744073709551584:Word) + 32 = 0 from by decide,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide]
  rw [pure_true_eq_emp]
  simp only [sepConj_emp_right']
  -- h_full mirrors the ps decomposition tree:
  -- outer: (cond_atoms @ ps_cond) ** (exponent_atoms @ ps_ef)
  -- cond: ((body_atoms @ ps_body) ** (x18 @ ps_x18))
  -- body: (x9x0 @ ps_x9x0) ** (condRest chain @ ps_cr)
  have h_full :
      (((((Reg.x9 ↦ᵣ 0) ** Reg.x0 ↦ᵣ 0) **
         ((Reg.x2 ↦ᵣ sp) **
          (Reg.x12 ↦ᵣ evmSp) **
          (Reg.x5 ↦ᵣ rwW.getLimbN 3) **
          (evmSp + 18446744073709551552 ↦ₘ a0) **
          (evmSp + 18446744073709551560 ↦ₘ a1) **
          (evmSp + 18446744073709551568 ↦ₘ a2) **
          (evmSp + 18446744073709551576 ↦ₘ a3) **
          ((sp ↦ₘ rwW.getLimbN 0) ** (sp + 8 ↦ₘ rwW.getLimbN 1) **
           (sp + 16 ↦ₘ rwW.getLimbN 2) ** (sp + 24 ↦ₘ rwW.getLimbN 3)) **
          ((evmSp + 32 ↦ₘ rwW.getLimbN 0) ** (evmSp + 40 ↦ₘ rwW.getLimbN 1) **
           (evmSp + 48 ↦ₘ rwW.getLimbN 2) ** (evmSp + 56 ↦ₘ rwW.getLimbN 3)) **
          regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
          (evmSp ↦ₘ w0) ** (evmSp + 8 ↦ₘ w1) ** (evmSp + 16 ↦ₘ w2) **
          (evmSp + 24 ↦ₘ w3) ** (Reg.x1 ↦ᵣ (base + (152 + 68))))) **
        (Reg.x18 ↦ᵣ bit)) **
       ((evmSp + 18446744073709551584 ↦ₘ exponentWord.getLimbN 0) **
        (evmSp + 18446744073709551592 ↦ₘ exponentWord.getLimbN 1) **
        (evmSp + 18446744073709551600 ↦ₘ exponentWord.getLimbN 2) **
        (evmSp + 18446744073709551608 ↦ₘ exponentWord.getLimbN 3))) ps := by
    refine ⟨ps_cond, ps_ef, hd_ef, hu_ef, ?_, ?_⟩
    · refine ⟨ps_body, ps_x18, hd_x18, hu_x18, ?_, h_x18⟩
      refine ⟨ps_x9x0, ps_cr, hd_cr, hu_cr, h_x9x0, ?_⟩
      refine ⟨ps_x2, ps_r1, hd1, hu1, h_x2, ?_⟩
      refine ⟨ps_x12, ps_r2, hd2, hu2, h_x12, ?_⟩
      refine ⟨ps_x5, ps_r3, hd3, hu3, h_x5, ?_⟩
      refine ⟨ps_a0, ps_r4, hd4, hu4, h_a0, ?_⟩
      refine ⟨ps_a1, ps_r5, hd5, hu5, h_a1, ?_⟩
      refine ⟨ps_a2, ps_r6, hd6, hu6, h_a2, ?_⟩
      refine ⟨ps_a3, ps_r7, hd7, hu7, h_a3, ?_⟩
      refine ⟨ps_sp, ps_r8, hd8, hu8, h_sp, ?_⟩
      refine ⟨ps_e32, ps_r9, hd9, hu9, h_e32, ?_⟩
      refine ⟨ps_x6, ps_r10, hd10, hu10, h_x6, ?_⟩
      refine ⟨ps_x7, ps_r11, hd11, hu11, h_x7, ?_⟩
      refine ⟨ps_x10, ps_r12, hd12, hu12, h_x10, ?_⟩
      refine ⟨ps_x11, ps_r13, hd13, hu13, h_x11, ?_⟩
      refine ⟨ps_w0, _, hd_w0, hu_w0, h_w0, ?_⟩
      refine ⟨ps_w1, _, hd_w1, hu_w1, h_w1, ?_⟩
      refine ⟨ps_w2, _, hd_w2, hu_w2, h_w2, ?_⟩
      exact ⟨ps_w3, ps_x1, hd_w3, hu_w3, h_w3, h_x1⟩
    · refine ⟨ps_ex0, _, hd_ex0, hu_ex0, h_ex0, ?_⟩
      refine ⟨ps_ex1, _, hd_ex1, hu_ex1, h_ex1, ?_⟩
      exact ⟨ps_ex2, ps_ex3, hd_ex23, hu_ex23, h_ex2, h_ex3⟩
  sep_perm h_full

theorem expTwoMulIterSkipExitPost_to_FullStackPreFrame
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squarW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterSkipPost 0 bit sp evmSp base a0 a1 a2 a3 squarW ((0 : Word) = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
          (squarW.getLimbN 3)
          (squarW.getLimbN 0) (squarW.getLimbN 1) (squarW.getLimbN 2) (squarW.getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3, squarW]
          ((0 : Word) = 0) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x1 ↦ᵣ ((base + 44) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  rw [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
      expTwoMulIterBaseFrame_unfold] at h
  simp only [evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32,
             EvmAsm.Rv64.AddrNorm.word_add_zero] at h
  simp only [BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide] at h
  rw [pure_true_eq_emp] at h
  simp only [sepConj_emp_right'] at h
  -- Extract bit=0 from SkipRest
  -- Structure: (((x9**x0) ** (x18 ** ⌜bit=0⌝ ** rest)) ** BaseFrame) ** exponent_frame
  have hbit : bit = 0 := by
    obtain ⟨_, _, _, _, h_A, _⟩ := h
    obtain ⟨_, _, _, _, h_inner, _⟩ := h_A
    obtain ⟨_, _, _, _, _, h_sr⟩ := h_inner
    obtain ⟨_, _, _, _, _, h_b0rest⟩ := h_sr
    exact ((sepConj_pure_left _).mp h_b0rest).1
  rw [show (⌜bit = 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hbit⟩⟩] at h
  simp only [sepConj_emp_left'] at h
  -- Navigate
  obtain ⟨ps_skip, ps_ef, hd_ef, hu_ef, h_skip, h_ef⟩ := h
  obtain ⟨ps_outer, ps_bf, hd_bf, hu_bf, h_outer, h_bf⟩ := h_skip
  obtain ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, h_sr⟩ := h_outer
  obtain ⟨ps_x18, ps_r1, hd1, hu1, h_x18, h_r1⟩ := h_sr
  obtain ⟨ps_x2, ps_r2, hd2, hu2, h_x2, h_r2⟩ := h_r1
  obtain ⟨ps_x12, ps_r3, hd3, hu3, h_x12, h_r3⟩ := h_r2
  obtain ⟨ps_x5, ps_r4, hd4, hu4, h_x5, h_r4⟩ := h_r3
  obtain ⟨ps_sp, ps_r5, hd5, hu5, h_sp, h_r5⟩ := h_r4
  obtain ⟨ps_e32, ps_r6, hd6, hu6, h_e32, h_r6⟩ := h_r5
  obtain ⟨ps_x6, ps_r7, hd7, hu7, h_x6, h_r7⟩ := h_r6
  obtain ⟨ps_x7, ps_r8, hd8, hu8, h_x7, h_r8⟩ := h_r7
  obtain ⟨ps_x10, ps_r9, hd9, hu9, h_x10, h_r9⟩ := h_r8
  obtain ⟨ps_x11, ps_r10, hd10, hu10, h_x11, h_r10⟩ := h_r9
  obtain ⟨w0, h_w0_chain⟩ := sepConj_choose_memOwn h_r10
  obtain ⟨ps_w0, ps_r11, hd_w0, hu_w0, h_w0, h_r11⟩ := h_w0_chain
  obtain ⟨w1, h_w1_chain⟩ := sepConj_choose_memOwn h_r11
  obtain ⟨ps_w1, ps_r12, hd_w1, hu_w1, h_w1, h_r12⟩ := h_w1_chain
  obtain ⟨w2, h_w2_chain⟩ := sepConj_choose_memOwn h_r12
  obtain ⟨ps_w2, ps_r13, hd_w2, hu_w2, h_w2, h_r13⟩ := h_w2_chain
  obtain ⟨w3, h_w3_chain⟩ := sepConj_choose_memOwn h_r13
  obtain ⟨ps_w3, ps_x1, hd_w3, hu_w3, h_w3, h_x1⟩ := h_w3_chain
  -- BaseFrame: 4 atoms
  obtain ⟨ps_a0, ps_bfr, hd_a0, hu_a0, h_a0, h_bfr⟩ := h_bf
  obtain ⟨ps_a1, ps_bfr2, hd_a1, hu_a1, h_a1, h_bfr2⟩ := h_bfr
  obtain ⟨ps_a2, ps_a3, hd_a23, hu_a23, h_a2, h_a3⟩ := h_bfr2
  -- Exponent_frame: 4 atoms
  obtain ⟨ps_ex0, ps_ef1, hd_ex0, hu_ex0, h_ex0, h_ef1⟩ := h_ef
  obtain ⟨ps_ex1, ps_ef2, hd_ex1, hu_ex1, h_ex1, h_ef2⟩ := h_ef1
  obtain ⟨ps_ex2, ps_ex3, hd_ex23, hu_ex23, h_ex2, h_ex3⟩ := h_ef2
  refine ⟨w0, w1, w2, w3, ?_⟩
  rw [expTwoMulLoopExitFullStackPreFrame_unfold, expTwoMulLoopExitControl_unfold]
  rw [show (evmSp - 64 : Word) = evmSp + 18446744073709551552 from by bv_omega]
  simp only [evmWordIs, evmStackIs,
             signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
             signExtend12_64,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc,
             expResultWord_getLimbN_0, expResultWord_getLimbN_1,
             expResultWord_getLimbN_2, expResultWord_getLimbN_3,
             show (18446744073709551552:Word) + 8 = 18446744073709551560 from by decide,
             show (18446744073709551552:Word) + 16 = 18446744073709551568 from by decide,
             show (18446744073709551552:Word) + 24 = 18446744073709551576 from by decide,
             show (18446744073709551552:Word) + 32 = 18446744073709551584 from by decide,
             show (18446744073709551552:Word) + 64 = 0 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide,
             show (18446744073709551584:Word) + 32 = 0 from by decide,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide]
  rw [pure_true_eq_emp]
  simp only [sepConj_emp_right']
  -- h_full mirrors the ps decomposition tree:
  -- outermost: (skip_atoms @ ps_skip) ** (exponent_atoms @ ps_ef)
  -- skip: ((inner_atoms @ ps_outer) ** (base_atoms @ ps_bf))
  -- inner: ((x9x0 @ ps_x9x0) ** (SkipRest chain @ ps_sr))  ← grouped
  have h_full :
      ((((((Reg.x9 ↦ᵣ 0) ** Reg.x0 ↦ᵣ 0) **
          (Reg.x18 ↦ᵣ bit) **
          (Reg.x2 ↦ᵣ sp) **
          (Reg.x12 ↦ᵣ evmSp) **
          (Reg.x5 ↦ᵣ squarW.getLimbN 3) **
          ((sp ↦ₘ squarW.getLimbN 0) ** (sp + 8 ↦ₘ squarW.getLimbN 1) **
           (sp + 16 ↦ₘ squarW.getLimbN 2) ** (sp + 24 ↦ₘ squarW.getLimbN 3)) **
          ((evmSp + 32 ↦ₘ squarW.getLimbN 0) ** (evmSp + 40 ↦ₘ squarW.getLimbN 1) **
           (evmSp + 48 ↦ₘ squarW.getLimbN 2) ** (evmSp + 56 ↦ₘ squarW.getLimbN 3)) **
          regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
          (evmSp ↦ₘ w0) ** (evmSp + 8 ↦ₘ w1) ** (evmSp + 16 ↦ₘ w2) **
          (evmSp + 24 ↦ₘ w3) ** (Reg.x1 ↦ᵣ (base + (44 + 68)))) **
         (evmSp + 18446744073709551552 ↦ₘ a0) **
         (evmSp + 18446744073709551560 ↦ₘ a1) **
         (evmSp + 18446744073709551568 ↦ₘ a2) **
         (evmSp + 18446744073709551576 ↦ₘ a3)) **
        (evmSp + 18446744073709551584 ↦ₘ exponentWord.getLimbN 0) **
        (evmSp + 18446744073709551592 ↦ₘ exponentWord.getLimbN 1) **
        (evmSp + 18446744073709551600 ↦ₘ exponentWord.getLimbN 2) **
        (evmSp + 18446744073709551608 ↦ₘ exponentWord.getLimbN 3))) ps := by
    refine ⟨ps_skip, ps_ef, hd_ef, hu_ef, ?_, ?_⟩
    · refine ⟨ps_outer, ps_bf, hd_bf, hu_bf, ?_, ?_⟩
      · refine ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, ?_⟩
        refine ⟨ps_x18, ps_r1, hd1, hu1, h_x18, ?_⟩
        refine ⟨ps_x2, ps_r2, hd2, hu2, h_x2, ?_⟩
        refine ⟨ps_x12, ps_r3, hd3, hu3, h_x12, ?_⟩
        refine ⟨ps_x5, ps_r4, hd4, hu4, h_x5, ?_⟩
        refine ⟨ps_sp, ps_r5, hd5, hu5, h_sp, ?_⟩
        refine ⟨ps_e32, ps_r6, hd6, hu6, h_e32, ?_⟩
        refine ⟨ps_x6, ps_r7, hd7, hu7, h_x6, ?_⟩
        refine ⟨ps_x7, ps_r8, hd8, hu8, h_x7, ?_⟩
        refine ⟨ps_x10, ps_r9, hd9, hu9, h_x10, ?_⟩
        refine ⟨ps_x11, ps_r10, hd10, hu10, h_x11, ?_⟩
        refine ⟨ps_w0, _, hd_w0, hu_w0, h_w0, ?_⟩
        refine ⟨ps_w1, _, hd_w1, hu_w1, h_w1, ?_⟩
        refine ⟨ps_w2, _, hd_w2, hu_w2, h_w2, ?_⟩
        exact ⟨ps_w3, ps_x1, hd_w3, hu_w3, h_w3, h_x1⟩
      · refine ⟨ps_a0, _, hd_a0, hu_a0, h_a0, ?_⟩
        refine ⟨ps_a1, _, hd_a1, hu_a1, h_a1, ?_⟩
        exact ⟨ps_a2, ps_a3, hd_a23, hu_a23, h_a2, h_a3⟩
    · refine ⟨ps_ex0, _, hd_ex0, hu_ex0, h_ex0, ?_⟩
      refine ⟨ps_ex1, _, hd_ex1, hu_ex1, h_ex1, ?_⟩
      exact ⟨ps_ex2, ps_ex3, hd_ex23, hu_ex23, h_ex2, h_ex3⟩
  sep_perm h_full

theorem expTwoMulIterExitPost_to_FullStackPreFrame_framed
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squarW rwW exponentWord : EvmWord}
    {ps : PartialState}
    (h : (expTwoMulIterExitPost 0 bit sp evmSp base a0 a1 a2 a3 squarW rwW **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ tOld r0 r1 r2 r3 w0 w1 w2 w3 vx18 vx1,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0 tOld r0 r1 r2 r3
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3, expResultWord r0 r1 r2 r3]
          ((0 : Word) = 0) **
       (.x18 ↦ᵣ vx18) ** (.x1 ↦ᵣ vx1) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  obtain ⟨ps_ep, ps_ef, hd_ef, hu_ef, h_ep, h_ef⟩ := h
  rw [expTwoMulIterExitPost_unfold] at h_ep
  rcases h_ep with hCond | hSkip
  · obtain ⟨w0, w1, w2, w3, hpre⟩ :=
      expTwoMulIterCondExitPost_to_FullStackPreFrame
        ⟨ps_ep, ps_ef, hd_ef, hu_ef, hCond, h_ef⟩
    -- hpre uses [expResultWord w0..w3, rwW]; convert rwW → expResultWord rwW.0..3
    have hpre' : (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
          (rwW.getLimbN 3) (rwW.getLimbN 0) (rwW.getLimbN 1) (rwW.getLimbN 2) (rwW.getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3,
           expResultWord (rwW.getLimbN 0) (rwW.getLimbN 1) (rwW.getLimbN 2) (rwW.getLimbN 3)]
          ((0 : Word) = 0) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x1 ↦ᵣ ((base + 152) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
      rw [expResultWord_getLimbN_self]; exact hpre
    exact ⟨rwW.getLimbN 3, rwW.getLimbN 0, rwW.getLimbN 1, rwW.getLimbN 2, rwW.getLimbN 3,
           w0, w1, w2, w3, bit + signExtend12 0, (base + 152) + 68, hpre'⟩
  · obtain ⟨w0, w1, w2, w3, hpre⟩ :=
      expTwoMulIterSkipExitPost_to_FullStackPreFrame
        ⟨ps_ep, ps_ef, hd_ef, hu_ef, hSkip, h_ef⟩
    have hpre' : (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) 0
          (squarW.getLimbN 3) (squarW.getLimbN 0) (squarW.getLimbN 1) (squarW.getLimbN 2)
          (squarW.getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3,
           expResultWord (squarW.getLimbN 0) (squarW.getLimbN 1) (squarW.getLimbN 2)
             (squarW.getLimbN 3)]
          ((0 : Word) = 0) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x1 ↦ᵣ ((base + 44) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
      rw [expResultWord_getLimbN_self]; exact hpre
    exact ⟨squarW.getLimbN 3, squarW.getLimbN 0, squarW.getLimbN 1, squarW.getLimbN 2,
           squarW.getLimbN 3, w0, w1, w2, w3, bit + signExtend12 0, (base + 44) + 68, hpre'⟩

end EvmAsm.Evm64.Exp.Compose
