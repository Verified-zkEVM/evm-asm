/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedExitBridge

  Exit bridge for the fixed-x20 EXP loop body: from a final-iteration exit
  post-condition disjunct (`expTwoMulFixedIter*CountPost … (IterCountNew = 0)`)
  plus the exponent frame `evmWordIs (evmSp + signExtend12 (-32)) exponentWord`,
  prove `(expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) … ** leftover) ps`.

  Mirrors `SavedBitIterExitBridge.lean`, adapted for the fixed per-limb counter
  in `x20` (carried into the leftover; irrelevant at loop exit) and the fixed
  rest-structures.  The iteration runs at `evmSp_iter = evmSp + 64`, so the
  bridge maps `…(evmSp_iter)… → LoopExitFullStackPreFrame sp (evmSp_iter − 64)`.

  Bead: evm-asm-20z6.13.7 (exit bridge / step 3).
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePosts

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Skip (no-reload, bit=0) exit-post disjunct → full-stack exit pre-frame. -/
theorem expTwoMulFixedIterSkipCountPost_to_FullStackPreFrame
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exponentWord : EvmWord} {ps : PartialState}
    (h : (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base (expTwoMulIterCountNew iterCount = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64)
          (expTwoMulIterCountNew iterCount)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3, expSquaringCallSquareW r0 r1 r2 r3]
          (expTwoMulIterCountNew iterCount = 0) **
       (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x20 ↦ᵣ (c6 + signExtend12 (-1 : BitVec 12))) **
       (.x18 ↦ᵣ (e >>> (63 : BitVec 6).toNat)) **
       (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  simp only [expTwoMulFixedIterSkipCountPost, expTwoMulFixedIterSkipRest,
             expTwoMulFixedIterBaseFrame, evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide] at h
  -- Navigate the source tree: ((Inner ** BaseFrame) ** exponentFrame)
  obtain ⟨ps_LB, ps_ef, hd_ef, hu_ef, h_LB, h_ef⟩ := h
  obtain ⟨ps_inner, ps_bf, hd_bf, hu_bf, h_inner, h_bf⟩ := h_LB
  obtain ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, h_sr⟩ := h_inner
  obtain ⟨ps_x2, ps_r1, hd1, hu1, h_x2, h_r1⟩ := h_sr
  obtain ⟨ps_x12, ps_r2, hd2, hu2, h_x12, h_r2⟩ := h_r1
  obtain ⟨ps_x5, ps_r3, hd3, hu3, h_x5, h_r3⟩ := h_r2
  -- evmWordIs sp squareW (4-atom group)
  obtain ⟨ps_spG, ps_r4, hd4, hu4, h_spG, h_r4⟩ := h_r3
  obtain ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0, h_spG1⟩ := h_spG
  obtain ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1, h_spG2⟩ := h_spG1
  obtain ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩ := h_spG2
  -- evmWordIs (evmSp+32) squareW (4-atom group)
  obtain ⟨ps_eG, ps_r5, hd5, hu5, h_eG, h_r5⟩ := h_r4
  obtain ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a, h_eG1⟩ := h_eG
  obtain ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b, h_eG2⟩ := h_eG1
  obtain ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩ := h_eG2
  obtain ⟨ps_x6, ps_r12, hd12, hu12, h_x6, h_r12⟩ := h_r5
  obtain ⟨ps_x7, ps_r13, hd13, hu13, h_x7, h_r13⟩ := h_r12
  obtain ⟨ps_x10, ps_r14, hd14, hu14, h_x10, h_r14⟩ := h_r13
  obtain ⟨ps_x11, ps_r15, hd15, hu15, h_x11, h_r15⟩ := h_r14
  obtain ⟨w0, h_w0c⟩ := sepConj_choose_memOwn h_r15
  obtain ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, h_r16⟩ := h_w0c
  obtain ⟨w1, h_w1c⟩ := sepConj_choose_memOwn h_r16
  obtain ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, h_r17⟩ := h_w1c
  obtain ⟨w2, h_w2c⟩ := sepConj_choose_memOwn h_r17
  obtain ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, h_r18⟩ := h_w2c
  obtain ⟨w3, h_w3c⟩ := sepConj_choose_memOwn h_r18
  obtain ⟨ps_w3, ps_r19, hdw3, huw3, h_w3, h_r19⟩ := h_w3c
  obtain ⟨ps_x1, ps_r20, hd20, hu20, h_x1, h_r20⟩ := h_r19
  obtain ⟨ps_x19, ps_r21, hd21, hu21, h_x19, h_r21⟩ := h_r20
  obtain ⟨ps_x20, ps_r22, hd22, hu22, h_x20, h_r22⟩ := h_r21
  obtain ⟨ps_x18, ps_r23, hd23, hu23, h_x18, h_r23⟩ := h_r22
  obtain ⟨_pne, _pbit⟩ := (sepConj_pure_left _).mp h_r23
  -- BaseFrame: 4 atoms
  obtain ⟨ps_a0, ps_bf1, hda0, hua0, h_a0, h_bf1⟩ := h_bf
  obtain ⟨ps_a1, ps_bf2, hda1, hua1, h_a1, h_bf2⟩ := h_bf1
  obtain ⟨ps_a2, ps_a3, hda23, hua23, h_a2, h_a3⟩ := h_bf2
  -- exponent frame: 4 atoms
  obtain ⟨ps_x0, ps_ef1, hdx0, hux0, h_x0, h_ef1⟩ := h_ef
  obtain ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e, h_ef2⟩ := h_ef1
  obtain ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩ := h_ef2
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
  have hr23emp : ps_r23 = PartialState.empty := _pbit.1
  have h_full :
      (((((Reg.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (Reg.x0 ↦ᵣ 0) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) **
         (Reg.x2 ↦ᵣ sp) ** (Reg.x12 ↦ᵣ evmSp) **
         (Reg.x5 ↦ᵣ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) **
         (((sp ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) **
            (sp + 8 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1) **
            (sp + 16 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) **
            (sp + 24 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3))) **
         (((evmSp + 32 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) **
            (evmSp + 40 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1) **
            (evmSp + 48 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) **
            (evmSp + 56 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3))) **
         regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
         (evmSp ↦ₘ w0) ** (evmSp + 8 ↦ₘ w1) ** (evmSp + 16 ↦ₘ w2) **
         (evmSp + 24 ↦ₘ w3) **
         (Reg.x1 ↦ᵣ base + (44 + (32 + 68))) **
         (Reg.x19 ↦ᵣ e <<< (1 : BitVec 6).toNat) **
         (Reg.x20 ↦ᵣ c6 + signExtend12 (-1 : BitVec 12)) **
         ((Reg.x18 ↦ᵣ e >>> (63 : BitVec 6).toNat) ** empAssertion)) **
        ((evmSp + 18446744073709551552 ↦ₘ a0) **
         (evmSp + 18446744073709551560 ↦ₘ a1) **
         (evmSp + 18446744073709551568 ↦ₘ a2) **
         (evmSp + 18446744073709551576 ↦ₘ a3))) **
       ((evmSp + 18446744073709551584 ↦ₘ exponentWord.getLimbN 0) **
        (evmSp + 18446744073709551592 ↦ₘ exponentWord.getLimbN 1) **
        (evmSp + 18446744073709551600 ↦ₘ exponentWord.getLimbN 2) **
        (evmSp + 18446744073709551608 ↦ₘ exponentWord.getLimbN 3))) ps := by
    refine ⟨ps_LB, ps_ef, hd_ef, hu_ef, ?_, ?_⟩
    · refine ⟨ps_inner, ps_bf, hd_bf, hu_bf, ?_, ?_⟩
      · refine ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, ?_⟩
        refine ⟨ps_x2, ps_r1, hd1, hu1, h_x2, ?_⟩
        refine ⟨ps_x12, ps_r2, hd2, hu2, h_x12, ?_⟩
        refine ⟨ps_x5, ps_r3, hd3, hu3, h_x5, ?_⟩
        refine ⟨ps_spG, ps_r4, hd4, hu4, ?_, ?_⟩
        · exact ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0,
            ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1,
              ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩⟩⟩
        refine ⟨ps_eG, ps_r5, hd5, hu5, ?_, ?_⟩
        · exact ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a,
            ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b,
              ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩⟩⟩
        refine ⟨ps_x6, ps_r12, hd12, hu12, h_x6, ?_⟩
        refine ⟨ps_x7, ps_r13, hd13, hu13, h_x7, ?_⟩
        refine ⟨ps_x10, ps_r14, hd14, hu14, h_x10, ?_⟩
        refine ⟨ps_x11, ps_r15, hd15, hu15, h_x11, ?_⟩
        refine ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, ?_⟩
        refine ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, ?_⟩
        refine ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, ?_⟩
        refine ⟨ps_w3, ps_r19, hdw3, huw3, h_w3, ?_⟩
        refine ⟨ps_x1, ps_r20, hd20, hu20, h_x1, ?_⟩
        refine ⟨ps_x19, ps_r21, hd21, hu21, h_x19, ?_⟩
        refine ⟨ps_x20, ps_r22, hd22, hu22, h_x20, ?_⟩
        exact ⟨ps_x18, ps_r23, hd23, hu23, h_x18, hr23emp⟩
      · exact ⟨ps_a0, ps_bf1, hda0, hua0, h_a0,
          ⟨ps_a1, ps_bf2, hda1, hua1, h_a1,
            ⟨ps_a2, ps_a3, hda23, hua23, h_a2, h_a3⟩⟩⟩
    · exact ⟨ps_x0, ps_ef1, hdx0, hux0, h_x0,
        ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e,
          ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩⟩⟩
  sep_perm h_full

/-- SkipCond (no-reload, bit≠0) exit-post disjunct → full-stack exit pre-frame. -/
theorem expTwoMulFixedIterSkipCondCountPost_to_FullStackPreFrame
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exponentWord : EvmWord} {ps : PartialState}
    (h : (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base (expTwoMulIterCountNew iterCount = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64)
          (expTwoMulIterCountNew iterCount)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3,
            expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3]
          (expTwoMulIterCountNew iterCount = 0) **
       (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x20 ↦ᵣ (c6 + signExtend12 (-1 : BitVec 12))) **
       (.x18 ↦ᵣ (e >>> (63 : BitVec 6).toNat)) **
       (.x1 ↦ᵣ (((base + 44) + 140) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  simp only [expTwoMulFixedIterSkipCondCountPost, expTwoMulFixedIterSkipCondRest,
             expTwoMulFixedIterSkipCondFrame, evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide] at h
  -- Navigate: (((x9x0pure ** SkipCondRest) ** SkipCondFrame) ** expFrame)
  obtain ⟨ps_LB, ps_ef, hd_ef, hu_ef, h_LB, h_ef⟩ := h
  obtain ⟨ps_inner, ps_scf, hd_scf, hu_scf, h_inner, h_scf⟩ := h_LB
  obtain ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, h_sr⟩ := h_inner
  obtain ⟨ps_x2, ps_r1, hd1, hu1, h_x2, h_r1⟩ := h_sr
  obtain ⟨ps_x12, ps_r2, hd2, hu2, h_x12, h_r2⟩ := h_r1
  obtain ⟨ps_x5, ps_r3, hd3, hu3, h_x5, h_r3⟩ := h_r2
  obtain ⟨ps_a0, ps_ra0, hda0, hua0, h_a0, h_ra0⟩ := h_r3
  obtain ⟨ps_a1, ps_ra1, hda1, hua1, h_a1, h_ra1⟩ := h_ra0
  obtain ⟨ps_a2, ps_ra2, hda2, hua2, h_a2, h_ra2⟩ := h_ra1
  obtain ⟨ps_a3, ps_r3b, hda3, hua3, h_a3, h_r3b⟩ := h_ra2
  -- evmWordIs sp rw (4-atom group)
  obtain ⟨ps_spG, ps_r4, hd4, hu4, h_spG, h_r4⟩ := h_r3b
  obtain ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0, h_spG1⟩ := h_spG
  obtain ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1, h_spG2⟩ := h_spG1
  obtain ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩ := h_spG2
  -- evmWordIs (evmSp+32) rw (4-atom group)
  obtain ⟨ps_eG, ps_r5, hd5, hu5, h_eG, h_r5⟩ := h_r4
  obtain ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a, h_eG1⟩ := h_eG
  obtain ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b, h_eG2⟩ := h_eG1
  obtain ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩ := h_eG2
  obtain ⟨ps_x6, ps_r12, hd12, hu12, h_x6, h_r12⟩ := h_r5
  obtain ⟨ps_x7, ps_r13, hd13, hu13, h_x7, h_r13⟩ := h_r12
  obtain ⟨ps_x10, ps_r14, hd14, hu14, h_x10, h_r14⟩ := h_r13
  obtain ⟨ps_x11, ps_r15, hd15, hu15, h_x11, h_r15⟩ := h_r14
  obtain ⟨w0, h_w0c⟩ := sepConj_choose_memOwn h_r15
  obtain ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, h_r16⟩ := h_w0c
  obtain ⟨w1, h_w1c⟩ := sepConj_choose_memOwn h_r16
  obtain ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, h_r17⟩ := h_w1c
  obtain ⟨w2, h_w2c⟩ := sepConj_choose_memOwn h_r17
  obtain ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, h_r18⟩ := h_w2c
  obtain ⟨w3, h_w3c⟩ := sepConj_choose_memOwn h_r18
  obtain ⟨ps_w3, ps_x1, hdw3, huw3, h_w3, h_x1⟩ := h_w3c
  -- SkipCondFrame: x19, x20, x18, then two pure facts (drop → one emp)
  obtain ⟨ps_x19, ps_scf1, hd19, hu19, h_x19, h_scf1⟩ := h_scf
  obtain ⟨ps_x20, ps_scf2, hd20, hu20, h_x20, h_scf2⟩ := h_scf1
  obtain ⟨ps_x18, ps_pures, hd18, hu18, h_x18, h_pures⟩ := h_scf2
  obtain ⟨_pc6, h_bit⟩ := (sepConj_pure_left _).mp h_pures
  have hpures_emp : ps_pures = PartialState.empty := h_bit.1
  -- exponent frame: 4 atoms
  obtain ⟨ps_x0e, ps_ef1, hdx0, hux0, h_x0e, h_ef1⟩ := h_ef
  obtain ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e, h_ef2⟩ := h_ef1
  obtain ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩ := h_ef2
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
  have h_full :
      (((((Reg.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (Reg.x0 ↦ᵣ 0) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) **
         (Reg.x2 ↦ᵣ sp) ** (Reg.x12 ↦ᵣ evmSp) **
         (Reg.x5 ↦ᵣ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) **
         (evmSp + 18446744073709551552 ↦ₘ a0) **
         (evmSp + 18446744073709551560 ↦ₘ a1) **
         (evmSp + 18446744073709551568 ↦ₘ a2) **
         (evmSp + 18446744073709551576 ↦ₘ a3) **
         (((sp ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) **
            (sp + 8 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1) **
            (sp + 16 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) **
            (sp + 24 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3))) **
         (((evmSp + 32 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) **
            (evmSp + 40 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1) **
            (evmSp + 48 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) **
            (evmSp + 56 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3))) **
         regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
         (evmSp ↦ₘ w0) ** (evmSp + 8 ↦ₘ w1) ** (evmSp + 16 ↦ₘ w2) **
         (evmSp + 24 ↦ₘ w3) **
         (Reg.x1 ↦ᵣ base + (44 + (140 + 68)))) **
        ((Reg.x19 ↦ᵣ e <<< (1 : BitVec 6).toNat) **
         (Reg.x20 ↦ᵣ c6 + signExtend12 (-1 : BitVec 12)) **
         ((Reg.x18 ↦ᵣ e >>> (63 : BitVec 6).toNat) ** empAssertion))) **
       ((evmSp + 18446744073709551584 ↦ₘ exponentWord.getLimbN 0) **
        (evmSp + 18446744073709551592 ↦ₘ exponentWord.getLimbN 1) **
        (evmSp + 18446744073709551600 ↦ₘ exponentWord.getLimbN 2) **
        (evmSp + 18446744073709551608 ↦ₘ exponentWord.getLimbN 3))) ps := by
    refine ⟨ps_LB, ps_ef, hd_ef, hu_ef, ?_, ?_⟩
    · refine ⟨ps_inner, ps_scf, hd_scf, hu_scf, ?_, ?_⟩
      · refine ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, ?_⟩
        refine ⟨ps_x2, ps_r1, hd1, hu1, h_x2, ?_⟩
        refine ⟨ps_x12, ps_r2, hd2, hu2, h_x12, ?_⟩
        refine ⟨ps_x5, ps_r3, hd3, hu3, h_x5, ?_⟩
        refine ⟨ps_a0, ps_ra0, hda0, hua0, h_a0, ?_⟩
        refine ⟨ps_a1, ps_ra1, hda1, hua1, h_a1, ?_⟩
        refine ⟨ps_a2, ps_ra2, hda2, hua2, h_a2, ?_⟩
        refine ⟨ps_a3, ps_r3b, hda3, hua3, h_a3, ?_⟩
        refine ⟨ps_spG, ps_r4, hd4, hu4, ?_, ?_⟩
        · exact ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0,
            ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1,
              ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩⟩⟩
        refine ⟨ps_eG, ps_r5, hd5, hu5, ?_, ?_⟩
        · exact ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a,
            ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b,
              ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩⟩⟩
        refine ⟨ps_x6, ps_r12, hd12, hu12, h_x6, ?_⟩
        refine ⟨ps_x7, ps_r13, hd13, hu13, h_x7, ?_⟩
        refine ⟨ps_x10, ps_r14, hd14, hu14, h_x10, ?_⟩
        refine ⟨ps_x11, ps_r15, hd15, hu15, h_x11, ?_⟩
        refine ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, ?_⟩
        refine ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, ?_⟩
        refine ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, ?_⟩
        refine ⟨ps_w3, ps_x1, hdw3, huw3, h_w3, h_x1⟩
      · refine ⟨ps_x19, ps_scf1, hd19, hu19, h_x19, ?_⟩
        refine ⟨ps_x20, ps_scf2, hd20, hu20, h_x20, ?_⟩
        exact ⟨ps_x18, ps_pures, hd18, hu18, h_x18, hpures_emp⟩
    · exact ⟨ps_x0e, ps_ef1, hdx0, hux0, h_x0e,
        ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e,
          ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩⟩⟩
  sep_perm h_full

/-- ReloadCond (reload, bit≠0) exit-post disjunct → full-stack exit pre-frame. -/
theorem expTwoMulFixedIterReloadCondCountPost_to_FullStackPreFrame
    {iterCount e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exponentWord : EvmWord} {ps : PartialState}
    (h : (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base (expTwoMulIterCountNew iterCount = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64)
          (expTwoMulIterCountNew iterCount)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3,
            expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3]
          (expTwoMulIterCountNew iterCount = 0) **
       (.x19 ↦ᵣ nextLimb) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x18 ↦ᵣ (e >>> (63 : BitVec 6).toNat)) **
       (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
       (.x1 ↦ᵣ (((base + 44) + 140) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  simp only [expTwoMulFixedIterReloadCondCountPost, expTwoMulFixedIterSkipCondRest,
             expTwoMulFixedIterReloadCondFrame, evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide] at h
  obtain ⟨ps_LB, ps_ef, hd_ef, hu_ef, h_LB, h_ef⟩ := h
  obtain ⟨ps_inner, ps_scf, hd_scf, hu_scf, h_inner, h_scf⟩ := h_LB
  obtain ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, h_sr⟩ := h_inner
  obtain ⟨ps_x2, ps_r1, hd1, hu1, h_x2, h_r1⟩ := h_sr
  obtain ⟨ps_x12, ps_r2, hd2, hu2, h_x12, h_r2⟩ := h_r1
  obtain ⟨ps_x5, ps_r3, hd3, hu3, h_x5, h_r3⟩ := h_r2
  obtain ⟨ps_a0, ps_ra0, hda0, hua0, h_a0, h_ra0⟩ := h_r3
  obtain ⟨ps_a1, ps_ra1, hda1, hua1, h_a1, h_ra1⟩ := h_ra0
  obtain ⟨ps_a2, ps_ra2, hda2, hua2, h_a2, h_ra2⟩ := h_ra1
  obtain ⟨ps_a3, ps_r3b, hda3, hua3, h_a3, h_r3b⟩ := h_ra2
  obtain ⟨ps_spG, ps_r4, hd4, hu4, h_spG, h_r4⟩ := h_r3b
  obtain ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0, h_spG1⟩ := h_spG
  obtain ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1, h_spG2⟩ := h_spG1
  obtain ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩ := h_spG2
  obtain ⟨ps_eG, ps_r5, hd5, hu5, h_eG, h_r5⟩ := h_r4
  obtain ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a, h_eG1⟩ := h_eG
  obtain ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b, h_eG2⟩ := h_eG1
  obtain ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩ := h_eG2
  obtain ⟨ps_x6, ps_r12, hd12, hu12, h_x6, h_r12⟩ := h_r5
  obtain ⟨ps_x7, ps_r13, hd13, hu13, h_x7, h_r13⟩ := h_r12
  obtain ⟨ps_x10, ps_r14, hd14, hu14, h_x10, h_r14⟩ := h_r13
  obtain ⟨ps_x11, ps_r15, hd15, hu15, h_x11, h_r15⟩ := h_r14
  obtain ⟨w0, h_w0c⟩ := sepConj_choose_memOwn h_r15
  obtain ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, h_r16⟩ := h_w0c
  obtain ⟨w1, h_w1c⟩ := sepConj_choose_memOwn h_r16
  obtain ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, h_r17⟩ := h_w1c
  obtain ⟨w2, h_w2c⟩ := sepConj_choose_memOwn h_r17
  obtain ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, h_r18⟩ := h_w2c
  obtain ⟨w3, h_w3c⟩ := sepConj_choose_memOwn h_r18
  obtain ⟨ps_w3, ps_x1, hdw3, huw3, h_w3, h_x1⟩ := h_w3c
  -- ReloadCondFrame: x19, x20, x18, ⌜c6New=0⌝ (absorbed), x16, ptr-cell, ⌜bit≠0⌝ (→emp)
  obtain ⟨ps_x19, ps_scf1, hd19, hu19, h_x19, h_scf1⟩ := h_scf
  obtain ⟨ps_x20, ps_scf2, hd20, hu20, h_x20, h_scf2⟩ := h_scf1
  obtain ⟨ps_x18, ps_scf3, hd18, hu18, h_x18, h_scf3⟩ := h_scf2
  obtain ⟨_pc6, h_aft⟩ := (sepConj_pure_left _).mp h_scf3
  obtain ⟨ps_x16, ps_aft2, hd16, hu16, h_x16, h_aft2⟩ := h_aft
  obtain ⟨ps_ptr, ps_bit, hdptr, huptr, h_ptr, h_bitpure⟩ := h_aft2
  have hbit_emp : ps_bit = PartialState.empty := h_bitpure.1
  -- exponent frame: 4 atoms
  obtain ⟨ps_x0e, ps_ef1, hdx0, hux0, h_x0e, h_ef1⟩ := h_ef
  obtain ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e, h_ef2⟩ := h_ef1
  obtain ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩ := h_ef2
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
  have h_full :
      (((((Reg.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (Reg.x0 ↦ᵣ 0) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) **
         (Reg.x2 ↦ᵣ sp) ** (Reg.x12 ↦ᵣ evmSp) **
         (Reg.x5 ↦ᵣ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) **
         (evmSp + 18446744073709551552 ↦ₘ a0) **
         (evmSp + 18446744073709551560 ↦ₘ a1) **
         (evmSp + 18446744073709551568 ↦ₘ a2) **
         (evmSp + 18446744073709551576 ↦ₘ a3) **
         (((sp ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) **
            (sp + 8 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1) **
            (sp + 16 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) **
            (sp + 24 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3))) **
         (((evmSp + 32 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) **
            (evmSp + 40 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1) **
            (evmSp + 48 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) **
            (evmSp + 56 ↦ₘ (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3))) **
         regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
         (evmSp ↦ₘ w0) ** (evmSp + 8 ↦ₘ w1) ** (evmSp + 16 ↦ₘ w2) **
         (evmSp + 24 ↦ₘ w3) **
         (Reg.x1 ↦ᵣ base + (44 + (140 + 68)))) **
        ((Reg.x19 ↦ᵣ nextLimb) **
         (Reg.x20 ↦ᵣ (0 : Word) + signExtend12 (64 : BitVec 12)) **
         (Reg.x18 ↦ᵣ e >>> (63 : BitVec 6).toNat) **
         (Reg.x16 ↦ᵣ ptr + signExtend12 (-8 : BitVec 12)) **
         (ptr ↦ₘ nextLimb) ** empAssertion)) **
       ((evmSp + 18446744073709551584 ↦ₘ exponentWord.getLimbN 0) **
        (evmSp + 18446744073709551592 ↦ₘ exponentWord.getLimbN 1) **
        (evmSp + 18446744073709551600 ↦ₘ exponentWord.getLimbN 2) **
        (evmSp + 18446744073709551608 ↦ₘ exponentWord.getLimbN 3))) ps := by
    refine ⟨ps_LB, ps_ef, hd_ef, hu_ef, ?_, ?_⟩
    · refine ⟨ps_inner, ps_scf, hd_scf, hu_scf, ?_, ?_⟩
      · refine ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, ?_⟩
        refine ⟨ps_x2, ps_r1, hd1, hu1, h_x2, ?_⟩
        refine ⟨ps_x12, ps_r2, hd2, hu2, h_x12, ?_⟩
        refine ⟨ps_x5, ps_r3, hd3, hu3, h_x5, ?_⟩
        refine ⟨ps_a0, ps_ra0, hda0, hua0, h_a0, ?_⟩
        refine ⟨ps_a1, ps_ra1, hda1, hua1, h_a1, ?_⟩
        refine ⟨ps_a2, ps_ra2, hda2, hua2, h_a2, ?_⟩
        refine ⟨ps_a3, ps_r3b, hda3, hua3, h_a3, ?_⟩
        refine ⟨ps_spG, ps_r4, hd4, hu4, ?_, ?_⟩
        · exact ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0,
            ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1,
              ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩⟩⟩
        refine ⟨ps_eG, ps_r5, hd5, hu5, ?_, ?_⟩
        · exact ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a,
            ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b,
              ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩⟩⟩
        refine ⟨ps_x6, ps_r12, hd12, hu12, h_x6, ?_⟩
        refine ⟨ps_x7, ps_r13, hd13, hu13, h_x7, ?_⟩
        refine ⟨ps_x10, ps_r14, hd14, hu14, h_x10, ?_⟩
        refine ⟨ps_x11, ps_r15, hd15, hu15, h_x11, ?_⟩
        refine ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, ?_⟩
        refine ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, ?_⟩
        refine ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, ?_⟩
        refine ⟨ps_w3, ps_x1, hdw3, huw3, h_w3, h_x1⟩
      · refine ⟨ps_x19, ps_scf1, hd19, hu19, h_x19, ?_⟩
        refine ⟨ps_x20, ps_scf2, hd20, hu20, h_x20, ?_⟩
        refine ⟨ps_x18, ps_scf3, hd18, hu18, h_x18, ?_⟩
        refine ⟨ps_x16, ps_aft2, hd16, hu16, h_x16, ?_⟩
        exact ⟨ps_ptr, ps_bit, hdptr, huptr, h_ptr, hbit_emp⟩
    · exact ⟨ps_x0e, ps_ef1, hdx0, hux0, h_x0e,
        ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e,
          ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩⟩⟩
  sep_perm h_full

/-- ReloadSkip (reload, bit=0) exit-post disjunct → full-stack exit pre-frame. -/
theorem expTwoMulFixedIterReloadSkipCountPost_to_FullStackPreFrame
    {iterCount e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exponentWord : EvmWord} {ps : PartialState}
    (h : (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base (expTwoMulIterCountNew iterCount = 0) **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64)
          (expTwoMulIterCountNew iterCount)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3, expSquaringCallSquareW r0 r1 r2 r3]
          (expTwoMulIterCountNew iterCount = 0) **
       (.x19 ↦ᵣ nextLimb) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x18 ↦ᵣ (e >>> (63 : BitVec 6).toNat)) **
       (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
       (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  simp only [expTwoMulFixedIterReloadSkipCountPost, expTwoMulFixedIterReloadSkipRest,
             expTwoMulFixedIterBaseFrame, evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide,
             show (18446744073709551584:Word) + 8 = 18446744073709551592 from by decide,
             show (18446744073709551584:Word) + 16 = 18446744073709551600 from by decide,
             show (18446744073709551584:Word) + 24 = 18446744073709551608 from by decide] at h
  obtain ⟨ps_LB, ps_ef, hd_ef, hu_ef, h_LB, h_ef⟩ := h
  obtain ⟨ps_inner, ps_bf, hd_bf, hu_bf, h_inner, h_bf⟩ := h_LB
  obtain ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, h_sr⟩ := h_inner
  obtain ⟨ps_x2, ps_r1, hd1, hu1, h_x2, h_r1⟩ := h_sr
  obtain ⟨ps_x12, ps_r2, hd2, hu2, h_x12, h_r2⟩ := h_r1
  obtain ⟨ps_x5, ps_r3, hd3, hu3, h_x5, h_r3⟩ := h_r2
  obtain ⟨ps_spG, ps_r4, hd4, hu4, h_spG, h_r4⟩ := h_r3
  obtain ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0, h_spG1⟩ := h_spG
  obtain ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1, h_spG2⟩ := h_spG1
  obtain ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩ := h_spG2
  obtain ⟨ps_eG, ps_r5, hd5, hu5, h_eG, h_r5⟩ := h_r4
  obtain ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a, h_eG1⟩ := h_eG
  obtain ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b, h_eG2⟩ := h_eG1
  obtain ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩ := h_eG2
  obtain ⟨ps_x6, ps_r12, hd12, hu12, h_x6, h_r12⟩ := h_r5
  obtain ⟨ps_x7, ps_r13, hd13, hu13, h_x7, h_r13⟩ := h_r12
  obtain ⟨ps_x10, ps_r14, hd14, hu14, h_x10, h_r14⟩ := h_r13
  obtain ⟨ps_x11, ps_r15, hd15, hu15, h_x11, h_r15⟩ := h_r14
  obtain ⟨w0, h_w0c⟩ := sepConj_choose_memOwn h_r15
  obtain ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, h_r16⟩ := h_w0c
  obtain ⟨w1, h_w1c⟩ := sepConj_choose_memOwn h_r16
  obtain ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, h_r17⟩ := h_w1c
  obtain ⟨w2, h_w2c⟩ := sepConj_choose_memOwn h_r17
  obtain ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, h_r18⟩ := h_w2c
  obtain ⟨w3, h_w3c⟩ := sepConj_choose_memOwn h_r18
  obtain ⟨ps_w3, ps_r19, hdw3, huw3, h_w3, h_r19⟩ := h_w3c
  obtain ⟨ps_x1, ps_r20, hd20, hu20, h_x1, h_r20⟩ := h_r19
  obtain ⟨ps_x19, ps_r21, hd21, hu21, h_x19, h_r21⟩ := h_r20
  obtain ⟨ps_x20, ps_r22, hd22, hu22, h_x20, h_r22⟩ := h_r21
  obtain ⟨ps_x18, ps_r23, hd23, hu23, h_x18, h_r23⟩ := h_r22
  obtain ⟨_pc6, h_aft⟩ := (sepConj_pure_left _).mp h_r23
  obtain ⟨ps_x16, ps_aft2, hd16, hu16, h_x16, h_aft2⟩ := h_aft
  obtain ⟨ps_ptr, ps_bit, hdptr, huptr, h_ptr, h_bitpure⟩ := h_aft2
  have hbit_emp : ps_bit = PartialState.empty := h_bitpure.1
  obtain ⟨ps_a0, ps_bf1, hda0, hua0, h_a0, h_bf1⟩ := h_bf
  obtain ⟨ps_a1, ps_bf2, hda1, hua1, h_a1, h_bf2⟩ := h_bf1
  obtain ⟨ps_a2, ps_a3, hda23, hua23, h_a2, h_a3⟩ := h_bf2
  obtain ⟨ps_x0, ps_ef1, hdx0, hux0, h_x0, h_ef1⟩ := h_ef
  obtain ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e, h_ef2⟩ := h_ef1
  obtain ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩ := h_ef2
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
  have h_full :
      (((((Reg.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (Reg.x0 ↦ᵣ 0) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) **
         (Reg.x2 ↦ᵣ sp) ** (Reg.x12 ↦ᵣ evmSp) **
         (Reg.x5 ↦ᵣ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) **
         (((sp ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) **
            (sp + 8 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1) **
            (sp + 16 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) **
            (sp + 24 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3))) **
         (((evmSp + 32 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) **
            (evmSp + 40 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1) **
            (evmSp + 48 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) **
            (evmSp + 56 ↦ₘ (expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3))) **
         regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
         (evmSp ↦ₘ w0) ** (evmSp + 8 ↦ₘ w1) ** (evmSp + 16 ↦ₘ w2) **
         (evmSp + 24 ↦ₘ w3) **
         (Reg.x1 ↦ᵣ base + (44 + (32 + 68))) **
         (Reg.x19 ↦ᵣ nextLimb) **
         (Reg.x20 ↦ᵣ (0 : Word) + signExtend12 (64 : BitVec 12)) **
         (Reg.x18 ↦ᵣ e >>> (63 : BitVec 6).toNat) **
         (Reg.x16 ↦ᵣ ptr + signExtend12 (-8 : BitVec 12)) **
         ((ptr ↦ₘ nextLimb) ** empAssertion)) **
        ((evmSp + 18446744073709551552 ↦ₘ a0) **
         (evmSp + 18446744073709551560 ↦ₘ a1) **
         (evmSp + 18446744073709551568 ↦ₘ a2) **
         (evmSp + 18446744073709551576 ↦ₘ a3))) **
       ((evmSp + 18446744073709551584 ↦ₘ exponentWord.getLimbN 0) **
        (evmSp + 18446744073709551592 ↦ₘ exponentWord.getLimbN 1) **
        (evmSp + 18446744073709551600 ↦ₘ exponentWord.getLimbN 2) **
        (evmSp + 18446744073709551608 ↦ₘ exponentWord.getLimbN 3))) ps := by
    refine ⟨ps_LB, ps_ef, hd_ef, hu_ef, ?_, ?_⟩
    · refine ⟨ps_inner, ps_bf, hd_bf, hu_bf, ?_, ?_⟩
      · refine ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, ?_⟩
        refine ⟨ps_x2, ps_r1, hd1, hu1, h_x2, ?_⟩
        refine ⟨ps_x12, ps_r2, hd2, hu2, h_x12, ?_⟩
        refine ⟨ps_x5, ps_r3, hd3, hu3, h_x5, ?_⟩
        refine ⟨ps_spG, ps_r4, hd4, hu4, ?_, ?_⟩
        · exact ⟨ps_sp0, ps_spG1, hsd0, hsu0, h_sp0,
            ⟨ps_sp1, ps_spG2, hsd1, hsu1, h_sp1,
              ⟨ps_sp2, ps_sp3, hsd2, hsu2, h_sp2, h_sp3⟩⟩⟩
        refine ⟨ps_eG, ps_r5, hd5, hu5, ?_, ?_⟩
        · exact ⟨ps_e32a, ps_eG1, hed0, heu0, h_e32a,
            ⟨ps_e32b, ps_eG2, hed1, heu1, h_e32b,
              ⟨ps_e32c, ps_e32d, hed2, heu2, h_e32c, h_e32d⟩⟩⟩
        refine ⟨ps_x6, ps_r12, hd12, hu12, h_x6, ?_⟩
        refine ⟨ps_x7, ps_r13, hd13, hu13, h_x7, ?_⟩
        refine ⟨ps_x10, ps_r14, hd14, hu14, h_x10, ?_⟩
        refine ⟨ps_x11, ps_r15, hd15, hu15, h_x11, ?_⟩
        refine ⟨ps_w0, ps_r16, hdw0, huw0, h_w0, ?_⟩
        refine ⟨ps_w1, ps_r17, hdw1, huw1, h_w1, ?_⟩
        refine ⟨ps_w2, ps_r18, hdw2, huw2, h_w2, ?_⟩
        refine ⟨ps_w3, ps_r19, hdw3, huw3, h_w3, ?_⟩
        refine ⟨ps_x1, ps_r20, hd20, hu20, h_x1, ?_⟩
        refine ⟨ps_x19, ps_r21, hd21, hu21, h_x19, ?_⟩
        refine ⟨ps_x20, ps_r22, hd22, hu22, h_x20, ?_⟩
        refine ⟨ps_x18, ps_r23, hd23, hu23, h_x18, ?_⟩
        refine ⟨ps_x16, ps_aft2, hd16, hu16, h_x16, ?_⟩
        exact ⟨ps_ptr, ps_bit, hdptr, huptr, h_ptr, hbit_emp⟩
      · exact ⟨ps_a0, ps_bf1, hda0, hua0, h_a0,
          ⟨ps_a1, ps_bf2, hda1, hua1, h_a1,
            ⟨ps_a2, ps_a3, hda23, hua23, h_a2, h_a3⟩⟩⟩
    · exact ⟨ps_x0, ps_ef1, hdx0, hux0, h_x0,
        ⟨ps_x1e, ps_ef2, hdx1, hux1, h_x1e,
          ⟨ps_x2e, ps_x3e, hdx23, hux23, h_x2e, h_x3e⟩⟩⟩
  sep_perm h_full
