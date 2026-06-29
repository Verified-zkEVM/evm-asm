import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomCompose

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Word-folded epilogue block (instr idx 93, byte +372..408) lifted onto the
    headroom program. This keeps the result stack word folded for the final
    EXP wrapper composition. -/
theorem exp_headroom_epilogue_word_lifted
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 9 (base + 372) (base + 408)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
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
  have h := exp_epilogue_word_spec_within sp evmSp tOld r0 r1 r2 r3
    d0 d1 d2 d3 (base + 372)
  rw [show (base + 372 + 36 : Word) = base + 408 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 372)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_epilogue 93
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- Canonical appended-code variant of `exp_headroom_epilogue_word_lifted`. -/
theorem exp_headroom_epilogue_word_canonical_appended
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base : Word) :
    cpsTripleWithin 9 (base + 372) (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
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
  have h := exp_headroom_epilogue_word_lifted sp evmSp tOld r0 r1 r2 r3
    d0 d1 d2 d3 base
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.union_mono_left a i ha

/-- Entry prefix plus the fixed 256-step loop, with the explicit bridge frame
    folded into the first-iteration residual precondition. This is the main
    headroom body surface before the final epilogue writes the result back. -/
theorem exp_headroom_entry_to_final_loop_post
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193)) base (base + 72 + 296)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) **
       expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest))
      (expFinalLoopFirstIterPost sp (evmSp + signExtend12 ((-128) : BitVec 12))
        (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3)
        (expResultWord b0 b1 b2 b3 :: expResultWord e0 e1 e2 e3 :: rest)) := by
  let bridgeFrame := expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest
  have hEntry :=
    exp_headroom_entry_to_loopadvance_canonical_appended_folded_framed
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
      bridgeFrame (by
        dsimp [bridgeFrame]
        exact expHeadroomLoopEntryBridgeFrame_pcFree)
  have hLoop :=
    exp_headroom_loop_lifted_folded_canonical_appended
      sp (evmSp + signExtend12 ((-128) : BitVec 12)) base
      (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3)
      dWord eWord
      (expResultWord b0 b1 b2 b3 :: expResultWord e0 e1 e2 e3 :: rest)
      lookahead vOld v18 hbase
  rw [show (base + 72 + 44 : Word) = base + 116 from by bv_addr] at hLoop
  refine cpsTripleWithin_seq_perm_same_cr ?_ hEntry hLoop
  intro ps hps
  dsimp [bridgeFrame] at hps
  exact expHeadroomLoopEntryPost_to_firstIterPreWithResidual hps


end EvmAsm.Evm64.Exp.Compose
