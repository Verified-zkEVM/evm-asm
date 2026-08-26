/-
  EvmAsm.Evm64.DivMod.Compose.PhaseC2V5

  v5 phase-C2 brick (4 steps, phaseC2Off → normBOff, shift ≠ 0 / BEQ-not-taken)
  over `divCode_noNop_v5`.  Mirror of `divK_phaseC2_ntaken_spec_within_v4_noNop`
  (Norm.lean): phase-C2 doesn't touch div128, so its body extends to the v5 code
  via the v5 block subsumption `sharedNoNop_v5_b3_div`.  Fourth brick of the v5
  n=1 preloop.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.Norm
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Phase-C2 block instructions are subsumed by `divCode_noNop_v5`. -/
private theorem divK_phaseC2_code_sub_divCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseC2_code 172 (base + phaseC2Off)) a = some i →
      (divCode_noNop_v5 base) a = some i := by
  unfold divK_phaseC2_code
  intro a i h
  exact sharedNoNop_v5_b3_div a i h

/-- BEQ x6 x0 172 singleton subsumed by `divCode_noNop_v5`. -/
private theorem beq_shift_sub_divCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseC2Off + 12) (.BEQ .x6 .x0 172)) a = some i →
      (divCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseC2Off) (divK_phaseC2 172) 3
    (by decide) (by decide)
  rw [show (BitVec.ofNat 64 (4 * 3) : Word) = (12 : Word) from by decide] at hlookup
  exact divK_phaseC2_code_sub_divCode_noNop_v5 a i
    (CodeReq.singleton_mono hlookup a i h)

private theorem divK_phaseC2_body_divCode_noNop_v5_within
    (sp shift v2 shiftMem : Word) (base : Word) :
    cpsTripleWithin 3 (base + phaseC2Off) (base + phaseC2Off + 12) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_spec_within sp shift v2 shiftMem 172 (base + phaseC2Off)
  exact cpsTripleWithin_extend_code divK_phaseC2_code_sub_divCode_noNop_v5 hbody

/-- v5 phase-C2 (shift ≠ 0): store shift, compute antiShift, BEQ not taken → normB. -/
theorem divK_phaseC2_ntaken_spec_within_v5_noNop (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + normBOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode_noNop_v5_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 (show shift ≠ (0 : Word) from hshift_nz))
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_divCode_noNop_v5 hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

/-- v5 phase-C2 (shift = 0): store shift, compute antiShift, BEQ taken → copyAU
    (skips the normB/normA normalization shifts since no normalization is needed).
    Mirror of `divK_phaseC2_ntaken_spec_within_v5_noNop` with the taken branch;
    first brick of the v5 n=1 shift=0 preloop.  Bead `evm-asm-wbc4i.9.1`. -/
theorem divK_phaseC2_taken_spec_within_v5_noNop (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + copyAUOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode_noNop_v5_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_divCode_noNop_v5 hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

end EvmAsm.Evm64
