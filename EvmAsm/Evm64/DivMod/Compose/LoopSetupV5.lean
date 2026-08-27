/-
  EvmAsm.Evm64.DivMod.Compose.LoopSetupV5

  v5 loop-setup brick: the BLT-not-taken fall-through into the loop body, over
  `divCode_noNop_v5`.  Mirror of `divK_loopSetup_ntaken_spec_within_v4_noNop`
  (NormA.lean) — the loop-setup instructions do not touch div128, so the same
  version-agnostic instruction bodies are extended to the v5 code via the v5 block
  subsumption `sharedNoNop_v5_b7_div`.  First brick of the v5 n=1 preloop
  (toward the n=1 lane wrapper).  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.NormA
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The loop-setup block instructions are subsumed by `divCode_noNop_v5`. -/
private theorem divK_loopSetup_code_sub_divCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_loopSetup_code 464 (base + loopSetupOff)) a = some i →
      (divCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b7_div a i h

/-- BLT singleton at base+loopSetupOff+12 is subsumed by `divCode_noNop_v5`. -/
private theorem blt_loopSetup_sub_divCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + loopSetupOff + 12) (.BLT .x9 .x0 464)) a = some i →
      (divCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + loopSetupOff) (divK_loopSetup 464) 3
    (by decide) (by decide)
  rw [show (BitVec.ofNat 64 (4 * 3) : Word) = (12 : Word) from by decide] at hlookup
  exact divK_loopSetup_code_sub_divCode_noNop_v5 a i
    (CodeReq.singleton_mono hlookup a i h)

/-- LoopSetup (m ≥ 0, n ≤ 4): falls through to the loop body, over
    `divCode_noNop_v5`.  Mirror of the v4 analog. -/
theorem divK_loopSetup_ntaken_spec_within_v5_noNop (sp n v1 v5 : Word) (base : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTripleWithin 4 (base + loopSetupOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (divKLoopSetupNtakenPreNoNop sp v5 v1 n)
      (divKLoopSetupNtakenPostNoNop sp n m) := by
  intro m
  rw [divKLoopSetupNtakenPreNoNop_unfold, divKLoopSetupNtakenPostNoNop_unfold]
  have hbody := divK_loopSetup_body_spec_within sp n v1 v5 464 (base + loopSetupOff)
  have hbodye := cpsTripleWithin_extend_code divK_loopSetup_code_sub_divCode_noNop_v5 hbody
  have hblt_raw := blt_spec_gen_within .x9 .x0 464 m (0 : Word) (base + loopSetupOff + 12)
  rw [show (base + loopSetupOff + 12 : Word) + signExtend13 464 = base + denormOff from by rv64_addr,
      show (base + loopSetupOff + 12 : Word) + 4 = base + loopBodyOff from by bv_addr] at hblt_raw
  have hblt_clean := cpsBranchWithin_ntakenStripPure2 hblt_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hm_ge)
  have hblte := cpsTripleWithin_extend_code blt_loopSetup_sub_divCode_noNop_v5 hblt_clean
  have hbltef := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

end EvmAsm.Evm64
