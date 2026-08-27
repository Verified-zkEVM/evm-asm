/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialMaxV5

  v5 trial-quotient max path over `sharedDivModCodeNoNop_v5`: save j + trial load
  + BLTU not-taken + trial_max.  Mechanical mirror of
  `divK_trial_max_full_v4_spec_within_noNop` (TrialMax.lean), swapping the code
  surface `sharedDivModCodeNoNop_v4` → `_v5` and the subsumption lemma
  `lb_sub_noNop_v4` → `lb_sub_noNop_v5`.  The max path does NOT enter div128 (the
  only v4/v5-differing block), so the proof is otherwise identical.

  Feeds the v5 n=1 max+skip loop bodies (next).  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.TrialMax
public import EvmAsm.Evm64.DivMod.Compose.V5Code

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Trial quotient max path over `sharedDivModCodeNoNop_v5`: save j + load +
    BLTU not-taken + trial_max, when `uHi >= vTop`.  Mirror of the v4 analog. -/
theorem divK_trial_max_full_v5_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old uHi uLo vTop : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 16 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) ** (.x11 ↦ᵣ signExtend12 4095) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro uAddr vtopBase
  have SJ := divK_save_j_spec_within sp j jOld (base + loopBodyOff)
  rw [show (base + loopBodyOff : Word) + 4 = base + (loopBodyOff + 4) from by
    simp [BitVec.add_assoc]] at SJ
  have SJe := cpsTripleWithin_extend_code (hmono :=
    lb_sub_noNop_v5 0 _ _ (by decide) (by bv_addr) (by decide)) SJ
  have SJf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) SJe
  have TL := divK_trial_load_spec_within sp j n v5Old v6Old v7Old v10Old uHi uLo vTop
    (base + (loopBodyOff + 4))
  dsimp only [] at TL
  rw [show (base + (loopBodyOff + 4) : Word) + 48 = base + trialCallOff from by bv_addr] at TL
  have TLe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_noNop_v5 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 8 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 9 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 11 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_noNop_v5 12 _ _ (by decide) (by bv_addr) (by decide))))))))))))) TL
  seqFrame SJf TLe
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v5 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  have ntaken := cpsBranchWithin_ntakenPath hbltu_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hbltu hpure)
  have ntaken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) ntaken
  have TM := divK_trial_max_spec_within v11Old (base + trialMaxOff)
  dsimp only [] at TM
  rw [show (base + trialMaxOff : Word) + 12 = base + div128CallRetOff from by bv_addr] at TM
  have TMe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_noNop_v5 14 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_noNop_v5 15 _ _ (by decide) (by bv_addr) (by decide))) TM
  have STLf := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) SJfTLe
  have ntaken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) ntaken_clean
  have STLfntaken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf ntaken_framed
  have TMf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TMe
  have STLfntaken_cleanTM := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLfntaken_clean TMf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    STLfntaken_cleanTM

end EvmAsm.Evm64
