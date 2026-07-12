/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5

  v5 trial-quotient call path, pre-call half: save-j + trial-load over the
  **v5** loop-body code (`sharedDivModCodeNoNop_v5`).

  This is the v5 analog of the private `divK_save_trial_load_v4_spec_within_noNop`
  (TrialCall.lean).  The instructions executed here (save the current `j`, load
  the trial-window limbs `uHi`/`uLo`/`vTop` into registers) are IDENTICAL in v4
  and v5 — only the later `div128` subroutine differs — so the proof is a
  mechanical mirror, swapping the loop-body code-subsumption lemma
  `lb_sub_noNop_v4` → `lb_sub_noNop_v5` and the code surface
  `sharedDivModCodeNoNop_v4` → `_v5`.  The underlying single-instruction specs
  (`divK_save_j_spec_within`, `divK_trial_load_spec_within`) are version-agnostic.

  This is the first brick of the v5 n=1 loop-body execution layer (bead
  `evm-asm-wbc4i.7.2`): it feeds `divK_trial_call_full_v5` (next), which composes
  it with the BLTU taken-path and the existing v5 trial-call-path
  (`divK_trial_call_path_v5_spec_within_noNop_exact_x1`, #7210).
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallPath
import EvmAsm.Evm64.DivMod.Compose.V5Code
import EvmAsm.Evm64.DivMod.Compose.Div128V5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 save-j + trial-load over `sharedDivModCodeNoNop_v5`.  Mechanical mirror of
    `divK_save_trial_load_v4_spec_within_noNop` with the v5 code subsumption. -/
theorem divK_save_trial_load_v5_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 13 (base + loopBodyOff) (base + trialCallOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
       (sp + signExtend12 3976 ↦ₘ jOld) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
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
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

/-- v5 trial-quotient call full post.  Unlike `divKTrialCallFullPostV4` (which
    names the exit register values via reducible `divKTrialCallV4*` defs), the v5
    trial defs are `@[irreducible]` and the `div128_v5` post (`div128V5SpecPost`)
    is stated with raw `let`-bindings — so we reuse `div128V5SpecPost` directly
    and add the trial-load frame.  The bridge to `divKTrialCallV5QHat` /
    `div128Quot_v5` is supplied separately by the existing v5 trial-bound
    lemmas. -/
def divKTrialCallFullPostV5 (sp j n uHi uLo vTop base scratchMem : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  div128V5SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
  regOwn .x1 **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop)

/-- v5 trial-quotient call full path over `sharedDivModCodeNoNop_v5`: save-j +
    trial-load + BLTU taken + JAL + `divK_div128_v5`.  Mirror of
    `divK_trial_call_full_v4_spec_within_noNop`, composing the v5 save-trial-load
    (above) with the existing v5 trial-call-path (#7210).  Brick 3 of the v5 n=1
    loop-body execution layer (bead `evm-asm-wbc4i.7.2`). -/
theorem divK_trial_call_full_v5_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 98 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (divKTrialCallFullPostV5 sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  have STL := divK_save_trial_load_v5_spec_within_noNop
    sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop base
  dsimp only [] at STL
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v5 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  have TCP := divK_trial_call_path_v5_spec_within_noNop_exact_x1
    sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) taken_clean
  have TCPf := cpsTripleWithin_frameR
    ((sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TCP
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  have STLf_taken_scratch := cpsTripleWithin_frameR
    (sp + signExtend12 3936 ↦ₘ scratchMem)
    (by pcFree) STLf_taken_clean
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_scratch TCPf
  unfold divKTrialCallFullPostV5
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

end EvmAsm.Evm64
