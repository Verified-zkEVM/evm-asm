/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCall

  Extracted from `LoopBody.lean` (Section 11b).

  `divK_trial_call_full_spec_within`: full trial-quotient call path —
  save j + trial load + BLTU taken + JAL + div128 — composing into a
  single base+448 → base+516 spec when `uHi < vTop`. Used by every
  `LoopBodyN{1..4}.lean` and `LoopIterN1.{Call,CallBeq}`.

  Also defines the `@[irreducible]` bundled postcondition
  `divKTrialCallFullPost` that callers see opaque (with a documented
  `unfold` at use sites).

  Uses public helpers from `LoopBody.lean`:
  - `lb_sub`, `lb_bltu_taken`, `lb_bltu_ntaken` (now public, made
    non-`private` for this split).
  - `divK_save_trial_load_spec_within`, `divK_trial_call_path_spec_within`.
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCallPath
import EvmAsm.Evm64.DivMod.LoopBody.TrialMax

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 11b: Trial quotient call path (BLTU taken): save + load + BLTU + JAL + div128
-- When uHi < vTop, calls div128 to compute the trial quotient.
-- Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base.
-- ============================================================================

/-- Bundled postcondition for `divK_trial_call_full_spec_within` (#1139). Inlines
    the 30+ let chain so xperm / seqFrame see all atoms in one flat sepConj
    when bridging. Marked `@[irreducible]` so the theorem *signature* hides
    the bundle from consumers; call-sites that need per-limb atoms must
    `unfold divKTrialCallFullPost at TF` after invoking the spec. -/
@[irreducible]
def divKTrialCallFullPost (sp j n uHi uLo vTop base : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0Div := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0Div
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0Div
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ x1Exit) **
  (.x5 ↦ᵣ q0') ** (.x6 ↦ᵣ dHi) **
  (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1') ** (.x11 ↦ᵣ q) **
  (.x2 ↦ᵣ (base + 516)) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ vTop) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0Div)

/-- Trial quotient call path: save j + load + BLTU taken + JAL + div128.
    When uHi < vTop, computes qHat = div128(uHi, uLo, vTop).
    Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base. -/
theorem divK_trial_call_full_spec_within
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 66 (base + loopBodyOff) (base + 516) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem))
      (divKTrialCallFullPost sp j n uHi uLo vTop base) := by
  intro uAddr vtopBase
  -- Define the same lets locally so the proof body (unchanged from before
  -- bundling) can still reference q0', x1Exit, x7Exit, etc. by name. The
  -- goal's post stays `divKTrialCallFullPost ...` (opaque) throughout the
  -- intermediate `seqFrame` steps — keeping it opaque is what avoids the
  -- `maxRecDepth` blowup a naive `unfold`-at-start would hit.
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0Div := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0Div
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0Div
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  -- 1. Save j + trial load (base+448 → base+500)
  have STL := divK_save_trial_load_spec_within sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop
    base
  dsimp only [] at STL
  -- 2. BLTU x7 x10 12 at base+500
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + 500)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  -- Eliminate ntaken path (⌜¬BitVec.ult uHi vTop⌝ contradicts hbltu)
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  -- Strip pure fact from taken postcondition
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  -- 3. Trial call path (base+512 → base+516)
  have TCP := divK_trial_call_path_spec_within sp j uLo uHi vTop vtopBase base
    v2Old v11Old retMem dMem dloMem un0Mem
    halign
  unfold div128SpecPost at TCP
  -- 4. Frame save_trial_load with x2, x11, x0, scratch memory
  have STLf := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
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
  -- 5. Compose save_trial_load + BLTU taken
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  -- 6. Compose (save_trial_load + BLTU) + trial_call_path
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_clean TCPf
  -- 7. Final permutation — unfold the bundled post so xperm sees all atoms.
  unfold divKTrialCallFullPost
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

end EvmAsm.Evm64
