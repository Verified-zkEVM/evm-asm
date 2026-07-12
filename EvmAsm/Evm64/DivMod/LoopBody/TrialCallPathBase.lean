/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallPathBase

  Extracted from `LoopBody.lean` (Section 8b).

  `divK_trial_call_path_spec_within`: trial-quotient TAKEN path (uHi < vTop) —
  JAL x2 560 (instr [16]) at base+512 + div128 subroutine, returning
  to base+516 with x11 = q.

  Address-normalization helpers `lb_jal_target` / `lb_jal_ret` move
  here from `LoopBody.lean` (they were private and only used by this
  spec).

  Uses public helpers from `LoopBody.lean`:
  - `lb_sub`
-/

import EvmAsm.Evm64.DivMod.LoopBody
import EvmAsm.Evm64.DivMod.Compose.Div128
import EvmAsm.Evm64.DivMod.Compose.Div128V4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem lb_jal_target {base : Word} : (base + trialJalOff : Word) + signExtend21 (560 : BitVec 21) = base + div128Off := by
  rv64_addr
private theorem lb_jal_ret {base : Word} : (base + trialJalOff : Word) + 4 = base + div128CallRetOff := by bv_addr

/-- Trial call path: JAL x2 560 (instr [16]) + div128 subroutine.
    Entry: base+512, Exit: base+516, CodeReq: sharedDivModCode base.
    Computes qHat = div128(uHi, uLo, vTop). -/
theorem divK_trial_call_path_spec_within_exact_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 52 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCode base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem)) ** (.x1 ↦ᵣ v1Old))
      (div128SpecPost sp (base + div128CallRetOff) vTop uLo uHi ** regOwn .x1) := by
  -- Reuse the bundled `div128SpecPost` from `Compose/Div128Post.lean`. The
  -- post atoms here are identical to div128's (with retAddr ↦ base+516,
  -- d ↦ vTop) — just a permutation that the final `xperm_hyp` handles.
  -- Re-introduce the lets so the proof body can reference q1', q0', etc.
  -- by name.
  unfold div128SpecPost
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
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
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x9Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  -- 1. JAL x2 560 at base+512: x2 ← base+516, PC → base+1072
  have J := jal_spec_within .x2 v2Old (560 : BitVec 21) (base + trialJalOff) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTripleWithin_extend_code (hmono :=
    lb_sub 16 _ _ (by decide) (by bv_addr) (by decide)) J
  -- 2. div128 subroutine: base+1072 → base+516
  have D := div128_spec_within sp (base + div128CallRetOff) vTop uLo uHi base
    j vtopBase v11Old retMem dMem dloMem un0Mem
    halign
  unfold div128SpecPost at D
  -- 2b. Frame div128 with x1; div128 uses x9 as its scratch register.
  have Df := cpsTripleWithin_frameR (.x1 ↦ᵣ v1Old) (by pcFree) D
  -- 3. Frame JAL with all registers/memory for div128
  have Jf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) Je
  -- 4. Compose JAL + div128.
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf Df
  -- 5. Final permutation
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      apply sepConj_mono_right (regIs_implies_regOwn .x1) h
      xperm_hyp hq)
    full

/-- Trial call path: JAL x2 560 (instr [16]) + div128 subroutine.
    Entry: base+512, Exit: base+516, CodeReq: sharedDivModCode base.
    Computes qHat = div128(uHi, uLo, vTop), with `x1` existentially owned. -/
theorem divK_trial_call_path_spec_within
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 52 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCode base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem)) ** regOwn .x1)
      (div128SpecPost sp (base + div128CallRetOff) vTop uLo uHi ** regOwn .x1) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  exact divK_trial_call_path_spec_within_exact_x1 sp j uLo uHi vTop vtopBase base
    v1Old v2Old v11Old retMem dMem dloMem un0Mem halign

/-- Trial call path over `sharedDivModCode_v4`: JAL x2 560 (instr [16]) +
    the v4 div128 subroutine, with exact x1 framing and the additional v4
    scratch cell threaded explicitly. -/
theorem divK_trial_call_path_v4_spec_within_exact_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 74 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ v1Old))
      (div128V4SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  have J := jal_spec_within .x2 v2Old (560 : BitVec 21) (base + trialJalOff) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTripleWithin_extend_code (hmono :=
    lb_sub_v4 16 _ _ (by decide) (by bv_addr) (by decide)) J
  have D := div128_v4_spec_shared sp (base + div128CallRetOff) vTop uLo uHi base
    j vtopBase v11Old retMem dMem dloMem un0Mem scratchMem
    halign
  have Df := cpsTripleWithin_frameR (.x1 ↦ᵣ v1Old) (by pcFree) D
  have Jf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) Je
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf Df
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      apply sepConj_mono_right (regIs_implies_regOwn .x1) h
      xperm_hyp hq)
    full

/-- Trial call path over `sharedDivModCode_v4`, with `x1` existentially
    owned. -/
theorem divK_trial_call_path_v4_spec_within
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 74 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (div128V4SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  exact divK_trial_call_path_v4_spec_within_exact_x1
    sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign

/-- Trial call path over `divCode_noNop`: JAL x2 560 (instr [16]) + div128
    subroutine. -/
theorem divK_trial_call_path_spec_within_noNop_exact_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 52 (base + trialJalOff) (base + div128CallRetOff) (divCode_noNop base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem)) ** (.x1 ↦ᵣ v1Old))
      (div128SpecPost sp (base + div128CallRetOff) vTop uLo uHi ** regOwn .x1) := by
  unfold div128SpecPost
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
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
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x9Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  have J := jal_spec_within .x2 v2Old (560 : BitVec 21) (base + trialJalOff) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTripleWithin_extend_code (hmono :=
    lb_sub_noNop 16 _ _ (by decide) (by bv_addr) (by decide)) J
  have D := div128_spec_within_noNop sp (base + div128CallRetOff) vTop uLo uHi base
    j vtopBase v11Old retMem dMem dloMem un0Mem
    halign
  unfold div128SpecPost at D
  have Df := cpsTripleWithin_frameR (.x1 ↦ᵣ v1Old) (by pcFree) D
  have Jf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) Je

  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf Df
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      apply sepConj_mono_right (regIs_implies_regOwn .x1) h
      xperm_hyp hq)
    full

/-- Trial call path over `divCode_noNop`: JAL x2 560 (instr [16]) + div128
    subroutine, with `x1` existentially owned. -/
theorem divK_trial_call_path_spec_within_noNop
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 52 (base + trialJalOff) (base + div128CallRetOff) (divCode_noNop base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem)) ** regOwn .x1)
      (div128SpecPost sp (base + div128CallRetOff) vTop uLo uHi ** regOwn .x1) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  exact divK_trial_call_path_spec_within_noNop_exact_x1 sp j uLo uHi vTop vtopBase base
    v1Old v2Old v11Old retMem dMem dloMem un0Mem halign

/-- Trial call path over `sharedDivModCodeNoNop_v4`: JAL x2 560 (instr [16])
    plus the v4 div128 subroutine, preserving the framed concrete x1 value
    and threading the additional v4 scratch cell explicitly. -/
theorem divK_trial_call_path_v4_spec_within_noNop_preserving_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 74 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ v1Old))
      (div128V4SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        (.x1 ↦ᵣ v1Old)) := by
  have J := jal_spec_within .x2 v2Old (560 : BitVec 21) (base + trialJalOff) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTripleWithin_extend_code (hmono :=
    lb_sub_noNop_v4 16 _ _ (by decide) (by bv_addr) (by decide)) J
  have D := div128_v4_spec_shared_noNop sp (base + div128CallRetOff) vTop uLo uHi base
    j vtopBase v11Old retMem dMem dloMem un0Mem scratchMem
    halign
  have Df := cpsTripleWithin_frameR (.x1 ↦ᵣ v1Old) (by pcFree) D
  have Jf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) Je
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf Df
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

/-- Trial call path over `sharedDivModCodeNoNop_v4`: JAL x2 560 (instr [16])
    plus the v4 div128 subroutine, with exact x1 framing and the additional
    v4 scratch cell threaded explicitly. -/
theorem divK_trial_call_path_v4_spec_within_noNop_exact_x1
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v1Old v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 74 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ v1Old))
      (div128V4SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      apply sepConj_mono_right (regIs_implies_regOwn .x1) h
      xperm_hyp hq)
    (divK_trial_call_path_v4_spec_within_noNop_preserving_x1
      sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
      retMem dMem dloMem un0Mem scratchMem halign)

/-- Trial call path over `sharedDivModCodeNoNop_v4`, with `x1`
    existentially owned. -/
theorem divK_trial_call_path_v4_spec_within_noNop
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin 74 (base + trialJalOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (div128V4SpecPost sp (base + div128CallRetOff) vTop uLo uHi scratchMem **
        regOwn .x1) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  exact divK_trial_call_path_v4_spec_within_noNop_exact_x1
    sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign


end EvmAsm.Evm64
