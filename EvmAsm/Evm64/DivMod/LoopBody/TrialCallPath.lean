/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallPath

  Extracted from `LoopBody.lean` (Section 8b).

  `divK_trial_call_path_spec`: trial-quotient TAKEN path (uHi < vTop) —
  JAL x2 560 (instr [16]) at base+512 + div128 subroutine, returning
  to base+516 with x11 = q.

  Address-normalization helpers `lb_jal_target` / `lb_jal_ret` move
  here from `LoopBody.lean` (they were private and only used by this
  spec).

  Uses public helpers from `LoopBody.lean`:
  - `lb_sub`
-/

import EvmAsm.Evm64.DivMod.LoopBody

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem lb_jal_target {base : Word} : (base + 512 : Word) + signExtend21 (560 : BitVec 21) = base + div128Off := by
  rv64_addr
private theorem lb_jal_ret {base : Word} : (base + 512 : Word) + 4 = base + 516 := by bv_addr

/-- Trial call path: JAL x2 560 (instr [16]) + div128 subroutine.
    Entry: base+512, Exit: base+516, CodeReq: sharedDivModCode base.
    Computes qHat = div128(uHi, uLo, vTop). -/
theorem divK_trial_call_path_spec
    (sp j uLo uHi vTop vtopBase : Word) (base : Word)
    (v2Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516) :
    cpsTriple (base + 512) (base + 516) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (.x2 ↦ᵣ v2Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem))
      (div128SpecPost sp (base + 516) vTop uLo uHi) := by
  -- Reuse the bundled `div128SpecPost` from `Compose/Div128.lean`. The
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
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  -- 1. JAL x2 560 at base+512: x2 ← base+516, PC → base+1072
  have J := jal_spec .x2 v2Old (560 : BitVec 21) (base + 512) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTriple_extend_code (hmono :=
    lb_sub 16 _ _ (by decide) (by bv_addr) (by decide)) J
  -- 2. div128 subroutine: base+1072 → base+516
  have D := div128_spec sp (base + 516) vTop uLo uHi base
    j vtopBase v11Old retMem dMem dloMem un0Mem
    halign
  unfold div128SpecPost at D
  -- 3. Frame JAL with all registers/memory for div128
  have Jf := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) Je
  -- 4. Compose JAL + div128
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf D
  -- 5. Final permutation
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

end EvmAsm.Evm64
