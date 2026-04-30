/-
  EvmAsm.Evm64.DivMod.Compose.FullPath

  Full path merging: compose PhaseAB → CLZ → PhaseC2 → NormB → NormA → LoopSetup
  into end-to-end specs for the b≠0 non-zero path.

  Start with the n=4 (b[3]≠0, shift≠0) case as the primary composition.
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseAB
import EvmAsm.Evm64.DivMod.Compose.CLZ
import EvmAsm.Evm64.DivMod.Compose.Norm
import EvmAsm.Evm64.DivMod.Compose.NormA
import EvmAsm.Evm64.DivMod.Compose.Epilogue
import EvmAsm.Evm64.DivMod.Compose.ModEpilogue

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Phase AB(n=4) → CLZ composition: base → base+212
-- ============================================================================

/-- PhaseAB(n=4) + CLZ: b≠0, b[3]≠0.
    base → base+212. After CLZ, x6 = shift count, x5 = shifted leading limb. -/
theorem evm_div_phaseAB_n4_clz_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    cpsTriple base (base + phaseC2Off) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b3).1) ** (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  -- Phase AB(n=4): base → base+116
  have hAB := evm_div_phaseAB_n4_spec sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz
  -- CLZ: base+116 → base+212, needs x5=b3 (leading limb), x6=b1, x7=b2
  have hCLZ := divK_clz_spec b3 b1 b2 base
  -- Frame CLZ with x12, x10, and all memory atoms
  have hCLZf := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hCLZ
  -- Compose AB → CLZ
  have hABCLZ := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hCLZf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABCLZ

-- ============================================================================
-- PhaseAB(n=4) → CLZ → PhaseC2(ntaken) → NormB: base → base+312
-- ============================================================================

/-- PhaseAB(n=4) + CLZ + PhaseC2(shift≠0) + NormB: full normalization path.
    base → base+312. b[0..3] normalized in-place. -/
theorem evm_div_n4_to_normB_spec (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTriple base (base + normAOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (normBPost sp (4 : Word) (clzResult b3).1 b0 b1 b2 b3) := by
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  -- Step 1: PhaseAB(n=4) + CLZ (base → base+212)
  have hABCLZ := evm_div_phaseAB_n4_clz_spec sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz
  -- Frame AB+CLZ with x2 and shiftMem (not touched by AB or CLZ)
  have hABCLZf := cpsTriple_frameR
    ((.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  -- Step 2: PhaseC2 ntaken (base+212 → base+228)
  -- shift = (clzResult b3).1, need shift ≠ 0
  have hC2 := divK_phaseC2_ntaken_spec sp shift ((clzResult b3).2 >>> (63 : Nat))
    shiftMem base hshift_nz
  -- Frame C2 with x5, x10, and all other memory
  have hC2f := cpsTriple_frameR
    ((.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hC2
  -- Compose AB+CLZ → C2
  have hABC2 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  -- Step 3: NormB (base+228 → base+312)
  have hNB := divK_normB_full_spec sp b0 b1 b2 b3
    (clzResult b3).2 ((clzResult b3).2 >>> (63 : Nat))
    shift antiShift base
  intro_lets at hNB
  -- Frame NormB with x10, x0, and non-b[] memory
  have hNBf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  -- Compose AB+CLZ+C2 → NormB
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2 hNBf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta normBPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- Full n=4 path to LoopSetup: base → base+448
-- Composes: PhaseAB → CLZ → PhaseC2(ntaken) → NormB → NormA → LoopSetup(ntaken)
-- ============================================================================

/-- Full n=4 path from entry to loop body start (shift ≠ 0 case).
    base → base+448. Normalizes b[] and a[], sets up loop parameters. -/
theorem evm_div_n4_to_loopSetup_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    cpsTriple base (base + loopBodyOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (loopSetupPost sp (4 : Word) (clzResult b3).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  -- Step 1: PhaseAB(n=4) + CLZ + PhaseC2 + NormB (base → base+312)
  have hNormB := evm_div_n4_to_normB_spec sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3nz hshift_nz

  -- Frame NormB result with a[], u[] scratch, x1
  have hNormBf := cpsTriple_frameR
    ((.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hNormB
  -- Step 2: NormA (base+312 → base+432)
  have hNormA := divK_normA_full_spec sp a0 a1 a2 a3
    b0' (b0 >>> (antiShift.toNat % 64)) b3 shift antiShift
    u0Old u1Old u2Old u3Old u4Old base
  intro_lets at hNormA
  -- Frame NormA with x0, b[], scratch q/u5-7/n/shift
  have hNormAf := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNormA
  -- Compose NormB → NormA
  have hNA := cpsTriple_seq_perm_same_cr
    (fun h hp => by delta normBPost at hp; xperm_hyp hp) hNormBf hNormAf
  -- Step 3: LoopSetup ntaken (base+432 → base+448)
  -- For n=4: m = signExtend12(4) - 4 = 0, so BLT 0 < 0 is false → ntaken
  have hLS := divK_loopSetup_ntaken_spec sp (4 : Word)
    (signExtend12 (4 : BitVec 12) - (4 : Word)) u1 base
    (by decide)
  -- Frame LoopSetup with everything except x5, x1, x0 + nMem
  have hLSf := cpsTriple_frameR
    ((.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
     (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLS
  -- Compose (through NormA) → LoopSetup
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hNA hLSf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta loopSetupPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- Full n=4 path to LoopSetup (shift = 0 case): base → base+448
-- Composes: PhaseAB → CLZ → PhaseC2(taken) → CopyAU → LoopSetup(ntaken)
-- Skips NormB/NormA since b[] is already normalized when shift=0.
-- ============================================================================

/-- Full n=4 path from entry to loop body start (shift = 0 case).
    base → base+448. b[] already normalized, u[] = copy of a[]. -/
theorem evm_div_n4_shift0_to_loopSetup_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0) :
    cpsTriple base (base + loopBodyOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b3).1) ** (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ signExtend12 (0 : BitVec 12) - (clzResult b3).1) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1)) := by
  -- Step 1: PhaseAB(n=4) + CLZ (base → base+212)
  have hABCLZ := evm_div_phaseAB_n4_clz_spec sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz
  -- Frame AB+CLZ with x2, x1, a[], u[0..4], shiftMem
  have hABCLZf := cpsTriple_frameR
    ((.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  -- Step 2: PhaseC2 taken (base+212 → base+396), shift = 0
  have hC2 := divK_phaseC2_taken_spec sp ((clzResult b3).1)
    ((clzResult b3).2 >>> (63 : Nat)) shiftMem base hshift_z
  -- Frame C2 with everything not in C2's assertion
  have hC2f := cpsTriple_frameR
    ((.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hC2
  -- Compose AB+CLZ → C2
  have hABC2 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  -- Step 3: CopyAU (base+396 → base+432)
  have hCopy := divK_copyAU_full_spec sp a0 a1 a2 a3
    u0Old u1Old u2Old u3Old u4Old ((clzResult b3).2) base

  -- Normalize signExtend12 0 → 0 in CopyAU spec for xperm matching
  simp only [EvmAsm.Evm64.DivMod.AddrNorm.se12_0] at hCopy
  -- Frame CopyAU with registers and memory not in CopyAU
  have hCopyf := cpsTriple_frameR
    ((.x6 ↦ᵣ (clzResult b3).1) **
     (.x2 ↦ᵣ signExtend12 (0 : BitVec 12) - (clzResult b3).1) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hCopy
  -- Compose → CopyAU
  have hABC2C := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2 hCopyf
  -- Step 4: LoopSetup ntaken (base+432 → base+448)
  -- For n=4: m = signExtend12(4) - 4, BLT 0 < 0 is false → ntaken
  have hLS := divK_loopSetup_ntaken_spec sp (4 : Word)
    (signExtend12 (4 : BitVec 12) - (4 : Word)) a3 base
    (by decide)
  -- Frame LoopSetup
  have hLSf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) **
     (.x6 ↦ᵣ (clzResult b3).1) **
     (.x2 ↦ᵣ signExtend12 (0 : BitVec 12) - (clzResult b3).1) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
     ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hLS
  -- Compose all → LoopSetup
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2C hLSf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

-- ============================================================================
-- Post-loop chain: Denorm → DIV Epilogue (base+916 → base+1068)
-- Denormalize u[] then load q[] to output.
-- ============================================================================

/-- Post-loop chain for DIV: denormalize u[], then load q[] to output.
    base+916 → base+1068. Shift ≠ 0 case (denorm body executed). -/
theorem evm_div_denorm_epilogue_spec (sp base : Word)
    (u0 u1 u2 u3 v2 v5 v7 v10 shift : Word)
    (q0 q1 q2 q3 m0 m8 m16 m24 : Word) :
    cpsTriple (base + 916) (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3) := by
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  -- Step 1: Denorm body (base+916 → base+1008)
  have hDenorm := divK_denorm_body_spec sp u0 u1 u2 u3 v2 v5 v7 shift base

  intro_lets at hDenorm
  -- Frame denorm with x10, q[], output memory
  have hDenormF := cpsTriple_frameR
    ((.x10 ↦ᵣ v10) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hDenorm
  -- Step 2: DIV epilogue (base+1008 → base+1068)
  -- After denorm: x5=u3', x6=shift, x7=(u3<<<antiShift%64), x10=v10
  have hEpi := divK_div_epilogue_spec sp base q0 q1 q2 q3
    u3' shift (u3 <<< (antiShift.toNat % 64)) v10 m0 m8 m16 m24

  -- Frame epilogue with x2, x0, u'[]
  have hEpiF := cpsTriple_frameR
    ((.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
     ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3'))
    (by pcFree) hEpi
  -- Compose denorm → epilogue
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hDenormF hEpiF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta denormDivPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- Post-loop chain: Denorm → MOD Epilogue (base+916 → base+1068)
-- Denormalize u[] then load u'[] (remainder) to output.
-- ============================================================================

/-- Post-loop chain for MOD: denormalize u[], then load u'[] to output.
    base+916 → base+1068. Shift ≠ 0 case (denorm body executed). -/
theorem evm_mod_denorm_epilogue_spec (sp base : Word)
    (u0 u1 u2 u3 v2 v5 v7 v10 shift : Word)
    (m0 m8 m16 m24 : Word) :
    cpsTriple (base + 916) (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormModPost sp shift u0 u1 u2 u3) := by
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  -- Step 1: Denorm body (base+916 → base+1008, modCode)
  have hDenorm := mod_denorm_body_spec sp u0 u1 u2 u3 v2 v5 v7 shift base

  intro_lets at hDenorm
  -- Frame denorm with x10, output memory
  have hDenormF := cpsTriple_frameR
    ((.x10 ↦ᵣ v10) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hDenorm
  -- Step 2: MOD epilogue (base+1008 → base+1068, modCode)
  -- After denorm: x5=u3', x6=shift, x7=(u3<<<antiShift%64), x10=v10
  -- Epilogue loads u'[] from 4056..4032 (the denormalized values)
  have hEpi := divK_mod_epilogue_spec sp base u0' u1' u2' u3'
    u3' shift (u3 <<< (antiShift.toNat % 64)) v10 m0 m8 m16 m24

  -- Frame epilogue with x2, x0
  have hEpiF := cpsTriple_frameR
    ((.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hEpi
  -- Compose denorm → epilogue
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hDenormF hEpiF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta denormModPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- Post-loop chain with preamble: Preamble → Denorm → DIV Epilogue (base+908 → base+1068)
-- Loads shift from memory, denormalizes u[], then loads q[] to output.
-- ============================================================================

/-- Post-loop chain for DIV with preamble: loads shift, denormalizes u[], outputs q[].
    base+908 → base+1068. Shift ≠ 0 case. -/
theorem evm_div_preamble_denorm_epilogue_spec (sp base : Word)
    (u0 u1 u2 u3 shift v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 m0 m8 m16 m24 : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTriple (base + denormOff) (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3 **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  -- Step 1: Preamble (base+908 → base+916)
  have hPre := divK_denorm_preamble_spec sp shift v5 v6 v7 v2 v10 base hshift_nz
  -- Frame preamble with u[], q[], output memory
  have hPreF := cpsTriple_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  -- Step 2: Denorm + Epilogue (base+916 → base+1068)
  have hDE := evm_div_denorm_epilogue_spec sp base u0 u1 u2 u3 v2 v5 v7 v10 shift
    q0 q1 q2 q3 m0 m8 m16 m24
  -- Frame epilogue with shiftMem
  have hDEF := cpsTriple_frameR
    (((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hDE
  -- Compose preamble → denorm+epilogue
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hDEF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

-- ============================================================================
-- MOD Denorm preamble: LD shift + BEQ (base+908 → base+916) with modCode
-- Same instructions as divK_denorm_preamble_spec, but proved against modCode.
-- ============================================================================

/-- Denorm code (block 9) is subsumed by modCode.
    Re-proved here because the version in ModEpilogue.lean is private. -/
private theorem divK_denorm_code_sub_modCode' (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + denormOff) divK_denorm) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Denorm preamble for shift≠0 with modCode: LD shift from memory + BEQ not taken.
    base+908 → base+916. -/
theorem mod_denorm_preamble_spec (sp shift v5 v6 v7 v2 v10 : Word) (base : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTriple (base + denormOff) (base + 916) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  -- 1. LD x6 x12 3992 at base+908 (denorm instr [0])
  have hld := ld_spec_gen .x6 .x12 sp v6 shift (3992 : BitVec 12) (base + denormOff) (by nofun)
  rw [show (base + denormOff : Word) + 4 = base + 912 from by bv_addr] at hld
  have hlde := cpsTriple_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_modCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff) divK_denorm
        [.LD .x6 .x12 3992] 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hld
  -- 2. BEQ x6 x0 96 at base+912 (denorm instr [1])
  have hbeq := beq_spec_gen .x6 .x0 (96 : BitVec 13) shift (0 : Word) (base + 912)
  rw [show (base + 912 : Word) + signExtend13 (96 : BitVec 13) = base + epilogueOff from by rv64_addr,
      show (base + 912 : Word) + 4 = base + 916 from by bv_addr] at hbeq
  have hbeqe := cpsBranch_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_modCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 912) divK_denorm
        [.BEQ .x6 .x0 96] 1 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hbeq
  -- 3. Eliminate taken branch: shift ≠ 0 means BEQ not taken
  have hbeq_exit := cpsBranch_ntakenPath hbeqe
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
      exact hshift_nz hpure)
  have hbeq_clean := cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbeq_exit
  -- 4. Frame LD with x0, x5, x7, x2, x10
  have hldf := cpsTriple_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10))
    (by pcFree) hlde
  -- 5. Frame BEQ exit with x12, x5, x7, x2, x10, shiftMem
  have hbeqf := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq_clean
  -- 6. Compose LD → BEQ exit
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hldf hbeqf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

-- ============================================================================
-- Post-loop chain with preamble: Preamble → Denorm → MOD Epilogue (base+908 → base+1068)
-- Loads shift from memory, denormalizes u[], then loads u'[] (remainder) to output.
-- ============================================================================

/-- Post-loop chain for MOD with preamble: loads shift, denormalizes u[], outputs u'[] (remainder).
    base+908 → base+1068. Shift ≠ 0 case. -/
theorem evm_mod_preamble_denorm_epilogue_spec (sp base : Word)
    (u0 u1 u2 u3 shift v2 v5 v6 v7 v10 : Word)
    (m0 m8 m16 m24 : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTriple (base + denormOff) (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      (denormModPost sp shift u0 u1 u2 u3 **
       ((sp + signExtend12 3992) ↦ₘ shift)) := by
  -- Step 1: Preamble (base+908 → base+916)
  have hPre := mod_denorm_preamble_spec sp shift v5 v6 v7 v2 v10 base hshift_nz
  -- Frame preamble with u[], output memory
  have hPreF := cpsTriple_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  -- Step 2: Denorm + MOD Epilogue (base+916 → base+1068)
  have hDE := evm_mod_denorm_epilogue_spec sp base u0 u1 u2 u3 v2 v5 v7 v10 shift
    m0 m8 m16 m24
  -- Frame epilogue with shiftMem
  have hDEF := cpsTriple_frameR
    (((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hDE
  -- Compose preamble → denorm+epilogue
  have hFull := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hDEF
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

-- ============================================================================
-- Denorm code subsumption for divCode (re-proved here since private in Epilogue)
-- ============================================================================

/-- Denorm code (block 9) is subsumed by divCode.
    Re-proved here because the version in Epilogue.lean is private. -/
private theorem divK_denorm_code_sub_divCode' (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + denormOff) divK_denorm) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

-- ============================================================================
-- DIV shift=0 post-loop: Preamble (LD+BEQ taken) → DIV Epilogue (base+908 → base+1068)
-- When shift=0, BEQ is taken, skipping denorm body directly to epilogue at base+1008.
-- ============================================================================

/-- DIV shift=0 post-loop: LD shift + BEQ taken → DIV epilogue.
    base+908 → base+1068. Shift = 0 case (denorm body skipped). -/
theorem evm_div_shift0_epilogue_spec_within (sp base : Word)
    (_u0 _u1 _u2 _u3 shift v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 m0 m8 m16 m24 : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 12 (base + denormOff) (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
       ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) := by
  -- 1. LD x6 x12 3992 at base+908 (denorm instr [0])
  have hld := ld_spec_gen_within .x6 .x12 sp v6 shift (3992 : BitVec 12) (base + denormOff) (by nofun)
  rw [show (base + denormOff : Word) + 4 = base + 912 from by bv_addr] at hld
  have hlde := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_divCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff) divK_denorm
        [.LD .x6 .x12 3992] 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hld
  -- 2. BEQ x6 x0 96 at base+912 (denorm instr [1])
  have hbeq := beq_spec_gen_within .x6 .x0 (96 : BitVec 13) shift (0 : Word) (base + 912)
  rw [show (base + 912 : Word) + signExtend13 (96 : BitVec 13) = base + epilogueOff from by rv64_addr,
      show (base + 912 : Word) + 4 = base + 916 from by bv_addr] at hbeq
  have hbeqe := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_divCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 912) divK_denorm
        [.BEQ .x6 .x0 96] 1 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hbeq
  -- 3. Eliminate not-taken branch: shift = 0 means BEQ taken
  --    BEQ not-taken postcondition: (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ 0) ** ⌜shift ≠ 0⌝
  have hbeq_exit := cpsBranchWithin_takenStripPure2 hbeqe
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  -- 4. Frame LD with x0, x5, x7, x2, x10
  have hldf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10))
    (by pcFree) hlde
  -- 5. Frame BEQ taken with x12, x5, x7, x2, x10, shiftMem
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq_exit
  -- 6. Compose LD → BEQ taken: base+908 → base+1008
  have hPre := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hldf hbeqf
  -- Frame preamble with q[], output memory
  have hPreF := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  -- 7. DIV epilogue (base+1008 → base+1068)
  have hEpi := divK_div_epilogue_spec_within sp base q0 q1 q2 q3
    v5 shift v7 v10 m0 m8 m16 m24

  -- Frame epilogue with x2, x0, shiftMem
  have hEpiF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hEpi
  -- 8. Compose preamble → epilogue: base+908 → base+1068
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hEpiF
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

/-- Compatibility wrapper: forget the explicit step bound. -/
def evm_div_shift0_epilogue_spec := fun sp base
    _u0 _u1 _u2 _u3 shift v2 v5 v6 v7 v10
    q0 q1 q2 q3 m0 m8 m16 m24
    hshift_z =>
  (evm_div_shift0_epilogue_spec_within sp base
    _u0 _u1 _u2 _u3 shift v2 v5 v6 v7 v10
    q0 q1 q2 q3 m0 m8 m16 m24 hshift_z).to_cpsTriple

-- ============================================================================
-- MOD shift=0 post-loop: Preamble (LD+BEQ taken) → MOD Epilogue (base+908 → base+1068)
-- When shift=0, BEQ is taken, skipping denorm body directly to epilogue at base+1008.
-- ============================================================================

/-- MOD shift=0 post-loop: LD shift + BEQ taken → MOD epilogue.
    base+908 → base+1068. Shift = 0 case (denorm body skipped). -/
theorem evm_mod_shift0_epilogue_spec_within (sp base : Word)
    (u0 u1 u2 u3 shift v2 v5 v6 v7 v10 : Word)
    (m0 m8 m16 m24 : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 12 (base + denormOff) (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ u1) ** (.x7 ↦ᵣ u2) **
       (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ u3) **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ u0) ** ((sp + 40) ↦ₘ u1) **
       ((sp + 48) ↦ₘ u2) ** ((sp + 56) ↦ₘ u3)) := by
  -- 1. LD x6 x12 3992 at base+908 (denorm instr [0])
  have hld := ld_spec_gen_within .x6 .x12 sp v6 shift (3992 : BitVec 12) (base + denormOff) (by nofun)
  rw [show (base + denormOff : Word) + 4 = base + 912 from by bv_addr] at hld
  have hlde := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_modCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + denormOff) divK_denorm
        [.LD .x6 .x12 3992] 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hld
  -- 2. BEQ x6 x0 96 at base+912 (denorm instr [1])
  have hbeq := beq_spec_gen_within .x6 .x0 (96 : BitVec 13) shift (0 : Word) (base + 912)
  rw [show (base + 912 : Word) + signExtend13 (96 : BitVec 13) = base + epilogueOff from by rv64_addr,
      show (base + 912 : Word) + 4 = base + 916 from by bv_addr] at hbeq
  have hbeqe := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact divK_denorm_code_sub_modCode' base a i
      (CodeReq.ofProg_mono_sub (base + denormOff) (base + 912) divK_denorm
        [.BEQ .x6 .x0 96] 1 (by bv_addr) (by decide) (by decide) (by decide) a i h)) hbeq
  -- 3. Eliminate not-taken branch: shift = 0 means BEQ taken
  --    BEQ not-taken postcondition: (.x6 ↦ᵣ shift) ** (.x0 ↦ᵣ 0) ** ⌜shift ≠ 0⌝
  have hbeq_exit := cpsBranchWithin_takenStripPure2 hbeqe
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  -- 4. Frame LD with x0, x5, x7, x2, x10
  have hldf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10))
    (by pcFree) hlde
  -- 5. Frame BEQ taken with x12, x5, x7, x2, x10, shiftMem
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq_exit
  -- 6. Compose LD → BEQ taken: base+908 → base+1008
  have hPre := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hldf hbeqf
  -- Frame preamble with u[], output memory
  have hPreF := cpsTripleWithin_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
     ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hPre
  -- 7. MOD epilogue (base+1008 → base+1068)
  have hEpi := divK_mod_epilogue_spec_within sp base u0 u1 u2 u3
    v5 shift v7 v10 m0 m8 m16 m24

  -- Frame epilogue with x2, x0, shiftMem
  have hEpiF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hEpi
  -- 8. Compose preamble → epilogue: base+908 → base+1068
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPreF hEpiF
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

/-- Compatibility wrapper: forget the explicit step bound. -/
def evm_mod_shift0_epilogue_spec := fun sp base
    u0 u1 u2 u3 shift v2 v5 v6 v7 v10
    m0 m8 m16 m24
    hshift_z =>
  (evm_mod_shift0_epilogue_spec_within sp base
    u0 u1 u2 u3 shift v2 v5 v6 v7 v10
    m0 m8 m16 m24 hshift_z).to_cpsTriple

end EvmAsm.Evm64
