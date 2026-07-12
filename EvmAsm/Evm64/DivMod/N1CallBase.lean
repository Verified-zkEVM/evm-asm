/-
  EvmAsm.Evm64.DivMod.N1CallBase

  Shared declaration home for the n=1 call-path loop body and call specs.
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
import EvmAsm.Evm64.DivMod.LoopBody.TrialMax
import EvmAsm.Evm64.DivMod.LoopBody.StoreLoop
import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionSkip

/-
  EvmAsm.Evm64.DivMod.LoopBodyN1

  Fixed loop body compositions for n=1 (1-limb divisor).
  Eliminates the uAddr/window-cell and vtop/v0 overlaps in the generic spec.

  For n=1, three address overlaps exist:
  1. uAddr = uBase + signExtend12 4088  (both refer to u[j+1])
  2. uAddr + 8 = uBase + signExtend12 0  (both refer to u[j+0])
  3. vtopBase + signExtend12 32 = sp + signExtend12 32  (both refer to v[0])

  This file eliminates these overlaps by:
  - Expanding the trial spec's let-bindings via dsimp
  - Rewriting uAddr and vtopBase to canonical uBase-relative form
  - Framing only with cells NOT already in the trial spec
  - Composing without cell duplication in any separating conjunction
-/


open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address rewriting lemmas for n=1 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=1: uAddr = uBase + signExtend12 4088 -/
theorem u_addr_eq_n1 {sp j : Word} :
    sp + signExtend12 4056 - (j + (1 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- For n=1: (uBase + signExtend12 4088) + 8 = uBase + signExtend12 0 -/
theorem u_addr8_eq_n1 {sp j : Word} :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0 := by
  divmod_addr

/-- For n=1: vtopBase + signExtend12 32 = sp + signExtend12 32 -/
theorem vtop_eq_v0_n1 {sp : Word} :
    (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 32 := by
  divmod_addr

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.DivMod.LoopIterN1.Call

  Loop body cpsTripleWithin specs for n=1, BLTU taken (call path).
  Split from LoopIterN1.lean for faster builds.
-/


open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ skip, j=0 → cpsTripleWithin to base+904
-- ============================================================================

@[irreducible]
def loopBodyN1CallSkipJ0PreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
   (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
   (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
   (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
   ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
   ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
   ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
   ((uBase + signExtend12 4064) ↦ₘ uTop) **
   (qAddr ↦ₘ qOld) **
   (sp + signExtend12 3968 ↦ₘ retMem) **
   (sp + signExtend12 3960 ↦ₘ dMem) **
   (sp + signExtend12 3952 ↦ₘ dloMem) **
   (sp + signExtend12 3944 ↦ₘ scratch_un0) **
   (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)

@[irreducible]
def loopBodyN1CallSkipJ0PreV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
   (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
   (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
   (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
   ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
   ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
   ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
   ((uBase + signExtend12 4064) ↦ₘ uTop) **
   (qAddr ↦ₘ qOld) **
   (sp + signExtend12 3968 ↦ₘ retMem) **
   (sp + signExtend12 3960 ↦ₘ dMem) **
   (sp + signExtend12 3952 ↦ₘ dloMem) **
   (sp + signExtend12 3944 ↦ₘ scratch_un0) **
   (sp + signExtend12 3936 ↦ₘ scratchMem))

theorem loopBodyN1CallSkipJ0PreV4NoX1_pcFree
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  delta loopBodyN1CallSkipJ0PreV4NoX1
  pcFree

instance pcFreeInst_loopBodyN1CallSkipJ0PreV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) :
    Assertion.PCFree
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem) :=
  ⟨loopBodyN1CallSkipJ0PreV4NoX1_pcFree sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem⟩

theorem loopBodyN1CallSkipJ0PreV4NoX1_to_loopBodyN1CallSkipJ0PreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word) :
    ∀ h,
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem **
        regOwn .x1) h →
      loopBodyN1CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem h := by
  intro h hp
  delta loopBodyN1CallSkipJ0PreV4NoX1 loopBodyN1CallSkipJ0PreV4 at hp ⊢
  simpa only [sepConj_assoc'] using hp

@[irreducible]
def loopBodyN1CallSkipJ0PostV4
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  loopBodyN1SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut u1 u0 v0 scratchMem) **
  regOwn .x1

@[irreducible]
def loopBodyN1CallSkipJ0PostV4NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  loopBodyN1SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)

theorem loopBodyN1CallSkipJ0PostV4NoX1_unfold
    {sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word} :
    loopBodyN1CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    (
    let dLo := divKTrialCallV4DLo v0
    let div_un0 := divKTrialCallV4Un0 u0
    let qHat := divKTrialCallV4QHat u1 u0 v0
    loopBodyN1SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ dLo) **
    (sp + signExtend12 3944 ↦ₘ div_un0) **
    (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)) := by
  delta loopBodyN1CallSkipJ0PostV4NoX1
  rfl

theorem loopBodyN1CallSkipJ0PostV4NoX1_pcFree
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    (loopBodyN1CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem).pcFree := by
  delta loopBodyN1CallSkipJ0PostV4NoX1 loopBodyN1SkipPost
        loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
  pcFree

instance pcFreeInst_loopBodyN1CallSkipJ0PostV4NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    Assertion.PCFree
      (loopBodyN1CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) :=
  ⟨loopBodyN1CallSkipJ0PostV4NoX1_pcFree sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem⟩

theorem loopBodyN1CallSkipJ0PostV4NoX1_to_loopBodyN1CallSkipJ0PostV4
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    ∀ h,
      (loopBodyN1CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        regOwn .x1) h →
      loopBodyN1CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem h := by
  intro h hp
  delta loopBodyN1CallSkipJ0PostV4NoX1 loopBodyN1CallSkipJ0PostV4 at hp ⊢
  simpa only [sepConj_assoc'] using hp

@[irreducible]
def loopBodyN1CallSkipJ0BorrowV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV4QHat u1 u0 v0
  mulsubN4NoBorrow qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible]
private def n1CallV4DHi (v0 : Word) : Word :=
  v0 >>> (32 : BitVec 6).toNat

@[irreducible]
private def n1CallV4DLo (v0 : Word) : Word :=
  (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

@[irreducible]
private def n1CallV4Un1 (u0 : Word) : Word :=
  u0 >>> (32 : BitVec 6).toNat

@[irreducible]
private def n1CallV4Un0 (u0 : Word) : Word :=
  (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

@[irreducible]
private def n1CallV4Q1dd (u1 u0 v0 : Word) : Word :=
  let dHi := n1CallV4DHi v0
  let dLo := n1CallV4DLo v0
  let div_un1 := n1CallV4Un1 u0
  let q1 := rv64_divu u1 dHi
  let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
    then q1' + signExtend12 4095 else q1'

@[irreducible]
private def n1CallV4Un21 (u1 u0 v0 : Word) : Word :=
  let dHi := n1CallV4DHi v0
  let dLo := n1CallV4DLo v0
  let div_un1 := n1CallV4Un1 u0
  let q1 := rv64_divu u1 dHi
  let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
              then q1' + signExtend12 4095 else q1'
  let rhat'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                then rhat' + dHi else rhat'
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1'' * dLo
  cu_rhat_un1 - cu_q1_dlo

@[irreducible]
private def n1CallV4Rhat2c (u1 u0 v0 : Word) : Word :=
  let dHi := n1CallV4DHi v0
  let un21 := n1CallV4Un21 u1 u0 v0
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  if hi2 = 0 then rhat2 else rhat2 + dHi

@[irreducible]
private def n1CallV4Q0dd (u1 u0 v0 : Word) : Word :=
  let dHi := n1CallV4DHi v0
  let dLo := n1CallV4DLo v0
  let div_un0 := n1CallV4Un0 u0
  let un21 := n1CallV4Un21 u1 u0 v0
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2' := if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  div128Quot_phase2b_q0' q0' rhat2' dLo div_un0

@[irreducible]
private def n1CallV4QHat (u1 u0 v0 : Word) : Word :=
  (n1CallV4Q1dd u1 u0 v0 <<< (32 : BitVec 6).toNat) ||| n1CallV4Q0dd u1 u0 v0

@[irreducible]
private def n1CallV4X7Exit (u1 u0 v0 : Word) : Word :=
  let dLo := n1CallV4DLo v0
  let div_un0 := n1CallV4Un0 u0
  let un21 := n1CallV4Un21 u1 u0 v0
  let q0c :=
    let dHi := n1CallV4DHi v0
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := n1CallV4Rhat2c u1 u0 v0
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2' := if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + n1CallV4DHi v0 else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dLo
  if rhat2cHi ≠ 0 then un21 else if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2

@[irreducible]
private def n1CallV4X9Exit (u1 u0 v0 : Word) : Word :=
  let dLo := n1CallV4DLo v0
  let div_un0 := n1CallV4Un0 u0
  let rhat2c := n1CallV4Rhat2c u1 u0 v0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0c :=
    let dHi := n1CallV4DHi v0
    let un21 := n1CallV4Un21 u1 u0 v0
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    if hi2 = 0 then q0 else q0 + signExtend12 4095
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2' := if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + n1CallV4DHi v0 else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| div_un0
  if rhat2cHi ≠ 0 then rhat2cHi else if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0

@[irreducible]
private def n1CallV4ScratchOut (u1 u0 v0 scratchMem : Word) : Word :=
  let rhat2c := n1CallV4Rhat2c u1 u0 v0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  if rhat2cHi ≠ 0 then scratchMem else rhat2c

/-- v4 loop body cpsTripleWithin for n=1, call+skip, j=0.
    This consumes the v4 div128 call path and exits to denorm. -/
theorem divK_loop_body_n1_call_skip_j0_v4_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (sharedDivModCode_v4 base)
      (loopBodyN1CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
      (loopBodyN1CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  unfold loopBodyN1CallSkipJ0PreV4
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi v0
  let dLo := divKTrialCallV4DLo v0
  let div_un0 := divKTrialCallV4Un0 u0
  let q1'' := divKTrialCallV4Q1dd u1 u0 v0
  let q0'' := divKTrialCallV4Q0dd u1 u0 v0
  let x7Exit := divKTrialCallV4X7Exit u1 u0 v0
  let x9Exit := divKTrialCallV4X9Exit u1 u0 v0
  let qHat := divKTrialCallV4QHat u1 u0 v0
  let scratchOut := divKTrialCallV4ScratchOut u1 u0 v0 scratchMem
  have TF := divK_trial_call_full_v4_spec_within sp (0 : Word) (1 : Word)
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu
  unfold divKTrialCallFullPostV4 at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have hborrow' :
      mulsubN4NoBorrow qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
    unfold loopBodyN1CallSkipJ0BorrowV4 at hborrow
    exact hborrow
  have MCS := divK_mulsub_correction_skip_v4_spec_within sp qHat (0 : Word)
    v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x9Exit q0'' dHi x7Exit q1'' (base + div128CallRetOff) base
  have MCS0 := MCS hborrow'
  unfold divKMulsubCorrectionSkipPre at MCS0
  unfold n4McaNamedSkipPost at MCS0
  unfold mulsubN4 at MCS0
  dsimp only [] at MCS0
  have MCS0f := cpsTripleWithin_frameR ((sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) MCS0
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have SL := divK_store_loop_j0_v4_spec_within sp qHat u4_new (0 : Word) qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCS0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) **
     (sp + signExtend12 3936 ↦ₘ scratchOut) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold loopBodyN1CallSkipJ0PostV4
      unfold loopBodyN1SkipPost loopBodySkipPost loopExitPost
      unfold mulsubN4
      dsimp only []
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- Loop body cpsTripleWithin for n=1, call+skip, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTripleWithin to base+904. -/
theorem divK_loop_body_n1_call_skip_j0_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 126 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (loopBodyN1CallSkipPostJ sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec_within sp (0 : Word) (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have MCS := divK_mulsub_correction_skip_spec_within sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + div128CallRetOff) base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  have MCS0f := cpsTripleWithin_frameR (regOwn .x1) (by pcFree) MCS0
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have SL := divK_store_loop_j0_spec_within sp qHat u4_new (0 : Word) qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCS0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

theorem divK_loop_body_n1_call_skip_jgt0_spec_within (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 126 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (loopBodyN1CallSkipPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec_within sp j (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have MCS := divK_mulsub_correction_skip_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + div128CallRetOff) base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  have MCS0f := cpsTripleWithin_frameR (regOwn .x1) (by pcFree) MCS0
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have SL := divK_store_loop_jgt0_spec_within sp j qHat u4_new (0 : Word) qOld base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCS0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

/-- No-NOP variants of the n=1 call/skip loop-body specs. -/
theorem divK_loop_body_n1_call_skip_j0_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 126 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (loopBodyN1CallSkipPostJ sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec_within_noNop sp (0 : Word) (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have MCS := divK_mulsub_correction_skip_spec_within_noNop sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + div128CallRetOff) base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  have MCS0f := cpsTripleWithin_frameR (regOwn .x1) (by pcFree) MCS0
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have SL := divK_store_loop_j0_spec_within_noNop sp qHat u4_new (0 : Word) qOld base
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCS0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

theorem divK_loop_body_n1_call_skip_jgt0_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 126 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
      (loopBodyN1CallSkipPostJ sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  let dHi := v0 >>> (32 : BitVec 6).toNat
  let dLo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 dHi; let rhat := u1 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi; let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec_within_noNop sp j (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
    u1 u0 v0 retMem dMem dloMem scratch_un0 base
    halign hbltu
  unfold divKTrialCallFullPost at TF
  dsimp only [] at TF
  rw [u_addr_eq_n1] at TF
  rw [u_addr8_eq_n1] at TF
  rw [vtop_eq_v0_n1] at TF
  have MCS := divK_mulsub_correction_skip_spec_within_noNop sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    x1Exit q0' dHi x7Exit q1' (base + div128CallRetOff) base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  have MCS0f := cpsTripleWithin_frameR (regOwn .x1) (by pcFree) MCS0
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  have SL := divK_store_loop_jgt0_spec_within_noNop sp j qHat u4_new (0 : Word) qOld base hpos
  intro_lets at SL
  have TFf := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld))
    (by pcFree) TF
  seqFrame TFf MCS0f
  have SLf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ div_un0) ** regOwn .x1)
    (by pcFree) SL
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0f SLf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full


end EvmAsm.Evm64
