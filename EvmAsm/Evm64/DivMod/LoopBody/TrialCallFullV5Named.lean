/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5Named

  The v5 trial-call-full spec with a **compact NAMED post** — the brick-6
  unblock.  `divK_trial_call_full_v5` (TrialCallFullV5) produces
  `divKTrialCallFullPostV5 = div128V5SpecPost ** trial-frame`, whose registers
  are the huge raw Knuth-D quotient terms (the term-size wall).  Here we weaken
  that to `divKTrialCallFullPostV5Named`, mirror of the v4 `divKTrialCallFullPostV4`
  with the compact named v5 trial defs (`divKTrialCallV5QHat`/`Q1dd`/`Q0dd`/
  `DHi`/`X7Exit`/`X9Exit`/`ScratchOut`), using the register-name bridges
  (Div128V5FinalEqNamed / Div128V5X7X9Eq / #7252).  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallFullV5
import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5FinalEqNamed
import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5X7X9Eq
import EvmAsm.Evm64.DivMod.Spec.N1V5QuotNoBorrowShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Compact NAMED v5 trial-call-full post (mirror of `divKTrialCallFullPostV4`
    with v5 trial defs). -/
def divKTrialCallFullPostV5Named (sp j n uHi uLo vTop base scratchMem : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un0Div := divKTrialCallV5Un0 uLo
  let q1'' := divKTrialCallV5Q1dd uHi uLo vTop
  let q0'' := divKTrialCallV5Q0dd uHi uLo vTop
  let x7Exit := divKTrialCallV5X7Exit uHi uLo vTop
  let x9Exit := divKTrialCallV5X9Exit uHi uLo vTop
  let q := divKTrialCallV5QHat uHi uLo vTop
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Exit) ** regOwn .x1 **
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) **
  (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1'') ** (.x11 ↦ᵣ q) **
  (.x2 ↦ᵣ (base + div128CallRetOff)) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ vTop) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0Div) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut uHi uLo vTop scratchMem)

/-- Weaken the raw v5 trial-call-full post (`div128V5SpecPost ** trial-frame`,
    huge Knuth-D quotient terms) to the compact NAMED post. -/
theorem divKTrialCallFullPostV5_imp_named
    (sp j n uHi uLo vTop base scratchMem : Word) :
    ∀ h, divKTrialCallFullPostV5 sp j n uHi uLo vTop base scratchMem h →
      divKTrialCallFullPostV5Named sp j n uHi uLo vTop base scratchMem h := by
  intro h hq
  unfold divKTrialCallFullPostV5 div128V5SpecPost at hq
  unfold divKTrialCallFullPostV5Named
  rw [← div128V5_q1Final_eq_Q1dd uHi uLo vTop,
      ← div128V5_q0Final_eq_Q0dd uHi uLo vTop,
      div128V5_x7Exit_eq uHi uLo vTop,
      div128V5_x9Exit_eq uHi uLo vTop,
      ← div128V5CodeQuot_eq_divKTrialCallV5QHat uHi uLo vTop]
  unfold divKTrialCallV5ScratchOut
  rw [← div128V5_rhat2c_eq uHi uLo vTop, ← div128V5_un21_eq uHi uLo vTop]
  unfold div128V5CodeQuot divKTrialCallV5DHi divKTrialCallV5DLo
    divKTrialCallV5Un0 divKTrialCallV5Un1
  xperm_hyp hq

/-- v5 trial-quotient call full path with the **compact NAMED post**
    (`divKTrialCallFullPostV5Named`).  Same statement as
    `divK_trial_call_full_v5_spec_within_noNop` but with the post weakened via
    `divKTrialCallFullPostV5_imp_named`, so downstream composition (brick 6) sees
    compact named registers instead of the raw Knuth-D quotient terms. -/
theorem divK_trial_call_full_v5_named_spec_within_noNop
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
      (divKTrialCallFullPostV5Named sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (divKTrialCallFullPostV5_imp_named sp j n uHi uLo vTop base scratchMem)
    (divK_trial_call_full_v5_spec_within_noNop
      sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop
      retMem dMem dloMem un0Mem scratchMem base halign hbltu)

end EvmAsm.Evm64
