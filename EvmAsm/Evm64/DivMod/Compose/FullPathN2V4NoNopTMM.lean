/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopTMM

  Three-iteration call-max-max composition for the n=2 v4/no-NOP source path.
  j=2 takes the callable trial-division (call) path; j=1 and j=0 take the
  max-trial branch.
  Conditions: bltu_2=true (call), bltu_1=false (max), bltu_0=false (max).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopFinalPost

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Opaque alias for the j=1 `iterN2Max` result in the n=2 call-max-max path,
    parameterized on `r2 := r2CCCN2V4 ...`. -/
@[irreducible]
def r1TMMN2V4 (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterN2Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

theorem r1TMMN2V4_eq (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    r1TMMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop =
      (let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
       iterN2Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) := by
  delta r1TMMN2V4; rfl

/-- Compact postcondition for the n=2 v4/no-NOP source path whose j=2 iteration
    takes the callable trial-division path, while j=1 and j=0 both take the
    max-trial branch.  Neither max iteration updates the v4 scratch cells set by
    j=2, so they persist unchanged in the final postcondition. -/
@[irreducible]
def loopN2CallMaxMaxSourceFinalPostNoX1 (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    Assertion :=
  let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1TMMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  ((loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v1)) **
    (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 u1)) **
    (sp + signExtend12 3936 ↦ₘ scratch2) **
    (.x1 ↦ᵣ raVal)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
      (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
      (qAddr2 ↦ₘ r2.1))))

theorem loopN2CallMaxMaxSourceFinalPostNoX1_unfold (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    loopN2CallMaxMaxSourceFinalPostNoX1 sp base
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem =
    (let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := r1TMMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
     let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
     let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
     let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
     let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
     let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
     ((loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
       u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
       (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
       (sp + signExtend12 3960 ↦ₘ v1) **
       (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v1)) **
       (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 u1)) **
       (sp + signExtend12 3936 ↦ₘ scratch2) **
       (.x1 ↦ᵣ raVal)) **
       (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1)) **
        ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
         (qAddr2 ↦ₘ r2.1))))) := by
  delta loopN2CallMaxMaxSourceFinalPostNoX1
  rfl

/-- Branch/runtime conditions for the n=2 v4/no-NOP source path whose j=2
    iteration takes call, j=1 takes max, and j=0 takes max. -/
@[irreducible]
def loopN2CallMaxMaxSourceConds
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1TMMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  BitVec.ult u2 v1 ∧
  loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
  ¬BitVec.ult r2.2.2.1 v1 ∧
  isAddbackCarry2NzN2Max v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
  ¬BitVec.ult r1.2.2.1 v1 ∧
  isAddbackCarry2NzN2Max v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

theorem loopN2CallMaxMaxSourceConds_unfold
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) :
    loopN2CallMaxMaxSourceConds
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 =
    (let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := r1TMMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
     BitVec.ult u2 v1 ∧
     loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
     ¬BitVec.ult r2.2.2.1 v1 ∧
     isAddbackCarry2NzN2Max v0 v1 v2 v3
       u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
     ¬BitVec.ult r1.2.2.1 v1 ∧
     isAddbackCarry2NzN2Max v0 v1 v2 v3
       u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) := by
  delta loopN2CallMaxMaxSourceConds
  rfl

/-- The n=2 v4/no-NOP source path whose j=2 iteration takes the callable
    trial-division path and j=1/j=0 both take the max-trial branch.  The v4
    scratch cells written by j=2 persist unchanged through the two subsequent
    max iterations. -/
theorem divK_loop_n2_call_max_max_from_source_exact_loopIterScratch_v4_noNop
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hconds :
      loopN2CallMaxMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0) :
    cpsTripleWithin (224 + 152 + 152) (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2CallMaxMaxSourceFinalPostNoX1 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem) := by
  rw [loopN2CallMaxMaxSourceConds_unfold] at hconds
  simp only [r2CCCN2V4_eq, r1TMMN2V4_eq] at hconds
  obtain ⟨hbltu_2, hcarry2_nz_2, hbltu_1, hcarry2_nz_1, hbltu_0, hcarry2_nz_0⟩ := hconds
  -- j=2 call + j=1 max composed source theorem.
  have JCM := divK_loop_n2_call_max_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_2 hcarry2_nz_2 hbltu_1 hcarry2_nz_1
  -- j=0 max body theorem at the j=1 max iteration result.
  have J0 := divK_loop_body_n2_max_j0_exact_loopIterScratch_v4_noNop sp base
    (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3
      (signExtend12 4095 : Word)
      v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1)
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    v0 v1 v2 v3 u0Orig0
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    q0Old raVal
    (base + div128CallRetOff) v1
    (divKTrialCallV4DLo v1)
    (divKTrialCallV4Un0 u1)
    (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
    hbltu_0 hcarry2_nz_0
  -- Frame the j=0 max body with the j=1 and j=2 stored u4/q atoms.
  have J0f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1)) **
     (((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)))
    (by pcFree) J0
  -- Compose via the j=1 max -> j=0 max bridge that retains the j=2 frame.
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2MaxScratchX1_j1_to_max_j0_pre_with_j2_frame
      sp (base + div128CallRetOff) v1 (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 u1)
      (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
      v0 v1 v2 v3 u0Orig1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      u0Orig0 q0Old raVal
      (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    JCM J0f
  have hsteps : (224 + 152) + 152 = 224 + 152 + 152 := by decide
  rw [hsteps] at hcomp
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hcomp
  intro h hp
  rw [loopN2CallMaxMaxSourceFinalPostNoX1_unfold]
  simp only [r2CCCN2V4_eq, r1TMMN2V4_eq] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
