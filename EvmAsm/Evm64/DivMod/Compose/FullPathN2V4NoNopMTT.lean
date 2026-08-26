/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopMTT

  Three-iteration max-call-call composition for the n=2 v4/no-NOP source path.
  j=2 takes the max-trial branch; j=1 and j=0 take the callable trial-division
  (call) path.
  Conditions: bltu_2=false (max), bltu_1=true (call), bltu_0=true (call).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopFinalPost

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Opaque alias for the j=2 `iterN2Max` result in the n=2 max-call-call path. -/
@[irreducible]
def r2MTTN2V4 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

theorem r2MTTN2V4_eq (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta r2MTTN2V4; rfl

/-- Opaque alias for the j=1 `iterWithDoubleAddback` result in the n=2
    max-call-call path, parameterized on `r2 := r2MTTN2V4 ...`. -/
@[irreducible]
def r1MTTN2V4 (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r2 := r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterWithDoubleAddback (divKTrialCallV4QHat r2.2.2.1 r2.2.1 v1)
    v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

theorem r1MTTN2V4_eq (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    r1MTTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop =
      (let r2 := r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
       iterWithDoubleAddback (divKTrialCallV4QHat r2.2.2.1 r2.2.1 v1)
         v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) := by
  delta r1MTTN2V4; rfl

/-- Compact postcondition for the n=2 v4/no-NOP source path whose j=2 iteration
    takes the max-trial branch and j=1/j=0 both take the callable trial-division
    path.  j=1 and j=0 are both calls, so the scratch chain is
    scratch1 → scratch0 with scratch1 derived from j=1's computation. -/
@[irreducible]
def loopN2MaxCallCallSourceFinalPostNoX1 (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    Assertion :=
  let r2 := r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1MTTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  let qHat0 := divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1
  let dLo0 := divKTrialCallV4DLo v1
  let divUn00 := divKTrialCallV4Un0 r1.2.1
  let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
  let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  ((loopIterPostN2CallScratchNoX1 sp base (0 : Word)
    qHat0 dLo0 divUn00 scratch0
    v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (.x1 ↦ᵣ raVal)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
      (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
      (qAddr2 ↦ₘ r2.1))))

theorem loopN2MaxCallCallSourceFinalPostNoX1_unfold (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    loopN2MaxCallCallSourceFinalPostNoX1 sp base
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem =
    (let r2 := r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := r1MTTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
     let qHat0 := divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1
     let dLo0 := divKTrialCallV4DLo v1
     let divUn00 := divKTrialCallV4Un0 r1.2.1
     let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
     let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
     let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
     let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
     let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
     let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
     ((loopIterPostN2CallScratchNoX1 sp base (0 : Word)
       qHat0 dLo0 divUn00 scratch0
       v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
       (.x1 ↦ᵣ raVal)) **
       (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1)) **
        ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
         (qAddr2 ↦ₘ r2.1))))) := by
  delta loopN2MaxCallCallSourceFinalPostNoX1
  rfl

/-- Branch/runtime conditions for the n=2 v4/no-NOP source path whose j=2
    iteration takes max and j=1/j=0 both take call. -/
@[irreducible]
def loopN2MaxCallCallSourceConds
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1MTTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  ¬BitVec.ult u2 v1 ∧
  isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
  BitVec.ult r2.2.2.1 v1 ∧
  loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
  BitVec.ult r1.2.2.1 v1 ∧
  loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

theorem loopN2MaxCallCallSourceConds_unfold
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) :
    loopN2MaxCallCallSourceConds
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 =
    (let r2 := r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := r1MTTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
     ¬BitVec.ult u2 v1 ∧
     isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
     BitVec.ult r2.2.2.1 v1 ∧
     loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
       u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
     BitVec.ult r1.2.2.1 v1 ∧
     loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
       u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) := by
  delta loopN2MaxCallCallSourceConds
  rfl

/-- The n=2 v4/no-NOP source path whose j=2 iteration takes the max-trial
    branch and j=1/j=0 both take the callable trial-division path. -/
theorem divK_loop_n2_max_call_call_from_source_exact_loopIterScratch_v4_noNop
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hconds :
      loopN2MaxCallCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0) :
    cpsTripleWithin (152 + 224 + 224) (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2MaxCallCallSourceFinalPostNoX1 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem) := by
  rw [loopN2MaxCallCallSourceConds_unfold] at hconds
  simp only [r2MTTN2V4_eq, r1MTTN2V4_eq] at hconds
  obtain ⟨hbltu_2, hcarry2_nz_2, hbltu_1, hcarry2_nz_1, hbltu_0, hcarry2_nz_0⟩ := hconds
  -- j=2 max + j=1 call composed source theorem (raw MC shape).
  have JMC := divK_loop_n2_max_call_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_2 hcarry2_nz_2 hbltu_1 hcarry2_nz_1
  -- j=0 call body theorem at the j=1 call result.
  have J0 := divK_loop_body_n2_call_j0_exact_loopIterScratch_v4_noNop sp base
    (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3
      (divKTrialCallV4QHat
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1)
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    v0 v1 v2 v3 u0Orig0
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
    (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    q0Old raVal
    (base + div128CallRetOff) v1
    (divKTrialCallV4DLo v1)
    (divKTrialCallV4Un0
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1)
    (divKTrialCallV4ScratchOut
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1
      scratchMem)
    halign hbltu_0 hcarry2_nz_0
  -- Frame the j=0 call body with the j=1 and j=2 stored u4/q atoms.
  have J0f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
      (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).1)) **
     (((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)))
    (by pcFree) J0
  -- Compose via the j=1 call -> j=0 call bridge that retains the j=2 frame.
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2CallScratchNoX1_j1_to_call_j0_pre_with_j2_frame
      sp base
      (divKTrialCallV4QHat
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1)
      (divKTrialCallV4ScratchOut
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1
        scratchMem)
      v0 v1 v2 v3 u0Orig1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      u0Orig0 q0Old raVal
      (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    JMC J0f
  have hsteps : (152 + 224) + 224 = 152 + 224 + 224 := by decide
  rw [hsteps] at hcomp
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hcomp
  intro h hp
  rw [loopN2MaxCallCallSourceFinalPostNoX1_unfold]
  simp only [r2MTTN2V4_eq, r1MTTN2V4_eq] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
