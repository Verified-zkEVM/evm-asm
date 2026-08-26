module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopSource

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Opaque alias for the j=2 `iterWithDoubleAddback` result in the n=2
    call-call-call path. Hides the heavy nested expression from `whnf` so
    downstream proofs can permute assertions without exhausting heartbeats. -/
@[irreducible]
def r2CCCN2V4 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop

theorem r2CCCN2V4_eq (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta r2CCCN2V4; rfl

/-- Opaque alias for the j=1 `iterWithDoubleAddback` result in the n=2
    call-call-call path, parameterized on `r2 := r2CCCN2V4 ...`. -/
@[irreducible]
def r1CCCN2V4 (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterWithDoubleAddback (divKTrialCallV4QHat r2.2.2.1 r2.2.1 v1)
    v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

theorem r1CCCN2V4_eq (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    r1CCCN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop =
      (let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
       iterWithDoubleAddback (divKTrialCallV4QHat r2.2.2.1 r2.2.1 v1)
         v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) := by
  delta r1CCCN2V4; rfl

/-- Compact postcondition for the n=2 v4/no-NOP source path whose three loop
    iterations all take the callable trial-division path.  The definition keeps
    the final source-to-j0 theorem statement small enough for Lean to elaborate:
    the expanded form is the j=0 call post plus retained j=1/j=2 stored u4/q
    atoms and exact caller `x1`. -/
@[irreducible]
def loopN2CallCallCallSourceFinalPostNoX1 (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    Assertion :=
  let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1CCCN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  let qHat0 := divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1
  let dLo0 := divKTrialCallV4DLo v1
  let divUn00 := divKTrialCallV4Un0 r1.2.1
  let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
  let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
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

theorem loopN2CallCallCallSourceFinalPostNoX1_unfold (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    loopN2CallCallCallSourceFinalPostNoX1 sp base
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem =
    let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let qHat0 := divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1
    let dLo0 := divKTrialCallV4DLo v1
    let divUn00 := divKTrialCallV4Un0 r1.2.1
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
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
        (qAddr2 ↦ₘ r2.1)))) := by
  delta loopN2CallCallCallSourceFinalPostNoX1
  rfl

/-- Branch/runtime conditions for the n=2 v4/no-NOP source path whose three
    loop iterations all take the callable trial-division path.  Bundling these
    conditions keeps downstream theorem signatures small. -/
@[irreducible]
def loopN2CallCallCallSourceConds
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1CCCN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  BitVec.ult u2 v1 ∧
  loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
  BitVec.ult r2.2.2.1 v1 ∧
  loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
  BitVec.ult r1.2.2.1 v1 ∧
  loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

theorem loopN2CallCallCallSourceConds_unfold
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) :
    loopN2CallCallCallSourceConds
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 =
    let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    BitVec.ult u2 v1 ∧
    loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
    BitVec.ult r2.2.2.1 v1 ∧
    loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
    BitVec.ult r1.2.2.1 v1 ∧
    loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  delta loopN2CallCallCallSourceConds
  rfl

/-- Compact CPS spec for the n=2 v4/no-NOP source path whose three loop
    iterations all take the callable trial-division path.  This names the full
    `cpsTripleWithin` proposition so the proof theorem can expose a small
    result type and unfold the CPS surface only inside the proof. -/
@[irreducible]
def loopN2CallCallCallSourceSpec (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Prop :=
  cpsTripleWithin (224 + 224 + 224) (base + loopBodyOff) (base + denormOff)
    (divCode_noNop_v4 base)
    (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem **
      (.x1 ↦ᵣ raVal))
    (loopN2CallCallCallSourceFinalPostNoX1 sp base
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem)

theorem loopN2CallCallCallSourceSpec_unfold (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    loopN2CallCallCallSourceSpec sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem =
    cpsTripleWithin (224 + 224 + 224) (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2CallCallCallSourceFinalPostNoX1 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem) := by
  delta loopN2CallCallCallSourceSpec
  rfl

/-- Inputs for the n=2 call×call×call v4/no-NOP source path, bundled so the
    eventual source theorem does not expose a large telescoped parameter list. -/
structure LoopN2CallCallCallSourceInput where
  sp : Word
  base : Word
  jOld : Word
  v5Old : Word
  v6Old : Word
  v7Old : Word
  v10Old : Word
  v11Old : Word
  v2Old : Word
  v0 : Word
  v1 : Word
  v2 : Word
  v3 : Word
  u0 : Word
  u1 : Word
  u2 : Word
  u3 : Word
  uTop : Word
  u0Orig1 : Word
  u0Orig0 : Word
  q2Old : Word
  q1Old : Word
  q0Old : Word
  raVal : Word
  retMem : Word
  dMem : Word
  dloMem : Word
  scratchUn0 : Word
  scratchMem : Word

@[irreducible]
def LoopN2CallCallCallSourceInput.Conds (I : LoopN2CallCallCallSourceInput) : Prop :=
  loopN2CallCallCallSourceConds I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig1 I.u0Orig0

@[irreducible]
def LoopN2CallCallCallSourceInput.Spec (I : LoopN2CallCallCallSourceInput) : Prop :=
  loopN2CallCallCallSourceSpec I.sp I.base I.jOld I.v5Old I.v6Old I.v7Old I.v10Old
    I.v11Old I.v2Old I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old I.raVal I.retMem I.dMem I.dloMem
    I.scratchUn0 I.scratchMem

theorem LoopN2CallCallCallSourceInput.Conds_unfold
    (I : LoopN2CallCallCallSourceInput) :
    I.Conds =
      loopN2CallCallCallSourceConds I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig1 I.u0Orig0 := by
  delta LoopN2CallCallCallSourceInput.Conds
  rfl

theorem LoopN2CallCallCallSourceInput.Spec_unfold
    (I : LoopN2CallCallCallSourceInput) :
    I.Spec =
      loopN2CallCallCallSourceSpec I.sp I.base I.jOld I.v5Old I.v6Old I.v7Old I.v10Old
        I.v11Old I.v2Old I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old I.raVal I.retMem I.dMem I.dloMem
        I.scratchUn0 I.scratchMem := by
  delta LoopN2CallCallCallSourceInput.Spec
  rfl

end EvmAsm.Evm64
