/-
  EvmAsm.Evm64.SDiv.Compose.DivCallN1V4Handoff

  N1/v4-shaped exact handoff wrappers for the SDIV div-call path.
-/

import EvmAsm.Evm64.DivMod.Spec.N1ExactNoNop
import EvmAsm.Evm64.SDiv.DivCallExactShared

namespace EvmAsm.Evm64.SDiv.Compose

/-- Normalized N1 dividend tuple for SDIV's absolute-value operands. -/
abbrev sdivN1V4NormU
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop divisorLimb0 divisorTop : Word) :
    Word × Word × Word × Word × Word :=
  EvmAsm.Evm64.fullDivN1NormU
    (sdivAbsSum0 dividendLimb0 dividendTop)
    (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
    (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
    (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
    (sdivAbsSum0 divisorLimb0 divisorTop)

/-- Normalized N1 divisor tuple for SDIV's absolute-value operands. -/
abbrev sdivN1V4NormV
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    Word × Word × Word × Word :=
  EvmAsm.Evm64.fullDivN1NormV
    (sdivAbsSum0 divisorLimb0 divisorTop)
    (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
    (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)

/-- The v4-only trial-call scratch cell after the SDIV N1 call/max/max/max
    DIV path, expressed over SDIV's absolute-value divisor limbs. -/
abbrev sdivN1V4ScratchOut
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem : Word) :
    Word :=
  EvmAsm.Evm64.divKTrialCallV4ScratchOut
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.2
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
    scratchMem

/-- SDIV absolute-limb spelling of the N1 `j = 1` non-borrow branch
    condition used by the call/max/max/max DIV path. -/
abbrev sdivN1V4Hbltu1
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Prop :=
  ¬BitVec.ult
    (EvmAsm.Evm64.loopN1CallMaxmaxmaxR2
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.2
      0 0 0
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.1).2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1

/-- SDIV absolute-limb spelling of the N1 `j = 0` non-borrow branch
    condition used by the call/max/max/max DIV path. -/
abbrev sdivN1V4Hbltu0
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Prop :=
  ¬BitVec.ult
    (EvmAsm.Evm64.loopN1CallMaxmaxmaxR1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.2
      0 0 0
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.1).2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1

/-- SDIV absolute-limb spelling of the N1/v4 quotient limb 3 computed by the
    call/max/max/max DIV path. -/
abbrev sdivN1V4Quot3
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Word :=
  (EvmAsm.Evm64.loopN1CallMaxmaxmaxR3
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.1
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.2
    0 0 0).1

/-- SDIV absolute-limb spelling of the N1/v4 quotient limb 2 computed by the
    call/max/max/max DIV path. -/
abbrev sdivN1V4Quot2
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Word :=
  (EvmAsm.Evm64.loopN1CallMaxmaxmaxR2
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.1
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.2
    0 0 0
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.1).1

/-- SDIV absolute-limb spelling of the N1/v4 quotient limb 1 computed by the
    call/max/max/max DIV path. -/
abbrev sdivN1V4Quot1
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Word :=
  (EvmAsm.Evm64.loopN1CallMaxmaxmaxR1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.1
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.2.2
    0 0 0
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.2.1
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).2.1).1

/-- SDIV absolute-limb spelling of the N1/v4 quotient limb 0 computed by the
    call/max/max/max DIV path. -/
abbrev sdivN1V4Quot0
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Word :=
  (EvmAsm.Evm64.iterN1Max
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
    (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
    (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorTop).1
    (EvmAsm.Evm64.loopN1CallMaxmaxmaxR1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.2
      0 0 0
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.1).2.1
    (EvmAsm.Evm64.loopN1CallMaxmaxmaxR1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.2
      0 0 0
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.1).2.2.1
    (EvmAsm.Evm64.loopN1CallMaxmaxmaxR1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.2
      0 0 0
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.1).2.2.2.1
    (EvmAsm.Evm64.loopN1CallMaxmaxmaxR1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.1
      (sdivN1V4NormV divisorLimb0 divisorLimb1 divisorLimb2 divisorTop).2.2.2
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.2.2
      0 0 0
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.2.1
      (sdivN1V4NormU dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorTop).2.1).2.2.2.2.1).1

/-- Exact SDIV div-call handoff specialized to the v4 scratch frame shape
    produced by the N1 call/max/max/max no-NOP DIV path. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4Scratch_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem scratchOut : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))) := by
  exact
    saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_frame_transform_spec_in_sdivCodeV4
      (FPre := ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (FPost := ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 (EvmAsm.Rv64.signExtend12 4095 : Word)
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      hbase hStack

/-- Exact SDIV div-call handoff specialized to the named N1/v4 scratch output
    produced by the call/max/max/max DIV path. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4ScratchOut_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ
          sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
            divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ
        sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem))) := by
  exact
    saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4Scratch_spec_in_sdivCodeV4
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      (sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem)
      hbase hStack

/-- Exact-frame variant of the named N1/v4 scratch-output SDIV handoff. -/
theorem saveRaDivCallDispatchReadyPost_exact_frame_x9out_divCode_n1_v4ScratchOut_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
        (EvmAsm.Evm64.divStackDispatchPostCallableExactFrame sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          ((base + divCallOff) + 4)
          (EvmAsm.Rv64.signExtend12 4095 : Word) **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ
          sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
            divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ
        sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem))) := by
  exact
    saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4ScratchOut_spec_in_sdivCodeV4
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      hbase
      (EvmAsm.Rv64.cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun _ hp => by
          simpa [EvmAsm.Evm64.divStackDispatchPostCallableExactFrame_unfold] using hp)
        hStack)

/-- Unified-bound DIV stack spec for SDIV's N1/v4 absolute-limb handoff
    surface, with the v4 scratch cell framed explicitly. -/
theorem sdivN1V4_abs_stack_spec
    (sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz :
      sdivAbsSum0 divisorLimb0 divisorTop |||
        sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop |||
        sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop |||
        sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop ≠ 0)
    (hb3z : sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0)
    (hb2z : sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0)
    (hb1z : sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop = 0)
    (hshift_nz : (EvmAsm.Evm64.clzResult (sdivAbsSum0 divisorLimb0 divisorTop)).1 ≠ 0)
    (halign : EvmAsm.Evm64.fullDivN1CallMaxmaxmaxExactInputAligned sp
      (base + wrapperEndOff) jMem (1 : Word)
      (EvmAsm.Evm64.fullDivN1Shift (sdivAbsSum0 divisorLimb0 divisorTop))
      (EvmAsm.Evm64.fullDivN1NormU
        (sdivAbsSum0 dividendLimb0 dividendTop)
        (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
        (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsSum0 divisorLimb0 divisorTop)).1
      (sdivAbsSum0 dividendLimb0 dividendTop >>>
        ((EvmAsm.Evm64.fullDivN1AntiShift
          (sdivAbsSum0 divisorLimb0 divisorTop)).toNat % 64))
      (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (EvmAsm.Evm64.fullDivN1AntiShift (sdivAbsSum0 divisorLimb0 divisorTop))
      (sdivAbsSum0 dividendLimb0 dividendTop)
      (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
      (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum0 divisorLimb0 divisorTop)
      (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
      (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem ((base + divCallOff) + 4))
    (hbltu3 : EvmAsm.Evm64.isTrialN1_j3 true
      (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum0 divisorLimb0 divisorTop))
    (hbltu2 : ¬BitVec.ult
      (EvmAsm.Evm64.loopN1CallMaxmaxmaxR3
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.2
        (EvmAsm.Evm64.fullDivN1NormU
          (sdivAbsSum0 dividendLimb0 dividendTop)
          (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
          (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum0 divisorLimb0 divisorTop)).2.2.2.1
        (EvmAsm.Evm64.fullDivN1NormU
          (sdivAbsSum0 dividendLimb0 dividendTop)
          (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
          (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum0 divisorLimb0 divisorTop)).2.2.2.2
        0 0 0).2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1)
    (hbltu1 :
      sdivN1V4Hbltu1 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hbltu0 :
      sdivN1V4Hbltu0 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hcarry2 : EvmAsm.Evm64.Carry2NzAll
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.2)
    (hdiv0 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 0 =
        sdivN1V4Quot0 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hdiv1 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 1 =
        sdivN1V4Quot1 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hdiv2 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 2 =
        sdivN1V4Quot2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hdiv3 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 3 =
        sdivN1V4Quot3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :
    EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
      (base + wrapperEndOff)
      ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
      (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSign divisorTop) ((base + divCallOff) + 4)
        ((EvmAsm.Evm64.clzResult (sdivAbsSum0 divisorLimb0 divisorTop)).2 >>> (63 : Nat))
        v5 v6
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsMask divisorTop)
        (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((EvmAsm.Evm64.divStackDispatchPostCallable sp
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
        (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ
        sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem)) := by
  simpa [sdivN1V4ScratchOut, sdivN1V4Hbltu1, sdivN1V4Hbltu0,
      sdivN1V4Quot0, sdivN1V4Quot1, sdivN1V4Quot2, sdivN1V4Quot3,
      sdivN1V4NormU, sdivN1V4NormV] using
    EvmAsm.Evm64.evm_div_n1_call_maxmaxmax_stack_spec_within_word_noNop_v4_preNoX1_callableExtra_x9In_unified
      sp (base + wrapperEndOff)
      (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsSum0 dividendLimb0 dividendTop)
      (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
      (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum0 divisorLimb0 divisorTop)
      (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
      (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      v5 v6
      (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsMask divisorTop)
      (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsSign divisorTop)
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
      ((base + divCallOff) + 4)
      (sdivAbsDividendWord_getLimbN_0 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsDividendWord_getLimbN_1 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsDividendWord_getLimbN_2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsDividendWord_getLimbN_3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsDivisorWord_getLimbN_0 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsDivisorWord_getLimbN_1 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsDivisorWord_getLimbN_2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsDivisorWord_getLimbN_3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      hbnz hb3z hb2z hb1z hshift_nz halign hbltu3 hbltu2 hbltu1 hbltu0 hcarry2
      hdiv0 hdiv1 hdiv2 hdiv3

/-- Concrete N1 call/max/max/max SDIV handoff over the absolute-value
    dividend and divisor words, using the v4 scratch-output postcondition. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4_abs_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbase : base &&& 1 = 0)
    (_hbnz :
      sdivAbsSum0 divisorLimb0 divisorTop |||
        sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop |||
        sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop |||
        sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop ≠ 0)
    (_hb3z : sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0)
    (_hb2z : sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0)
    (_hb1z : sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop = 0)
    (_hshift_nz : (EvmAsm.Evm64.clzResult (sdivAbsSum0 divisorLimb0 divisorTop)).1 ≠ 0)
    (_halign : EvmAsm.Evm64.fullDivN1CallMaxmaxmaxExactInputAligned sp
      (base + wrapperEndOff) jMem (1 : Word)
      (EvmAsm.Evm64.fullDivN1Shift (sdivAbsSum0 divisorLimb0 divisorTop))
      (EvmAsm.Evm64.fullDivN1NormU
        (sdivAbsSum0 dividendLimb0 dividendTop)
        (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
        (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsSum0 divisorLimb0 divisorTop)).1
      (sdivAbsSum0 dividendLimb0 dividendTop >>>
        ((EvmAsm.Evm64.fullDivN1AntiShift
          (sdivAbsSum0 divisorLimb0 divisorTop)).toNat % 64))
      (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (EvmAsm.Evm64.fullDivN1AntiShift (sdivAbsSum0 divisorLimb0 divisorTop))
      (sdivAbsSum0 dividendLimb0 dividendTop)
      (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
      (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum0 divisorLimb0 divisorTop)
      (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
      (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem ((base + divCallOff) + 4))
    (_hbltu3 : EvmAsm.Evm64.isTrialN1_j3 true
      (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum0 divisorLimb0 divisorTop))
    (_hbltu2 : ¬BitVec.ult
      (EvmAsm.Evm64.loopN1CallMaxmaxmaxR3
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.2
        (EvmAsm.Evm64.fullDivN1NormU
          (sdivAbsSum0 dividendLimb0 dividendTop)
          (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
          (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum0 divisorLimb0 divisorTop)).2.2.2.1
        (EvmAsm.Evm64.fullDivN1NormU
          (sdivAbsSum0 dividendLimb0 dividendTop)
          (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
          (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum0 divisorLimb0 divisorTop)).2.2.2.2
        0 0 0).2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1)
    (_hbltu1 :
      sdivN1V4Hbltu1 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (_hbltu0 :
      sdivN1V4Hbltu0 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (_hcarry2 : EvmAsm.Evm64.Carry2NzAll
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.2)
    (_hdiv0 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 0 =
        sdivN1V4Quot0 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (_hdiv1 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 1 =
        sdivN1V4Quot1 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (_hdiv2 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 2 =
        sdivN1V4Quot2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (_hdiv3 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 3 =
        sdivN1V4Quot3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        ((EvmAsm.Evm64.clzResult (sdivAbsSum0 divisorLimb0 divisorTop)).2 >>> (63 : Nat))
        v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ
        sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem))) := by
  exact
    saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4ScratchOut_spec_in_sdivCodeV4
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      ((EvmAsm.Evm64.clzResult (sdivAbsSum0 divisorLimb0 divisorTop)).2 >>> (63 : Nat))
      v5 v6
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      hbase
      (sdivN1V4_abs_stack_spec
        sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v5 v6
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
        _hbnz _hb3z _hb2z _hb1z _hshift_nz _halign _hbltu3 _hbltu2
        _hbltu1 _hbltu0 _hcarry2 _hdiv0 _hdiv1 _hdiv2 _hdiv3)

/-- Concrete N1/v4 SDIV handoff with an externally named dispatch `x2`
    value.  The full DIV stack proof is still built internally; callers only
    need to identify `v2` with the clz-derived dispatch bit. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4_abs_v2_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbase : base &&& 1 = 0)
    (hv2 :
      v2 =
        ((EvmAsm.Evm64.clzResult (sdivAbsSum0 divisorLimb0 divisorTop)).2 >>>
          (63 : Nat)))
    (hbnz :
      sdivAbsSum0 divisorLimb0 divisorTop |||
        sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop |||
        sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop |||
        sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop ≠ 0)
    (hb3z : sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0)
    (hb2z : sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0)
    (hb1z : sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop = 0)
    (hshift_nz : (EvmAsm.Evm64.clzResult (sdivAbsSum0 divisorLimb0 divisorTop)).1 ≠ 0)
    (halign : EvmAsm.Evm64.fullDivN1CallMaxmaxmaxExactInputAligned sp
      (base + wrapperEndOff) jMem (1 : Word)
      (EvmAsm.Evm64.fullDivN1Shift (sdivAbsSum0 divisorLimb0 divisorTop))
      (EvmAsm.Evm64.fullDivN1NormU
        (sdivAbsSum0 dividendLimb0 dividendTop)
        (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
        (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsSum0 divisorLimb0 divisorTop)).1
      (sdivAbsSum0 dividendLimb0 dividendTop >>>
        ((EvmAsm.Evm64.fullDivN1AntiShift
          (sdivAbsSum0 divisorLimb0 divisorTop)).toNat % 64))
      (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (EvmAsm.Evm64.fullDivN1AntiShift (sdivAbsSum0 divisorLimb0 divisorTop))
      (sdivAbsSum0 dividendLimb0 dividendTop)
      (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
      (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum0 divisorLimb0 divisorTop)
      (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
      (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem ((base + divCallOff) + 4))
    (hbltu3 : EvmAsm.Evm64.isTrialN1_j3 true
      (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsSum0 divisorLimb0 divisorTop))
    (hbltu2 : ¬BitVec.ult
      (EvmAsm.Evm64.loopN1CallMaxmaxmaxR3
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.1
        (EvmAsm.Evm64.fullDivN1NormV
          (sdivAbsSum0 divisorLimb0 divisorTop)
          (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
          (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.2
        (EvmAsm.Evm64.fullDivN1NormU
          (sdivAbsSum0 dividendLimb0 dividendTop)
          (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
          (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum0 divisorLimb0 divisorTop)).2.2.2.1
        (EvmAsm.Evm64.fullDivN1NormU
          (sdivAbsSum0 dividendLimb0 dividendTop)
          (sdivAbsSum1 dividendLimb0 dividendLimb1 dividendTop)
          (sdivAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsSum0 divisorLimb0 divisorTop)).2.2.2.2
        0 0 0).2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1)
    (hbltu1 :
      sdivN1V4Hbltu1 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hbltu0 :
      sdivN1V4Hbltu0 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hcarry2 : EvmAsm.Evm64.Carry2NzAll
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.1
      (EvmAsm.Evm64.fullDivN1NormV
        (sdivAbsSum0 divisorLimb0 divisorTop)
        (sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop)
        (sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
        (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).2.2.2)
    (hdiv0 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 0 =
        sdivN1V4Quot0 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hdiv1 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 1 =
        sdivN1V4Quot1 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hdiv2 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 2 =
        sdivN1V4Quot2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
    (hdiv3 :
      (EvmAsm.Evm64.EvmWord.div
        (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
        (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)).getLimbN 3 =
        sdivN1V4Quot3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ
        sdivN1V4ScratchOut dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop scratchMem))) := by
  subst v2
  exact
    saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4_abs_spec_in_sdivCodeV4
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v5 v6
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      hbase hbnz hb3z hb2z hb1z hshift_nz halign hbltu3 hbltu2 hbltu1
      hbltu0 hcarry2 hdiv0 hdiv1 hdiv2 hdiv3

/-- Exact SDIV div-call handoff specialized to the N1/v4 scratch frame shape,
    accepting the N1 path's native bound and lifting it to `unifiedDivBound`. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4Scratch_bound_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem scratchOut : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin
        ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ (EvmAsm.Rv64.signExtend12 4095 : Word))) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchOut))) := by
  apply
    saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_n1_v4Scratch_spec_in_sdivCodeV4
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem scratchOut
      hbase
  exact
    EvmAsm.Evm64.evm_div_n1_call_maxmaxmax_stack_spec_within_word_noNop_v4_preNoX1_callableExtra_bound_unified
      (base + wrapperEndOff) hStack

end EvmAsm.Evm64.SDiv.Compose
