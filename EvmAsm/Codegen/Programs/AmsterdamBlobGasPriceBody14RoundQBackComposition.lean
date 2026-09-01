/- Source-level closure of the K70 Taylor round QBACK exit. -/

/- PR #18: Parity + OuterFold folded into QBack (namespace preserved). -/

import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundMul5FFQOVFComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Backedge
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceAbiShell
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody6Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody10Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
open EvmAsm.Codegen.AmsterdamBlobGasPrice

set_option maxRecDepth 8000

/- The source exit list is concrete: `taylor_round` has no residual tail.
   Naming it here lets the final composition discharge `rest` instead of
   carrying an existential beyond the last source exit. -/
@[reducible] def taylorRoundSourceFull
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v5 _v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) :
    List (Word × Assertion) :=
  [(PriceK + 804,
      taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceMul0 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceMul1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceMul3 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceMul4 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceMul5 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceMulFF newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 964,
      taylorRoundSourceQOVFComputed newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 144,
      taylorRoundSourceQBACKComputed newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)]

theorem taylor_round_source_full_from_taylor_round
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v5 v6 v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceFull newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v5 v6 v7 v28 v29 v30 v31 FR) := by
  have h := taylor_round newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR hFR
  simpa only [taylorRoundSourceFull, taylorRoundSourcePre,
    taylorRoundSourceZero, taylorRoundSourceCap, taylorRoundSourceCarry,
    taylorRoundSourceMul0, taylorRoundSourceMul1, taylorRoundSourceMul2,
    taylorRoundSourceMul3, taylorRoundSourceMul4, taylorRoundSourceMul5,
    taylorRoundSourceMulFF, taylorRoundSourceQOVFComputed,
    taylorRoundSourceQOVF, taylorRoundSourceQBACKComputed,
    taylorRoundSourceQBACK, roundAccum, roundP0, roundP1, roundP2,
    roundP3, roundP4, roundP5, taylorRoundFinalHigh,
    taylorRoundFinalOverflow, roundS0, roundS1, roundS2, roundS3,
    roundS4, roundS5] using h

/- The concrete source list above is the final boundary for this round.  This
   theorem consumes every source exit that has a one-instruction status tail;
   QBACK is deliberately retained as the last entry for the closure theorem
   below.  Unlike the intermediate siblings, there is no existential tail. -/
theorem taylor_round_source_full_status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree)
    {exits : List (Word × Assertion)}
    (hZero : cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits) :
    cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          [(PriceK + 968,
            taylorRoundTerminalStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundCarryStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
           taylorRoundSourceMul2Status1 newSp excess outPtr iVal AB PB vals
             a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
           taylorRoundSourceMul3Status1 newSp excess outPtr iVal AB PB vals
             a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
           taylorRoundSourceMul4Status1 newSp excess outPtr iVal AB PB vals
             a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul5Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 144,
            taylorRoundSourceQBACKComputed newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))]) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  have hRound := taylor_round_source_full_from_taylor_round
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR0 hFR0
  let source0 : Assertion :=
    taylorRoundSourceMul0 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let source1 : Assertion :=
    taylorRoundSourceMul1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let source2 : Assertion :=
    taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let source3 : Assertion :=
    taylorRoundSourceMul3 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let source4 : Assertion :=
    taylorRoundSourceMul4 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let source5 : Assertion :=
    taylorRoundSourceMul5 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let sourceFF : Assertion :=
    taylorRoundSourceMulFF newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let sourceQOVF : Assertion :=
    taylorRoundSourceQOVFComputed newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let sourceQBACK : Assertion :=
    taylorRoundSourceQBACKComputed newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let terminalPre : Assertion :=
    (.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
      ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
      ((.x0 ↦ᵣ (0 : Word)) **
        roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5 FR0)
  let terminalOut : Assertion :=
    taylorRoundTerminalStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let carryOut : Assertion :=
    taylorRoundCarryStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  let out0 : Assertion :=
    taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  let out1 : Assertion :=
    taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  let out2 : Assertion :=
    taylorRoundSourceMul2Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      FR0
  let out3 : Assertion :=
    taylorRoundSourceMul3Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      FR0
  let out4 : Assertion :=
    taylorRoundSourceMul4Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      FR0
  let out5 : Assertion :=
    taylorRoundSourceMul5Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let outFF : Assertion :=
    taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  let outQOVF : Assertion :=
    taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  have hRound' :
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((PriceK + 804,
            taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0) ::
          (PriceK + 964,
            taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0) ::
          (PriceK + 964,
            taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0) ::
          (PriceK + 964, source0) :: (PriceK + 964, source1) ::
          (PriceK + 964, source2) :: (PriceK + 964, source3) ::
          (PriceK + 964, source4) :: (PriceK + 964, source5) ::
          (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
          [(PriceK + 144, sourceQBACK)]) := by
    simpa only [taylorRoundSourceFull, source0, source1, source2, source3,
      source4, source5, sourceFF, sourceQOVF, sourceQBACK,
      List.cons_append, List.nil_append, List.append_assoc] using hRound
  have hZero' :
      cpsNBranchWithin 4183 (PriceK + 804) priceCode
        (roundZero newSp excess outPtr iVal AB PB vals
          (roundAccum a0 a1 a2 a3 a4 a5)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v7 v28 v29 v30 v31 FR0) exits := by
    simpa only [FR0] using hZero
  have hZero_pre : ∀ h,
      taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h →
      roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 v7 v28 v29 v30 v31 FR0 h := by
    intro h hp
    simp only [taylorRoundSourceZero, roundZero, roundFrame,
      roundAccum, EvmAsm.Rv64.AddrNorm.se12_0,
      EvmAsm.Rv64.AddrNorm.se12_8, EvmAsm.Rv64.AddrNorm.se12_16,
      EvmAsm.Rv64.AddrNorm.se12_24, EvmAsm.Rv64.AddrNorm.se12_32,
      EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  have hTerm := terminalIndex_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hTerm_pre : ∀ h,
      taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h → terminalPre h := by
    intro h hp
    simp only [terminalPre, taylorRoundSourceCap, roundFrame,
      EvmAsm.Rv64.AddrNorm.se12_0,
      EvmAsm.Rv64.AddrNorm.se12_8, EvmAsm.Rv64.AddrNorm.se12_16,
      EvmAsm.Rv64.AddrNorm.se12_24, EvmAsm.Rv64.AddrNorm.se12_32,
      EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  let c : Word := rCry a5 s5 (rCry a4 s4 (rCry a3 s3
    (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
  let t0 : Word := (a0 + s0) + 0
  let t1 : Word := (a1 + s1) + rCry a0 s0 0
  let t2 : Word := (a2 + s2) + rCry a1 s1 (rCry a0 s0 0)
  let t3 : Word := (a3 + s3) + rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))
  let t4 : Word := (a4 + s4) + rCry a3 s3
    (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))
  let t5 : Word := (a5 + s5) + rCry a4 s4
    (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))
  let carryPre : Assertion :=
    (((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝) **
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (vals .x1)) **
        (.x10 ↦ᵣ excess) ** (.x11 ↦ᵣ outPtr) **
        (.x8 ↦ᵣ excess) ** (.x9 ↦ᵣ taylorDW) **
        (.x18 ↦ᵣ iVal) ** (.x19 ↦ᵣ AB) ** (.x20 ↦ᵣ PB) **
        (.x21 ↦ᵣ outPtr) ** (.x22 ↦ᵣ (newSp + signExtend12 160)) **
        (.x6 ↦ᵣ a5) ** (.x7 ↦ᵣ s5) ** (.x28 ↦ᵣ (a5 + s5)) **
        (.x29 ↦ᵣ c) ** (.x30 ↦ᵣ t5) **
        (.x31 ↦ᵣ (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)) **
        frameSlotsSaved priceFrame newSp vals **
        ((AB + signExtend12 0) ↦ₘ a0) **
        ((AB + signExtend12 8) ↦ₘ a1) **
        ((AB + signExtend12 16) ↦ₘ a2) **
        ((AB + signExtend12 24) ↦ₘ a3) **
        ((AB + signExtend12 32) ↦ₘ a4) **
        ((AB + signExtend12 40) ↦ₘ a5) **
        ((PB + signExtend12 0) ↦ₘ p0) **
        ((PB + signExtend12 8) ↦ₘ p1) **
        ((PB + signExtend12 16) ↦ₘ p2) **
        ((PB + signExtend12 24) ↦ₘ p3) **
        ((PB + signExtend12 32) ↦ₘ p4) **
        ((PB + signExtend12 40) ↦ₘ p5) **
        (((newSp + signExtend12 160) + signExtend12 0) ↦ₘ t0) **
        (((newSp + signExtend12 160) + signExtend12 8) ↦ₘ t1) **
        (((newSp + signExtend12 160) + signExtend12 16) ↦ₘ t2) **
        (((newSp + signExtend12 160) + signExtend12 24) ↦ₘ t3) **
        (((newSp + signExtend12 160) + signExtend12 32) ↦ₘ t4) **
        (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ t5) ** FR0))
  let carryOut : Assertion :=
    taylorRoundCarryStatus1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  have hCarry := add6Carry_status1_tail
    newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5) c t5
      (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR0 hFR0
  have hCarry_pre : ∀ h,
      taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h → carryPre h := by
    intro h hp
    simp only [carryPre, c, t0, t1, t2, t3, t4, t5,
      taylorRoundSourceCarry, EvmAsm.Rv64.AddrNorm.se12_0,
      EvmAsm.Rv64.AddrNorm.se12_8, EvmAsm.Rv64.AddrNorm.se12_16,
      EvmAsm.Rv64.AddrNorm.se12_24, EvmAsm.Rv64.AddrNorm.se12_32,
      EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  have hFirst := taylor_round_zero_terminal_carry_status1
    (rest := (PriceK + 964, source0) :: (PriceK + 964, source1) ::
      (PriceK + 964, source2) :: (PriceK + 964, source3) ::
      (PriceK + 964, source4) :: (PriceK + 964, source5) ::
      (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
      [(PriceK + 144, sourceQBACK)])
    hRound' hZero' hZero_pre hTerm hTerm_pre hCarry hCarry_pre
  have hFirst' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut)]) ++
          ((PriceK + 964, source0) :: (PriceK + 964, source1) ::
            (PriceK + 964, source2) :: (PriceK + 964, source3) ::
            (PriceK + 964, source4) :: (PriceK + 964, source5) ::
            (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
            [(PriceK + 144, sourceQBACK)])) := by
    simpa only [terminalOut, carryOut, List.cons_append, List.nil_append,
      List.append_assoc] using hFirst
  have hMul0 := taylor_round_source_mul0_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter0 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut)])
    (mid := PriceK + 964) (Qm := source0)
    (rest := (PriceK + 964, source1) :: (PriceK + 964, source2) ::
      (PriceK + 964, source3) :: (PriceK + 964, source4) ::
      (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
      (PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])
    hFirst' (cpsTripleWithin_as_cpsNBranchWithin hMul0)
  have hAfter0' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
          (PriceK + 968, out0)]) ++
          ((PriceK + 964, source1) :: (PriceK + 964, source2) ::
            (PriceK + 964, source3) :: (PriceK + 964, source4) ::
            (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
            (PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])) := by
    simpa only [out0, List.cons_append, List.nil_append, List.append_assoc,
      Nat.add_assoc] using hAfter0
  have hMul1 := taylor_round_source_mul1_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter1 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
      (PriceK + 968, out0)])
    (mid := PriceK + 964) (Qm := source1)
    (rest := (PriceK + 964, source2) :: (PriceK + 964, source3) ::
      (PriceK + 964, source4) :: (PriceK + 964, source5) ::
      (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
      [(PriceK + 144, sourceQBACK)])
    hAfter0' (cpsTripleWithin_as_cpsNBranchWithin hMul1)
  have hAfter1' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
          (PriceK + 968, out0), (PriceK + 968, out1)]) ++
          ((PriceK + 964, source2) :: (PriceK + 964, source3) ::
            (PriceK + 964, source4) :: (PriceK + 964, source5) ::
            (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
            [(PriceK + 144, sourceQBACK)])) := by
    simpa only [out1, List.cons_append, List.nil_append, List.append_assoc,
      Nat.add_assoc] using hAfter1
  have hMul2 := taylor_round_source_mul2_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter2 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
      (PriceK + 968, out0), (PriceK + 968, out1)])
    (mid := PriceK + 964) (Qm := source2)
    (rest := (PriceK + 964, source3) :: (PriceK + 964, source4) ::
      (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
      (PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])
    hAfter1' (cpsTripleWithin_as_cpsNBranchWithin hMul2)
  have hAfter2' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
          (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2)]) ++
          ((PriceK + 964, source3) :: (PriceK + 964, source4) ::
            (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
            (PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])) := by
    simpa only [out2, List.cons_append, List.nil_append, List.append_assoc,
      Nat.add_assoc] using hAfter2
  have hMul3 := taylor_round_source_mul3_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter3 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
      (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2)])
    (mid := PriceK + 964) (Qm := source3)
    (rest := (PriceK + 964, source4) :: (PriceK + 964, source5) ::
      (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
      [(PriceK + 144, sourceQBACK)])
    hAfter2' (cpsTripleWithin_as_cpsNBranchWithin hMul3)
  have hAfter3' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
          (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3)]) ++
          ((PriceK + 964, source4) :: (PriceK + 964, source5) ::
            (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
            [(PriceK + 144, sourceQBACK)])) := by
    simpa only [out3, List.cons_append, List.nil_append, List.append_assoc,
      Nat.add_assoc] using hAfter3
  have hMul4 := taylor_round_source_mul4_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter4 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
      (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3)])
    (mid := PriceK + 964) (Qm := source4)
    (rest := (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
      (PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])
    hAfter3' (cpsTripleWithin_as_cpsNBranchWithin hMul4)
  have hAfter4' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
          (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3), (PriceK + 968, out4)]) ++
          ((PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
            (PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])) := by
    simpa only [out4, List.cons_append, List.nil_append, List.append_assoc,
      Nat.add_assoc] using hAfter4
  have hMul5 := taylor_round_source_mul5_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter5 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
      (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3), (PriceK + 968, out4)])
    (mid := PriceK + 964) (Qm := source5)
    (rest := (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
      [(PriceK + 144, sourceQBACK)])
    hAfter4' (cpsTripleWithin_as_cpsNBranchWithin hMul5)
  have hAfter5' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
          (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3), (PriceK + 968, out4), (PriceK + 968, out5)]) ++
          ((PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
            [(PriceK + 144, sourceQBACK)])) := by
    simpa only [out5, List.cons_append, List.nil_append, List.append_assoc,
      Nat.add_assoc] using hAfter5
  have hMulFF := taylor_round_source_mulFF_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfterFF := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
      (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3), (PriceK + 968, out4), (PriceK + 968, out5)])
    (mid := PriceK + 964) (Qm := sourceFF)
    (rest := (PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])
    hAfter5' (cpsTripleWithin_as_cpsNBranchWithin hMulFF)
  have hAfterFF' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
          (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3), (PriceK + 968, out4), (PriceK + 968, out5),
          (PriceK + 968, outFF)]) ++
          ((PriceK + 964, sourceQOVF) :: [(PriceK + 144, sourceQBACK)])) := by
    simpa only [outFF, List.cons_append, List.nil_append, List.append_assoc,
      Nat.add_assoc] using hAfterFF
  have hQOVF := taylor_round_source_qovf_computed_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5
    s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfterQOVF := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut),
      (PriceK + 968, out0), (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3), (PriceK + 968, out4), (PriceK + 968, out5),
      (PriceK + 968, outFF)])
    (mid := PriceK + 964) (Qm := sourceQOVF)
    (rest := [(PriceK + 144, sourceQBACK)])
    hAfterFF' (cpsTripleWithin_as_cpsNBranchWithin hQOVF)
  simpa only [FR0, terminalOut, carryOut, out0, out1, out2, out3, out4,
    out5, outFF, outQOVF, sourceQBACK, List.cons_append, List.nil_append,
    List.append_assoc, Nat.add_assoc] using hAfterQOVF

/- The final source entry is the concrete QBACK post.  At the linked call site
   its two workspace bases are the parity-selected buffers, so the existing
   backedge adapter closes it directly into the next outer-loop invariant. -/
theorem taylor_round_source_qback_computed_to_parity
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) :
    ∀ h,
      taylorRoundSourceQBACKComputed newSp excess outPtr iVal
        (parityBuffer j evenBase oddBase)
        (parityBuffer j oddBase evenBase) vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR h →
      (taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
        (iVal + signExtend12 (1 : BitVec 12)) evenBase oddBase
        (taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5)
        [a0, a1, a2, a3, a4, a5]
        (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR **
        (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  apply taylor_round_backedge_to_parity newSp excess outPtr iVal vals
    j evenBase oddBase a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 FR h
  simpa only [taylorRoundSourceQBACKComputed, taylorRoundSourceQBACK,
    taylorRoundBackedgePost, roundQBACK, QBACKP,
    EvmAsm.Codegen.AmsterdamBlobGasPriceBody11Spec.QBACKP,
    EvmAsm.Rv64.AddrNorm.word_add_zero] using hp

/- Replace only the last exit post of an N-branch.  Keeping this helper local
   makes the status exits above remain the exact source exits while the final
   QBACK post is discharged into the parity invariant. -/
private theorem nb_weaken_last_post
    {n : Nat} {entry m : Word} {cr : CodeReq} {P Q Q' : Assertion}
    {pre : List (Word × Assertion)}
    (hQ : ∀ h, Q h → Q' h)
    (h : cpsNBranchWithin n entry cr P (pre ++ [(m, Q)])) :
    cpsNBranchWithin n entry cr P (pre ++ [(m, Q')]) := by
  apply cpsNBranchWithin_weaken_posts h
  intro ex hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hpre | rfl
  · exact ⟨ex, List.mem_append.mpr (Or.inl hpre), rfl, fun _ hx => hx⟩
  · exact ⟨(m, Q'), List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)),
      rfl, hQ⟩

/- The full round composition with the final QBACK source post closed into
   the next outer-loop parity invariant.  The equality hypotheses identify
   the caller's two workspace bases with the parity-selected physical
   buffers; the remaining ten exits are the status exits of the round. -/
theorem taylor_round_source_full_status1_to_parity
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree)
    (hAB_parity : AB = parityBuffer j evenBase oddBase)
    (hPB_parity : PB = parityBuffer j oddBase evenBase)
    {exits : List (Word × Assertion)}
    (hZero : cpsNBranchWithin 4183 (PriceK + 804) priceCode
      (roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits) :
    cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          [(PriceK + 968,
            taylorRoundTerminalStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundCarryStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul2Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul3Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul4Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMul5Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 968,
            taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)),
           (PriceK + 144,
            taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
              (iVal + signExtend12 (1 : BitVec 12)) evenBase oddBase
              (taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5)
              [a0, a1, a2, a3, a4, a5]
              (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)
                (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
              (.x0 ↦ᵣ (0 : Word)))]) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  let qbackPost : Assertion :=
    taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
      (iVal + signExtend12 (1 : BitVec 12)) evenBase oddBase
      (taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5)
      [a0, a1, a2, a3, a4, a5]
      (taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) **
      (.x0 ↦ᵣ (0 : Word))
  have hStatus := taylor_round_source_full_status1
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR
    (exits := exits) hZero
  have hStatus' :
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++
          [(PriceK + 968,
            taylorRoundTerminalStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0),
           (PriceK + 968,
            taylorRoundCarryStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
           (PriceK + 968,
            taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
           (PriceK + 968,
            taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
           (PriceK + 968,
            taylorRoundSourceMul2Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
           (PriceK + 968,
            taylorRoundSourceMul3Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
           (PriceK + 968,
            taylorRoundSourceMul4Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0),
           (PriceK + 968,
            taylorRoundSourceMul5Status1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0),
           (PriceK + 968,
            taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0),
           (PriceK + 968,
            taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0)]) ++
          [(PriceK + 144,
            taylorRoundSourceQBACKComputed newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR0)]) := by
    simpa only [FR0, List.append_assoc, List.cons_append, List.nil_append] using hStatus
  have hQ : ∀ h,
      taylorRoundSourceQBACKComputed newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0 h → qbackPost h := by
    intro h hp
    unfold qbackPost
    apply (taylor_round_source_qback_computed_to_parity newSp excess outPtr iVal vals
      j evenBase oddBase a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0 h)
    rw [hAB_parity, hPB_parity] at hp
    exact hp
  have hFinal := nb_weaken_last_post hQ hStatus'
  simpa only [FR0, qbackPost, List.append_assoc, List.cons_append, List.nil_append] using hFinal

#print axioms taylor_round_source_full_from_taylor_round
#print axioms taylor_round_source_full_status1
#print axioms taylor_round_source_qback_computed_to_parity
#print axioms taylor_round_source_full_status1_to_parity

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
namespace EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
open EvmAsm.Codegen.AmsterdamBlobGasPrice

set_option maxRecDepth 8000

/- The physical exit-divide buffers alternate with the outer-loop parity.  This
   helper is deliberately stated at the zero arm: it is the small boundary at
   which the linked tail is consumed, before the rest of the round is folded. -/
theorem round_zero_from_parity_tail_core
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hEvenBase : evenBase = newSp + signExtend12 (64 : BitVec 12))
    (hOddBase : oddBase = newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) :
    ∃ exits : List (Word × Assertion),
      cpsNBranchWithin 4183 (PriceK + 804) priceCode
        (roundZero newSp excess outPtr iVal
          (parityBuffer j evenBase oddBase)
          (parityBuffer j oddBase evenBase) vals
          (roundAccum a0 a1 a2 a3 a4 a5)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5
          v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits := by
  by_cases h_even : j % 2 = 0
  · have hAB : parityBuffer j evenBase oddBase =
        newSp + signExtend12 (64 : BitVec 12) := by
      simp [parityBuffer, h_even, hEvenBase]
    have hPB : parityBuffer j oddBase evenBase =
        newSp + signExtend12 (112 : BitVec 12) := by
      simp [parityBuffer, h_even, hOddBase]
    have hTail := exitdiv_tail_core_x0_split
      newSp excess outPtr iVal vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      o0 o1 o2 o3 (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) FR
      hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
    have hZero := EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec.round_zero_exitdiv_tail
      newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB hTail
    exact ⟨_, hZero⟩
  · have h_odd : j % 2 = 1 := by omega
    have hAB : parityBuffer j evenBase oddBase =
        newSp + signExtend12 (112 : BitVec 12) := by
      simp [parityBuffer, h_odd, hOddBase]
    have hPB : parityBuffer j oddBase evenBase =
        newSp + signExtend12 (64 : BitVec 12) := by
      simp [parityBuffer, h_odd, hEvenBase]
    /- The parity swaps are a matched pair: pass the p-limbs first so the
       physical tail cells still match the logical AB/PB view.  Swapping only
       the bases or only the limb arguments would silently exchange the
       logical buffers rather than preserve this round's assertion. -/
    have hTail := exitdiv_tail_core_x0_split
      newSp excess outPtr iVal vals
      p0 p1 p2 p3 p4 p5 a0 a1 a2 a3 a4 a5
      s0 s1 s2 s3 s4 s5 o0 o1 o2 o3
      (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) FR
      hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
    have hZero := round_zero_exitdiv_tail_swapped
      newSp excess outPtr iVal
      (parityBuffer j evenBase oddBase)
      (parityBuffer j oddBase evenBase) vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB hTail
    exact ⟨_, hZero⟩

/- The source-round adapter can now consume the linked tail at either parity.
   The existential only hides the two private tail posts produced by
   `exitdiv_tail_core_x0_split`; `taylor_round_source_full_status1_to_parity`
   still supplies every fixed overflow/status arm and the parity backedge. -/
theorem taylor_round_source_full_from_parity_tail_core
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hEvenBase : evenBase = newSp + signExtend12 (64 : BitVec 12))
    (hOddBase : oddBase = newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) :
    ∃ exits : List (Word × Assertion),
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal
          (parityBuffer j evenBase oddBase)
          (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits := by
  obtain ⟨tailExits, hZero⟩ := round_zero_from_parity_tail_core
    newSp excess outPtr iVal vals j evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
    o0 o1 o2 o3 FR hEvenBase hOddBase
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
  have hFull := EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec.taylor_round_source_full_status1_to_parity
    newSp excess outPtr iVal
    (parityBuffer j evenBase oddBase)
    (parityBuffer j oddBase evenBase) vals j evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31
    o0 o1 o2 o3 FR hFR rfl rfl (exits := tailExits) hZero
  exact ⟨_, hFull⟩

/- Source-preserving sibling for the model-linked outer fold.  The ordinary
   adapter above closes the final QBACK into the parity invariant, which is
   the right public post for callers that do not inspect the recurrence.  The
   outer model needs the concrete QBACK representation first, so retain that
   last exit here and leave its conversion to the model bridge. -/
theorem taylor_round_source_full_from_parity_tail_core_source
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (j : Nat) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hEvenBase : evenBase = newSp + signExtend12 (64 : BitVec 12))
    (hOddBase : oddBase = newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) :
    ∃ exits : List (Word × Assertion),
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal
          (parityBuffer j evenBase oddBase)
          (parityBuffer j oddBase evenBase) vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) exits := by
  obtain ⟨tailExits, hZero⟩ := round_zero_from_parity_tail_core
    newSp excess outPtr iVal vals j evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    s0 s1 s2 s3 s4 s5 v7 v28 v29 v30 v31
    o0 o1 o2 o3 FR hEvenBase hOddBase
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
  have hFull := EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec.taylor_round_source_full_status1
    newSp excess outPtr iVal
    (parityBuffer j evenBase oddBase)
    (parityBuffer j oddBase evenBase) vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    s0 s1 s2 s3 s4 s5 v5 v6 v7 v28 v29 v30 v31
    o0 o1 o2 o3 FR hFR (exits := tailExits) hZero
  exact ⟨_, hFull⟩

#print axioms round_zero_from_parity_tail_core
#print axioms taylor_round_source_full_from_parity_tail_core
#print axioms taylor_round_source_full_from_parity_tail_core_source

end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
namespace EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Stateless.SpecRef
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceDivisionBridge
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

set_option exponentiation.threshold 384
set_option maxRecDepth 8000

/- The linked QBACK post carries six concrete quotient limbs.  These small
   bridges turn the pure 384-bit division/addition results into the canonical
   limb lists used by the model, without putting an arithmetic premise on the
   machine post. -/
theorem div384by64_quot_to_natToLimbs
    (d : Word) (ws : List Word) (n : Nat)
    (hd : 0 < d.toNat) (hd63 : d.toNat ≤ 2 ^ 63)
    (hlen : ws.length = 6)
    (hval : limbsToNat ws / d.toNat = n) :
    (div384by64 d ws).1 = natToLimbs 6 n := by
  have hquot := div384by64_quot d ws hd hd63
  have hquot_val : limbsToNat (div384by64 d ws).1 = n := by
    rw [hquot, hval]
  have hquot_len : (div384by64 d ws).1.length = 6 := by
    rw [div384by64_length, hlen]
  have hquot_bound :
      limbsToNat (div384by64 d ws).1 < 2 ^ (64 * 6) :=
    limbsToNat_lt _ 6 hquot_len
  apply natToLimbs_eq_of_limbsToNat
    (div384by64 d ws).1 6 n hquot_len
  · rw [← hquot_val]
    exact hquot_bound
  · exact hquot_val

theorem add384_low_to_natToLimbs
    (as ss : List Word) (n : Nat)
    (hlen : as.length = 6) (hlen2 : ss.length = 6)
    (hsum : limbsToNat as + limbsToNat ss < 2 ^ 384)
    (hval : limbsToNat as + limbsToNat ss = n) :
    (add384Run as ss (0 : Word)).1 = natToLimbs 6 n := by
  have hlow := add384_low_of_lt as ss hlen hlen2 hsum
  have hout_len : (add384Run as ss (0 : Word)).1.length = 6 := by
    rw [add384Run_length as ss 0 (by omega)]
    exact hlen
  have hout_bound :
      limbsToNat (add384Run as ss (0 : Word)).1 < 2 ^ (64 * 6) :=
    limbsToNat_lt _ 6 hout_len
  have hn_bound : n < 2 ^ (64 * 6) := by
    have hn_bound' : n < 2 ^ 384 := by
      rw [← hval]
      exact hsum
    simpa only [show 64 * 6 = 384 by decide] using hn_bound'
  apply natToLimbs_eq_of_limbsToNat
    (add384Run as ss (0 : Word)).1 6 n hout_len hn_bound
  rw [hlow, hval]

/- These irreducible wrappers keep the machine-shaped lists folded while the
   model bridge is elaborated.  The equalities below identify them with the
   existing source post definitions, so they do not introduce a second
   computation. -/
@[irreducible] def qbackWordsModel
    (iVal excess a0 a1 a2 a3 a4 a5 : Word) : List Word :=
  (divstSix (taylorDW * iVal)
    (roundP0 a0 excess) (roundP1 a0 a1 excess)
    (roundP2 a0 a1 a2 excess) (roundP3 a0 a1 a2 a3 excess)
    (roundP4 a0 a1 a2 a3 a4 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)).1

@[irreducible] def sbackWordsModel
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) : List Word :=
  (add384Run [a0, a1, a2, a3, a4, a5]
    [s0, s1, s2, s3, s4, s5] (0 : Word)).1

theorem qbackWordsModel_eq_existing
    (iVal excess a0 a1 a2 a3 a4 a5 : Word) :
    qbackWordsModel iVal excess a0 a1 a2 a3 a4 a5 =
      taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5 := by
  unfold qbackWordsModel taylorRoundBackedgeQuotient
  rfl

theorem sbackWordsModel_eq_existing
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) :
    sbackWordsModel a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 =
      taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 := by
  unfold sbackWordsModel taylorRoundBackedgeSum
  rw [roundS_eq_add384Run]

/- The linked exit-divide window is the Body5 mirror of the Body3 divider
   already connected to the pure model by `DivisionBridge`.  Keep the
   namespace bridge explicit: the two source files deliberately duplicate
   the machine definition, so an unqualified `divst` is not enough to make
   this equality visible to Lean. -/
theorem body5_divst_eq_body3_divst
    (dv r0 t0 q0 : Word) (j : Nat) :
    AmsterdamBlobGasPriceBody5Spec.divst dv r0 t0 q0 j =
      AmsterdamBlobGasPriceBody3Spec.divst dv r0 t0 q0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [AmsterdamBlobGasPriceBody5Spec.divst,
      AmsterdamBlobGasPriceBody3Spec.divst]
    rw [ih]

/- `exitdivQ*` are the quotient limbs of the linked Body5 mirror.  This
   theorem only changes representation: it identifies their six-step list
   with the Body3-shaped `divstSix` consumed by `DivisionBridge`. -/
theorem exitdiv_q_eq_divstSix
    (s0 s1 s2 s3 s4 s5 : Word) :
    [exitdivQ0 s0 s1 s2 s3 s4 s5, exitdivQ1 s0 s1 s2 s3 s4 s5,
      exitdivQ2 s0 s1 s2 s3 s4 s5, exitdivQ3 s0 s1 s2 s3 s4 s5,
      exitdivQ4 s0 s1 s2 s3 s4 s5, exitdivQ5 s0 s1 s2 s3 s4 s5] =
      (AmsterdamBlobGasPriceDivisionBridge.divstSix
        EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec.taylorDW
        s0 s1 s2 s3 s4 s5).1 := by
  simp only [exitdivQ0, exitdivQ1, exitdivQ2, exitdivQ3, exitdivQ4,
    exitdivQ5, exitdivZ0, exitdivZ1, exitdivZ2, exitdivZ3, exitdivZ4,
    exitdivZ5, AmsterdamBlobGasPriceDivisionBridge.divstSix]
  simp only [body5_divst_eq_body3_divst]

/- The terminal exit-divide is the model's final `sum / D`.  At a successful
   model result, the prefix invariant at `j = 495` has zero accumulator, so
   the linked six-limb sum is exactly the quotient input consumed by
   `exitdivQ*`.  This is a terminal step lemma, not a new machine-post
   premise: all arithmetic facts come from the existing `h_some` result and
   the invariant's sum equality. -/
theorem exitdiv_q_model_step
    (num result : Nat) (s0 s1 s2 s3 s4 s5 : Word)
    (h_num : num < taylorWord64Bound)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_s : limbsToNat [s0, s1, s2, s3, s4, s5] =
      (priceLoopPrefix num 495).2) :
    [exitdivQ0 s0 s1 s2 s3 s4 s5, exitdivQ1 s0 s1 s2 s3 s4 s5,
      exitdivQ2 s0 s1 s2 s3 s4 s5, exitdivQ3 s0 s1 s2 s3 s4 s5,
      exitdivQ4 s0 s1 s2 s3 s4 s5, exitdivQ5 s0 s1 s2 s3 s4 s5] =
      natToLimbs 6 result := by
  have h_zero := priceLoopPrefix_acc_zero_of_some num result h_num h_some
  have h_rel := priceLoopPrefix_taylorNatAux num 495
  rw [taylorNatAux.eq_1, if_pos h_zero] at h_rel
  have h_init := taylor384Aux_some_implies_nat_lt
    num 1 taylorDenominator 0 result h_some
  have h_result : (priceLoopPrefix num 495).2 / taylorDenominator = result := by
    rw [h_rel, h_init.2]
  have hval : limbsToNat [s0, s1, s2, s3, s4, s5] /
      taylorDW.toNat = result := by
    rw [h_s]
    have hD : taylorDW.toNat = taylorDenominator := by decide
    rw [hD, h_result]
  have hdiv := AmsterdamBlobGasPriceDivisionBridge.divstSix_eq_div384by64
    taylorDW s0 s1 s2 s3 s4 s5
  have hq := div384by64_quot_to_natToLimbs
    taylorDW [s0, s1, s2, s3, s4, s5] result
    (by decide) (by decide) (by simp) hval
  have hq' :
      (AmsterdamBlobGasPriceDivisionBridge.divstSix
        taylorDW s0 s1 s2 s3 s4 s5).1 = natToLimbs 6 result := by
    rw [hdiv]
    exact hq
  rw [exitdiv_q_eq_divstSix]
  exact hq'

/- QBACK's quotient is the next model accumulator when the ordinary
   recurrence is still live.  The `some` hypothesis supplies the strict
   256-bit result bound; the local `h_acc` and `h_j` hypotheses are the same
   guards that the emitted round has already taken. -/
theorem qbackWordsModel_eq_prefix
    (num result j : Nat) (iVal excess : Word)
    (a0 a1 a2 a3 a4 a5 : Word)
    (h_num : num < taylorWord64Bound)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_acc : (priceLoopPrefix num j).1 ≠ 0)
    (h_a : limbsToNat [a0, a1, a2, a3, a4, a5] =
      (priceLoopPrefix num j).1)
    (h_i : iVal = taylorLoopIndex j)
    (h_excess : excess.toNat = num)
    (h_j : j < 495) :
    qbackWordsModel iVal excess a0 a1 a2 a3 a4 a5 =
      natToLimbs 6 (priceLoopPrefix num (j + 1)).1 := by
  have hD : taylorDW.toNat = taylorDenominator := by decide
  have hiNat : iVal.toNat = j + 1 := by
    rw [h_i]
    simp [taylorLoopIndex, BitVec.toNat_ofNat]
    have hj : j + 1 ≤ 495 := by omega
    omega
  have hdivisor := priceLoopPrefix_divisor_lt_word64 j h_j
  have hdivisor_pos : 0 < taylorDenominator * (j + 1) := by
    norm_num [taylorDenominator]
  have hdivisor63 : taylorDenominator * (j + 1) ≤ 2 ^ 63 := by
    have hbound : taylorDenominator * 495 ≤ 2 ^ 63 := by decide
    exact le_trans
      (Nat.mul_le_mul_left taylorDenominator (by omega)) hbound
  have hden_value :
      (taylorDW * iVal).toNat = taylorDenominator * (j + 1) := by
    rw [BitVec.toNat_mul, hD, hiNat]
    have hdivisor' : taylorDenominator * (j + 1) < 2 ^ 64 := by
      simpa [taylorWord64Bound] using hdivisor
    exact Nat.mod_eq_of_lt hdivisor'
  have h_product := priceLoopPrefix_product_lt_word384_of_some
    num result j h_num h_some h_acc
  have h_product' : (priceLoopPrefix num j).1 * num < 2 ^ 384 := by
    simpa [taylorWord384Bound] using h_product
  have hmul_value :
      limbsToNat [roundP0 a0 excess, roundP1 a0 a1 excess,
        roundP2 a0 a1 a2 excess, roundP3 a0 a1 a2 a3 excess,
        roundP4 a0 a1 a2 a3 a4 excess,
        roundP5 a0 a1 a2 a3 a4 a5 excess] =
        (priceLoopPrefix num j).1 * num := by
    rw [roundP_eq_mul384Run]
    have hlow := mul384_low_of_lt
      [a0, a1, a2, a3, a4, a5] excess
      (by simp) (by simpa [h_a, h_excess] using h_product')
    rw [hlow, h_a, h_excess]
  have hden_pos : 0 < (taylorDW * iVal).toNat := by
    rw [hden_value]
    exact hdivisor_pos
  have hden_63 : (taylorDW * iVal).toNat ≤ 2 ^ 63 := by
    rw [hden_value]
    exact hdivisor63
  have hqdiv :
      limbsToNat
          [roundP0 a0 excess, roundP1 a0 a1 excess,
            roundP2 a0 a1 a2 excess, roundP3 a0 a1 a2 a3 excess,
            roundP4 a0 a1 a2 a3 a4 excess,
            roundP5 a0 a1 a2 a3 a4 a5 excess] /
          (taylorDW * iVal).toNat =
        (priceLoopPrefix num j).1 * num /
          (taylorDenominator * (j + 1)) := by
    rw [hmul_value, hden_value]
  have hnext :
      (priceLoopPrefix num (j + 1)).1 =
        (priceLoopPrefix num j).1 * num /
          (taylorDenominator * (j + 1)) := by
    rw [priceLoopPrefix_step]
  let ws : List Word :=
    [roundP0 a0 excess, roundP1 a0 a1 excess,
      roundP2 a0 a1 a2 excess, roundP3 a0 a1 a2 a3 excess,
      roundP4 a0 a1 a2 a3 a4 excess,
      roundP5 a0 a1 a2 a3 a4 a5 excess]
  have hws_len : ws.length = 6 := by simp [ws]
  have hq := div384by64_quot_to_natToLimbs
    (taylorDW * iVal) ws (priceLoopPrefix num (j + 1)).1
    hden_pos hden_63 hws_len (by rw [hqdiv, ← hnext])
  unfold qbackWordsModel
  rw [divstSix_eq_div384by64]
  simpa [ws] using hq

theorem sbackWordsModel_eq_prefix
    (num result j : Nat)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_acc : (priceLoopPrefix num j).1 ≠ 0)
    (h_a : limbsToNat [a0, a1, a2, a3, a4, a5] =
      (priceLoopPrefix num j).1)
    (h_s : limbsToNat [s0, s1, s2, s3, s4, s5] =
      (priceLoopPrefix num j).2) :
    sbackWordsModel a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 =
      natToLimbs 6 (priceLoopPrefix num (j + 1)).2 := by
  have hsum := priceLoopPrefix_sum_lt_word384_of_some
    num result j h_some h_acc
  have hsum' : (priceLoopPrefix num j).1 + (priceLoopPrefix num j).2 <
      2 ^ 384 := by
    simpa [taylorWord384Bound, Nat.add_comm] using hsum
  have hsum_value :
      limbsToNat [a0, a1, a2, a3, a4, a5] +
          limbsToNat [s0, s1, s2, s3, s4, s5] =
        (priceLoopPrefix num j).1 + (priceLoopPrefix num j).2 := by
    rw [h_a, h_s]
  have hnext :
      (priceLoopPrefix num (j + 1)).2 =
        (priceLoopPrefix num j).2 + (priceLoopPrefix num j).1 := by
    rw [priceLoopPrefix_step]
  have hlist := add384_low_to_natToLimbs
    [a0, a1, a2, a3, a4, a5] [s0, s1, s2, s3, s4, s5]
    (priceLoopPrefix num (j + 1)).2
    (by simp) (by simp)
    (by simpa [hsum_value, Nat.add_comm] using hsum')
    (by rw [hsum_value, hnext]; omega)
  unfold sbackWordsModel
  exact hlist

/- Convert the concrete QBACK post to the model-linked backedge post.  The
   parity adapter already supplies the machine-state part; these two model
   equalities replace only its quotient and sum lists. -/
theorem taylor_round_qback_model_step
    (num result j : Nat) (newSp excess outPtr iVal : Word)
    (vals : Reg → Word) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (h_num : num < taylorWord64Bound)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_acc : (priceLoopPrefix num j).1 ≠ 0)
    (h_a : limbsToNat [a0, a1, a2, a3, a4, a5] =
      (priceLoopPrefix num j).1)
    (h_s : limbsToNat [s0, s1, s2, s3, s4, s5] =
      (priceLoopPrefix num j).2)
    (h_i : iVal = taylorLoopIndex j)
    (h_excess : excess.toNat = num)
    (h_j : j < 495) :
    ∀ h,
      taylorRoundSourceQBACKComputed newSp excess outPtr iVal
        (parityBuffer j evenBase oddBase)
        (parityBuffer j oddBase evenBase) vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR h →
      (taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
        (iVal + signExtend12 (1 : BitVec 12)) evenBase oddBase
        (natToLimbs 6 (priceLoopPrefix num (j + 1)).1)
        [a0, a1, a2, a3, a4, a5]
        (natToLimbs 6 (priceLoopPrefix num (j + 1)).2) FR **
        (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  have hparity := taylor_round_source_qback_computed_to_parity
    newSp excess outPtr iVal vals j evenBase oddBase
    a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR h hp
  have hq := qbackWordsModel_eq_prefix
    num result j iVal excess a0 a1 a2 a3 a4 a5
    h_num h_some h_acc h_a h_i h_excess h_j
  have hs := sbackWordsModel_eq_prefix
    num result j a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
    h_some h_acc h_a h_s
  rw [qbackWordsModel_eq_existing] at hq
  rw [sbackWordsModel_eq_existing] at hs
  rw [hq, hs] at hparity
  exact hparity

theorem nbranch_extend_last
    {n1 n2 : Nat} {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {terminal exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (terminal ++ [(mid, Q)]))
    (h2 : cpsNBranchWithin n2 mid cr Q exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P (terminal ++ exits2) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hterminal | hmid
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, List.mem_append.mpr (Or.inl hterminal), hpc1, hQ1⟩
  · rcases hmid with hmid | hnil
    · subst ex
      have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
      obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
        h2 R hR s1 hcr' hQ1 hpc1
      exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
        stepN_add_eq hstep1 hstep2, ex2,
        List.mem_append.mpr (Or.inr hmem2), hpc2, hQ2⟩
    · simp at hnil

/- When the continuation has the same terminal list as the current round,
   discard the duplicate copy introduced by ordinary list concatenation. -/
theorem nbranch_extend_last_same_terminal
    {n1 n2 : Nat} {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {terminal : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (terminal ++ [(mid, Q)]))
    (h2 : cpsNBranchWithin n2 mid cr Q terminal) :
    cpsNBranchWithin (n1 + n2) entry cr P terminal := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hterminal | hmid
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, hterminal, hpc1, hQ1⟩
  · rcases hmid with hmid | hnil
    · subst ex
      have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
      obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
        h2 R hR s1 hcr' hQ1 hpc1
      exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
        stepN_add_eq hstep1 hstep2, ex2, hmem2, hpc2, hQ2⟩
    · simp at hnil

/- A finite fold of a round with a fixed terminal exit list.  Each of the
   first `N` rounds has the same terminal list and a QBACK transition to the
   next invariant.  The final continuation is supplied separately at `inv N`;
   this avoids treating a zero-round run as if it had already reached a
   terminal arm. -/
theorem finite_nbranch_loop_spec
    {N m mLast : Nat} {hdr : Word} {cr : CodeReq}
    {inv : Nat → Assertion} {terminal : List (Word × Assertion)}
    (hround : ∀ j, j < N →
      cpsNBranchWithin m hdr cr (inv j)
        (terminal ++ [(hdr, inv (j + 1))]))
    (htail : cpsNBranchWithin mLast hdr cr (inv N) terminal) :
    cpsNBranchWithin (m * N + mLast) hdr cr (inv 0) terminal := by
  revert mLast inv
  induction N using Nat.strongRecOn with
  | _ N ih =>
      intro mLast inv hround htail
      cases N with
      | zero =>
          simpa using htail
      | succ N =>
          have hfirst := hround 0 (by omega)
          have hround' : ∀ j, j < N →
              cpsNBranchWithin m hdr cr (inv (j + 1))
                (terminal ++ [(hdr, inv ((j + 1) + 1))]) := by
            intro j hj
            exact hround (j + 1) (by omega)
          have htail' : cpsNBranchWithin mLast hdr cr (inv (N + 1)) terminal := by
            simpa [Nat.succ_eq_add_one] using htail
          have hrest := ih N (by omega) (mLast := mLast)
            (inv := fun j => inv (j + 1)) hround' htail'
          have hfold := nbranch_extend_last_same_terminal hfirst hrest
          simpa [Nat.succ_eq_add_one, Nat.mul_succ, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using hfold

theorem flatMap_range_succ_shift {α : Type} (f : Nat → List α) (n : Nat) :
    List.flatMap f (List.range (n + 1)) =
      f 0 ++ List.flatMap (fun j => f (j + 1)) (List.range n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        List.flatMap f (List.range (Nat.succ n + 1)) =
            List.flatMap f (List.range (n + 1) ++ [n + 1]) := by
              simp [List.range_succ]
        _ = List.flatMap f (List.range (n + 1)) ++ f (n + 1) := by
              simp [List.flatMap_append]
        _ = (f 0 ++ List.flatMap (fun j => f (j + 1)) (List.range n)) ++
              f (n + 1) := by
              rw [ih]
        _ = f 0 ++ List.flatMap (fun j => f (j + 1))
              (List.range (Nat.succ n)) := by
              simp [List.range_succ, List.flatMap_append, List.append_assoc]

/- A finite fold for rounds whose terminal exits depend on the iteration index.
   The per-round terminal lists are retained in order; only the final invariant
   exit is threaded into the next round. -/
theorem finite_nbranch_loop_spec_indexed
    {N m mLast : Nat} {hdr : Word} {cr : CodeReq}
    {inv : Nat → Assertion} {terminal : Nat → List (Word × Assertion)}
    (hround : ∀ j, j < N →
      cpsNBranchWithin m hdr cr (inv j)
        (terminal j ++ [(hdr, inv (j + 1))]))
    (htail : cpsNBranchWithin mLast hdr cr (inv N) (terminal N)) :
    cpsNBranchWithin (m * N + mLast) hdr cr (inv 0)
      ((List.range N).flatMap terminal ++ terminal N) := by
  revert mLast inv terminal
  induction N using Nat.strongRecOn with
  | _ N ih =>
      intro mLast inv terminal hround htail
      cases N with
      | zero =>
          simpa using htail
      | succ N =>
          have hfirst := hround 0 (by omega)
          have hround' : ∀ j, j < N →
              cpsNBranchWithin m hdr cr (inv (j + 1))
                (terminal (j + 1) ++ [(hdr, inv ((j + 1) + 1))]) := by
            intro j hj
            exact hround (j + 1) (by omega)
          have htail' : cpsNBranchWithin mLast hdr cr
              (inv (N + 1)) (terminal (N + 1)) := by
            simpa [Nat.succ_eq_add_one] using htail
          have hrest := ih N (by omega) (mLast := mLast)
            (inv := fun j => inv (j + 1))
            (terminal := fun j => terminal (j + 1)) hround' htail'
          have hfold := nbranch_extend_last hfirst hrest
          have hflat := flatMap_range_succ_shift terminal N
          have hlist :
              terminal 0 ++
                  (List.flatMap (fun j => terminal (j + 1)) (List.range N) ++
                    terminal (N + 1)) =
                List.flatMap terminal (List.range (N + 1)) ++ terminal (N + 1) := by
            rw [hflat]
            simp [List.append_assoc]
          rw [hlist] at hfold
          simpa [Nat.succ_eq_add_one, List.range_succ,
            List.flatMap_cons, List.flatMap_nil, Nat.mul_succ,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfold

theorem taylor_outer_fold_from_rounds
    {N m mLast : Nat} {hdr : Word} {cr : CodeReq}
    {inv : Nat → Assertion} {terminal : List (Word × Assertion)}
    (hround : ∀ j, j < N →
      cpsNBranchWithin m hdr cr (inv j)
        (terminal ++ [(hdr, inv (j + 1))]))
    (htail : cpsNBranchWithin mLast hdr cr (inv N) terminal) :
    cpsNBranchWithin (m * N + mLast) hdr cr (inv 0) terminal :=
  finite_nbranch_loop_spec hround htail


end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
