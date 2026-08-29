/- Source-level closure of the K70 Taylor round QBACK exit. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundMul5FFQOVFComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Backedge

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
