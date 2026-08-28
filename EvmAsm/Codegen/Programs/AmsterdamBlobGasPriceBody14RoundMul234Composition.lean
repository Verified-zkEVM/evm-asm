/- Source-level composition of the first three remaining K70 multiply exits. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundComposition

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

@[reducible] def taylorRoundSourceMul2Status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry2 a0 a1 a2 excess) (rv64_mulhu a2 excess)
        then (1 : Word) else 0)
      a2 (a2 * excess) (rv64_mulhu a2 excess) (mul6Low2 a0 a1 a2 excess)
      (mul6HighCarry2 a0 a1 a2 excess) (mul6HighCarry1 a0 a1 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      p2 p3 p4 p5
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

theorem taylor_round_source_mul2_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceMul2Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) := by
  have hTail := mul6PQOVF2_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p2 p3 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR hFR
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := ?_) hTail
  · intro h hh
    simpa only [taylorRoundSourceMul2] using hh
  · intro h hh
    simpa only [taylorRoundSourceMul2Status1] using hh

@[reducible] def taylorRoundSourceMul3Status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry3 a0 a1 a2 a3 excess) (rv64_mulhu a3 excess)
        then (1 : Word) else 0)
      a3 (a3 * excess) (rv64_mulhu a3 excess) (mul6Low3 a0 a1 a2 a3 excess)
      (mul6HighCarry3 a0 a1 a2 a3 excess) (mul6HighCarry2 a0 a1 a2 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) p3 p4 p5
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

theorem taylor_round_source_mul3_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceMul3 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceMul3Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) := by
  have hTail := mul6PQOVF3_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p3 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR hFR
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := ?_) hTail
  · intro h hh
    simpa only [taylorRoundSourceMul3] using hh
  · intro h hh
    simpa only [taylorRoundSourceMul3Status1] using hh

@[reducible] def taylorRoundSourceMul4Status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 _p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry4 a0 a1 a2 a3 a4 excess) (rv64_mulhu a4 excess)
        then (1 : Word) else 0)
      a4 (a4 * excess) (rv64_mulhu a4 excess) (mul6Low4 a0 a1 a2 a3 a4 excess)
      (mul6HighCarry4 a0 a1 a2 a3 a4 excess) (mul6HighCarry3 a0 a1 a2 a3 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess) p4 p5
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

theorem taylor_round_source_mul4_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceMul4 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceMul4Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) := by
  have hTail := mul6PQOVF4_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR hFR
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := ?_) hTail
  · intro h hh
    simpa only [taylorRoundSourceMul4] using hh
  · intro h hh
    simpa only [taylorRoundSourceMul4Status1] using hh

@[reducible] def taylorRoundFinalHigh
    (a0 a1 a2 a3 a4 a5 excess : Word) : Word :=
  rv64_mulhu a5 excess +
    if BitVec.ult (roundP5 a0 a1 a2 a3 a4 a5 excess) (a5 * excess) then
      (1 : Word) else 0

@[reducible] def taylorRoundFinalOverflow
    (a0 a1 a2 a3 a4 a5 excess : Word) : Word :=
  if BitVec.ult (taylorRoundFinalHigh a0 a1 a2 a3 a4 a5 excess)
      (rv64_mulhu a5 excess) then (1 : Word) else 0

@[reducible] def taylorRoundSourceQOVFComputed
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  taylorRoundSourceQOVF newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5
    (roundP0 a0 excess) (roundP1 a0 a1 excess)
    (roundP2 a0 a1 a2 excess) (roundP3 a0 a1 a2 a3 excess)
    (roundP4 a0 a1 a2 a3 a4 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5)
    (rv64_mulhu a5 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (taylorRoundFinalOverflow a0 a1 a2 a3 a4 a5 excess)
    (taylorRoundFinalHigh a0 a1 a2 a3 a4 a5 excess)
    (taylorRoundFinalHigh a0 a1 a2 a3 a4 a5 excess) FR

/- Expose the complete source prefix through the quotient-overflow exit.  The
   remaining head is the QBACK loopback; keeping it existential here lets the
   first three multiply compositions and the next file consume their own
   concrete arms without re-normalizing the entire source post. -/
theorem taylor_round_source_head_qovf_of_taylor_round
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (hFR : FR.pcFree) :
    ∃ rest : List (Word × Assertion),
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR)
        ((PriceK + 804,
            taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul0 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul3 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul4 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul5 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMulFF newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceQOVFComputed newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) :: rest) := by
  have h := taylor_round newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR hFR
  have hprefix : ∀ {xs : List (Word × Assertion)},
      cpsNBranchWithin 4028 (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR)
        ((PriceK + 804,
            taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul0 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul1 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul3 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul4 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMul5 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceMulFF newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) ::
          (PriceK + 964,
            taylorRoundSourceQOVFComputed newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) :: xs) →
      ∃ rest : List (Word × Assertion),
        cpsNBranchWithin 4028 (PriceK + 144) priceCode
          (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
            v5 v6 v7 v28 v29 v30 v31 FR)
          ((PriceK + 804,
              taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceMul0 newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceMul1 newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceMul3 newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceMul4 newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceMul5 newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceMulFF newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) ::
            (PriceK + 964,
              taylorRoundSourceQOVFComputed newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31 FR) :: rest) := by
    intro xs hxs
    exact ⟨xs, hxs⟩
  apply hprefix
  simpa only [taylorRoundSourcePre, taylorRoundSourceZero,
    taylorRoundSourceCap, taylorRoundSourceCarry, taylorRoundSourceMul0,
    taylorRoundSourceMul1, taylorRoundSourceMul2, taylorRoundSourceMul3,
    taylorRoundSourceMul4, taylorRoundSourceMul5, taylorRoundSourceMulFF,
    taylorRoundSourceQOVFComputed, taylorRoundSourceQOVF, roundAccum,
    roundP0, roundP1, roundP2, roundP3, roundP4, roundP5,
    taylorRoundFinalHigh, taylorRoundFinalOverflow,
    roundS0, roundS1, roundS2, roundS3, roundS4, roundS5] using h

@[reducible] def taylorRoundSourceMul234Prefix
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) :
    List (Word × Assertion) :=
  [(PriceK + 968,
      taylorRoundTerminalStatus1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 968,
      taylorRoundCarryStatus1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
    (PriceK + 968,
      taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
    (PriceK + 968,
      taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
    (PriceK + 968,
      taylorRoundSourceMul2Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
    (PriceK + 968,
      taylorRoundSourceMul3Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
    (PriceK + 968,
      taylorRoundSourceMul4Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR),
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
        v7 v28 v29 v30 v31 FR)]

/- The first sibling consumes the three middle multiply exits while retaining
   the later `mul5`, `mulFF`, and quotient-overflow source heads for the next
   sibling.  The terminal-index citation for this chain is the linked
   `li t0,496` at `0x8000b414` followed by `bgeu` at `0x8000b418` targeting
   `0x8000b710`; the three new tails remain one instruction each. -/
theorem taylor_round_source_mul234_status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree)
    (hAB : AB = newSp + signExtend12 (64 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (112 : BitVec 12))
    {exits : List (Word × Assertion)}
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        o0 o1 o2 o3 AB PB FR) exits) :
    ∃ rest : List (Word × Assertion),
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          (taylorRoundSourceMul234Prefix newSp excess outPtr iVal AB PB vals
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
            v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) ++
            rest)) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  obtain ⟨rest, hRound⟩ := taylor_round_source_head_qovf_of_taylor_round
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
  let terminalPre : Assertion :=
    ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
      ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
      ((.x0 ↦ᵣ (0 : Word)) **
        roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          s0 s1 s2 s3 s4 s5 FR0))
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
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  let out3 : Assertion :=
    taylorRoundSourceMul3Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  let out4 : Assertion :=
    taylorRoundSourceMul4Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  have hZero := round_zero_exitdiv_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB hTail
  have hZero_pre : ∀ h,
      taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h →
      roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h := by
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
  have hCarry := add6Carry_status1_tail
    newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5) c t5
      (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR0 hFR0
  have hCarry_pre : ∀ h,
      taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h →
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
            (((newSp + signExtend12 160) + signExtend12 40) ↦ₘ t5) ** FR0)) h := by
    intro h hp
    simp only [taylorRoundSourceCarry, c, t0, t1, t2, t3, t4, t5,
      EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
      EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
      EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  have hFirst0 := taylor_round_zero_terminal_carry_status1
    (rest := (PriceK + 964, source0) :: (PriceK + 964, source1) ::
      (PriceK + 964, source2) :: (PriceK + 964, source3) ::
      (PriceK + 964, source4) :: (PriceK + 964, source5) ::
      (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) :: rest)
    hRound hZero hZero_pre hTerm hTerm_pre hCarry hCarry_pre
  have hFirst :
      cpsNBranchWithin (4028 + 4183 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut)]) ++
          ((PriceK + 964, source0) :: (PriceK + 964, source1) ::
            (PriceK + 964, source2) :: (PriceK + 964, source3) ::
            (PriceK + 964, source4) :: (PriceK + 964, source5) ::
            (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) :: rest)) := by
    simpa only [terminalOut, carryOut, source0, source1, source2, source3,
      source4, source5, sourceFF, sourceQOVF,
      List.cons_append, List.nil_append, List.append_assoc] using hFirst0
  have hMul0 := taylor_round_source_mul0_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter0 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut)])
    (mid := PriceK + 964) (Qm := source0)
    (rest := (PriceK + 964, source1) :: (PriceK + 964, source2) ::
      (PriceK + 964, source3) :: (PriceK + 964, source4) ::
      (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
      (PriceK + 964, sourceQOVF) :: rest)
    hFirst (cpsTripleWithin_as_cpsNBranchWithin hMul0)
  have hAfter0' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, out0)]) ++
          ((PriceK + 964, source1) :: (PriceK + 964, source2) ::
            (PriceK + 964, source3) :: (PriceK + 964, source4) ::
            (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
            (PriceK + 964, sourceQOVF) :: rest)) := by
    simpa only [out0, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_assoc] using hAfter0
  have hMul1 := taylor_round_source_mul1_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter1 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, out0)])
    (mid := PriceK + 964) (Qm := source1)
    (rest := (PriceK + 964, source2) :: (PriceK + 964, source3) ::
      (PriceK + 964, source4) :: (PriceK + 964, source5) ::
      (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) :: rest)
    hAfter0' (cpsTripleWithin_as_cpsNBranchWithin hMul1)
  have hAfter1' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1) (PriceK + 144)
        priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, out0),
          (PriceK + 968, out1)]) ++
          ((PriceK + 964, source2) :: (PriceK + 964, source3) ::
            (PriceK + 964, source4) :: (PriceK + 964, source5) ::
            (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) :: rest)) := by
    simpa only [out1, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_assoc] using hAfter1
  have hMul2 := taylor_round_source_mul2_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter2 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, out0),
      (PriceK + 968, out1)])
    (mid := PriceK + 964) (Qm := source2)
    (rest := (PriceK + 964, source3) :: (PriceK + 964, source4) ::
      (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
      (PriceK + 964, sourceQOVF) :: rest)
    hAfter1' (cpsTripleWithin_as_cpsNBranchWithin hMul2)
  have hAfter2' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1) (PriceK + 144)
        priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, out0),
          (PriceK + 968, out1), (PriceK + 968, out2)]) ++
          ((PriceK + 964, source3) :: (PriceK + 964, source4) ::
            (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
            (PriceK + 964, sourceQOVF) :: rest)) := by
    simpa only [out2, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_assoc] using hAfter2
  have hMul3 := taylor_round_source_mul3_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter3 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, out0),
      (PriceK + 968, out1), (PriceK + 968, out2)])
    (mid := PriceK + 964) (Qm := source3)
    (rest := (PriceK + 964, source4) :: (PriceK + 964, source5) ::
      (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) :: rest)
    hAfter2' (cpsTripleWithin_as_cpsNBranchWithin hMul3)
  have hAfter3' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1) (PriceK + 144)
        priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, out0),
          (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3)]) ++
          ((PriceK + 964, source4) :: (PriceK + 964, source5) ::
            (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) :: rest)) := by
    simpa only [out3, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_assoc] using hAfter3
  have hMul4 := taylor_round_source_mul4_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter4 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, out0),
      (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3)])
    (mid := PriceK + 964) (Qm := source4)
    (rest := (PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
      (PriceK + 964, sourceQOVF) :: rest)
    hAfter3' (cpsTripleWithin_as_cpsNBranchWithin hMul4)
  refine ⟨rest, ?_⟩
  simpa only [FR0, taylorRoundSourceMul234Prefix, terminalOut, carryOut,
    out0, out1, out2, out3, out4, source0, source1, source2, source3,
    source4, source5, sourceFF, sourceQOVF,
    List.cons_append, List.nil_append, List.append_assoc, Nat.add_assoc] using hAfter4

#print axioms taylor_round_source_mul2_status1_tail
#print axioms taylor_round_source_mul3_status1_tail
#print axioms taylor_round_source_mul4_status1_tail
#print axioms taylor_round_source_head_qovf_of_taylor_round
#print axioms taylor_round_source_mul234_status1

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
