/- Source-level composition of the remaining K70 multiply and quotient exits. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundMul234Composition

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

@[reducible] def taylorRoundSourceMul5Status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 _p3 _p4 p5
      s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
          (rv64_mulhu a5 excess) then (1 : Word) else 0)
      a5 (a5 * excess) (rv64_mulhu a5 excess)
      (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
      (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
      (mul6HighCarry4 a0 a1 a2 a3 a4 excess)
      a0 a1 a2 a3 a4 a5
      (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess)
      (mul6Low4 a0 a1 a2 a3 a4 excess) p5
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

theorem taylor_round_source_mul5_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceMul5 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceMul5Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
  have hTail := mul6PQOVF5_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR hFR
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := ?_) hTail
  · intro h hh
    simpa only [taylorRoundSourceMul5] using hh
  · intro h hh
    simpa only [taylorRoundSourceMul5Status1] using hh

@[reducible] def taylorRoundSourceMulFFStatus1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 _p3 _p4 _p5
      s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (mul6FinalOverflowRest newSp excess outPtr iVal AB PB vals
      a5 (a5 * excess) (rv64_mulhu a5 excess)
      (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
      (if BitVec.ult (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
          (rv64_mulhu a5 excess) then (1 : Word) else 0)
      (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
      (mul6HighCarry5 a0 a1 a2 a3 a4 a5 excess)
      a0 a1 a2 a3 a4 a5
      (mul6Low0 a0 excess) (mul6Low1 a0 a1 excess)
      (mul6Low2 a0 a1 a2 excess) (mul6Low3 a0 a1 a2 a3 excess)
      (mul6Low4 a0 a1 a2 a3 a4 excess)
      (mul6Low5 a0 a1 a2 a3 a4 a5 excess)
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

theorem taylor_round_source_mulFF_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceMulFF newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
  have hTail := mul6PQOVFF_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR hFR
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := ?_) hTail
  · intro h hh
    simpa only [taylorRoundSourceMulFF] using hh
  · intro h hh
    simpa only [taylorRoundSourceMulFFStatus1] using hh

@[reducible] def taylorRoundSourceQOVFComputedStatus1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (qOverflowRest newSp excess outPtr iVal AB PB vals
      (rv64_mulhu taylorDW iVal) (taylorDW * iVal)
      (rv64_mulhu a5 excess) (roundP5 a0 a1 a2 a3 a4 a5 excess)
      (taylorRoundFinalOverflow a0 a1 a2 a3 a4 a5 excess)
      (taylorRoundFinalHigh a0 a1 a2 a3 a4 a5 excess)
      (taylorRoundFinalHigh a0 a1 a2 a3 a4 a5 excess)
      a0 a1 a2 a3 a4 a5
      (roundP0 a0 excess) (roundP1 a0 a1 excess)
      (roundP2 a0 a1 a2 excess) (roundP3 a0 a1 a2 a3 excess)
      (roundP4 a0 a1 a2 a3 a4 excess)
      (roundP5 a0 a1 a2 a3 a4 a5 excess)
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

theorem taylor_round_source_qovf_computed_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 _p3 _p4 _p5
      s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceQOVFComputed newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR) := by
  have hTail := QOVFDIVP_status1_tail
    newSp excess outPtr iVal AB PB vals
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
    (rv64_mulhu a5 excess) (roundP5 a0 a1 a2 a3 a4 a5 excess)
    (taylorRoundFinalOverflow a0 a1 a2 a3 a4 a5 excess)
    (taylorRoundFinalHigh a0 a1 a2 a3 a4 a5 excess)
    (taylorRoundFinalHigh a0 a1 a2 a3 a4 a5 excess) FR hFR
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := ?_) hTail
  · intro h hh
    simpa only [taylorRoundSourceQOVFComputed, taylorRoundSourceQOVF] using hh
  · intro h hh
    simpa only [taylorRoundSourceQOVFComputedStatus1] using hh

@[reducible] def taylorRoundSourceMul5FFQOVFPrefix
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
    (PriceK + 968,
      taylorRoundSourceMul5Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 968,
      taylorRoundSourceMulFFStatus1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 968,
      taylorRoundSourceQOVFComputedStatus1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR),
    (PriceK + 144,
      taylorRoundSourceQBACKComputed newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)]

/- This sibling consumes `mul5`, `mulFF`, and quotient-overflow after the
   preceding batched continuation.  The QBACK head remains explicit for the
   final loopback/closure sibling. -/
theorem taylor_round_source_mul5_ff_qovf_status1
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
      cpsNBranchWithin
        (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          (taylorRoundSourceMul5FFQOVFPrefix newSp excess outPtr iVal AB PB vals
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
            v7 v28 v29 v30 v31
            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) ++ rest)) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  obtain ⟨rest, h234⟩ := taylor_round_source_mul234_status1
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB hTail
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
  have h234' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, out0),
          (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3), (PriceK + 968, out4)]) ++
          ((PriceK + 964, source5) :: (PriceK + 964, sourceFF) ::
            (PriceK + 964, sourceQOVF) ::
            (PriceK + 144, sourceQBACK) :: rest)) := by
    simpa only [taylorRoundSourceMul234Prefix, terminalOut, carryOut,
      out0, out1, out2, out3, out4, source5, sourceFF, sourceQOVF,
      sourceQBACK, List.cons_append, List.nil_append, List.append_assoc] using h234
  have hMul5 := taylor_round_source_mul5_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter5 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, out0),
      (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3), (PriceK + 968, out4)])
    (mid := PriceK + 964) (Qm := source5)
    (rest := (PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
      (PriceK + 144, sourceQBACK) :: rest)
    h234' (cpsTripleWithin_as_cpsNBranchWithin hMul5)
  have hAfter5' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, out0),
          (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3), (PriceK + 968, out4),
          (PriceK + 968, out5)]) ++
          ((PriceK + 964, sourceFF) :: (PriceK + 964, sourceQOVF) ::
            (PriceK + 144, sourceQBACK) :: rest)) := by
    simpa only [out5, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_assoc] using hAfter5
  have hMulFF := taylor_round_source_mulFF_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfterFF := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, out0),
      (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3), (PriceK + 968, out4),
      (PriceK + 968, out5)])
    (mid := PriceK + 964) (Qm := sourceFF)
    (rest := (PriceK + 964, sourceQOVF) ::
      (PriceK + 144, sourceQBACK) :: rest)
    hAfter5' (cpsTripleWithin_as_cpsNBranchWithin hMulFF)
  have hAfterFF' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, out0),
          (PriceK + 968, out1), (PriceK + 968, out2),
          (PriceK + 968, out3), (PriceK + 968, out4),
          (PriceK + 968, out5), (PriceK + 968, outFF)]) ++
          ((PriceK + 964, sourceQOVF) ::
            (PriceK + 144, sourceQBACK) :: rest)) := by
    simpa only [outFF, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_assoc] using hAfterFF
  have hQOVF := taylor_round_source_qovf_computed_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfterQOVF := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, out0),
      (PriceK + 968, out1), (PriceK + 968, out2),
      (PriceK + 968, out3), (PriceK + 968, out4),
      (PriceK + 968, out5), (PriceK + 968, outFF)])
    (mid := PriceK + 964) (Qm := sourceQOVF)
    (rest := (PriceK + 144, sourceQBACK) :: rest)
    hAfterFF' (cpsTripleWithin_as_cpsNBranchWithin hQOVF)
  refine ⟨rest, ?_⟩
  simpa only [FR0, taylorRoundSourceMul5FFQOVFPrefix, terminalOut,
    carryOut, out0, out1, out2, out3, out4, out5, outFF, outQOVF,
    source5, sourceFF, sourceQOVF, sourceQBACK,
    List.cons_append, List.nil_append, List.append_assoc, Nat.add_assoc] using hAfterQOVF

#print axioms taylor_round_source_mul5_status1_tail
#print axioms taylor_round_source_mulFF_status1_tail
#print axioms taylor_round_source_qovf_computed_status1_tail
#print axioms taylor_round_source_mul5_ff_qovf_status1

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
