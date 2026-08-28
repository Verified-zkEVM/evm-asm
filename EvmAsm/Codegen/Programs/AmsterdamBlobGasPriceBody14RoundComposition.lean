/- Source-level composition of the K70 Taylor round (#12851). -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Composition
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

/- The first three source posts are kept verbatim up to associativity.  In
   particular, the zero arm puts x18 in the retained source frame, whereas
   the normalized round-zero adapter names it before that frame. -/
@[reducible] def taylorRoundSourcePre
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (regIs .x2 newSp) ** (regIs .x1 (vals .x1)) **
  (regIs .x10 excess) ** (regIs .x11 outPtr) **
  (regIs .x8 excess) ** (regIs .x9 taylorDW) **
  (regIs .x18 iVal) ** (regIs .x19 AB) **
  (regIs .x20 PB) ** (regIs .x21 outPtr) **
  (regIs .x22 (newSp + signExtend12 (160 : BitVec 12))) **
  (regIs .x0 0) ** (regIs .x5 v5) ** (regIs .x6 v6) **
  (regIs .x7 v7) ** (regIs .x28 v28) ** (regIs .x29 v29) **
  (regIs .x30 v30) ** (regIs .x31 v31) **
  frameSlotsSaved priceFrame newSp vals **
  (memIs (AB + signExtend12 (0 : BitVec 12)) a0) **
  (memIs (AB + signExtend12 (8 : BitVec 12)) a1) **
  (memIs (AB + signExtend12 (16 : BitVec 12)) a2) **
  (memIs (AB + signExtend12 (24 : BitVec 12)) a3) **
  (memIs (AB + signExtend12 (32 : BitVec 12)) a4) **
  (memIs (AB + signExtend12 (40 : BitVec 12)) a5) **
  (memIs (PB + signExtend12 (0 : BitVec 12)) p0) **
  (memIs (PB + signExtend12 (8 : BitVec 12)) p1) **
  (memIs (PB + signExtend12 (16 : BitVec 12)) p2) **
  (memIs (PB + signExtend12 (24 : BitVec 12)) p3) **
  (memIs (PB + signExtend12 (32 : BitVec 12)) p4) **
  (memIs (PB + signExtend12 (40 : BitVec 12)) p5) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) s0) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) s1) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) s2) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) s3) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) s4) **
  (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) s5) ** FR

@[reducible] def taylorRoundSourceZero
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  ((regIs .x5 (roundAccum a0 a1 a2 a3 a4 a5)) ** (regIs .x0 0) **
    ⌜roundAccum a0 a1 a2 a3 a4 a5 = 0⌝) **
  ((regIs .x2 newSp) ** (regIs .x1 (vals .x1)) **
   (regIs .x10 excess) ** (regIs .x11 outPtr) **
   (regIs .x8 excess) ** (regIs .x9 taylorDW) **
   (regIs .x18 iVal) ** (regIs .x19 AB) **
   (regIs .x20 PB) ** (regIs .x21 outPtr) **
   (regIs .x22 (newSp + signExtend12 (160 : BitVec 12))) **
   (regIs .x6 a5) ** (regIs .x7 v7) ** (regIs .x28 v28) **
   (regIs .x29 v29) ** (regIs .x30 v30) ** (regIs .x31 v31) **
   frameSlotsSaved priceFrame newSp vals **
   (memIs (AB + signExtend12 (0 : BitVec 12)) a0) **
   (memIs (AB + signExtend12 (8 : BitVec 12)) a1) **
   (memIs (AB + signExtend12 (16 : BitVec 12)) a2) **
   (memIs (AB + signExtend12 (24 : BitVec 12)) a3) **
   (memIs (AB + signExtend12 (32 : BitVec 12)) a4) **
   (memIs (AB + signExtend12 (40 : BitVec 12)) a5) **
   (memIs (PB + signExtend12 (0 : BitVec 12)) p0) **
   (memIs (PB + signExtend12 (8 : BitVec 12)) p1) **
   (memIs (PB + signExtend12 (16 : BitVec 12)) p2) **
   (memIs (PB + signExtend12 (24 : BitVec 12)) p3) **
   (memIs (PB + signExtend12 (32 : BitVec 12)) p4) **
   (memIs (PB + signExtend12 (40 : BitVec 12)) p5) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) s0) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) s1) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) s2) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) s3) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) s4) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) s5) ** FR)

@[reducible] def taylorRoundSourceCap
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  ((regIs .x18 iVal) ** (regIs .x5 496) **
    ⌜¬ BitVec.ult iVal (496 : Word)⌝) **
  ((regIs .x2 newSp) ** (regIs .x1 (vals .x1)) **
   (regIs .x10 excess) ** (regIs .x11 outPtr) **
   (regIs .x8 excess) ** (regIs .x9 taylorDW) **
   (regIs .x19 AB) ** (regIs .x20 PB) **
   (regIs .x21 outPtr) ** (regIs .x22 (newSp + signExtend12 (160 : BitVec 12))) **
   (regIs .x6 a5) ** (regIs .x7 v7) ** (regIs .x28 v28) **
   (regIs .x29 v29) ** (regIs .x30 v30) ** (regIs .x31 v31) **
   (regIs .x0 0) ** frameSlotsSaved priceFrame newSp vals **
   (memIs (AB + signExtend12 (0 : BitVec 12)) a0) **
   (memIs (AB + signExtend12 (8 : BitVec 12)) a1) **
   (memIs (AB + signExtend12 (16 : BitVec 12)) a2) **
   (memIs (AB + signExtend12 (24 : BitVec 12)) a3) **
   (memIs (AB + signExtend12 (32 : BitVec 12)) a4) **
   (memIs (AB + signExtend12 (40 : BitVec 12)) a5) **
   (memIs (PB + signExtend12 (0 : BitVec 12)) p0) **
   (memIs (PB + signExtend12 (8 : BitVec 12)) p1) **
   (memIs (PB + signExtend12 (16 : BitVec 12)) p2) **
   (memIs (PB + signExtend12 (24 : BitVec 12)) p3) **
   (memIs (PB + signExtend12 (32 : BitVec 12)) p4) **
   (memIs (PB + signExtend12 (40 : BitVec 12)) p5) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) s0) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) s1) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) s2) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) s3) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) s4) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) s5) ** FR)

@[reducible] def taylorRoundSourceCarry
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  let c := rCry a5 s5 (rCry a4 s4 (rCry a3 s3
    (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
  let t0 := (a0 + s0) + 0
  let t1 := (a1 + s1) + rCry a0 s0 0
  let t2 := (a2 + s2) + rCry a1 s1 (rCry a0 s0 0)
  let t3 := (a3 + s3) + rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))
  let t4 := (a4 + s4) + rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))
  let t5 := (a5 + s5) + rCry a4 s4 (rCry a3 s3
    (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))
  ((regIs .x5 c) ** (regIs .x0 0) ** ⌜c ≠ 0⌝) **
  ((regIs .x2 newSp) ** (regIs .x1 (vals .x1)) **
   (regIs .x10 excess) ** (regIs .x11 outPtr) **
   (regIs .x8 excess) ** (regIs .x9 taylorDW) **
   (regIs .x18 iVal) ** (regIs .x19 AB) ** (regIs .x20 PB) **
   (regIs .x21 outPtr) ** (regIs .x22 (newSp + signExtend12 (160 : BitVec 12))) **
   (regIs .x6 a5) ** (regIs .x7 s5) ** (regIs .x28 (a5 + s5)) **
   (regIs .x29 c) ** (regIs .x30 ((a5 + s5) + rCry a4 s4
     (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))) **
   (regIs .x31 (if BitVec.ult ((a5 + s5) + rCry a4 s4
       (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))) (a5 + s5)
     then 1 else 0)) ** frameSlotsSaved priceFrame newSp vals **
   (memIs (AB + signExtend12 (0 : BitVec 12)) a0) **
   (memIs (AB + signExtend12 (8 : BitVec 12)) a1) **
   (memIs (AB + signExtend12 (16 : BitVec 12)) a2) **
   (memIs (AB + signExtend12 (24 : BitVec 12)) a3) **
   (memIs (AB + signExtend12 (32 : BitVec 12)) a4) **
   (memIs (AB + signExtend12 (40 : BitVec 12)) a5) **
   (memIs (PB + signExtend12 (0 : BitVec 12)) p0) **
   (memIs (PB + signExtend12 (8 : BitVec 12)) p1) **
   (memIs (PB + signExtend12 (16 : BitVec 12)) p2) **
   (memIs (PB + signExtend12 (24 : BitVec 12)) p3) **
   (memIs (PB + signExtend12 (32 : BitVec 12)) p4) **
   (memIs (PB + signExtend12 (40 : BitVec 12)) p5) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) t0) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (8 : BitVec 12)) t1) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (16 : BitVec 12)) t2) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (24 : BitVec 12)) t3) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (32 : BitVec 12)) t4) **
   (memIs ((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (40 : BitVec 12)) t5) ** FR)

@[reducible] def taylorRoundSourceMul0
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  mul6PQOVF0 newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] def taylorRoundSourceMul1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  mul6PQOVF1 newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] def taylorRoundSourceMul2
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  mul6PQOVF2 newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p2 p3 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] def taylorRoundSourceMul3
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  mul6PQOVF3 newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p3 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] def taylorRoundSourceMul4
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 _p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  mul6PQOVF4 newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] def taylorRoundSourceMul5
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 _p3 _p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  mul6PQOVF5 newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] def taylorRoundSourceMulFF
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 _p1 _p2 _p3 _p4 _p5 s0 s1 s2 s3 s4 s5 : Word)
    (_v7 _v28 _v29 _v30 _v31 : Word) (FR : Assertion) : Assertion :=
  mul6PQOVFF newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) ** FR

@[reducible] def taylorRoundTerminalStatus1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (terminalIndexRest newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR)

@[reducible] def taylorRoundCarryStatus1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  let c := rCry a5 s5 (rCry a4 s4 (rCry a3 s3
    (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
  let t0 := (a0 + s0) + 0
  let t1 := (a1 + s1) + rCry a0 s0 0
  let t2 := (a2 + s2) + rCry a1 s1 (rCry a0 s0 0)
  let t3 := (a3 + s3) + rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))
  let t4 := (a4 + s4) + rCry a3 s3
    (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))
  let t5 := (a5 + s5) + rCry a4 s4
    (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))
  (.x10 ↦ᵣ (1 : Word)) **
    (add6CarryRest newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5)
      c t5 (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR)

@[reducible] def taylorRoundSourceMul0Status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult ((rv64_mulhu a0 excess) +
          (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
            then (1 : Word) else (0 : Word))) (rv64_mulhu a0 excess)
        then (1 : Word) else 0)
      a0 (a0 * excess) (rv64_mulhu a0 excess) ((a0 * excess) + (0 : Word))
      ((rv64_mulhu a0 excess) +
        (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
          then (1 : Word) else (0 : Word))) (0 : Word)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

/- Keep the Body10-to-source adapter separate from the list-level composition.
   Applying the generic status tail here avoids asking the larger composition
   theorem to normalize the full `cpsTripleWithin` type at once. -/
theorem taylor_round_source_mul0_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceMul0 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) := by
  let FR' : Assertion :=
    mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult ((rv64_mulhu a0 excess) +
          (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
            then (1 : Word) else (0 : Word))) (rv64_mulhu a0 excess)
        then (1 : Word) else (0 : Word))
      a0 (a0 * excess) (rv64_mulhu a0 excess) ((a0 * excess) + (0 : Word))
      ((rv64_mulhu a0 excess) +
        (if BitVec.ult ((a0 * excess) + (0 : Word)) (a0 * excess)
          then (1 : Word) else (0 : Word))) (0 : Word)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR
  have hFR' : FR'.pcFree := by
    unfold FR'
    pcFree
    exact hFR
  have hTail := status1_tail excess FR' hFR'
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := fun _ hp => hp) hTail
  intro h hh
  simp only [taylorRoundSourceMul0,
    FR', mul6OverflowRest] at hh ⊢
  xperm_hyp hh

@[reducible] def taylorRoundSourceMul1Status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 _p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (FR : Assertion) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) **
    (mul6OverflowRest newSp excess outPtr iVal AB PB vals
      (if BitVec.ult (mul6HighCarry1 a0 a1 excess) (rv64_mulhu a1 excess)
        then (1 : Word) else 0)
      a1 (a1 * excess) (rv64_mulhu a1 excess) (mul6Low1 a0 a1 excess)
      (mul6HighCarry1 a0 a1 excess) (mul6HighCarry0 a0 excess)
      a0 a1 a2 a3 a4 a5 (mul6Low0 a0 excess) p1 p2 p3 p4 p5
      (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
      (roundS2 a0 a1 a2 s0 s1 s2)
      (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
      (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
      (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR)

theorem taylor_round_source_mul1_status1_tail
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) (hFR : FR.pcFree) :
    cpsTripleWithin 1 (PriceK + 964) (PriceK + 968) priceCode
      (taylorRoundSourceMul1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR)
      (taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR) := by
  have hTail := mul6PQOVF1_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p1 p2 p3 p4 p5
    (roundS0 a0 s0) (roundS1 a0 a1 s0 s1)
    (roundS2 a0 a1 a2 s0 s1 s2)
    (roundS3 a0 a1 a2 a3 s0 s1 s2 s3)
    (roundS4 a0 a1 a2 a3 a4 s0 s1 s2 s3 s4)
    (roundS5 a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5) FR hFR
  apply cpsTripleWithin_weaken
    (hpre := ?_) (hpost := ?_) hTail
  · intro h hh
    simpa only [taylorRoundSourceMul1] using hh
  · intro h hh
    simpa only [taylorRoundSourceMul1Status1] using hh

/- The source-level terminal-index composition keeps the first two exits in
   the exact nesting emitted by `taylor_round`.  The continuation adapters
   below only reassociate those posts: the zero arm enters the exit-divide
   window, while the taken `li x5,496; bgeu` arm enters the common status-1
   tail.  The linked artifact places those instructions at
   `0x8000b414`/`0x8000b418`, targeting `0x8000b710`. -/
theorem taylor_round_source_terminal_496_status1
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree)
    (hAB : AB = newSp + signExtend12 (64 : BitVec 12))
    (hPB : PB = newSp + signExtend12 (112 : BitVec 12))
    {rest exits : List (Word × Assertion)}
    (hRound : cpsNBranchWithin 4028 (PriceK + 144) priceCode
      (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v5 v6 v7 v28 v29 v30 v31
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      ((PriceK + 804,
          taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
            v7 v28 v29 v30 v31
            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) ::
        (PriceK + 964,
          taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
            v7 v28 v29 v30 v31
            (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) :: rest))
    (hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        o0 o1 o2 o3 AB PB FR) exits) :
    cpsNBranchWithin (4028 + 4183 + 1) (PriceK + 144) priceCode
      (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v5 v6 v7 v28 v29 v30 v31
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      (exits ++
        ((PriceK + 968,
          (.x10 ↦ᵣ (1 : Word)) **
            (terminalIndexRest newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31
              (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))) :: rest)) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  have hZero := round_zero_exitdiv_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB hTail
  have hZero_pre : ∀ h,
      taylorRoundSourceZero newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) h →
      roundZero newSp excess outPtr iVal AB PB vals
        (roundAccum a0 a1 a2 a3 a4 a5)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) h := by
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
    v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) hFR0
  have hTerm_pre : ∀ h,
      taylorRoundSourceCap newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR) h →
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
        ((.x0 ↦ᵣ (0 : Word)) **
          roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
            s0 s1 s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))) h := by
    intro h hp
    simp only [taylorRoundSourceCap, roundFrame,
      EvmAsm.Rv64.AddrNorm.se12_0,
      EvmAsm.Rv64.AddrNorm.se12_8, EvmAsm.Rv64.AddrNorm.se12_16,
      EvmAsm.Rv64.AddrNorm.se12_24, EvmAsm.Rv64.AddrNorm.se12_32,
      EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  have hOut := taylor_round_zero_terminal_status1_weaken
    (hRound := hRound) hZero hZero_pre hTerm hTerm_pre
  simpa [FR0] using hOut

/- Keep the source's unchanged overflow posts in the list rather than
   rebuilding them in the composition proof. -/
@[reducible] def taylorRoundSourceQOVF
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  QOVFDIVP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR

@[reducible] def taylorRoundSourceQBACK
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion) : Assertion :=
  QBACKP newSp excess outPtr iVal AB PB vals a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR

/- The existing `taylor_round` theorem supplies the complete source list.  This
   small bridge only exposes its first two entries with names that the
   continuation theorem above can consume; the suffix remains existentially
   abstract here so no generated overflow expression is duplicated. -/
theorem taylor_round_source_head_of_taylor_round
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
                v7 v28 v29 v30 v31 FR) :: rest) := by
    intro xs hxs
    exact ⟨xs, hxs⟩
  apply hprefix
  simpa only [taylorRoundSourcePre, taylorRoundSourceZero,
    taylorRoundSourceCap, roundAccum] using h

theorem taylor_round_source_head3_of_taylor_round
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
                v7 v28 v29 v30 v31 FR) :: rest) := by
    intro xs hxs
    exact ⟨xs, hxs⟩
  apply hprefix
  simpa only [taylorRoundSourcePre, taylorRoundSourceZero,
    taylorRoundSourceCap, taylorRoundSourceCarry, roundAccum] using h

theorem taylor_round_source_head4_of_taylor_round
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
                v7 v28 v29 v30 v31 FR) :: rest) := by
    intro xs hxs
    exact ⟨xs, hxs⟩
  apply hprefix
  simpa only [taylorRoundSourcePre, taylorRoundSourceZero,
    taylorRoundSourceCap, taylorRoundSourceCarry, taylorRoundSourceMul0,
    roundAccum, roundS0, roundS1, roundS2, roundS3, roundS4, roundS5] using h

/- The first three source exits can now be consumed by the two continuation
   adapters: the zero arm enters exit-divide, the terminal-index arm enters
   the status-1 tail, and the carry arm enters the same tail after the
   terminal post has been retained. -/
theorem taylor_round_source_terminal_carry_status1
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
      cpsNBranchWithin (4028 + 4183 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          ((PriceK + 968,
            (.x10 ↦ᵣ (1 : Word)) **
              (terminalIndexRest newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31
                (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))) ::
            ((PriceK + 968,
              (.x10 ↦ᵣ (1 : Word)) **
              add6CarryRest newSp excess outPtr iVal AB PB vals
                (rCry a5 s5 (rCry a4 s4 (rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))))
                a5 s5 (a5 + s5)
                (rCry a5 s5 (rCry a4 s4 (rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))))
                ((a5 + s5) + rCry a4 s4
                  (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                (if BitVec.ult
                    ((a5 + s5) + rCry a4 s4
                      (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                    (a5 + s5) then (1 : Word) else 0)
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
                ((a0 + s0) + 0)
                ((a1 + s1) + rCry a0 s0 0)
                ((a2 + s2) + rCry a1 s1 (rCry a0 s0 0))
                ((a3 + s3) + rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))
                ((a4 + s4) + rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))
                ((a5 + s5) + rCry a4 s4
                  (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) :: rest))) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  obtain ⟨rest, hRound⟩ := taylor_round_source_head3_of_taylor_round
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR0 hFR0
  have hTerminal := taylor_round_source_terminal_496_status1
    (rest := (PriceK + 964,
      taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0) :: rest)
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 o0 o1 o2 o3 FR hFR hAB hPB hRound hTail
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
  let Qcarry : Assertion :=
    ((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝) **
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
      ((newSp + signExtend12 160 + signExtend12 0) ↦ₘ t0) **
      ((newSp + signExtend12 160 + signExtend12 8) ↦ₘ t1) **
      ((newSp + signExtend12 160 + signExtend12 16) ↦ₘ t2) **
      ((newSp + signExtend12 160 + signExtend12 24) ↦ₘ t3) **
      ((newSp + signExtend12 160 + signExtend12 32) ↦ₘ t4) **
      ((newSp + signExtend12 160 + signExtend12 40) ↦ₘ t5) ** FR0)
  have hCarry := add6Carry_status1_tail
    newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5) c t5
      (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR0 hFR0
  have hCarry_pre : ∀ h,
      taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h → Qcarry h := by
    intro h hp
    simp only [Qcarry, c, t0, t1, t2, t3, t4, t5,
      taylorRoundSourceCarry,
      EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
      EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
      EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  have hCarry' := cpsTripleWithin_weaken
    (hpre := hCarry_pre) (hpost := fun _ hp => hp) hCarry
  have hOut := nb_extend_after_second hTerminal
    (cpsTripleWithin_as_cpsNBranchWithin hCarry')
  refine ⟨rest, ?_⟩
  simpa [FR0, Qcarry, c, t0, t1, t2, t3, t4, t5, Nat.add_assoc] using hOut

/- Continue the same source-level composition through the first multiply
   overflow arm.  The source post is kept explicit here because its six
   `s` values are the round accumulators, while the public Body10 tail exposes
   the corresponding low/high carry state. -/
theorem taylor_round_source_terminal_carry_mul0_status1
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
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          ((PriceK + 968,
            (.x10 ↦ᵣ (1 : Word)) **
              (terminalIndexRest newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31
                (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))) ::
            ((PriceK + 968,
              (.x10 ↦ᵣ (1 : Word)) **
              add6CarryRest newSp excess outPtr iVal AB PB vals
                (rCry a5 s5 (rCry a4 s4 (rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))))
                a5 s5 (a5 + s5)
                (rCry a5 s5 (rCry a4 s4 (rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))))
                ((a5 + s5) + rCry a4 s4
                  (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                (if BitVec.ult
                    ((a5 + s5) + rCry a4 s4
                      (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                    (a5 + s5) then (1 : Word) else 0)
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
                ((a0 + s0) + 0)
                ((a1 + s1) + rCry a0 s0 0)
                ((a2 + s2) + rCry a1 s1 (rCry a0 s0 0))
                ((a3 + s3) + rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))
                ((a4 + s4) + rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))
                ((a5 + s5) + rCry a4 s4
                  (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) ::
              ((PriceK + 968,
                taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
                  a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                  (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) :: rest)))) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  obtain ⟨rest, hRound⟩ := taylor_round_source_head4_of_taylor_round
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v5 v6 v7 v28 v29 v30 v31 FR0 hFR0
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
        v7 v28 v29 v30 v31 FR0 h →
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
        ((.x0 ↦ᵣ (0 : Word)) **
          roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
            s0 s1 s2 s3 s4 s5 FR0)) h := by
    intro h hp
    simp only [taylorRoundSourceCap, roundFrame,
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
  let Qcarry : Assertion :=
    ((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝) **
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
      ((newSp + signExtend12 160 + signExtend12 0) ↦ₘ t0) **
      ((newSp + signExtend12 160 + signExtend12 8) ↦ₘ t1) **
      ((newSp + signExtend12 160 + signExtend12 16) ↦ₘ t2) **
      ((newSp + signExtend12 160 + signExtend12 24) ↦ₘ t3) **
      ((newSp + signExtend12 160 + signExtend12 32) ↦ₘ t4) **
      ((newSp + signExtend12 160 + signExtend12 40) ↦ₘ t5) ** FR0)
  have hCarry := add6Carry_status1_tail
    newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5) c t5
      (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR0 hFR0
  have hCarry_pre : ∀ h,
      taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h → Qcarry h := by
    intro h hp
    simp only [Qcarry, c, t0, t1, t2, t3, t4, t5,
      taylorRoundSourceCarry,
      EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
      EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
      EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  have hMul0' := taylor_round_source_mul0_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  let terminalOut : Assertion :=
    (.x10 ↦ᵣ (1 : Word)) **
      (terminalIndexRest newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0)
  let carryOut : Assertion :=
    (.x10 ↦ᵣ (1 : Word)) **
      add6CarryRest newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5) c t5
        (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR0
  let sourceOut : Assertion :=
    taylorRoundSourceMul0 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
      v7 v28 v29 v30 v31 FR0
  have hFirst :
      cpsNBranchWithin (4028 + 4183 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        (exits ++
          ((PriceK + 968, terminalOut) ::
            ((PriceK + 968, carryOut) ::
              ((PriceK + 964, sourceOut) :: rest)))) := by
    exact taylor_round_zero_terminal_carry_status1
      (rest := (PriceK + 964, sourceOut) :: rest)
      hRound hZero hZero_pre hTerm hTerm_pre hCarry hCarry_pre
  have hFirst' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut)]) ++
          ((PriceK + 964, sourceOut) :: rest)) := by
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using hFirst
  have hAll := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut), (PriceK + 968, carryOut)])
    (mid := PriceK + 964) (Qm := sourceOut) (rest := rest) hFirst'
    (cpsTripleWithin_as_cpsNBranchWithin hMul0')
  refine ⟨rest, ?_⟩
  simpa only [FR0, List.cons_append, List.nil_append, List.append_assoc, Nat.add_assoc] using hAll

/- Expose the next source exits as well.  The continuation proof consumes the
   first two multiply exits and leaves `mul6PQOVF2` at the residual head for
   the next composition step. -/
theorem taylor_round_source_head5_of_taylor_round
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
          ((PriceK + 964,
            taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
              a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
              v7 v28 v29 v30 v31 FR) :: rest)) := by
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
                      v7 v28 v29 v30 v31 FR) :: rest) := by
    intro xs hxs
    exact ⟨xs, hxs⟩
  apply hprefix
  simpa only [taylorRoundSourcePre, taylorRoundSourceZero,
    taylorRoundSourceCap, taylorRoundSourceCarry, taylorRoundSourceMul0,
    taylorRoundSourceMul1, taylorRoundSourceMul2, roundAccum, roundS0,
    roundS1, roundS2, roundS3, roundS4, roundS5] using h

/- Consume the next source exit, `mul6PQOVF1`.  The preceding theorem leaves
   that source arm at the head of its residual list; this theorem replaces it
   with the corresponding status-1 post and keeps the earlier three exits
   explicit in the output order. -/
theorem taylor_round_source_terminal_carry_mul0_mul1_status1
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
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31
          (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
        (exits ++
          ((PriceK + 968,
            (.x10 ↦ᵣ (1 : Word)) **
              (terminalIndexRest newSp excess outPtr iVal AB PB vals
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                v7 v28 v29 v30 v31
                (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))) ::
            ((PriceK + 968,
              (.x10 ↦ᵣ (1 : Word)) **
              add6CarryRest newSp excess outPtr iVal AB PB vals
                (rCry a5 s5 (rCry a4 s4 (rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))))
                a5 s5 (a5 + s5)
                (rCry a5 s5 (rCry a4 s4 (rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))))
                ((a5 + s5) + rCry a4 s4
                  (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                (if BitVec.ult
                    ((a5 + s5) + rCry a4 s4
                      (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                    (a5 + s5) then (1 : Word) else 0)
                a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
                ((a0 + s0) + 0)
                ((a1 + s1) + rCry a0 s0 0)
                ((a2 + s2) + rCry a1 s1 (rCry a0 s0 0))
                ((a3 + s3) + rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))
                ((a4 + s4) + rCry a3 s3
                  (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0))))
                ((a5 + s5) + rCry a4 s4
                  (rCry a3 s3 (rCry a2 s2 (rCry a1 s1 (rCry a0 s0 0)))))
                (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) ::
              ((PriceK + 968,
                taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
                  a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                  (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) ::
                ((PriceK + 968,
                taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
                  a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                    (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) ::
                  ((PriceK + 964,
                    taylorRoundSourceMul2 newSp excess outPtr iVal AB PB vals
                      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
                      v7 v28 v29 v30 v31 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) :: rest)))))) := by
  let FR0 : Assertion := exitdivOutputCells outPtr o0 o1 o2 o3 ** FR
  have hFR0 : FR0.pcFree := by
    unfold FR0
    pcFree
    exact hFR
  obtain ⟨rest, hRound⟩ := taylor_round_source_head5_of_taylor_round
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
  let terminalOut : Assertion :=
    (.x10 ↦ᵣ (1 : Word)) **
      terminalIndexRest newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0
  let mul0Out : Assertion :=
    taylorRoundSourceMul0Status1 newSp excess outPtr iVal AB PB vals
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 FR0
  let mul1Out : Assertion :=
    taylorRoundSourceMul1Status1 newSp excess outPtr iVal AB PB vals
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
        v7 v28 v29 v30 v31 FR0 h →
      ((.x18 ↦ᵣ iVal) ** (.x5 ↦ᵣ (496 : Word)) **
        ⌜¬ BitVec.ult iVal (496 : Word)⌝ **
        ((.x0 ↦ᵣ (0 : Word)) **
          roundFrame newSp excess outPtr AB PB vals a5 v7 v28 v29 v30 v31
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
            s0 s1 s2 s3 s4 s5 FR0)) h := by
    intro h hp
    simp only [taylorRoundSourceCap, roundFrame,
      EvmAsm.Rv64.AddrNorm.se12_0,
      EvmAsm.Rv64.AddrNorm.se12_8,
      EvmAsm.Rv64.AddrNorm.se12_16,
      EvmAsm.Rv64.AddrNorm.se12_24,
      EvmAsm.Rv64.AddrNorm.se12_32,
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
  let carryOut : Assertion :=
    (.x10 ↦ᵣ (1 : Word)) **
      add6CarryRest newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5) c t5
        (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR0
  let Qcarry : Assertion :=
    ((.x5 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜c ≠ (0 : Word)⌝) **
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
      ((newSp + signExtend12 160 + signExtend12 0) ↦ₘ t0) **
      ((newSp + signExtend12 160 + signExtend12 8) ↦ₘ t1) **
      ((newSp + signExtend12 160 + signExtend12 16) ↦ₘ t2) **
      ((newSp + signExtend12 160 + signExtend12 24) ↦ₘ t3) **
      ((newSp + signExtend12 160 + signExtend12 32) ↦ₘ t4) **
      ((newSp + signExtend12 160 + signExtend12 40) ↦ₘ t5) ** FR0)
  have hCarry := add6Carry_status1_tail
    newSp excess outPtr iVal AB PB vals c a5 s5 (a5 + s5) c t5
      (if BitVec.ult t5 (a5 + s5) then (1 : Word) else 0)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 t0 t1 t2 t3 t4 t5 FR0 hFR0
  have hCarry_pre : ∀ h,
      taylorRoundSourceCarry newSp excess outPtr iVal AB PB vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR0 h → Qcarry h := by
    intro h hp
    simp only [Qcarry, c, t0, t1, t2, t3, t4, t5,
      taylorRoundSourceCarry,
      EvmAsm.Rv64.AddrNorm.se12_0, EvmAsm.Rv64.AddrNorm.se12_8,
      EvmAsm.Rv64.AddrNorm.se12_16, EvmAsm.Rv64.AddrNorm.se12_24,
      EvmAsm.Rv64.AddrNorm.se12_32, EvmAsm.Rv64.AddrNorm.se12_40,
      EvmAsm.Rv64.AddrNorm.word_add_zero] at hp ⊢
    xperm_hyp hp
  have hFirst0 := taylor_round_zero_terminal_carry_status1
    hRound hZero hZero_pre hTerm hTerm_pre hCarry hCarry_pre
  have hFirst0' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut)]) ++
          ((PriceK + 964, source0) ::
            ((PriceK + 964, source1) ::
              ((PriceK + 964, source2) :: rest)))) := by
    simpa only [terminalOut, carryOut, source0, source1, source2,
      List.cons_append, List.nil_append, List.append_assoc] using hFirst0
  have hMul0 := taylor_round_source_mul0_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter0 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut)])
    (mid := PriceK + 964) (Qm := source0)
    (rest := (PriceK + 964, source1) :: (PriceK + 964, source2) :: rest) hFirst0'
    (cpsTripleWithin_as_cpsNBranchWithin hMul0)
  have hAfter0' :
      cpsNBranchWithin (4028 + 4183 + 1 + 1 + 1) (PriceK + 144) priceCode
        (taylorRoundSourcePre newSp excess outPtr iVal AB PB vals
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
          v5 v6 v7 v28 v29 v30 v31 FR0)
        ((exits ++ [(PriceK + 968, terminalOut),
          (PriceK + 968, carryOut), (PriceK + 968, mul0Out)]) ++
          ((PriceK + 964, source1) :: ((PriceK + 964, source2) :: rest))) := by
    simpa only [mul0Out, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_assoc] using hAfter0
  have hMul1 := taylor_round_source_mul1_status1_tail
    newSp excess outPtr iVal AB PB vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR0 hFR0
  have hAfter1 := nb_extend_after_prefix
    (preExits := exits ++ [(PriceK + 968, terminalOut),
      (PriceK + 968, carryOut), (PriceK + 968, mul0Out)])
    (mid := PriceK + 964) (Qm := source1)
    (rest := (PriceK + 964, source2) :: rest) hAfter0'
    (cpsTripleWithin_as_cpsNBranchWithin hMul1)
  refine ⟨rest, ?_⟩
  simpa only [FR0, terminalOut, carryOut, mul0Out, mul1Out, source2,
    List.cons_append, List.nil_append, List.append_assoc, Nat.add_assoc] using hAfter1

#print axioms taylor_round_source_head_of_taylor_round
#print axioms taylor_round_source_head3_of_taylor_round
#print axioms taylor_round_source_terminal_496_status1
#print axioms taylor_round_source_terminal_carry_status1
#print axioms taylor_round_source_head4_of_taylor_round
#print axioms taylor_round_source_terminal_carry_mul0_status1
#print axioms taylor_round_source_terminal_carry_mul0_mul1_status1

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
