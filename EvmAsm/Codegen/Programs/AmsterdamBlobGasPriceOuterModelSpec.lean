/-
  EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterModelSpec

  Model-linked adapters for the K70 outer loop.  The low-level tail and
  terminal definitions remain in `AmsterdamBlobGasPriceOuterSpec`; this file
  keeps the model-specific q-zero threading in a separate import layer.
-/

import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody5Spec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14TerminalSpec
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceTaylorTie

set_option maxRecDepth 8000

/- Strong variant of the x0 split for the model-linked terminal path.  The
   status-0 tail's `q4 ||| q5 = 0` fact is not a disposable proof hint: after
   the exit divide it is the converse half of the representability bridge.
   Preserve it in the post while still factoring x0 out exactly once. -/
theorem tail_core_status0_source_of_tail_core_x0_split_with_qzero
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
      p0 p1 p2 p3 p4 p5 : Word)
    (v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 : Word)
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (FR : Assertion) (hFR : FR.pcFree) :
    cpsNBranchWithin 296 (PriceK + 900) priceCode
      (tailCorePre newSp excess outPtr vals q0 q1 q2 q3 q4 q5
        o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
        v5 v6 v7 v18 v19 v20 v28 v29 v30 v31 FR)
      [(PriceK + 968,
        (tailStatus1NoX0 newSp excess outPtr vals
          q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
          p0 p1 p2 p3 p4 p5 v7 v18 v19 v20 v28 v29 v30 v31 FR) **
          (.x0 ↦ᵣ (0 : Word))),
       (PriceK + 968,
        ((tailStatus0BytesNoX0 newSp excess outPtr vals
          q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5
          p0 p1 p2 p3 p4 p5 v18 v19 v20 v31 FR) **
          ⌜(q4 ||| q5) = (0 : Word)⌝) **
          (.x0 ↦ᵣ (0 : Word)))] := by
  have hTail := EvmAsm.Codegen.AmsterdamBlobGasPriceBody7Spec.tail_core
    newSp excess outPtr vals
    q0 q1 q2 q3 q4 q5 o0 o1 o2 o3 a0 a1 a2 a3 a4 a5
    p0 p1 p2 p3 p4 p5 v5 v6 v7 v18 v19 v20 v28 v29 v30 v31
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid FR hFR
  apply cpsNBranchWithin_weaken_two_same_pc hTail
  · intro h hp
    simp only [tailStatus1NoX0]
    xperm_hyp hp
  · intro h hp
    have hp' := (sepConj_pure_right h).mp hp
    have hqzero := hp'.2
    rw [EvmAsm.Rv64.Tactics.sepConj_pure_mid_assoc_eq]
    apply (sepConj_pure_left h).2
    constructor
    · exact hqzero
    · unfold tailStatus0BytesNoX0
      rw [← tailOutputCells_eq_bytesRegion outPtr q0 q1 q2 q3 o3 o2 o1 o0]
      simp only [tailStatus0RestNoX0, tailOutputFullReplaceBE]
      have hpbase := hp'.1
      xperm_hyp hpbase

/- Strong variant for the model-linked terminal path.  Keep the ordinary
   adapter above unchanged for existing callers; this version retains the
   status-0 quotient-high-limb fact through the exit-divide continuation. -/
theorem exitdiv_tail_core_x0_split_with_qzero
    (newSp excess outPtr iVal : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 v19 v20 : Word) (FR : Assertion)
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true)
    (hFR : FR.pcFree) :
    cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr iVal vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3 v19 v20 FR)
      [(PriceK + 968,
        tailStatus1NoX0 newSp excess outPtr vals
          (exitdivQ0 s0 s1 s2 s3 s4 s5)
          (exitdivQ1 s0 s1 s2 s3 s4 s5)
          (exitdivQ2 s0 s1 s2 s3 s4 s5)
          (exitdivQ3 s0 s1 s2 s3 s4 s5)
          (exitdivQ4 s0 s1 s2 s3 s4 s5)
          (exitdivQ5 s0 s1 s2 s3 s4 s5)
          o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
          (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 iVal v19 v20
          (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
          (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
            signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR **
          (.x0 ↦ᵣ (0 : Word))),
       (PriceK + 968,
        ((tailStatus0BytesNoX0 newSp excess outPtr vals
          (exitdivQ0 s0 s1 s2 s3 s4 s5)
          (exitdivQ1 s0 s1 s2 s3 s4 s5)
          (exitdivQ2 s0 s1 s2 s3 s4 s5)
          (exitdivQ3 s0 s1 s2 s3 s4 s5)
          (exitdivQ4 s0 s1 s2 s3 s4 s5)
          (exitdivQ5 s0 s1 s2 s3 s4 s5)
          a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 iVal v19 v20
          (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR) **
          ⌜((exitdivQ4 s0 s1 s2 s3 s4 s5) ||| (exitdivQ5 s0 s1 s2 s3 s4 s5)) =
            (0 : Word)⌝) **
          (.x0 ↦ᵣ (0 : Word)))] := by
  have hCore := tail_core_status0_source_of_tail_core_x0_split_with_qzero
    newSp excess outPtr vals
    (exitdivQ0 s0 s1 s2 s3 s4 s5)
    (exitdivQ1 s0 s1 s2 s3 s4 s5)
    (exitdivQ2 s0 s1 s2 s3 s4 s5)
    (exitdivQ3 s0 s1 s2 s3 s4 s5)
    (exitdivQ4 s0 s1 s2 s3 s4 s5)
    (exitdivQ5 s0 s1 s2 s3 s4 s5)
    o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
    taylorDW (exitdivZ0 s0 s1 s2 s3 s4 s5).1
    (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 iVal v19 v20
    (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
    (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
      signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12))
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid FR hFR
  simpa only [exitdivTailPre] using hCore

/- Explicit form of the terminal adapter for the model bridge.  Unlike the
   existential packaging above, this exposes the two concrete exit posts so
   the status-0 quotient-high-limb fact remains available to the caller. -/
theorem taylor_round_terminal_496_from_parity_exitdiv_tail_core_with_qzero
    (newSp excess outPtr : Word) (vals : Reg → Word)
    (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5 : Word)
    (o0 o1 o2 o3 : Word) (FR : Assertion)
    (hFR : FR.pcFree) (hFRx0 : x0FreeAssertion FR)
    (hAB : parityBuffer 495 evenBase oddBase =
      newSp + signExtend12 (64 : BitVec 12))
    (hPB : parityBuffer 495 oddBase evenBase =
      newSp + signExtend12 (112 : BitVec 12))
    (hSumAlign : (newSp + signExtend12 (160 : BitVec 12)).toNat % 8 = 0)
    (hOutAlign : outPtr.toNat % 8 = 0)
    (hSumRange : (newSp + signExtend12 (160 : BitVec 12)).toNat + 40 < 2 ^ 64)
    (hOutRange : outPtr.toNat + 32 < 2 ^ 64)
    (hSumValid : ∀ i < 32,
      isValidByteAccess ((newSp + signExtend12 (160 : BitVec 12)) + BitVec.ofNat 64 i) = true)
    (hOutValid : ∀ i < 32, isValidByteAccess (outPtr + BitVec.ofNat 64 i) = true) :
    cpsNBranchWithin (17 + 4183) (PriceK + 144) priceCode
      (taylorLoopInvParityAt newSp excess outPtr vals 495 (496 : Word)
        evenBase oddBase [a0, a1, a2, a3, a4, a5]
        [p0, p1, p2, p3, p4, p5] [s0, s1, s2, s3, s4, s5]
        (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR))
      [ (PriceK + 968,
          tailStatus1NoX0 newSp excess outPtr vals
            (exitdivQ0 s0 s1 s2 s3 s4 s5)
            (exitdivQ1 s0 s1 s2 s3 s4 s5)
            (exitdivQ2 s0 s1 s2 s3 s4 s5)
            (exitdivQ3 s0 s1 s2 s3 s4 s5)
            (exitdivQ4 s0 s1 s2 s3 s4 s5)
            (exitdivQ5 s0 s1 s2 s3 s4 s5)
            o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
            (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase)
            (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
            (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
              signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR),
        (PriceK + 968,
          (tailStatus0BytesNoX0 newSp excess outPtr vals
            (exitdivQ0 s0 s1 s2 s3 s4 s5)
            (exitdivQ1 s0 s1 s2 s3 s4 s5)
            (exitdivQ2 s0 s1 s2 s3 s4 s5)
            (exitdivQ3 s0 s1 s2 s3 s4 s5)
            (exitdivQ4 s0 s1 s2 s3 s4 s5)
            (exitdivQ5 s0 s1 s2 s3 s4 s5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase)
            (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR) **
            ⌜((exitdivQ4 s0 s1 s2 s3 s4 s5) ||| (exitdivQ5 s0 s1 s2 s3 s4 s5)) =
              (0 : Word)⌝),
        (PriceK + 968,
          terminalStatus1Any newSp excess outPtr (496 : Word)
            (parityBuffer 495 evenBase oddBase)
            (parityBuffer 495 oddBase evenBase) vals
            (roundAccum a0 a1 a2 a3 a4 a5)
            a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
            s2 s3 s4 s5 (exitdivOutputCells outPtr o0 o1 o2 o3 ** FR)) ] := by
  let AB := parityBuffer 495 evenBase oddBase
  let PB := parityBuffer 495 oddBase evenBase
  let Q1 : Assertion :=
    tailStatus1NoX0 newSp excess outPtr vals
      (exitdivQ0 s0 s1 s2 s3 s4 s5)
      (exitdivQ1 s0 s1 s2 s3 s4 s5)
      (exitdivQ2 s0 s1 s2 s3 s4 s5)
      (exitdivQ3 s0 s1 s2 s3 s4 s5)
      (exitdivQ4 s0 s1 s2 s3 s4 s5)
      (exitdivQ5 s0 s1 s2 s3 s4 s5)
      o0 o1 o2 o3 a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5
      (exitdivZ0 s0 s1 s2 s3 s4 s5).2.1 (496 : Word) AB PB
      (exitdivQ0 s0 s1 s2 s3 s4 s5) (0 : Word)
      (((newSp + signExtend12 (160 : BitVec 12)) + signExtend12 (0 : BitVec 12)) +
        signExtend12 (-8 : BitVec 12)) (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR
  let Q0 : Assertion :=
    (tailStatus0BytesNoX0 newSp excess outPtr vals
      (exitdivQ0 s0 s1 s2 s3 s4 s5)
      (exitdivQ1 s0 s1 s2 s3 s4 s5)
      (exitdivQ2 s0 s1 s2 s3 s4 s5)
      (exitdivQ3 s0 s1 s2 s3 s4 s5)
      (exitdivQ4 s0 s1 s2 s3 s4 s5)
      (exitdivQ5 s0 s1 s2 s3 s4 s5)
      a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 (496 : Word) AB PB
      (lcnt 5 + signExtend12 (-1 : BitVec 12)) FR) **
      ⌜((exitdivQ4 s0 s1 s2 s3 s4 s5) ||| (exitdivQ5 s0 s1 s2 s3 s4 s5)) =
        (0 : Word)⌝
  let exits : List (Word × Assertion) :=
    [(PriceK + 968, Q1), (PriceK + 968, Q0)]
  have hTail0 := exitdiv_tail_core_x0_split_with_qzero
    newSp excess outPtr (496 : Word) vals
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1 s2 s3 s4 s5
    o0 o1 o2 o3 AB PB FR
    hSumAlign hOutAlign hSumRange hOutRange hSumValid hOutValid hFR
  have hTail : cpsNBranchWithin 296 (PriceK + 900) priceCode
      (exitdivTailPre newSp excess outPtr (496 : Word) vals
        a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
        s2 s3 s4 s5 o0 o1 o2 o3 AB PB FR)
      (exits.map (fun ex => (ex.1, ex.2 ** regIs .x0 (0 : Word)))) := by
    simpa [AB, PB, Q1, Q0, exits] using hTail0
  have hOut := taylor_round_terminal_496_from_parity_exitdiv
    newSp excess outPtr vals evenBase oddBase
    a0 a1 a2 a3 a4 a5 p0 p1 p2 p3 p4 p5 s0 s1
    s2 s3 s4 s5 o0 o1 o2 o3 FR hFR hFRx0 hAB hPB hTail
  simpa [AB, PB, Q1, Q0, exits] using hOut

#print axioms tail_core_status0_source_of_tail_core_x0_split_with_qzero
#print axioms exitdiv_tail_core_x0_split_with_qzero
#print axioms taylor_round_terminal_496_from_parity_exitdiv_tail_core_with_qzero

end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
