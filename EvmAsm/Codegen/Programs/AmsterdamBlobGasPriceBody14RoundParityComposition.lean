/- Parity-parametric outer-round adapters for K70 (#12851). -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceOuterSpec

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

#print axioms round_zero_from_parity_tail_core
#print axioms taylor_round_source_full_from_parity_tail_core

end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
