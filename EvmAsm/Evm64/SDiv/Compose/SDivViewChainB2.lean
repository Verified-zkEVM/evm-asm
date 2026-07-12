/-
  EvmAsm.Evm64.SDiv.Compose.SDivViewChainB2

  Shared declaration home for SDIV dispatch and sign-prefix views.
-/

import EvmAsm.Evm64.SDiv.Compose.SDivViewChainC
import EvmAsm.Evm64.SDiv.Compose.BaseFinalBlockSpecs
import EvmAsm.Evm64.SDiv.Compose.SignXorPost
import EvmAsm.Evm64.SDiv.Compose.DivCallCallable
import EvmAsm.Evm64.SDiv.Compose.Base
import EvmAsm.Evm64.SDiv.Compose.Bridges
import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost

/-
  EvmAsm.Evm64.SDiv.Compose.SignXorSequence

  Composed SDIV prefix through the sign-XOR instruction: takes the entry
  shape (saved-`ra` slot + dividend/divisor limbs in memory) all the way
  to having `x8 = sign(a) ^ sign(b)` and both operands stored in
  absolute value. Split out from `Compose/Base.lean` to respect the
  per-file line cap on Compose files.
-/


namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
theorem saveRa_signs_abs_then_signXor_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 48 base ((base + signXorOff) + 4) (sdivCodeV4 base)
      (saveRaSignsAbsThenSignXorPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (saveRaSignsAbsThenSignXorPost vRa sp
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaSignsAbsThenSignXorPre_unfold,
      saveRaSignsAbsThenSignXorPost_unfold]
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultSign := dividendSign ^^^ divisorSign
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let dividendMask := (0 : Word) - dividendSign
  let dividendXored0 := dividendLimb0 ^^^ dividendMask
  let dividendSum0 := dividendXored0 + dividendSign
  let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendXored1 := dividendLimb1 ^^^ dividendMask
  let dividendSum1 := dividendXored1 + dividendCarry0
  let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendXored2 := dividendLimb2 ^^^ dividendMask
  let dividendSum2 := dividendXored2 + dividendCarry1
  let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendXored3 := dividendTop ^^^ dividendMask
  let dividendSum3 := dividendXored3 + dividendCarry2
  let divisorMask := (0 : Word) - divisorSign
  let divisorXored0 := divisorLimb0 ^^^ divisorMask
  let divisorSum0 := divisorXored0 + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorXored1 := divisorLimb1 ^^^ divisorMask
  let divisorSum1 := divisorXored1 + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorXored2 := divisorLimb2 ^^^ divisorMask
  let divisorSum2 := divisorXored2 + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorXored3 := divisorTop ^^^ divisorMask
  let divisorSum3 := divisorXored3 + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         (dividendMem3 ↦ₘ dividendTop))) **
       ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
      (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       ((dividendMem0 ↦ₘ dividendLimb0) **
        (dividendMem1 ↦ₘ dividendLimb1) **
        (dividendMem2 ↦ₘ dividendLimb2)))) **
     ((divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2)))
  let prefixPost : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  let signFrame : EvmAsm.Rv64.Assertion :=
    (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  let signPre : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ dividendSign) ** (.x9 ↦ᵣ divisorSign)) ** signFrame)
  let post : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) ** signFrame)
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 47 base (base + signXorOff)
      (sdivCodeV4 base) pre prefixPost := by
    dsimp [pre, prefixPost, dividendSign, divisorSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem0, divisorMem1,
      divisorMem2, divisorMem3, EvmAsm.Evm64.evm_sdivDividendTopLimbOff,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, divisorMask, divisorXored0, divisorSum0,
      divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3]
    simpa [divisorAbsOff, signXorOff, BitVec.add_assoc,
      saveRaSignsAbsThenDivisorAbsPre_unfold,
      saveRaSignsAbsThenDivisorAbsPost_unfold] using
      (saveRa_signs_abs_then_divisorAbs_spec_in_sdivCodeV4
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hXor : EvmAsm.Rv64.cpsTripleWithin 1 (base + signXorOff) ((base + signXorOff) + 4)
      (sdivCodeV4 base) signPre post := by
    dsimp [signPre, post, signFrame, resultSign]
    exact EvmAsm.Rv64.cpsTripleWithin_frameR signFrame (by pcFree)
      (signXor_spec_in_sdivCodeV4 dividendSign divisorSign base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [prefixPost, signPre, signFrame] at hp ⊢
      xperm_hyp hp) hPrefix hXor
  simpa [pre, post] using hSeq

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.DivCallPreView

  Named precondition bundle for the SDIV wrapper prefix through the near
  call into `evm_div_callable`.
-/


namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV save-ra/signs/dividendAbs/divisorAbs/signXor
    /divCall block: same entry shape as the divisor-abs and signXor
    sequences. Wrapped `@[irreducible]` so downstream proofs do not
    re-reduce the 18-atom sepConj at each use site. -/
@[irreducible]
def saveRaSignsAbsSignXorThenDivCallPre
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
       (dividendMem3 ↦ₘ dividendTop))) **
     ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
      (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
     ((dividendMem0 ↦ₘ dividendLimb0) **
      (dividendMem1 ↦ₘ dividendLimb1) **
      (dividendMem2 ↦ₘ dividendLimb2)))) **
   ((divisorMem0 ↦ₘ divisorLimb0) **
    (divisorMem1 ↦ₘ divisorLimb1) **
    (divisorMem2 ↦ₘ divisorLimb2))

theorem saveRaSignsAbsSignXorThenDivCallPre_unfold
    {vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
       let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
       let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
       let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
       let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
       let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
       let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
           ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
            (dividendMem3 ↦ₘ dividendTop))) **
          ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
         (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
           (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
          ((dividendMem0 ↦ₘ dividendLimb0) **
           (dividendMem1 ↦ₘ dividendLimb1) **
           (dividendMem2 ↦ₘ dividendLimb2)))) **
        ((divisorMem0 ↦ₘ divisorLimb0) **
         (divisorMem1 ↦ₘ divisorLimb1) **
         (divisorMem2 ↦ₘ divisorLimb2))) := by
  delta saveRaSignsAbsSignXorThenDivCallPre
  rfl

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.DivCallPostView

  Named postcondition bundle for the SDIV wrapper prefix through the near
  call into `evm_div_callable`.
-/


namespace EvmAsm.Evm64.SDiv.Compose

/-- Postcondition for the SDIV save-ra/signs/dividendAbs/divisorAbs/signXor
    /divCall block: `x1` holds the post-JAL return PC (`base + divCallOff
    + 4`), `x8` holds the result sign, the rest matches the signXor
    postcondition. Wrapped `@[irreducible]` to hide the 23-atom sepConj
    from downstream proofs. -/
@[irreducible]
def saveRaSignsAbsSignXorThenDivCallPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultSign := dividendSign ^^^ divisorSign
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let dividendMask := (0 : Word) - dividendSign
  let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
  let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
  let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
  let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  ((.x1 ↦ᵣ ((base + divCallOff) + 4)) **
   (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
    ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
     ((dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))))

theorem saveRaSignsAbsSignXorThenDivCallPost_unfold
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaSignsAbsSignXorThenDivCallPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let resultSign := dividendSign ^^^ divisorSign
       let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
       let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
       let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
       let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
       let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
       let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
       let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       let dividendMask := (0 : Word) - dividendSign
       let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
       let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
       let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
       let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
       let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
       let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
       let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
       let divisorMask := (0 : Word) - divisorSign
       let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
       let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
       let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
       let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
       let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
       let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
       let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
       let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
       ((.x1 ↦ᵣ ((base + divCallOff) + 4)) **
        (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
         ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
          ((dividendMem0 ↦ₘ dividendSum0) **
           (dividendMem1 ↦ₘ dividendSum1) **
           (dividendMem2 ↦ₘ dividendSum2) **
           (dividendMem3 ↦ₘ dividendSum3) **
           (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
           (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
           (.x11 ↦ᵣ divisorCarry3) **
           (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
           (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))))) := by
  delta saveRaSignsAbsSignXorThenDivCallPost
  rfl

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.DivCallViews

  Named pre/postcondition bundles for the SDIV wrapper prefix through the
  near call into `evm_div_callable`.
-/


namespace EvmAsm.Evm64.SDiv.Compose

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.DivCallPrefix

  Sequencing proof for the SDIV wrapper prefix through the near call into
  `evm_div_callable`, before adding dispatcher scratch framing.
-/


namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_signs_abs_signXor_then_divCall_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (saveRaSignsAbsSignXorThenDivCallPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaSignsAbsSignXorThenDivCallPre_unfold,
      saveRaSignsAbsSignXorThenDivCallPost_unfold]
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultSign := dividendSign ^^^ divisorSign
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let dividendMask := (0 : Word) - dividendSign
  let dividendXored0 := dividendLimb0 ^^^ dividendMask
  let dividendSum0 := dividendXored0 + dividendSign
  let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendXored1 := dividendLimb1 ^^^ dividendMask
  let dividendSum1 := dividendXored1 + dividendCarry0
  let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendXored2 := dividendLimb2 ^^^ dividendMask
  let dividendSum2 := dividendXored2 + dividendCarry1
  let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendXored3 := dividendTop ^^^ dividendMask
  let dividendSum3 := dividendXored3 + dividendCarry2
  let divisorMask := (0 : Word) - divisorSign
  let divisorXored0 := divisorLimb0 ^^^ divisorMask
  let divisorSum0 := divisorXored0 + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorXored1 := divisorLimb1 ^^^ divisorMask
  let divisorSum1 := divisorXored1 + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorXored2 := divisorLimb2 ^^^ divisorMask
  let divisorSum2 := divisorXored2 + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorXored3 := divisorTop ^^^ divisorMask
  let divisorSum3 := divisorXored3 + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         (dividendMem3 ↦ₘ dividendTop))) **
       ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
      (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       ((dividendMem0 ↦ₘ dividendLimb0) **
        (dividendMem1 ↦ₘ dividendLimb1) **
        (dividendMem2 ↦ₘ dividendLimb2)))) **
     ((divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2)))
  let signPost : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
     (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
       (.x11 ↦ᵣ divisorCarry3) **
       (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
       (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))))
  let callFrame : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
     ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
      ((dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
       (.x11 ↦ᵣ divisorCarry3) **
       (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
       (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))))
  let callPre : EvmAsm.Rv64.Assertion := (.x1 ↦ᵣ vRa) ** callFrame
  let post : EvmAsm.Rv64.Assertion := (.x1 ↦ᵣ ((base + divCallOff) + 4)) ** callFrame
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 48 base (base + divCallOff)
      (sdivCodeV4 base) pre signPost := by
    dsimp [pre, signPost, dividendSign, divisorSign, resultSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem0, divisorMem1,
      divisorMem2, divisorMem3, EvmAsm.Evm64.evm_sdivDividendTopLimbOff,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, divisorMask, divisorXored0, divisorSum0,
      divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3]
    simpa [signXorOff, divCallOff, BitVec.add_assoc,
      saveRaSignsAbsThenSignXorPre_unfold,
      saveRaSignsAbsThenSignXorPost_unfold] using
      (saveRa_signs_abs_then_signXor_spec_in_sdivCodeV4
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hCall : EvmAsm.Rv64.cpsTripleWithin 1 (base + divCallOff)
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV4 base) callPre post := by
    dsimp [callPre, post]
    exact EvmAsm.Rv64.cpsTripleWithin_frameR callFrame (by pcFree)
      (divCall_spec_in_sdivCodeV4 vRa base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [signPost, callPre, callFrame] at hp ⊢
      xperm_hyp hp) hPrefix hCall
  simpa [pre, post, callFrame] using hSeq

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.DivCallDispatchFrame

  Dispatcher scratch framing for the SDIV wrapper prefix through `divCall`.
-/


namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- v4 variant of `saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCode`. -/
theorem saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaSignsAbsSignXorThenDivCallPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) := by
  have hFramePcFree :
      ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0).pcFree := by
    rw [EvmAsm.Evm64.divScratchValuesCallNoX1_unfold]
    unfold EvmAsm.Evm64.divScratchValues
    pcFree
  exact EvmAsm.Rv64.cpsTripleWithin_frameR _ hFramePcFree
    (saveRa_signs_abs_signXor_then_divCall_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.DispatchPrefix

  Generic SDIV prefix sequencing into the unsigned DIV callable handoff shape.
-/


namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- v4 prefix through the SDIV `divCall`, weakened to the exact
    dispatch-ready postcondition consumed by v4 callable wrappers. -/
theorem saveRa_signs_abs_signXor_then_divCall_dispatchReady_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    rw [saveRaSignsAbsSignXorThenDivCallPost_unfold] at hq
    rw [saveRaDivCallDispatchReadyPost_unfold]
    dsimp only at hq ⊢
    rw [divModStackDispatchPreNoX1_unfold_explicit_sdiv]
    simp [sdivAbsDividendWord, sdivAbsDivisorWord, rippleNegWord, EvmWord.getLimbN,
      EvmWord.getLimb_fromLimbs] at hq ⊢
    xperm_hyp hq) hPrefix

/-- v4 sequence of the SDIV wrapper prefix with any callable proof that consumes
    the exact dispatch-ready post. -/
theorem saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCodeV4
    {nSteps : Nat} {callPost : EvmAsm.Rv64.Assertion}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base callableExit : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) callableExit (sdivCodeV4 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        callPost) :
    EvmAsm.Rv64.cpsTripleWithin (49 + nSteps) base callableExit (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      callPost := by
  have hPrefixRaw :=
    saveRa_signs_abs_signXor_then_divCall_dispatchReady_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
    rw [← divCall_target_eq_wrapperEndOff base]
    exact hPrefixRaw
  exact EvmAsm.Rv64.cpsTripleWithin_seq_same_cr hPrefix hCallable

end EvmAsm.Evm64.SDiv.Compose
