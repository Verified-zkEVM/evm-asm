/-
  Shared declaration home for the SMod V5 callable and return wrappers.
-/

import EvmAsm.Evm64.SMod.Compose.CodeHandlesV5
import EvmAsm.Evm64.DivMod.Compose.ModCallableV5Assembly
import EvmAsm.Evm64.SMod.Compose.ModCallGenericHandoff
import EvmAsm.Evm64.SMod.Compose.DispatchReadyView
import EvmAsm.Evm64.SMod.Compose.ModCallDispatchReadySequence
import EvmAsm.Evm64.SMod.Compose.BaseSpecsV5
import EvmAsm.Evm64.SMod.Compose.BaseCodeV5
import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFix
import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwnV5
import EvmAsm.Evm64.SMod.Compose.ModCallReturnGeneric

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 SMOD wrapper: M2's x9-owned mod callable spec framed by `F` and lifted
    onto `smodCodeV5` (the embedded `evm_mod_callable_v5` at `wrapperEndOff`).
    x9 is already owned in the post and the `sp+3936` scratch cell rides through. -/
theorem evm_mod_callable_v5_x9owned_framed_spec_in_smodCodeV5
    {F : Assertion} [Assertion.PCFree F]
    (sp base x9In raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (smodCodeV5 base)
      ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) ** F)
      ((EvmAsm.Evm64.modStackDispatchPostCallableX9Owned sp a b raVal **
        memOwn (sp + signExtend12 3936)) ** F) := by
  exact cpsTripleWithin_extend_code
    (hmono := evm_mod_callable_code_v5_sub_smodCodeV5 (base := base))
    (cpsTripleWithin_frameR F (by pcFree)
      (EvmAsm.Evm64.evm_mod_callable_v5_stack_spec_within_x9owned
        sp (base + wrapperEndOff) a b x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign))

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 dispatch-ready callable handoff: from `saveRaAbsThenModCallDispatchReadyPost`
    (+ the `sp+3936` scratch cell) to `saveRaAbsThenModCallCallablePost` with the
    scratch cell carried, over `smodCodeV5`.  Feeds the unconditional M2 callable
    (step 1) — no `h_stack`. -/
theorem saveRaAbsThenModCallDispatchReadyPost_x9owned_spec_in_smodCodeV5
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbase : base &&& 1 = 0)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV5 base)
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
      (saveRaAbsThenModCallCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       memOwn (sp + signExtend12 (3936 : BitVec 12))) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := smodAbsSign divisorTop
  let divisorMask := smodAbsMask divisorTop
  let divisorSum3 := smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let retAddr := (base + modCallOff) + 4
  let privateFrame := smodModCallPrivateFrame vRa dividendTop
  have hCallable :=
    evm_mod_callable_v5_x9owned_framed_spec_in_smodCodeV5
      (F := privateFrame)
      sp base divisorSign retAddr
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem halign
  rw [show retAddr &&& ~~~(1 : Word) = base + resultSignFixOff from by
    dsimp only [retAddr]; exact modCall_return_andn_one_eq_resultSignFixOff base hbase]
    at hCallable
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components] at hp
      dsimp only at hp
      rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold]
      dsimp only [dividendAbsWord, divisorAbsWord, divisorSign, retAddr,
        divisorMask, divisorSum3, divisorCarry3, privateFrame]
      rw [smodModCallPrivateFrame_unfold]
      dsimp only
      rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold] at hp
      xperm_chunked hp)
    (fun h hp => by
      simp only [EvmAsm.Evm64.modStackDispatchPostCallableX9Owned_unfold] at hp
      dsimp only [privateFrame] at hp
      rw [smodModCallPrivateFrame_unfold] at hp
      rw [saveRaAbsThenModCallCallablePost_unfold]
      dsimp only [dividendAbsWord, divisorAbsWord, privateFrame]
      rw [smodModCallPrivateFrame_unfold]
      dsimp only at hp ⊢
      xperm_chunked hp)
    hCallable

open EvmAsm.Rv64.Tactics

theorem saveRa_then_dividendSign_spec_in_smodCodeV5
    (vRa vSavedOld sp sOld dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 3 base ((base + dividendSignOff) + 8) (smodCodeV5 base)
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (((.x1 ↦ᵣ vRa) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
          dividendTop))) := by
  have hSave :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (by pcFree)
      (saveRa_spec_in_smodCodeV5 vRa vSavedOld base)
  have hSign :=
    EvmAsm.Rv64.cpsTripleWithin_frameL
      (((.x1 ↦ᵣ vRa) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))
      (by pcFree)
      (dividendSign_spec_in_smodCodeV5 sp sOld dividendTop base)
  have hFall :
      (base + saveRaOff) + 4 = base + dividendSignOff := by
    simp [saveRaOff, dividendSignOff]
  have hSign' :
      EvmAsm.Rv64.cpsTripleWithin 2 ((base + saveRaOff) + 4)
        ((base + dividendSignOff) + 8) (smodCodeV5 base)
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop)))
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) := by
    rw [hFall]
    exact hSign
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_same_cr hSave hSign'
  simpa [saveRaOff] using hSeq


theorem saveRa_dividendSign_then_preserve_spec_in_smodCodeV5
    (vRa vSavedOld sp sOld x13Old dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 4 base ((base + preserveDividendSignOff) + 4)
      (smodCodeV5 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old))
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       (((.x1 ↦ᵣ vRa) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ dividendSign) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
          dividendTop))) **
       (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let pre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     (.x13 ↦ᵣ x13Old))
  let mid : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ x13Old))
  let midPreserve : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ x13Old)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
  let postFrame : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     ((.x8 ↦ᵣ dividendSign) **
      (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 3 base
      ((base + dividendSignOff) + 8) (smodCodeV5 base) pre mid := by
    dsimp [pre, mid]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameR
        (.x13 ↦ᵣ x13Old)
        (by pcFree)
        (saveRa_then_dividendSign_spec_in_smodCodeV5
          vRa vSavedOld sp sOld dividendTop base)
  have hPreserve : EvmAsm.Rv64.cpsTripleWithin 1
      (base + preserveDividendSignOff) ((base + preserveDividendSignOff) + 4)
      (smodCodeV5 base) midPreserve postFrame := by
    dsimp [midPreserve, postFrame]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameL
        (((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x12 ↦ᵣ sp) **
          ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
            dividendTop)))
        (by pcFree)
        (preserveDividendSign_spec_in_smodCodeV5 dividendSign x13Old base)
  have hFall :
      (base + dividendSignOff) + 8 = base + preserveDividendSignOff := by
    simp [dividendSignOff, preserveDividendSignOff]
    bv_addr
  have hPreserve' :
      EvmAsm.Rv64.cpsTripleWithin 1 ((base + dividendSignOff) + 8)
        ((base + preserveDividendSignOff) + 4) (smodCodeV5 base) midPreserve postFrame := by
    rw [hFall]
    exact hPreserve
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, midPreserve] at hp ⊢
      xperm_hyp hp) hPrefix hPreserve'
  have hPostPerm : ∀ h, postFrame h → post h := by
    intro h hp
    dsimp [postFrame, post] at hp ⊢
    xperm_hyp hp
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      simpa [pre] using hp)
    hPostPerm
    (by
      simpa [pre, saveRaOff, dividendSign] using hSeq)


theorem saveRa_dividendSign_preserve_then_divisorSign_spec_in_smodCodeV5
    (vRa vSavedOld sp sDividendOld x13Old dividendTop sDivisorOld divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 6 base ((base + divisorSignOff) + 8)
      (smodCodeV5 base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop)))
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       ((((.x1 ↦ᵣ vRa) **
         (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ dividendSign) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
        (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x9 ↦ᵣ divisorSign) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) := by
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let divisorFrame : EvmAsm.Rv64.Assertion :=
    ((.x9 ↦ᵣ sDivisorOld) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
       divisorTop))
  let pre : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     (.x13 ↦ᵣ x13Old)) **
     divisorFrame)
  let mid : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     divisorFrame)
  let midDivisor : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sDivisorOld) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let postFrame : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let post : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 4 base
      ((base + preserveDividendSignOff) + 4) (smodCodeV5 base) pre mid := by
    dsimp [pre, mid, divisorFrame]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameR
        divisorFrame
        (by pcFree)
        (saveRa_dividendSign_then_preserve_spec_in_smodCodeV5
          vRa vSavedOld sp sDividendOld x13Old dividendTop base)
  have hDivisor : EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff)
      ((base + divisorSignOff) + 8) (smodCodeV5 base) midDivisor postFrame := by
    dsimp [midDivisor, postFrame]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x8 ↦ᵣ dividendSign) **
          ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
            dividendTop))) **
         (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
        (by pcFree)
        (divisorSign_spec_in_smodCodeV5 sp sDivisorOld divisorTop base)
  have hFall :
      (base + preserveDividendSignOff) + 4 = base + divisorSignOff := by
    simp [preserveDividendSignOff, divisorSignOff]
    bv_addr
  have hDivisor' :
      EvmAsm.Rv64.cpsTripleWithin 2 ((base + preserveDividendSignOff) + 4)
        ((base + divisorSignOff) + 8) (smodCodeV5 base) midDivisor postFrame := by
    rw [hFall]
    exact hDivisor
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, midDivisor, divisorFrame] at hp ⊢
      xperm_hyp hp) hPrefix hDivisor'
  have hPostPerm : ∀ h, postFrame h → post h := by
    intro h hp
    dsimp [postFrame, post] at hp ⊢
    xperm_hyp hp
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      simpa [pre, divisorFrame] using hp)
    hPostPerm
    (by
      simpa [pre, saveRaOff, dividendSign, divisorSign] using hSeq)


theorem saveRa_signs_then_dividendAbs_spec_in_smodCodeV5
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 27 base ((base + dividendAbsOff) + 84)
      (smodCodeV5 base)
      ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
         (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2))))
      (let sign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let mask := (0 : Word) - sign
       let xored0 := limb0 ^^^ mask
       let sum0 := xored0 + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let xored1 := limb1 ^^^ mask
       let sum1 := xored1 + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let xored2 := limb2 ^^^ mask
       let sum2 := xored2 + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let xored3 := dividendTop ^^^ mask
       let sum3 := xored3 + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (((((.x1 ↦ᵣ vRa) **
         (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x9 ↦ᵣ divisorSign) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
           divisorTop))) **
        (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           sum3)))) := by
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let xored0 := limb0 ^^^ mask
  let sum0 := xored0 + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let xored1 := limb1 ^^^ mask
  let sum1 := xored1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let xored2 := limb2 ^^^ mask
  let sum2 := xored2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let xored3 := dividendTop ^^^ mask
  let sum3 := xored3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  let extra : EvmAsm.Rv64.Assertion :=
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
      (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
     ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
     (.x13 ↦ᵣ x13Old)) **
     ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let mid : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) ** (mem3 ↦ₘ dividendTop))) **
     (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let absPre : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
      (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
      (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ dividendTop)))
  let post : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
      (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 6 base (base + dividendAbsOff)
      (smodCodeV5 base) pre mid := by
    dsimp [pre, mid, extra, mem3, divisorMem3, sign, divisorSign]
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        extra
        (by pcFree)
        (saveRa_dividendSign_preserve_then_divisorSign_spec_in_smodCodeV5
          vRa vSavedOld sp sDividendOld x13Old dividendTop sDivisorOld divisorTop
          base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff)
      ((base + dividendAbsOff) + 84) (smodCodeV5 base) absPre post := by
    have hSpec := dividendAbs_spec_in_smodCodeV5
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
      base
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.condNegate256BlockPre,
      EvmAsm.Evm64.condNegate256BlockPost,
      EvmAsm.Evm64.evm_smodDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
         (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
        (by pcFree)
        hSpec
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post, sign, divisorSign, mask, xored0, sum0, carry0, xored1,
    sum1, carry1, xored2, sum2, carry2, xored3, sum3, carry3, mem0, mem1,
    mem2, mem3, divisorMem3] using hSeq


theorem saveRa_signs_abs_then_divisorAbs_spec_in_smodCodeV5
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 48 base ((base + divisorAbsOff) + 84)
      (smodCodeV5 base)
      (((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2)))
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
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
       (((((.x1 ↦ᵣ vRa) **
         (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x8 ↦ᵣ dividendSign) **
         ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendSum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendSum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendSum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendSum3))) **
        (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
         (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) ** (.x11 ↦ᵣ divisorCarry3) **
         ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorSum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorSum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorSum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
           divisorSum3)))) := by
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff
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
  let dividendCarry3 := if BitVec.ult dividendSum3 dividendCarry2 then (1 : Word) else 0
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
  let divisorLower : EvmAsm.Rv64.Assertion :=
    ((divisorMem0 ↦ₘ divisorLimb0) ** (divisorMem1 ↦ₘ divisorLimb1) **
     (divisorMem2 ↦ₘ divisorLimb2))
  let pre : EvmAsm.Rv64.Assertion :=
    (((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (dividendMem3 ↦ₘ dividendTop))) **
     (.x13 ↦ᵣ x13Old)) **
     ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
       (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
      ((dividendMem0 ↦ₘ dividendLimb0) **
       (dividendMem1 ↦ₘ dividendLimb1) **
       (dividendMem2 ↦ₘ dividendLimb2)))) **
     divisorLower)
  let mid : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ dividendSign) **
      (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
      (.x11 ↦ᵣ dividendCarry3) **
      (dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3))) **
     divisorLower)
  let absPre : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      (dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
      (.x11 ↦ᵣ dividendCarry3) **
      (divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2) **
      (divisorMem3 ↦ₘ divisorTop)))
  let post : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      (dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 27 base (base + divisorAbsOff)
      (smodCodeV5 base) pre mid := by
    dsimp [pre, mid, divisorLower, dividendSign, divisorSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem3,
      EvmAsm.Evm64.evm_smodDividendTopLimbOff,
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, dividendCarry3]
    simpa [dividendAbsOff, divisorAbsOff, BitVec.add_assoc] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        divisorLower
        (by pcFree)
        (saveRa_signs_then_dividendAbs_spec_in_smodCodeV5
          vRa vSavedOld sp sDividendOld x13Old sDivisorOld divisorTop
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff)
      ((base + divisorAbsOff) + 84) (smodCodeV5 base) absPre post := by
    simpa [absPre, post, divisorMem0, divisorMem1, divisorMem2, divisorMem3,
      EvmAsm.Evm64.condNegate256BlockPre,
      EvmAsm.Evm64.condNegate256BlockPost,
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff, divisorMask, divisorXored0,
      divisorSum0, divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x8 ↦ᵣ dividendSign) **
          (dividendMem0 ↦ₘ dividendSum0) **
          (dividendMem1 ↦ₘ dividendSum1) **
          (dividendMem2 ↦ₘ dividendSum2) **
          (dividendMem3 ↦ₘ dividendSum3))) **
         (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
        (by pcFree)
        (divisorAbs_spec_in_smodCodeV5
          sp divisorSign dividendMask dividendSum3 dividendCarry3
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, absPre, divisorLower] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post, dividendSign, divisorSign, dividendMask, dividendXored0,
    dividendSum0, dividendCarry0, dividendXored1, dividendSum1, dividendCarry1,
    dividendXored2, dividendSum2, dividendCarry2, dividendXored3, dividendSum3,
    dividendCarry3, divisorMask, divisorXored0, divisorSum0, divisorCarry0,
    divisorXored1, divisorSum1, divisorCarry1, divisorXored2, divisorSum2,
    divisorCarry2, divisorXored3, divisorSum3, divisorCarry3, dividendMem0,
    dividendMem1, dividendMem2, dividendMem3, divisorMem0, divisorMem1,
    divisorMem2, divisorMem3] using hSeq


theorem saveRa_signs_abs_then_modCall_spec_in_smodCodeV5
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff)
      (smodCodeV5 base)
      ((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
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
       (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
       (((((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
        ((.x8 ↦ᵣ dividendSign) **
         ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendSum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendSum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendSum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendSum3))) **
        (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
         (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) ** (.x11 ↦ᵣ divisorCarry3) **
         ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorSum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorSum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorSum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
           divisorSum3))) **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))) := by
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff
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
  let dispatchExtra : EvmAsm.Rv64.Assertion :=
    ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     EvmAsm.Evm64.divScratchValuesCallNoX1 sp
       q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratchUn0)
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (dividendMem3 ↦ₘ dividendTop))) **
     (.x13 ↦ᵣ x13Old)) **
     ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
       (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
      ((dividendMem0 ↦ₘ dividendLimb0) **
       (dividendMem1 ↦ₘ dividendLimb1) **
       (dividendMem2 ↦ₘ dividendLimb2)))) **
     ((divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2))) **
     dispatchExtra)
  let mid : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      (dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))) **
     dispatchExtra)
  let callFrame : EvmAsm.Rv64.Assertion :=
    (((((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
      (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
       (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
       (.x11 ↦ᵣ divisorCarry3) **
       (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
       (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))) **
      dispatchExtra)
  let callPre : EvmAsm.Rv64.Assertion := (.x1 ↦ᵣ vRa) ** callFrame
  let callPost : EvmAsm.Rv64.Assertion :=
    (.x1 ↦ᵣ ((base + modCallOff) + 4)) ** callFrame
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 48 base (base + modCallOff)
      (smodCodeV5 base) pre mid := by
    dsimp [pre, mid, dispatchExtra, dividendMem0, dividendMem1, dividendMem2,
      dividendMem3, divisorMem0, divisorMem1, divisorMem2, divisorMem3,
      dividendSign, divisorSign, dividendMask, dividendXored0, dividendSum0,
      dividendCarry0, dividendXored1, dividendSum1, dividendCarry1,
      dividendXored2, dividendSum2, dividendCarry2, dividendXored3,
      dividendSum3, divisorMask, divisorXored0, divisorSum0, divisorCarry0,
      divisorXored1, divisorSum1, divisorCarry1, divisorXored2, divisorSum2,
      divisorCarry2, divisorXored3, divisorSum3, divisorCarry3]
    simpa [divisorAbsOff, modCallOff, BitVec.add_assoc] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        dispatchExtra
        (by pcFree)
        (saveRa_signs_abs_then_divisorAbs_spec_in_smodCodeV5
          vRa vSavedOld sp sDividendOld x13Old sDivisorOld
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base))
  have hCall : EvmAsm.Rv64.cpsTripleWithin 1 (base + modCallOff)
      ((base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff)
      (smodCodeV5 base) callPre callPost := by
    dsimp [callPre, callPost]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameR
        callFrame
        (by pcFree)
        (modCall_spec_in_smodCodeV5 vRa base)
  have hCallExit :
      (base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff =
        base + wrapperEndOff := by
    simp [modCallOff, wrapperEndOff, EvmAsm.Evm64.evm_smodCallOff]
    bv_addr
  have hCall' : EvmAsm.Rv64.cpsTripleWithin 1 (base + modCallOff)
      (base + wrapperEndOff) (smodCodeV5 base) callPre callPost := by
    rw [← hCallExit]
    exact hCall
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, callPre, callFrame, dispatchExtra] at hp ⊢
      xperm_hyp hp) hPrefix hCall'
  simpa [pre, callPost, callFrame, dispatchExtra, dividendSign, divisorSign,
    dividendMask, dividendXored0, dividendSum0, dividendCarry0, dividendXored1,
    dividendSum1, dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
    dividendXored3, dividendSum3, divisorMask, divisorXored0, divisorSum0,
    divisorCarry0, divisorXored1, divisorSum1, divisorCarry1, divisorXored2,
    divisorSum2, divisorCarry2, divisorXored3, divisorSum3, divisorCarry3,
    dividendMem0, dividendMem1, dividendMem2, dividendMem3, divisorMem0,
    divisorMem1, divisorMem2, divisorMem3] using hSeq


theorem saveRa_signs_abs_then_modCall_dispatchReady_spec_in_smodCodeV5
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff)
      (smodCodeV5 base)
      ((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hp => by
      rw [saveRaAbsThenModCallDispatchReadyPost_unfold_explicit_smod_components]
      simp only [smodAbsSign, smodAbsMask, smodAbsSum0, smodAbsCarry0,
        smodAbsSum1, smodAbsCarry1, smodAbsSum2, smodAbsCarry2,
        smodAbsSum3, smodAbsCarry3]
      rw [EvmAsm.Rv64.signExtend12_0] at hp ⊢
      simp at hp ⊢
      xperm_hyp hp)
    (saveRa_signs_abs_then_modCall_spec_in_smodCodeV5
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base)

/-- SMOD wrapper prefix + any callable proof consuming the exact dispatch-ready
    post (mirror of the SDIV `..._then_exact_callable_spec_in_sdivCodeV5`). -/
theorem saveRa_signs_abs_then_modCall_dispatchReady_then_exact_callable_spec_in_smodCodeV5
    {nSteps : Nat} {callPost : EvmAsm.Rv64.Assertion}
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base callableExit : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) callableExit (smodCodeV5 base)
        (saveRaAbsThenModCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
        callPost) :
    EvmAsm.Rv64.cpsTripleWithin (49 + nSteps) base callableExit (smodCodeV5 base)
      (((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      callPost := by
  have hPrefix := saveRa_signs_abs_then_modCall_dispatchReady_spec_in_smodCodeV5
    vRa vSavedOld sp sDividendOld x13Old sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
    divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
    v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  have hPrefixFramed := EvmAsm.Rv64.cpsTripleWithin_frameR
    ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem) (by pcFree) hPrefix
  exact EvmAsm.Rv64.cpsTripleWithin_seq_same_cr hPrefixFramed hCallable

open EvmAsm.Rv64

/-- v5 SMOD wrapper prefix + any exact unsigned-MOD callable proof (carrying the
    trailing `regOwn .x9 ** memOwn (sp+3936)` frame), then result-sign-fix. -/
theorem saveRaAbsThenModCall_then_resultSignFix_of_callable_post_noX9_spec_in_smodCodeV5
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV5 base)
        (saveRaAbsThenModCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (saveRaAbsThenModCallCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         memOwn (sp + signExtend12 3936))) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + nSteps) + 21)
      base ((base + resultSignFixOff) + 84) (smodCodeV5 base)
      (((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign dividendTop
       smodResultSignFixPost (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
       (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord **
        memOwn (sp + signExtend12 3936))) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
  let resultSign := smodAbsSign dividendTop
  have hPrefix :=
    saveRa_signs_abs_then_modCall_dispatchReady_then_exact_callable_spec_in_smodCodeV5
      (callPost := saveRaAbsThenModCallCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         memOwn (sp + signExtend12 3936))
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem
      base (base + resultSignFixOff) hCallable
  have hFramePc :
      (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord **
        memOwn (sp + signExtend12 3936)).pcFree :=
    EvmAsm.Rv64.pcFree_sepConj smodModCallResultSignFixFrame_pcFree (by pcFree)
  have hFix :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (smodModCallResultSignFixFrame vRa sp base dividendTop dividendAbsWord **
        memOwn (sp + signExtend12 3936))
      hFramePc
      (resultSignFix_regOwn_scratch_spec_in_smodCodeV5
        (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [saveRaAbsThenModCallCallablePost_smodResultSignFixPreOwnScratch] at hp
      dsimp only [dividendAbsWord, divisorAbsWord, modWord, resultSign] at hp
      xperm_hyp hp)
    hPrefix hFix

open EvmAsm.Rv64

/-- B7: v5 SMOD prefix + exact MOD callable + result-sign-fix + saved-RA return,
    landing the explicit return post (+ trailing `regOwn .x9 ** memOwn (sp+3936)`). -/
theorem saveRaAbsThenModCall_then_return_of_callable_post_noX9_spec_in_smodCodeV5
    {nSteps : Nat}
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) (base + resultSignFixOff) (smodCodeV5 base)
        (saveRaAbsThenModCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (saveRaAbsThenModCallCallablePost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
         memOwn (sp + signExtend12 3936))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + nSteps) + 21) + 1)
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (smodCodeV5 base)
      (((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign dividendTop
       ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (smodResultSignFixPost (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
        smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) **
       memOwn (sp + signExtend12 3936)) := by
  let dividendAbsWord : EvmWord :=
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
  let resultSign := smodAbsSign dividendTop
  have hPrefix :=
    saveRaAbsThenModCall_then_resultSignFix_of_callable_post_noX9_spec_in_smodCodeV5
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hCallable
  have hRetFramePc :
      (smodResultSignFixPost (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodSavedRaRetFrame sp base dividendTop dividendAbsWord).pcFree := by
    pcFree
  have hRetFramedInner :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (smodResultSignFixPost (sp + 32) resultSign
        (modWord.getLimbN 0) (modWord.getLimbN 1)
        (modWord.getLimbN 2) (modWord.getLimbN 3) **
       smodSavedRaRetFrame sp base dividendTop dividendAbsWord)
      hRetFramePc
      (savedRaRet_spec_in_smodCodeV5
        (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) base)
  have hTpc : (memOwn (sp + signExtend12 3936)).pcFree := by
    pcFree
  have hRetFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (memOwn (sp + signExtend12 3936))
      hTpc hRetFramedInner
  have hFall :
      (base + resultSignFixOff) + 84 = base + savedRaRetOff := by
    simp [resultSignFixOff, savedRaRetOff]
    bv_addr
  have hRetFramed' :
      EvmAsm.Rv64.cpsTripleWithin 1 ((base + resultSignFixOff) + 84)
        (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
          EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word))
        (smodCodeV5 base)
        (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (smodResultSignFixPost (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) **
          smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) **
         memOwn (sp + signExtend12 3936))
        (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (smodResultSignFixPost (sp + 32) resultSign
          (modWord.getLimbN 0) (modWord.getLimbN 1)
          (modWord.getLimbN 2) (modWord.getLimbN 3) **
          smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) **
         memOwn (sp + signExtend12 3936)) := by
    rw [hFall]
    exact hRetFramed
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [smodModCallResultSignFixFrame_to_savedRaRet] at hp
      xperm_hyp hp)
    hPrefix hRetFramed'

end EvmAsm.Evm64.SMod.Compose
