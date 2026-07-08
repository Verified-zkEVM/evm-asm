/-
  EvmAsm.Codegen.Programs.CalcExcessBlobGasSAsm

  Byte-identical return-terminating SAsm proof for `calc_excess_blob_gas`.
  The emitted routine has two `ret` tails, so this uses `Stmt.retIf` rather
  than the single-exit `Fn.Spec` path.
-/

import EvmAsm.Rv64.SAsm.StmtSound
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace CalcExcessBlobGasSAsm

def calcExcessBlobGasResult (parentExcess blobGasUsed target : Word) : Word :=
  let total := parentExcess + blobGasUsed
  if BitVec.ult total target = true then 0 else total - target

def calcExcessBlobGasBody : Stmt :=
  .block "sum" [.ADD .x5 .x10 .x11] ;;;
  .retIf "ge" (.bgeu .x5 .x12)
    (.block "sub" [.SUB .x10 .x5 .x12] ;;; .ret "ret_sub")
    (.block "zero" [.LI .x10 (0 : Word)] ;;; .ret "ret_zero")

def calcExcessBlobGasPre (parentExcess blobGasUsed target : Word) : Reach :=
  fun rf _ _ =>
    rf.get .x10 = parentExcess ∧ rf.get .x11 = blobGasUsed ∧ rf.get .x12 = target

def calcExcessBlobGasPost (parentExcess blobGasUsed target : Word) : Reach :=
  fun rf _ _ => rf.get .x10 = calcExcessBlobGasResult parentExcess blobGasUsed target

def calcExcessBlobGas_verified : Program :=
  calcExcessBlobGasBody.flatten 0

#guard (calcExcessBlobGas_verified : List Instr).length = 6
#guard calcExcessBlobGasBody.retOffsetsOk
#guard !calcExcessBlobGasBody.offsetsOk
#guard calcExcessBlobGasBody.flatten 0 = calcExcessBlobGas_prog

private theorem calcExcessBlobGas_sp_post
    (parentExcess blobGasUsed target : Word) :
    ∀ rf ws A,
      Stmt.sp Region.empty RwRegion.empty calcExcessBlobGasBody
          (calcExcessBlobGasPre parentExcess blobGasUsed target) rf ws A →
        calcExcessBlobGasPost parentExcess blobGasUsed target rf ws A := by
  intro rf ws A hsp
  unfold calcExcessBlobGasBody at hsp
  simp only [Stmt.sp] at hsp
  rcases hsp with hsub | hzero
  · rcases hsub with ⟨rfBranch, wsBranch, hlen, hreach, hrf, hws⟩
    rcases hreach with ⟨hsum, hcond⟩
    rcases hsum with ⟨rf0, ws0, hlen0, hpre, hrfBranch, hwsBranch⟩
    rcases hpre with ⟨hx10, hx11, hx12⟩
    subst hrf
    subst hrfBranch
    unfold calcExcessBlobGasPost calcExcessBlobGasResult
    simp [execBlock, execInstrRF, aluSem, Cond.holds, hx10, hx11, hx12] at hcond ⊢
    simp [hcond]
  · rcases hzero with ⟨rfBranch, wsBranch, hlen, hreach, hrf, hws⟩
    rcases hreach with ⟨hsum, hcond⟩
    rcases hsum with ⟨rf0, ws0, hlen0, hpre, hrfBranch, hwsBranch⟩
    rcases hpre with ⟨hx10, hx11, hx12⟩
    subst hrf
    subst hrfBranch
    unfold calcExcessBlobGasPost calcExcessBlobGasResult
    simp [execBlock, execInstrRF, aluSem, Cond.holds, hx10, hx11, hx12] at hcond ⊢
    intro hfalse
    rw [hcond] at hfalse
    contradiction

theorem calcExcessBlobGas_spec (parentExcess blobGasUsed target base ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin calcExcessBlobGasBody.steps base ret
      (CodeReq.ofProg base (calcExcessBlobGasBody.flatten base))
      ((((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
        (calcExcessBlobGasPre parentExcess blobGasUsed target)))
      ((((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
        (calcExcessBlobGasPost parentExcess blobGasUsed target))) := by
  have hsound := Stmt.retSound Region.empty RwRegion.empty calcExcessBlobGasBody base ret
    "calcExcessBlobGas." (calcExcessBlobGasPre parentExcess blobGasUsed target)
    Region.empty_wf RwRegion.empty_wf
    (by decide) (by decide) (by decide) halign
    (fun _ _ h => h)
    (by
      intro vc hvc
      unfold calcExcessBlobGasBody at hvc
      simp [Stmt.ret, Stmt.vcs, hasLoad, loadSem, storeSem] at hvc
      rcases hvc with rfl | hvc
      · decide
      rcases hvc with rfl | hvc
      · decide
      rcases hvc with rfl | hvc
      · decide)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (sepConj_mono_right (asrtM_mono
      (calcExcessBlobGas_sp_post parentExcess blobGasUsed target))) hsound

end CalcExcessBlobGasSAsm

end EvmAsm.Codegen
