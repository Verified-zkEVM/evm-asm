/-
  EvmAsm.Codegen.Programs.CalcExcessBlobGasFnSAsm

  Single-exit SAsm re-emission of `calc_excess_blob_gas`.  The existing
  `CalcExcessBlobGasSAsm` theorem verifies the emitted two-ret routine with
  `retIf`; this module supplies the caller-friendly `Fn` shape by selecting
  the result into `a0` and sharing one return epilogue.

  This changes guest bytes (the branch layout is different), so the module
  intentionally records an EEST A/B requirement rather than claiming the old
  byte tie.
-/

import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.CalcExcessBlobGasSAsm
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace CalcExcessBlobGasFnSAsm

open CalcExcessBlobGasSAsm

def calcExcessBlobGasFnBody : Stmt :=
  .block "sum" [.ADD .x5 .x10 .x11] ;;;
  .ite "ge" (.bgeu .x5 .x12)
    (.block "sub" [.SUB .x10 .x5 .x12])
    (.block "zero" [.LI .x10 (0 : Word)])

def calcExcessBlobGasFn (parentExcess blobGasUsed target : Word) : Fn where
  name := "calcExcessBlobGas"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun rf _ A =>
    rf.get .x10 = parentExcess ∧ rf.get .x11 = blobGasUsed ∧
      rf.get .x12 = target ∧ A = empAssertion
  post := fun rf _ A =>
    rf.get .x10 = calcExcessBlobGasResult parentExcess blobGasUsed target ∧
      A = empAssertion
  body := calcExcessBlobGasFnBody

/- The unified body is intentionally not byte-identical to the old two-ret
   Program.  It is a drop-in replacement only after EEST A/B and entry-table
   rewiring by the maintainer. -/
#guard ((calcExcessBlobGasFnBody.flatten 0 : List Instr).length) = 5
#guard ((calcExcessBlobGasFn 0 0 0).body.flatten 0 ++
    [Instr.JALR .x0 .x1 (0 : BitVec 12)]).length = 6

theorem calcExcessBlobGasFn_spec (parentExcess blobGasUsed target base : Word) :
    (calcExcessBlobGasFn parentExcess blobGasUsed target).Spec base := by
  vcgen
  case calcExcessBlobGas.post =>
    intro rf ws A hsp
    simp only [calcExcessBlobGasFn] at hsp ⊢
    rcases hsp with hsub | hzero
    · rcases hsub with ⟨hsum, hholds⟩
      rcases hholds with ⟨ws1, hlen1, hreach, hrf1, hws1⟩
      rcases hreach with ⟨hsumsp, hholds⟩
      rcases hsumsp with ⟨rf0, ws0, hlen0, hpre, rfl, rfl⟩
      rcases hpre with ⟨hx10, hx11, hx12, hA⟩
      rw [hA]
      rw [hrf1]
      unfold calcExcessBlobGasResult
      simp [execBlock, execInstrRF, aluSem, Cond.holds, hx10, hx11, hx12] at hholds ⊢
      intro hlt
      simp_all
    · rcases hzero with ⟨hsum, hnot⟩
      rcases hnot with ⟨ws1, hlen1, hreach, hrf1, hws1⟩
      rcases hreach with ⟨hsumsp, hnot⟩
      rcases hsumsp with ⟨rf0, ws0, hlen0, hpre, rfl, rfl⟩
      rcases hpre with ⟨hx10, hx11, hx12, hA⟩
      rw [hA]
      rw [hrf1]
      unfold calcExcessBlobGasResult
      simp [execBlock, execInstrRF, aluSem, Cond.holds, hx10, hx11, hx12] at hnot ⊢
      intro hge
      simp_all


end CalcExcessBlobGasFnSAsm
end EvmAsm.Codegen
