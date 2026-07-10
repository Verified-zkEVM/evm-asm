/- Byte-identical SAsm specification of `init_code_cost`. -/

import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace InitCodeCostSAsm

def initCodeCost (initCodeLength gasPerWord : Word) : Word :=
  ((initCodeLength + 31) >>> 5) * gasPerWord

def initCodeCostFn (initCodeLength gasPerWord outPtr : Word)
    (orig : List (BitVec 8)) : Fn where
  name := "initCodeCost"
  region := Region.empty
  rw := ⟨outPtr, 8⟩
  pre := fun rf ws A =>
    rf.get .x10 = initCodeLength ∧ rf.get .x11 = gasPerWord ∧
    rf.get .x12 = outPtr ∧ ws = orig ∧ orig.length = 8 ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = 0 ∧ ws = dwordBytes (initCodeCost initCodeLength gasPerWord) ∧
    A = empAssertion
  body := .block "initCodeCost"
    [ .ADDI .x5 .x10 (31 : BitVec 12),
      .SRLI .x5 .x5 (5 : BitVec 6),
      .MUL .x5 .x5 .x11,
      .SD .x12 .x5 (0 : BitVec 12),
      .LI .x10 (0 : Word) ]

theorem initCodeCost_byte_tie :
    (initCodeCostFn 0 0 0 []).body.flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] = initCodeCost_prog := by
  rfl

#guard (initCodeCostFn 0 0 0 []).body.flatten 0 =
  (initCodeCostFn 0 0 0 []).body.flatten 0x80000000

private theorem setBytes_zero_dword_eq (orig : List (BitVec 8))
    (v : Word) (h : orig.length = 8) :
    setBytes orig 0 (dwordBytes v) = dwordBytes v := by
  apply List.ext_getElem
  · simp only [length_setBytes, h, length_dwordBytes]
  · intro i hi hj
    rw [length_setBytes, h] at hi
    interval_cases i <;> simp [setBytes, dwordBytes]

theorem initCodeCostFn_spec (initCodeLength gasPerWord outPtr base : Word)
    (orig : List (BitVec 8)) (hrw : RwRegion.wf ⟨outPtr, 8⟩) :
    (initCodeCostFn initCodeLength gasPerWord outPtr orig).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case initCodeCost.mem =>
    rintro rf ws A hlen ⟨hx10, hx11, hx12, hws, horig, hA⟩
    subst ws
    simp only [initCodeCostFn, blockVCs, execInstrRF, aluSem, loadSem,
      storeSem, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
      reduceCtorEq, not_false_eq_true, hx10, hx11, hx12, horig,
      signExtend12_0, true_and]
    have hzero : (outPtr + (0 : Word) - outPtr).toNat = 0 := by
      rw [show outPtr + (0 : Word) - outPtr = (0 : Word) by bv_omega]
      decide
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · unfold inRw
      rw [horig, hzero]
    · rw [hzero]
      norm_num
  case initCodeCost.post =>
    rintro rf ws A ⟨rf0, ws0, hlen, ⟨hx10, hx11, hx12, hws, horig, hA⟩,
      rfl, rfl⟩
    subst ws0
    simp only [initCodeCostFn, initCodeCost, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, loadSem, storeSem, RegFile.get_set_self,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
      hx10, hx11, hx12, signExtend12_0]
    rw [show (outPtr + (0 : Word) - outPtr).toNat = 0 by bv_omega,
      show (5 : BitVec 6).toNat = 5 by decide,
      setBytes_zero_dword_eq orig _ horig, hA]
    norm_num

#print axioms initCodeCostFn_spec

end InitCodeCostSAsm
end EvmAsm.Codegen
