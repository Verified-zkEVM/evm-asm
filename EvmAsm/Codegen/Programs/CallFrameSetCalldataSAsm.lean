import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.CallFrameDescend

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt

namespace CallFrameSetCalldataSAsm

private theorem se12_416 : signExtend12 (416 : BitVec 12) = (416 : Word) := by decide
private theorem se12_424 : signExtend12 (424 : BitVec 12) = (424 : Word) := by decide

/-- Verified port of `call_frame_set_calldata`.

`a0` is the child environment base, `a1` is the parent memory base, `a2` is the
argument offset in parent memory, and `a3` is the argument length. The routine
stores `parentMem + argsOff` at child env offset 416 and `argsLen` at offset
424. -/
def callFrameSetCalldataFn (childEnv parentMem argsOff argsLen : Word)
    (orig : List (BitVec 8)) : Fn where
  name := "callFrameSetCalldata"
  region := Region.empty
  rw := ⟨childEnv, 432⟩
  pre := fun rf ws A =>
    rf.get .x10 = childEnv ∧ rf.get .x11 = parentMem ∧
    rf.get .x12 = argsOff ∧ rf.get .x13 = argsLen ∧
    ws = orig ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = childEnv ∧ rf.get .x11 = parentMem ∧
    rf.get .x12 = argsOff ∧ rf.get .x13 = argsLen ∧
    ws =
      setBytes (setBytes orig 416 (dwordBytes (parentMem + argsOff)))
        424 (dwordBytes argsLen) ∧
    A = empAssertion
  body := .block "body"
    [ .ADD .x5 .x11 .x12,
      .SD .x10 .x5 (416 : BitVec 12),
      .SD .x10 .x13 (424 : BitVec 12) ]

theorem callFrameSetCalldata_byte_tie :
    (callFrameSetCalldataFn 0 0 0 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = callFrameSetCalldata_prog := rfl

#guard ((callFrameSetCalldataFn 0 0 0 0 []).body.flatten 0).length = 3
#guard (callFrameSetCalldataFn 0 0 0 0 []).body.flatten 0 =
  (callFrameSetCalldataFn 0 0 0 0 []).body.flatten 0x80000000

theorem callFrameSetCalldataFn_spec (childEnv parentMem argsOff argsLen : Word)
    (orig : List (BitVec 8)) (base : Word)
    (h_wf : RwRegion.wf ⟨childEnv, 432⟩) :
    (callFrameSetCalldataFn childEnv parentMem argsOff argsLen orig).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, h_wf⟩
  case callFrameSetCalldata.body.mem =>
    rintro rf ws A h_ws h_pre
    obtain ⟨h_x10, h_x11, h_x12, h_x13, h_ws_orig, h_A⟩ := h_pre
    have h_ws_len : ws.length = 432 := h_ws
    simp only [callFrameSetCalldataFn, blockVCs, loadSem, storeSem, aluSem,
      execInstrRF, inRw, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_416, se12_424, h_x10, h_x11,
      h_x12, h_ws_len]
    constructor
    · trivial
    constructor
    · have h_idx : (childEnv + (416 : Word) - childEnv).toNat = 416 := by
        bv_omega
      rw [h_idx]
      exact ⟨by omega, by decide⟩
    constructor
    · have h_idx : (childEnv + (424 : Word) - childEnv).toNat = 424 := by
        bv_omega
      rw [h_idx, length_setBytes]
      exact ⟨by omega, by decide⟩
    · trivial
  case callFrameSetCalldata.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, h_ws₀, h_pre, rfl, rfl⟩
    obtain ⟨h_x10, h_x11, h_x12, h_x13, h_ws_orig, h_A⟩ := h_pre
    refine ⟨?_, ?_, ?_, ?_, ?_, h_A⟩
    · simp only [callFrameSetCalldataFn, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, loadSem, storeSem, RegFile.get_set_self,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, se12_416,
        se12_424, h_x10, h_x11, h_x12, h_x13]
    · simp only [callFrameSetCalldataFn, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, loadSem, storeSem, RegFile.get_set_self,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, se12_416,
        se12_424, h_x10, h_x11, h_x12, h_x13]
    · simp only [callFrameSetCalldataFn, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, loadSem, storeSem, RegFile.get_set_self,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, se12_416,
        se12_424, h_x10, h_x11, h_x12, h_x13]
    · simp only [callFrameSetCalldataFn, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, loadSem, storeSem, RegFile.get_set_self,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, se12_416,
        se12_424, h_x10, h_x11, h_x12, h_x13]
    · simp only [callFrameSetCalldataFn, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, loadSem, storeSem, RegFile.get_set_self,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, se12_416,
        se12_424, h_x10, h_x11, h_x12, h_x13, h_ws_orig]
      have h_idx416 : (childEnv + (416 : Word) - childEnv).toNat = 416 := by
        bv_omega
      have h_idx424 : (childEnv + (424 : Word) - childEnv).toNat = 424 := by
        bv_omega
      rw [h_idx416, h_idx424]

end CallFrameSetCalldataSAsm

end EvmAsm.Codegen
