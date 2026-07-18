import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Secp256k1Field

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt

namespace Secp256k1FieldGetBitLsbSAsm

def secfGetBitLsbOffset (bitIdx : Word) : Word :=
  (31 : Word) - (bitIdx >>> 3)

def secfGetBitLsbResult (src : Word) (bs : List (BitVec 8)) (bitIdx : Word) : Word :=
  ((((Region.byteAt ⟨src, bs⟩ (src + secfGetBitLsbOffset bitIdx)).zeroExtend 64 : Word)
      >>> (((bitIdx &&& (7 : Word)).toNat) % 64)) &&& (1 : Word))

def secfGetBitLsbFn (src bitIdx : Word) (bs : List (BitVec 8)) : Fn where
  name := "secfGetBitLsb"
  region := ⟨src, bs⟩
  rw := RwRegion.empty
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = bitIdx ∧ ws = [] ∧ bs.length = 32 ∧
    Region.loadOk ⟨src, bs⟩ (src + secfGetBitLsbOffset bitIdx) 1 ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = secfGetBitLsbResult src bs bitIdx ∧ ws = [] ∧ A = empAssertion
  body := .block "body"
    [ .SRLI .x5 .x11 (3 : BitVec 6),
      .LI .x6 (31 : Word),
      .SUB .x5 .x6 .x5,
      .ADD .x5 .x10 .x5,
      .LBU .x6 .x5 (0 : BitVec 12),
      .ANDI .x7 .x11 (7 : BitVec 12),
      .SRL .x6 .x6 .x7,
      .ANDI .x10 .x6 (1 : BitVec 12) ]

theorem secfGetBitLsb_byte_tie :
    (secfGetBitLsbFn 0 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = secfGetBitLsb_prog := rfl

#guard ((secfGetBitLsbFn 0 0 []).body.flatten 0).length = 8
#guard (secfGetBitLsbFn 0 0 []).body.flatten 0 =
  (secfGetBitLsbFn 0 0 []).body.flatten 0x80000000

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_7 : signExtend12 (7 : BitVec 12) = (7 : Word) := by decide

theorem secfGetBitLsbFn_spec (src bitIdx : Word) (bs : List (BitVec 8))
    (base : Word) (h_ro_wf : Region.wf ⟨src, bs⟩) :
    (secfGetBitLsbFn src bitIdx bs).Spec base := by
  vcgen
  case region => exact ⟨h_ro_wf, RwRegion.empty_wf⟩
  case secfGetBitLsb.body.mem =>
    rintro rf ws A h_ws h_pre
    obtain ⟨h_x10, h_x11, h_ws_eq, h_bs_len, h_load, h_A⟩ := h_pre
    subst ws
    simp only [secfGetBitLsbFn, secfGetBitLsbOffset, blockVCs, execInstrRF,
      aluSem, loadSem, storeSem, inRw, RwRegion.empty, RegFile.get_set_self,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, se12_0,
      h_x10, h_x11]
    refine ⟨trivial, trivial, trivial, trivial, ?_, trivial, trivial, trivial, trivial⟩
    simpa [secfGetBitLsbOffset] using h_load
  case secfGetBitLsb.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, h_ws₀, h_pre, rfl, rfl⟩
    obtain ⟨h_x10, h_x11, h_ws_eq, h_bs_len, h_load, h_A⟩ := h_pre
    subst ws'
    refine ⟨?_, rfl, h_A⟩
    simp only [secfGetBitLsbFn, secfGetBitLsbResult, secfGetBitLsbOffset,
      execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem, inRw,
      RwRegion.empty, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_0, se12_1, se12_7, h_x10, h_x11]
    have h_no_rw (a : Word) : ¬ a.toNat + 1 ≤ ([] : List (BitVec 8)).length := by
      simp
    simp only [h_no_rw, if_false, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
      reduceCtorEq, not_false_eq_true]
    simp [h_x11]

end Secp256k1FieldGetBitLsbSAsm

end EvmAsm.Codegen
