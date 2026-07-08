/-
  EvmAsm.Codegen.Programs.BalGasValidSAsm

  Verified SAsm leaf ports for small BAL gas-validation helpers.
-/

import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace BalGasValidSAsm

open SgLoadU32leSAsm

/-- The straight-line instruction sequence for `bgv_u32le`: four byte loads
    assembled little-endian into `a0`. -/
def bgvU32leInstrs : List Instr :=
  [ .LBU .x5 .x10 0,
    .LBU .x6 .x10 1, .SLLI .x6 .x6 8,  .OR .x5 .x5 .x6,
    .LBU .x6 .x10 2, .SLLI .x6 .x6 16, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 3, .SLLI .x6 .x6 24, .OR .x5 .x5 .x6,
    .MV .x10 .x5 ]

def bgvU32leBody : Stmt := .block "read" bgvU32leInstrs

/-- Verified port of `bgv_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def bgvU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "bgvU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := bgvU32leBody

theorem bgvU32le_byte_tie :
    (bgvU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = bgvU32le_prog := rfl

#guard ((bgvU32leFn 0 []).body.flatten 0).length = 11

private theorem bgvU32le_engine (reg : Region) (rwb : Word) (rf : RegFile)
    (hx10 : rf.get .x10 = reg.base) :
    (execBlock reg rwb rf [] bgvU32leInstrs).1.get .x10 = leU32 reg.bytes 0 := by
  have e0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - reg.base).toNat = 0 := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  have e1 : (rf.get .x10 + signExtend12 (1 : BitVec 12) - reg.base).toNat = 1 := by
    rw [hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    bv_omega
  have e2 : (rf.get .x10 + signExtend12 (2 : BitVec 12) - reg.base).toNat = 2 := by
    rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]
    bv_omega
  have e3 : (rf.get .x10 + signExtend12 (3 : BitVec 12) - reg.base).toNat = 3 := by
    rw [hx10, show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide]
    bv_omega
  simp only [bgvU32leInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil,
    aluSem, loadSem, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]
  simp only [Region.byteAt, e0, e1, e2, e3]
  rfl

theorem bgvU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (bgvU32leFn p bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case bgvU32le.read.mem =>
    rintro rf ws A hws ⟨hx10, hlen⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    have e0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - p).toNat = 0 := by
      rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have e1 : (rf.get .x10 + signExtend12 (1 : BitVec 12) - p).toNat = 1 := by
      rw [hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    have e2 : (rf.get .x10 + signExtend12 (2 : BitVec 12) - p).toNat = 2 := by
      rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]
      bv_omega
    have e3 : (rf.get .x10 + signExtend12 (3 : BitVec 12) - p).toNat = 3 := by
      rw [hx10, show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide]
      bv_omega
    simp only [execInstrRF_nil, aluSem, loadSem, storeSem, blockVCs, Region.loadOk,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, bgvU32leFn, bgvU32leInstrs, inRw, List.length_nil,
      Nat.le_zero, e0, e1, e2, e3]
    refine ⟨⟨Nat.one_dvd _, by omega⟩, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩,
      trivial, trivial, trivial, trivial⟩
  case bgvU32le.post =>
    intro rf' ws' A' h
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, _⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    show RegFile.get _ .x10 = leU32 bs 0
    exact bgvU32le_engine (bgvU32leFn p bs).region
      (bgvU32leFn p bs).rw.base rf₀ hx10


end BalGasValidSAsm

end EvmAsm.Codegen
