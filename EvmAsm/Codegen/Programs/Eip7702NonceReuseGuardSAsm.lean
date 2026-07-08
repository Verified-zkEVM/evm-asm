/-
  EvmAsm.Codegen.Programs.Eip7702NonceReuseGuardSAsm

  Verified SAsm port for `enrg_u32le`.
-/

import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Eip7702NonceReuseGuardSAsm

open SgLoadU32leSAsm (leU32)

/-- `enrg_u32le` reads four bytes and writes the final OR directly to `a0`. -/
def enrgU32leInstrs : List Instr :=
  [ .LBU .x5 .x10 0,
    .LBU .x6 .x10 1, .SLLI .x6 .x6 8,  .OR .x5 .x5 .x6,
    .LBU .x6 .x10 2, .SLLI .x6 .x6 16, .OR .x5 .x5 .x6,
    .LBU .x6 .x10 3, .SLLI .x6 .x6 24, .OR .x10 .x5 .x6 ]

/-- The straight-line body. Matches `enrg_u32le` sans its `ret`. -/
def enrgU32leBody : Stmt := .block "read" enrgU32leInstrs

/-- Verified port of `enrg_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def enrgU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "enrgU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := enrgU32leBody

private theorem enrgU32le_engine (reg : Region) (rwb : Word) (rf : RegFile)
    (hx10 : rf.get .x10 = reg.base) :
    (execBlock reg rwb rf [] enrgU32leInstrs).1.get .x10 = leU32 reg.bytes 0 := by
  have e0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - reg.base).toNat = 0 := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have e1 : (rf.get .x10 + signExtend12 (1 : BitVec 12) - reg.base).toNat = 1 := by
    rw [hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
  have e2 : (rf.get .x10 + signExtend12 (2 : BitVec 12) - reg.base).toNat = 2 := by
    rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]; bv_omega
  have e3 : (rf.get .x10 + signExtend12 (3 : BitVec 12) - reg.base).toNat = 3 := by
    rw [hx10, show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide]; bv_omega
  simp only [enrgU32leInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil,
    aluSem, loadSem, RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]
  simp only [Region.byteAt, e0, e1, e2, e3]
  rfl

theorem enrgU32le_byte_tie :
    (enrgU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = enrgU32le_prog := rfl

#guard ((enrgU32leFn 0 []).body.flatten 0).length = 10

theorem enrgU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (enrgU32leFn p bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case enrgU32le.read.mem =>
    rintro rf ws A hws ⟨hx10, hlen⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    have e0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - p).toNat = 0 := by
      rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
    have e1 : (rf.get .x10 + signExtend12 (1 : BitVec 12) - p).toNat = 1 := by
      rw [hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    have e2 : (rf.get .x10 + signExtend12 (2 : BitVec 12) - p).toNat = 2 := by
      rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]; bv_omega
    have e3 : (rf.get .x10 + signExtend12 (3 : BitVec 12) - p).toNat = 3 := by
      rw [hx10, show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide]; bv_omega
    simp only [execInstrRF_nil, aluSem, loadSem, storeSem, blockVCs, Region.loadOk,
      RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, enrgU32leFn, enrgU32leInstrs, inRw, List.length_nil,
      Nat.le_zero, e0, e1, e2, e3]
    refine ⟨⟨Nat.one_dvd _, by omega⟩, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩,
      trivial, trivial, trivial⟩
  case enrgU32le.post =>
    intro rf' ws' A' h
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, _⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    show RegFile.get _ .x10 = leU32 bs 0
    exact enrgU32le_engine (enrgU32leFn p bs).region
      (enrgU32leFn p bs).rw.base rf₀ hx10

end Eip7702NonceReuseGuardSAsm

end EvmAsm.Codegen
