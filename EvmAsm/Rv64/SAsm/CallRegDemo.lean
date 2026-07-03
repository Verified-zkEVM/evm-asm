/-
  EvmAsm.Rv64.SAsm.CallRegDemo

  Demo of the indirect-call construct `Stmt.callReg` (bead evm-asm-4ch8f.4):
  a caller selects one of two handler entry addresses at runtime, then
  dispatches through a register with `jalr ra, rs, 0`.  This is the SAsm
  shape of the guest's dispatch tables (the 256-entry `opcode_handlers`
  table, `tx_type_dispatch`, runtime-armed function-pointer backends): the
  table *load* is ordinary ro-region block machinery; the only new
  primitive is the register-indirect call, whose `.pre` VC demands the
  register hold the entry of one of a finite set of handles.

  The strongest postcondition of a `callReg` is the disjunction of the
  handles' posts.  When a caller needs to know WHICH handler ran (opcode
  dispatch), it instantiates the handles' ghost contracts per call site so
  each disjunct carries its discriminating fact — same pattern as the
  per-call-site region instantiation of `RoWidenDemo`.
-/

import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace CallRegDemo

open Stmt

/-- Handler A: set `x10 := 1`. -/
def crLeafA : Fn where
  name := "crleafA"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x10 = 1
  body := .block "set" [.LI .x10 1]

/-- Handler B: set `x10 := 2`. -/
def crLeafB : Fn where
  name := "crleafB"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x10 = 2
  body := .block "set" [.LI .x10 2]

theorem crLeafA_spec : crLeafA.Spec 0x2000 := by
  vcgen
  case crleafA.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, -, rfl, rfl⟩
    simp only [crLeafA, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    exact RegFile.get_set_self rf₀ .x10 1 (by decide)

theorem crLeafB_spec : crLeafB.Spec 0x2100 := by
  vcgen
  case crleafB.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, -, rfl, rfl⟩
    simp only [crLeafB, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    exact RegFile.get_set_self rf₀ .x10 2 (by decide)

def crLeafAHandle : FnHandle :=
  crLeafA.toHandle 0x2000 crLeafA_spec
    ((by decide : 4 * (crLeafA.body.size + 1) ≤ 2 ^ 64))

def crLeafBHandle : FnHandle :=
  crLeafB.toHandle 0x2100 crLeafB_spec
    ((by decide : 4 * (crLeafB.body.size + 1) ≤ 2 ^ 64))

/-- Dispatch: select a handler address on a runtime condition, call it
    indirectly.  The `.pre` VC of the `callReg` sees the two `LI` branches
    and picks the matching handle on each. -/
def crCallerFn : Fn where
  name := "crcaller"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x10 = 1 ∨ rf.get .x10 = 2
  body :=
    .ite "sel" (.beq .x11 .x0)
      (.block "goA" [.LI .x28 0x2000])
      (.block "goB" [.LI .x28 0x2100]) ;;;
    .callReg "disp" .x28 [crLeafAHandle, crLeafBHandle]

def crCallerCr : CodeReq :=
  ((CodeReq.ofProg 0x1000 (crCallerFn.body.flatten 0x1000)).union
    crLeafAHandle.code).union crLeafBHandle.code

theorem crCallerFn_spec : crCallerFn.SpecR 0x1000 crCallerCr := by
  have hcodeA : ∀ a i, crLeafAHandle.code a = some i →
      crCallerCr a = some i := by
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hk2 : kk < 2 := hk
    have hP : CodeReq.ofProg 0x1000 (crCallerFn.body.flatten 0x1000)
        ((0x2000 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
      apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have hk'5 : k' < 5 := hk'
      bv_omega
    simp only [crCallerCr, CodeReq.union, hP, h]
  have hcodeB : ∀ a i, crLeafBHandle.code a = some i →
      crCallerCr a = some i := by
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hk2 : kk < 2 := hk
    have hP : CodeReq.ofProg 0x1000 (crCallerFn.body.flatten 0x1000)
        ((0x2100 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
      apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have hk'5 : k' < 5 := hk'
      bv_omega
    have hA : crLeafAHandle.code
        ((0x2100 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
      show CodeReq.ofProg 0x2000 (crLeafA.programRet 0x2000)
        ((0x2100 : Word) + BitVec.ofNat 64 (4 * kk)) = none
      apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have hk'2 : k' < 2 := hk'
      bv_omega
    simp only [crCallerCr, CodeReq.union, hP, hA, h]
  show Fn.SpecR _ _ _
  vcgen
  case code =>
    intro a i h
    simp only [crCallerCr, CodeReq.union, h]
  case callees =>
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro h hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨hcodeA, rfl, rfl⟩
    · exact ⟨hcodeB, rfl, rfl⟩
  case calls =>
    refine ⟨⟨trivial, trivial⟩, ?_, ?_⟩
    · exact (by decide : (((0x1010 : Word) + 4) &&& ~~~(1 : Word)) = 0x1010 + 4)
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact (by decide :
          ((crLeafAHandle.entry &&& ~~~(1 : Word))) = crLeafAHandle.entry)
      · exact (by decide :
          ((crLeafBHandle.entry &&& ~~~(1 : Word))) = crLeafBHandle.entry)
  case crcaller.disp.pre =>
    rintro rf ws A (⟨rf₀, ws₀, hlen, -, rfl, rfl⟩ | ⟨rf₀, ws₀, hlen, -, rfl, rfl⟩)
    · refine ⟨crLeafAHandle, by simp, ?_, trivial⟩
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      exact RegFile.get_set_self rf₀ .x28 _ (by decide)
    · refine ⟨crLeafBHandle, by simp, ?_, trivial⟩
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      exact RegFile.get_set_self rf₀ .x28 _ (by decide)
  case crcaller.post =>
    rintro rf ws A ⟨h, hmem, hpost⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl hpost
    · exact Or.inr hpost

end CallRegDemo
end SAsm
end EvmAsm.Rv64
