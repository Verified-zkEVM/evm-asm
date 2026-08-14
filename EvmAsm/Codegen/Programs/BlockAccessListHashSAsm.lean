/-
  EvmAsm.Codegen.Programs.BlockAccessListHashSAsm

  Verified SAsm port for `bah_u32le`.
-/

import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace BlockAccessListHashSAsm

open SgLoadU32leSAsm

/-- Verified port of `bah_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def bahU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "bahU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ A => rf.get .x10 = p ∧ 4 ≤ bs.length ∧ A = empAssertion
  post := fun rf _ A => rf.get .x10 = leU32 bs 0 ∧ A = empAssertion
  body := sgLoadU32leBody

theorem bahU32le_byte_tie :
    (bahU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = bahU32le_prog := rfl

#guard ((bahU32leFn 0 []).body.flatten 0).length = 11

private theorem bahU32le_engine (reg : Region) (rwb : Word) (rf : RegFile)
    (hx10 : rf.get .x10 = reg.base) :
    (execBlock reg rwb rf [] SgLoadU32leSAsm.sgLoadU32leInstrs).1.get .x10 =
      leU32 reg.bytes 0 := by
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
  simp only [SgLoadU32leSAsm.sgLoadU32leInstrs, execBlock_cons, execBlock_nil,
    execInstrRF_nil, aluSem, loadSem, RegFile.get_set_self, RegFile.get_set_ne,
    ne_eq, reduceCtorEq, not_false_eq_true]
  simp only [Region.byteAt, e0, e1, e2, e3]
  rfl

theorem bahU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (bahU32leFn p bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case bahU32le.read.mem =>
    rintro rf ws A hws ⟨hx10, hlen, hA⟩
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
      not_false_eq_true, bahU32leFn, sgLoadU32leBody, sgLoadU32leInstrs, inRw,
      List.length_nil, Nat.le_zero, e0, e1, e2, e3]
    refine ⟨⟨Nat.one_dvd _, by omega⟩, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩,
      trivial, trivial, trivial, trivial⟩
  case bahU32le.post =>
    intro rf' ws' A' h
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, _, hA⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    refine ⟨?_, hA⟩
    show RegFile.get _ .x10 = leU32 bs 0
    exact bahU32le_engine (bahU32leFn p bs).region
      (bahU32leFn p bs).rw.base rf₀ hx10

def bahU32leCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bah_u32le : Word) bahU32le_prog

def bahU32leScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_bah (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf bahU32leScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bahU32leScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

theorem bahU32leFlat_spec (ret p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (hlen : 4 ≤ bs.length)
    (hsz : 4 * ((bahU32leFn p bs).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bahU32leFn p bs).body.steps + 1)
      (GuestAddrs.bah_u32le : Word) ret bahU32leCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) **
        regOwns bahU32leScratch ** bytesRegion p bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ leU32 bs 0) **
        regOwns bahU32leScratch ** bytesRegion p bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bahU32leScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** bytesRegion p bs)
      (fun vf => ?_))
  have hpre : (bahU32leFn p bs).pre
      (fun r => if r = .x10 then p else vf r) [] empAssertion := by
    refine ⟨?_, hlen, rfl⟩
    show RegFile.get _ .x10 = p
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (bahU32leFn p bs) (GuestAddrs.bah_u32le : Word)
    (bahU32leFn_spec p bs hwf (GuestAddrs.bah_u32le : Word)) hsz ret halign
    (fun r => if r = .x10 then p else vf r) [] empAssertion pcFree_emp rfl hpre
    (Q := (.x10 ↦ᵣ leU32 bs 0) ** regOwns bahU32leScratch)
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' hlen' hpost hp hh => by
      obtain ⟨hx10, _hA⟩ := hpost
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hlen'
      simp only [bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_bah,
        show rf' .x10 = leU32 bs 0 from by
          rw [← hx10, RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]] at hh
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) bahU32leScratch) hp hh)
  rw [show (bahU32leFn p bs).programRet
      (GuestAddrs.bah_u32le : Word) = bahU32le_prog from rfl] at had
  rw [show (bahU32leFn p bs).rw.base = (0 : Word) from rfl,
    show (bahU32leFn p bs).region = Region.mk p bs from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_bah,
    show (if (Reg.x10 : Reg) = .x10 then p else vf .x10) = p from if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then p else vf r) vf bahU32leScratch
      (fun r hr => by
        have hne : r ≠ (.x10 : Reg) := by
          intro heq
          subst heq
          have hnot : (.x10 : Reg) ∉ bahU32leScratch := by decide
          exact hnot hr
        simp [hne])] at had
  simp only [bytesRegion_nil, sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end BlockAccessListHashSAsm

end EvmAsm.Codegen
