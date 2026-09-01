/-
  EvmAsm.Codegen.Proofs.SgLoadU32leFlatEntry

  The flat whole-routine contract for `sg_load_u32le` at its linked
  guest address (#13091) — the sixth twin of the LBU-packed
  little-endian u32 reader family (`bah`/`enrg`/`spw`/`sws`/`eph`),
  lifted exactly as `sws_u32le` was in
  `SszWitnessStateSAsm.lean`: a separate ambient-PINNED `Fn` literal
  (the shared `sgLoadU32leFn`, with its five consumers, is left alone)
  whose spec delegates to the already-pinned `bahU32leFn_spec`, then
  `Fn.retSpecFlatAmbient` at the guest entry.
-/

import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.Programs.BlockAccessListHashSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.SgLoadU32leFlatEntry

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.SgLoadU32leSAsm

/-- Ambient-pinned twin of the shared `sgLoadU32leFn` (#12244 pattern):
    same region, same `sgLoadU32leBody`, `A = empAssertion` pinned so the
    flat lift applies.  The shared five-consumer `Fn` is untouched. -/
def sgluFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "sgLoadU32lePinned"
  region := ⟨p, bs⟩
  pre := fun rf _ A => rf.get .x10 = p ∧ 4 ≤ bs.length ∧ A = empAssertion
  post := fun rf _ A => rf.get .x10 = leU32 bs 0 ∧ A = empAssertion
  body := sgLoadU32leBody

theorem sglu_byte_tie :
    (sgluFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = sgLoadU32le_prog := rfl

theorem sgluFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (sgluFn p bs).Spec base := by
  -- `Fn.Spec` ignores the `name` field, so the two `Fn` literals have
  -- definitionally equal specs; `exact` closes that at default
  -- transparency (the `swsU32leFn_spec` route).
  exact EvmAsm.Codegen.BlockAccessListHashSAsm.bahU32leFn_spec p bs hwf base

/-- The routine's own image at the guest entry. -/
def sgluCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.sg_load_u32le : Word) sgLoadU32le_prog

def sgluScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_sglu (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf sgluScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [sgluScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- ⭐ **`sg_load_u32le`, whole-routine flat triple at the guest
    entry**: `a0` becomes `leU32 bs 0`, memory untouched. -/
theorem sgLoadU32leFlat_spec (ret p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (hlen : 4 ≤ bs.length)
    (hsz : 4 * ((sgluFn p bs).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((sgluFn p bs).body.steps + 1)
      (GuestAddrs.sg_load_u32le : Word) ret sgluCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) **
        regOwns sgluScratch ** bytesRegion p bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ leU32 bs 0) **
        regOwns sgluScratch ** bytesRegion p bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns sgluScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** bytesRegion p bs)
      (fun vf => ?_))
  have hpre : (sgluFn p bs).pre
      (fun r => if r = .x10 then p else vf r) [] empAssertion := by
    refine ⟨?_, hlen, rfl⟩
    show RegFile.get _ .x10 = p
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (sgluFn p bs) (GuestAddrs.sg_load_u32le : Word)
    (sgluFn_spec p bs hwf (GuestAddrs.sg_load_u32le : Word)) hsz ret halign
    (fun r => if r = .x10 then p else vf r) [] empAssertion pcFree_emp rfl hpre
    (Q := (.x10 ↦ᵣ leU32 bs 0) ** regOwns sgluScratch)
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' hlen' hpost hp hh => by
      obtain ⟨hx10, _hA⟩ := hpost
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hlen'
      simp only [bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_sglu,
        show rf' .x10 = leU32 bs 0 from by
          rw [← hx10, RegFile.get,
            if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]] at hh
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) sgluScratch) hp hh)
  rw [show (sgluFn p bs).programRet
      (GuestAddrs.sg_load_u32le : Word) = sgLoadU32le_prog from rfl] at had
  rw [show (sgluFn p bs).rw.base = (0 : Word) from rfl,
    show (sgluFn p bs).region = Region.mk p bs from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_sglu,
    show (if (Reg.x10 : Reg) = .x10 then p else vf .x10) = p from if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then p else vf r) vf sgluScratch
      (fun r hr => by
        have hne : r ≠ (.x10 : Reg) := by
          intro heq
          subst heq
          have hnot : (.x10 : Reg) ∉ sgluScratch := by decide
          exact hnot hr
        simp [hne])] at had
  simp only [bytesRegion_nil, sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

#print axioms sgLoadU32leFlat_spec

end EvmAsm.Codegen.SgLoadU32leFlatEntry
