/-
  EvmAsm.Codegen.Programs.EphU32leSAsm

  Verified SAsm port of the byte-wise `eph_u32le` SSZ leaf helper.  Its
  instruction sequence is the same four-LBU little-endian loader used by
  `sg_load_u32le`/`spw_u32le`; the generic proof is reused, while this module
  pins the helper's own emitted Program by a separate byte tie.
-/

import EvmAsm.Codegen.Programs.SszParentHeader
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.Programs.BlockAccessListHashSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace EphU32leSAsm

def ephU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "ephU32le"
  region := ⟨p, bs⟩
  -- ⚠️ Ambient PINNED (#12244), matching `BlockAccessListHashSAsm.bahU32leFn` — the
  -- SAME `Fn` (same region, same `sgLoadU32leBody`) whose ambient was already pinned
  -- and which is therefore already rowed. `AmbientFreeFlatTriples.lean`'s header named
  -- this routine as "unliftable until their contracts are pinned — a leaf change, not a
  -- lift"; this is that pin.
  -- ⭐ Note what is NOT touched: the SHARED `sgLoadU32leFn` (five consumers). This `Fn`
  -- is a separate definition that merely had identical contents, so re-delegating the
  -- spec below to bah's pinned twin leaves the shared definition alone.
  pre := fun rf _ A => rf.get .x10 = p ∧ 4 ≤ bs.length ∧ A = empAssertion
  post := fun rf _ A => rf.get .x10 = SgLoadU32leSAsm.leU32 bs 0 ∧ A = empAssertion
  body := SgLoadU32leSAsm.sgLoadU32leBody

theorem ephU32le_byte_tie :
    (ephU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = ephU32le_prog := by
  rfl

#guard ((ephU32leFn 0 []).body.flatten 0).length = 11
#guard ephU32le_prog.length = 12

theorem ephU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (ephU32leFn p bs).Spec base := by
  -- `Fn.Spec` ignores the `name` field, so the two `Fn` literals have
  -- definitionally equal specs; `exact` closes that at default transparency.
  exact BlockAccessListHashSAsm.bahU32leFn_spec p bs hwf base


/-! ## Flat linked-entry contract (#12244)

    Ported from `Eip7702NonceReuseGuardSAsm.enrgU32leFlat_spec`, itself ported from
    `BlockAccessListHashSAsm.bahU32leFlat_spec`: the same 4-byte little-endian load.
    Anchored over `CodeReq.ofProg (GuestAddrs.eph_u32le) ephU32le_prog` — the `GuestImageEntries`
    pairing — so this IS the image claim rather than a statement about a model.

    Geometry: non-empty read-only `region` riding through as the trailing conjunct,
    EMPTY writable `rw` (`ws = []`).  Memory is UNTOUCHED: the source region is pinned
    intact in the post, and the only state change is `a0`.

    Total over its argument types given ABI hypotheses (`4 ≤ bs.length`, region wf,
    aligned `ra`) — no input-domain restriction. -/

def ephU32leCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.eph_u32le : Word) ephU32le_prog

def ephU32leScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_ephU32le (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf ephU32leScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [ephU32leScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- **`eph_u32le`, whole-routine flat triple at the guest entry.** -/
theorem ephU32leFlat_spec (ret p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (hlen : 4 ≤ bs.length)
    (hsz : 4 * ((ephU32leFn p bs).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((ephU32leFn p bs).body.steps + 1)
      (GuestAddrs.eph_u32le : Word) ret ephU32leCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) **
        regOwns ephU32leScratch ** bytesRegion p bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ SgLoadU32leSAsm.leU32 bs 0) **
        regOwns ephU32leScratch ** bytesRegion p bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns ephU32leScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** bytesRegion p bs)
      (fun vf => ?_))
  have hpre : (ephU32leFn p bs).pre
      (fun r => if r = .x10 then p else vf r) [] empAssertion := by
    refine ⟨?_, hlen, rfl⟩
    show RegFile.get _ .x10 = p
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (ephU32leFn p bs) (GuestAddrs.eph_u32le : Word)
    (ephU32leFn_spec p bs hwf (GuestAddrs.eph_u32le : Word)) hsz ret halign
    (fun r => if r = .x10 then p else vf r) [] empAssertion pcFree_emp rfl hpre
    (Q := (.x10 ↦ᵣ SgLoadU32leSAsm.leU32 bs 0) ** regOwns ephU32leScratch)
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' hlen' hpost hp hh => by
      obtain ⟨hx10, _hA⟩ := hpost
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hlen'
      simp only [bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_ephU32le,
        show rf' .x10 = SgLoadU32leSAsm.leU32 bs 0 from by
          rw [← hx10, RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]] at hh
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) ephU32leScratch) hp hh)
  rw [show (ephU32leFn p bs).programRet
      (GuestAddrs.eph_u32le : Word) = ephU32le_prog from rfl] at had
  rw [show (ephU32leFn p bs).rw.base = (0 : Word) from rfl,
    show (ephU32leFn p bs).region = Region.mk p bs from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_ephU32le,
    show (if (Reg.x10 : Reg) = .x10 then p else vf .x10) = p from if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then p else vf r) vf ephU32leScratch
      (fun r hr => by
        have hne : r ≠ (.x10 : Reg) := by
          intro heq
          subst heq
          have hnot : (.x10 : Reg) ∉ ephU32leScratch := by decide
          exact hnot hr
        simp [hne])] at had
  simp only [bytesRegion_nil, sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end EphU32leSAsm
end EvmAsm.Codegen
