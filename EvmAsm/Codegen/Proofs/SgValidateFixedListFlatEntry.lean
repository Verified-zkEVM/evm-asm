/-
  EvmAsm.Codegen.Proofs.SgValidateFixedListFlatEntry

  The flat whole-routine contract for `sg_validate_fixed_list` at its
  linked guest address (#13071) — derived from the DCode `retSpec` of
  the proof-first guard cascade (`SgValidateFixedListSAsm`) by packing
  the caller's exposed-register atoms into the callee's `asrtM`
  register file, the `bslFlat_spec`/`callFrameForwardGasFlat_spec`
  shape.  Lives outside the SAsm file so the (rebuild-heavy)
  `GuestAddrs` dependency stays out of the derivation's import cone.
-/

import EvmAsm.Codegen.Programs.SgValidateFixedListSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.SgValidateFixedListSAsm

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

/-- The routine's linked guest entry. -/
abbrev SgvB : Word := (GuestAddrs.sg_validate_fixed_list : Word)

/-- The routine's own image at the guest entry (both return tails are in
    the code — no epilogue). -/
abbrev sgvCode : CodeReq := CodeReq.ofProg SgvB sgValidateFixedList_prog

/-- The generated `Stmt` is ghost-free (the cascade invariants live only
    in the `DStmt` proof component), so its flatten is the pinned program
    at ANY base. -/
private theorem sgv_flatten (len esz maxc b : Word) :
    ((sgvDeriv len esz maxc).stmt.flatten b : List Instr)
      = sgValidateFixedList_prog := rfl

private theorem sgv_steps (len esz maxc : Word) :
    (sgvDeriv len esz maxc).stmt.steps = 7 := rfl

/-- The exposed registers the routine's contract does not pin on entry
    (`a1`/`a2`/`a3` carry the arguments). -/
def sgvScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x10, .x14, .x15, .x16, .x17]

/-- On return only `a0` is pinned. -/
def sgvScratchPost : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem sgv_split_pre (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x11 : Reg) ↦ᵣ vf .x11) ** ((.x12 : Reg) ↦ᵣ vf .x12) **
          ((.x13 : Reg) ↦ᵣ vf .x13) ** regAtomsOf vf sgvScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [sgvScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem sgv_split_post (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x10 : Reg) ↦ᵣ vf .x10) ** regAtomsOf vf sgvScratchPost) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [sgvScratchPost, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- The explicit callee-entry register file. -/
private def sgvRf (len esz maxc : Word) (vf : Reg → Word) : RegFile :=
  fun r => if r = .x11 then len else if r = .x12 then esz
    else if r = .x13 then maxc else vf r

/-- ⭐ **`sg_validate_fixed_list` at its linked guest address.**  Entered
    with `a1` = section byte length, `a2` = element size, `a3` = max
    element count and an aligned return address, it returns
    `a0 = sgvOut len esz maxc` — `0` iff the element size is nonzero,
    tiles the section exactly, and the element count is within bound. -/
theorem sgValidateFixedListFlat_spec (len esz maxc ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7 SgvB ret sgvCode
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x12 : Reg) ↦ᵣ esz) ** ((.x13 : Reg) ↦ᵣ maxc) **
        regOwns sgvScratch)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ sgvOut len esz maxc) **
        regOwns sgvScratchPost) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns sgvScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x12 : Reg) ↦ᵣ esz) ** ((.x13 : Reg) ↦ᵣ maxc))
      (fun vf => ?_))
  have hret := sgValidateFixedList_retSpec len esz maxc SgvB ret halign
  rw [sgv_flatten, sgv_steps] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hret
  · -- pack: the atoms satisfy the callee's `asrtM` register file
    refine sepConj_mono_right (fun h' hp' => ?_) h (by xperm_hyp hp :
      ((((.x1 : Reg) ↦ᵣ ret)) **
        (((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ esz) **
          ((.x13 : Reg) ↦ᵣ maxc) ** regAtomsOf vf sgvScratch)) h)
    show (asrtOf RwRegion.empty _ ** bytesRegion Region.empty.base
      Region.empty.bytes) h'
    rw [show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil, sepConj_emp_right']
    refine ⟨sgvRf len esz maxc vf, [], empAssertion, rfl, pcFree_emp,
      ⟨?_, ?_, ?_, rfl⟩, ?_⟩
    · show RegFile.get _ .x11 = len
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = esz
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [sgvRf, if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
    · show RegFile.get _ .x13 = maxc
      rw [RegFile.get, if_neg (by decide : (Reg.x13 : Reg) ≠ .x0)]
      rw [sgvRf, if_neg (by decide : (Reg.x13 : Reg) ≠ .x11),
        if_neg (by decide : (Reg.x13 : Reg) ≠ .x12)]
      exact if_pos rfl
    · rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        sgv_split_pre,
        show sgvRf len esz maxc vf .x11 = len from if_pos rfl,
        show sgvRf len esz maxc vf .x12 = esz from by
          rw [sgvRf, if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
          exact if_pos rfl,
        show sgvRf len esz maxc vf .x13 = maxc from by
          rw [sgvRf, if_neg (by decide : (Reg.x13 : Reg) ≠ .x11),
            if_neg (by decide : (Reg.x13 : Reg) ≠ .x12)]
          exact if_pos rfl,
        regAtomsOf_congr (fun r => sgvRf len esz maxc vf r) vf sgvScratch
          (fun r hr => by
            show (if r = .x11 then len else if r = .x12 then esz
              else if r = .x13 then maxc else vf r) = vf r
            rw [if_neg (fun hc => (by decide :
                  (Reg.x11 : Reg) ∉ sgvScratch) (by rw [← hc]; exact hr)),
              if_neg (fun hc => (by decide :
                  (Reg.x12 : Reg) ∉ sgvScratch) (by rw [← hc]; exact hr)),
              if_neg (fun hc => (by decide :
                  (Reg.x13 : Reg) ∉ sgvScratch) (by rw [← hc]; exact hr))])]
      exact hp'
  · -- unpack: `a0` carries the flag, the rest returns to ownership
    refine sepConj_mono_right (fun h' hq' => ?_) h hq
    have hq'' : (asrtOf RwRegion.empty _ ** bytesRegion Region.empty.base
        Region.empty.bytes) h' := hq'
    rw [show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil, sepConj_emp_right'] at hq''
    obtain ⟨rf, ws, A, hws, -, ⟨h10, rfl⟩, hh⟩ := hq''
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
      regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
      sgv_split_post,
      show rf .x10 = sgvOut len esz maxc from by
        rw [show rf .x10 = rf.get .x10 from by
          rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
        exact h10] at hh
    exact sepConj_mono_right (regAtomsOf_to_regOwns _ _) h' hh

#print axioms sgValidateFixedListFlat_spec

end EvmAsm.Codegen.SgValidateFixedListSAsm
