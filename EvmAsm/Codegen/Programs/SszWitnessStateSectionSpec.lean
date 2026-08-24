/-
  EvmAsm.Codegen.Programs.SszWitnessStateSectionSpec

  Whole-routine contract for `extract_witness_state_section` (#12318 callee-
  composition lane): the 27-instruction ABI frame that calls `sws_u32le` three
  times and stores the derived `(state_ptr, state_len)` pair.

  ## ⛔ Why the rowed `sws_u32le` contract is not enough on its own

  `SszWitnessStateSAsm.swsU32leFlat_spec` is `.proven` and total, but its
  register frame surrenders **`x29`**: `swsU32leScratch` lists
  `x5 x6 x7 x28 x29 x30 x31 x11..x17`, and the flat triple takes `regOwns` of
  that whole set in the PRE and returns only `regOwns` in the POST. `x29` is
  therefore an arbitrary value on exit as far as that contract is concerned.

  `extract_witness_state_section` holds `state_off` in `x29` at index 13 and
  reads it back at indices 16 and 17 — **across the third call**. Composing the
  rowed contract as-is would make both stored results existential in an unknown
  word, i.e. the routine's entire output would be unspecified.

  This is the named-predicate-hides-a-requirement trap in its register form:
  "every callee is rowed" was true, and the row was even total, yet the row's
  *frame* — not its gate — is what blocks the composition.

  The routine does not in fact touch `x29`: `sgLoadU32leBody` writes `x5`, `x6`
  and `x10` and nothing else. So the fix is a leaf strengthening, not a domain
  restriction, and the composed row stays `.proven`. `swsU32lePresFn` below is a
  SEPARATE `Fn` over the SAME body, with `x29` pinned through pre and post;
  `SszWitnessStateSAsm`'s definitions and its registry row are untouched.
-/

import EvmAsm.Codegen.Programs.SszWitnessStateSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SszWitnessStateSectionSpec

open SgLoadU32leSAsm

/-! ## 1. The `x29`-preserving `sws_u32le` leaf -/

/-- `sws_u32le` again, over the SAME body as `SszWitnessStateSAsm.swsU32leFn`,
    with `x29` pinned through the contract. The extra conjunct is a
    *strengthening*: it constrains the final register file further and adds no
    input-domain restriction, so nothing this `Fn` proves is narrower than what
    the rowed contract proves. -/
def swsU32lePresFn (p : Word) (bs : List (BitVec 8)) (v29 : Word) : Fn where
  name := "swsU32lePres"
  region := ⟨p, bs⟩
  pre := fun rf _ A =>
    rf.get .x10 = p ∧ 4 ≤ bs.length ∧ A = empAssertion ∧ rf.get .x29 = v29
  post := fun rf _ A =>
    rf.get .x10 = leU32 bs 0 ∧ A = empAssertion ∧ rf.get .x29 = v29
  body := sgLoadU32leBody

/-- Byte tie: the strengthened `Fn` emits exactly the linked `sws_u32le`
    program. Same `rfl` as `SszWitnessStateSAsm.swsU32le_byte_tie` — the body is
    literally the same `Stmt`, so this is the guest routine and not a variant
    of it. -/
theorem swsU32lePres_byte_tie :
    (swsU32lePresFn 0 [] 0).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = swsU32le_prog := rfl

#guard ((swsU32lePresFn 0 [] 0).body.flatten 0).length = 11

private theorem swsU32lePres_engine (reg : Region) (rwb : Word) (rf : RegFile)
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

/-- The body never writes `x29`: `sgLoadU32leInstrs` touches `x5`, `x6` and
    `x10` only. -/
private theorem swsU32lePres_x29 (reg : Region) (rwb : Word) (rf : RegFile) :
    (execBlock reg rwb rf [] SgLoadU32leSAsm.sgLoadU32leInstrs).1.get .x29 =
      rf.get .x29 := by
  simp only [SgLoadU32leSAsm.sgLoadU32leInstrs, execBlock_cons, execBlock_nil,
    execInstrRF_nil, aluSem, loadSem, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem swsU32lePresFn_spec (p : Word) (bs : List (BitVec 8)) (v29 : Word)
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (swsU32lePresFn p bs v29).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case swsU32lePres.read.mem =>
    rintro rf ws A hws ⟨hx10, hlen, hA, hx29⟩
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
      not_false_eq_true, swsU32lePresFn, sgLoadU32leBody, sgLoadU32leInstrs, inRw,
      List.length_nil, Nat.le_zero, e0, e1, e2, e3]
    refine ⟨⟨Nat.one_dvd _, by omega⟩, ⟨Nat.one_dvd _, by omega⟩, trivial, trivial,
      ⟨Nat.one_dvd _, by omega⟩, trivial, trivial, ⟨Nat.one_dvd _, by omega⟩,
      trivial, trivial, trivial, trivial⟩
  case swsU32lePres.post =>
    intro rf' ws' A' h
    obtain ⟨rf₀, ws₀, hws₀, ⟨hx10, _, hA, hx29⟩, rfl, rfl⟩ := h
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    refine ⟨?_, hA, ?_⟩
    · show RegFile.get _ .x10 = leU32 bs 0
      exact swsU32lePres_engine (swsU32lePresFn p bs v29).region
        (swsU32lePresFn p bs v29).rw.base rf₀ hx10
    · show RegFile.get _ .x29 = v29
      rw [swsU32lePres_x29 (swsU32lePresFn p bs v29).region
        (swsU32lePresFn p bs v29).rw.base rf₀]
      exact hx29

/-! ### The flat linked-entry contract, with `x29` carried through

    Same `CodeReq` as the rowed contract — `SszWitnessStateSAsm.swsU32leCr`,
    the `guestImageEntries` pairing — so this is the same image claim, only
    with a register the routine demonstrably never writes kept in the frame
    instead of surrendered to `regOwns`. -/

def swsU32lePresScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_pres (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x29 ↦ᵣ vf .x29) **
        regAtomsOf vf swsU32lePresScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [swsU32lePresScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- **`sws_u32le`, whole-routine flat triple at the guest entry, preserving
    `x29`.** -/
theorem swsU32lePresFlat_spec (ret p v29 : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (hlen : 4 ≤ bs.length)
    (hsz : 4 * ((swsU32lePresFn p bs v29).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((swsU32lePresFn p bs v29).body.steps + 1)
      (GuestAddrs.sws_u32le : Word) ret SszWitnessStateSAsm.swsU32leCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** (.x29 ↦ᵣ v29) **
        regOwns swsU32lePresScratch ** bytesRegion p bs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ leU32 bs 0) ** (.x29 ↦ᵣ v29) **
        regOwns swsU32lePresScratch ** bytesRegion p bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns swsU32lePresScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ p) ** (.x29 ↦ᵣ v29) **
        bytesRegion p bs)
      (fun vf => ?_))
  have hpre : (swsU32lePresFn p bs v29).pre
      (fun r => if r = .x10 then p else if r = .x29 then v29 else vf r) []
      empAssertion := by
    refine ⟨?_, hlen, rfl, ?_⟩
    · show RegFile.get _ .x10 = p
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x29 = v29
      rw [RegFile.get, if_neg (by decide : (Reg.x29 : Reg) ≠ .x0)]
      rw [if_neg (by decide : ¬ ((Reg.x29 : Reg) = .x10))]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (swsU32lePresFn p bs v29) (GuestAddrs.sws_u32le : Word)
    (swsU32lePresFn_spec p bs v29 hwf (GuestAddrs.sws_u32le : Word)) hsz ret halign
    (fun r => if r = .x10 then p else if r = .x29 then v29 else vf r) []
    empAssertion pcFree_emp rfl hpre
    (Q := (.x10 ↦ᵣ leU32 bs 0) ** (.x29 ↦ᵣ v29) **
      regOwns swsU32lePresScratch)
    (fun _ _ _ hpost => hpost.2.1)
    (fun rf' ws' hlen' hpost hp hh => by
      obtain ⟨hx10, _hA, hx29⟩ := hpost
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hlen'
      simp only [bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_pres,
        show rf' .x10 = leU32 bs 0 from by
          rw [← hx10, RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)],
        show rf' .x29 = v29 from by
          rw [← hx29, RegFile.get, if_neg (by decide : (Reg.x29 : Reg) ≠ .x0)]] at hh
      exact sepConj_mono_right
        (sepConj_mono_right
          (regAtomsOf_to_regOwns (fun r => rf' r) swsU32lePresScratch)) hp hh)
  rw [show (swsU32lePresFn p bs v29).programRet
      (GuestAddrs.sws_u32le : Word) = swsU32le_prog from rfl] at had
  rw [show (swsU32lePresFn p bs v29).rw.base = (0 : Word) from rfl,
    show (swsU32lePresFn p bs v29).region = Region.mk p bs from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_pres,
    show (if (Reg.x10 : Reg) = .x10 then p
        else if (Reg.x10 : Reg) = .x29 then v29 else vf .x10) = p from if_pos rfl,
    show (if (Reg.x29 : Reg) = .x10 then p
        else if (Reg.x29 : Reg) = .x29 then v29 else vf .x29) = v29 from by
      rw [if_neg (by decide : ¬ ((Reg.x29 : Reg) = .x10))]; exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then p else if r = .x29 then v29 else vf r) vf
      swsU32lePresScratch
      (fun r hr => by
        have hne10 : r ≠ (.x10 : Reg) := by
          intro heq
          subst heq
          have hnot : (.x10 : Reg) ∉ swsU32lePresScratch := by decide
          exact hnot hr
        have hne29 : r ≠ (.x29 : Reg) := by
          intro heq
          subst heq
          have hnot : (.x29 : Reg) ∉ swsU32lePresScratch := by decide
          exact hnot hr
        simp [hne10, hne29])] at had
  simp only [bytesRegion_nil, sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had


end SszWitnessStateSectionSpec

end EvmAsm.Codegen
