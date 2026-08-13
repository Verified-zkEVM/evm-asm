/-
  EvmAsm.Codegen.Proofs.CallFrameCalldataFlatTriple

  `call_frame_set_calldata`, lifted to a whole-routine flat triple at its guest
  entry (#12244 ask 3). The FOURTH geometry in this harvest, and the reason the
  lift queue is not one template repeated:

  | | `region` (read-only) | `rw` (writable) | ambient |
  |---|---|---|---|
  | `u256_add_be`            | empty     | non-empty | non-empty (pinned) |
  | `bnf_eq32` + family      | non-empty | empty     | non-empty (pinned) |
  | `u256_from_u64_be`       | empty     | non-empty | **empty** |
  | `call_frame_set_calldata`| empty     | non-empty | **empty**, 4 ABI args |

  So this one mirrors `u256FromU64BeFlat_spec` (`Codegen/Proofs/U256BeFlatTriples.lean`)
  — the ambient-FREE adapter `Fn.retSpecFlat`, not `Fn.retSpecFlatAmbient` — with
  the argument count raised from two to four.

  ## Why the post pins all four argument registers

  The leaf's `post` already re-states `x10`–`x13` at their entry values, so
  discarding them into `regOwns exposedRegs` (as the two-argument template does)
  would throw away a fact the `Fn.Spec` hands over for free. The 432-byte child
  frame this routine writes into is addressed by `x10`, so a caller sequencing
  several `call_frame_*` writes needs exactly that: the frame pointer still in
  `x10` afterwards. Stating the strongest post the leaf supports is the cheaper
  choice here, not the more expensive one.

  ⚠️ Not to be confused with callee-saved: this is a *proved* property of this
  routine's body (three instructions, none of which writes `x10`–`x13`), not an
  ABI guarantee that other routines share.
-/

import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Codegen.Programs.CallFrameSetCalldataSAsm
import EvmAsm.Codegen.Programs.CallFrameDescend

namespace EvmAsm.Codegen.CallFrameCalldataFlat

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- `exposedRegs` minus the four ABI argument registers `a0`–`a3`. -/
def argScratch4 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x14, .x15, .x16, .x17]

/-- The four-way split of `exposedRegs`, used on BOTH sides of the triple: the
    pre supplies `a0`–`a3`, and the post pins them back. -/
private theorem exposedRegs_split_4 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** (.x12 ↦ᵣ vf .x12) **
          (.x13 ↦ᵣ vf .x13) ** regAtomsOf vf argScratch4) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [argScratch4, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_argScratch4 : (.x10 : Reg) ∉ argScratch4 := by decide
private theorem x11_notin_argScratch4 : (.x11 : Reg) ∉ argScratch4 := by decide
private theorem x12_notin_argScratch4 : (.x12 : Reg) ∉ argScratch4 := by decide
private theorem x13_notin_argScratch4 : (.x13 : Reg) ∉ argScratch4 := by decide

/-- The four-argument register file this routine is entered with. -/
private def rf4 (childEnv parentMem argsOff argsLen : Word) (vf : Reg → Word) :
    RegFile :=
  fun r =>
    if r = .x10 then childEnv else
    if r = .x11 then parentMem else
    if r = .x12 then argsOff else
    if r = .x13 then argsLen else vf r

/-- **`call_frame_set_calldata`, whole-routine flat triple at the guest entry.**

    Writes the calldata pointer `parentMem + argsOff` at offset 416 and the
    calldata length `argsLen` at offset 424 of the 432-byte child call frame
    based at `a0`, leaving the rest of the frame BYTE-FOR-BYTE unchanged (the
    post is a `setBytes … setBytes` of the *original* contents, not a havoc).

    Anchored at `GuestAddrs.call_frame_set_calldata` over
    `CodeReq.ofProg … callFrameSetCalldata_prog` — the pairing recorded in
    `GuestImageEntries.lean` — so this is a statement about the deployed image.

    All four argument registers are pinned in the post; see the module header for
    why that is the cheaper choice, not the more expensive one.

    Domain: the writable-region well-formedness `RwRegion.wf ⟨childEnv, 432⟩`, a
    432-byte original frame, and an aligned return address. No input-domain
    condition, so this is total over well-formed frames. -/
theorem callFrameSetCalldataFlat_spec
    (ret childEnv parentMem argsOff argsLen : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨childEnv, 432⟩) (hlenOrig : orig.length = 432)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((CallFrameSetCalldataSAsm.callFrameSetCalldataFn
          childEnv parentMem argsOff argsLen orig).body.steps + 1)
      (GuestAddrs.call_frame_set_calldata : Word) ret
      (CodeReq.ofProg (GuestAddrs.call_frame_set_calldata : Word)
        callFrameSetCalldata_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ childEnv) **
        ((.x11 : Reg) ↦ᵣ parentMem) ** ((.x12 : Reg) ↦ᵣ argsOff) **
        ((.x13 : Reg) ↦ᵣ argsLen) ** regOwns argScratch4 **
        bytesRegion childEnv orig)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ childEnv) **
        ((.x11 : Reg) ↦ᵣ parentMem) ** ((.x12 : Reg) ↦ᵣ argsOff) **
        ((.x13 : Reg) ↦ᵣ argsLen) ** regOwns argScratch4 **
        bytesRegion childEnv
          (setBytes (setBytes orig 416 (dwordBytes (parentMem + argsOff)))
            424 (dwordBytes argsLen))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns argScratch4 (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ childEnv) **
        ((.x11 : Reg) ↦ᵣ parentMem) ** ((.x12 : Reg) ↦ᵣ argsOff) **
        ((.x13 : Reg) ↦ᵣ argsLen) ** bytesRegion childEnv orig)
      (fun vf => ?_))
  have hg10 : (rf4 childEnv parentMem argsOff argsLen vf).get .x10 = childEnv := by
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have hg11 : (rf4 childEnv parentMem argsOff argsLen vf).get .x11 = parentMem := by
    rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
    show (if (Reg.x11 : Reg) = .x10 then childEnv else _) = parentMem
    rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
    exact if_pos rfl
  have hg12 : (rf4 childEnv parentMem argsOff argsLen vf).get .x12 = argsOff := by
    rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
    show (if (Reg.x12 : Reg) = .x10 then childEnv else _) = argsOff
    rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]
    exact if_pos rfl
  have hg13 : (rf4 childEnv parentMem argsOff argsLen vf).get .x13 = argsLen := by
    rw [RegFile.get, if_neg (by decide : (Reg.x13 : Reg) ≠ .x0)]
    show (if (Reg.x13 : Reg) = .x10 then childEnv else _) = argsLen
    rw [if_neg (by decide : ¬ ((Reg.x13 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x13 : Reg) = .x11)),
        if_neg (by decide : ¬ ((Reg.x13 : Reg) = .x12))]
    exact if_pos rfl
  have hpre : (CallFrameSetCalldataSAsm.callFrameSetCalldataFn
      childEnv parentMem argsOff argsLen orig).pre
      (rf4 childEnv parentMem argsOff argsLen vf) orig empAssertion :=
    ⟨hg10, hg11, hg12, hg13, rfl, rfl⟩
  have had := Fn.retSpecFlat
    (CallFrameSetCalldataSAsm.callFrameSetCalldataFn
      childEnv parentMem argsOff argsLen orig)
    (GuestAddrs.call_frame_set_calldata : Word)
    (CallFrameSetCalldataSAsm.callFrameSetCalldataFn_spec
      childEnv parentMem argsOff argsLen orig
      (GuestAddrs.call_frame_set_calldata : Word) hwf)
    (by show 4 * (3 + 1) ≤ 2 ^ 64; decide) ret halign
    (rf4 childEnv parentMem argsOff argsLen vf)
    orig (by exact hlenOrig) hpre
    (Q := (((.x10 : Reg) ↦ᵣ childEnv) ** ((.x11 : Reg) ↦ᵣ parentMem) **
        ((.x12 : Reg) ↦ᵣ argsOff) ** ((.x13 : Reg) ↦ᵣ argsLen) **
        regOwns argScratch4) **
      bytesRegion childEnv
        (setBytes (setBytes orig 416 (dwordBytes (parentMem + argsOff)))
          424 (dwordBytes argsLen)))
    -- `hpostEmp`: the leaf's post pins the ambient to `empAssertion`.
    (fun _ _ _ hpost => hpost.2.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hc10, hc11, hc12, hc13, hws, -⟩ := hpost
      subst hws
      -- Turn the four `RegFile.get` facts into plain applications.
      have g10 : rf' .x10 = childEnv := by
        rwa [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)] at hc10
      have g11 : rf' .x11 = parentMem := by
        rwa [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)] at hc11
      have g12 : rf' .x12 = argsOff := by
        rwa [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)] at hc12
      have g13 : rf' .x13 = argsLen := by
        rwa [RegFile.get, if_neg (by decide : (Reg.x13 : Reg) ≠ .x0)] at hc13
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_4, g10, g11, g12, g13] at hh
      refine sepConj_mono_left ?_ hp hh
      exact fun h hx =>
        sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (regAtomsOf_to_regOwns (fun r => rf' r) argScratch4)))) h hx)
  rw [show (CallFrameSetCalldataSAsm.callFrameSetCalldataFn
        childEnv parentMem argsOff argsLen orig).programRet
      (GuestAddrs.call_frame_set_calldata : Word)
      = callFrameSetCalldata_prog from rfl] at had
  rw [show (CallFrameSetCalldataSAsm.callFrameSetCalldataFn
          childEnv parentMem argsOff argsLen orig).region = Region.empty from rfl,
      show (CallFrameSetCalldataSAsm.callFrameSetCalldataFn
          childEnv parentMem argsOff argsLen orig).rw.base = childEnv from rfl,
      show Region.empty.base = (0 : Word) from rfl,
      show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_4,
    show (rf4 childEnv parentMem argsOff argsLen vf) .x10 = childEnv from if_pos rfl,
    show (rf4 childEnv parentMem argsOff argsLen vf) .x11 = parentMem from by
      show (if (Reg.x11 : Reg) = .x10 then childEnv else _) = parentMem
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    show (rf4 childEnv parentMem argsOff argsLen vf) .x12 = argsOff from by
      show (if (Reg.x12 : Reg) = .x10 then childEnv else _) = argsOff
      rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
          if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]
      exact if_pos rfl,
    show (rf4 childEnv parentMem argsOff argsLen vf) .x13 = argsLen from by
      show (if (Reg.x13 : Reg) = .x10 then childEnv else _) = argsLen
      rw [if_neg (by decide : ¬ ((Reg.x13 : Reg) = .x10)),
          if_neg (by decide : ¬ ((Reg.x13 : Reg) = .x11)),
          if_neg (by decide : ¬ ((Reg.x13 : Reg) = .x12))]
      exact if_pos rfl,
    regAtomsOf_congr (rf4 childEnv parentMem argsOff argsLen vf) vf argScratch4
      (fun r hr => by
        show (if r = .x10 then childEnv else if r = .x11 then parentMem else
              if r = .x12 then argsOff else if r = .x13 then argsLen else vf r)
            = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_argScratch4 (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_argScratch4 (hc ▸ hr)),
            if_neg (fun (hc : r = .x12) => x12_notin_argScratch4 (hc ▸ hr)),
            if_neg (fun (hc : r = .x13) => x13_notin_argScratch4 (hc ▸ hr))])]
    at had
  -- `region = Region.empty` leaves a trailing `empAssertion` on BOTH sides; clear
  -- it before permuting (same step as `u256FromU64BeFlat_spec`, the other
  -- empty-region member of this harvest).
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by
      rw [sepConj_emp_right'] at hq
      xperm_hyp hq) had

end EvmAsm.Codegen.CallFrameCalldataFlat
