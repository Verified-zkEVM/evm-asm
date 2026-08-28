/-
  EvmAsm.Codegen.Programs.U256AddBeAInPlaceSAsm

  The guest-address lift of `u256_add_be`'s **first-operand-aliased** call
  shape: `a0 = a2`, i.e. `*a0 := *a0 + *a1`.

  WHY THIS FILE EXISTS.  `U256AddBeSAsm.u256AddBeInPlace_spec` has proved the
  `Fn`-level contract for exactly this aliasing since it was written, and
  `U256AddBeSAsm.u256AddBeInPlaceBody_flatten` proves by `rfl` that the
  in-place body flattens to the SAME `u256AddBe_prog_of L` as the
  non-aliased one — so it is a statement about the same deployed bytes at
  `GuestAddrs.u256_add_be`, not about a different routine.  What was missing
  is the lift to a guest-address `cpsTripleWithin`, which is what a caller can
  actually compose.  Until now that spec had **zero consumers tree-wide**; this
  retires that orphan.

  WHY A CALLER CANNOT USE `u256AddBeFlat_spec` HERE.  That contract's domain
  carries `hdisjA : aPtr + 32 ≤ outPtr ∨ outPtr + 32 ≤ aPtr`.  With
  `aPtr = outPtr` both disjuncts are false, and its precondition holds
  `bytesRegion outPtr orig ** bytesRegion aPtr aBytes` as SEPARATE conjuncts —
  two disjoint 32-byte windows at one address.  The aliased call site is
  outside its domain, not merely unproven for it.

  WHY THE ALIAS IS SAFE.  The emitted loop walks byte 31 down to byte 0 and
  reads the aliased byte before overwriting it, so the first operand is fully
  consumed as it is replaced.  That is the same argument
  `U256AddBeBInPlaceSAsm` makes for the OTHER aliasing (`a1 = a2`), and this
  file is a direct mirror of that one — the two lifts are meant to be read
  side by side.

  Three distinct contracts now exist over the one routine, and they are not
  interchangeable:
    * `U256BeFlat.u256AddBeFlat_spec`        — `a0`, `a1`, `a2` all distinct
    * `U256AddBeBInPlaceSAsm.…BInPlaceFlat_spec` — `a1 = a2`
    * `u256AddBeAInPlaceFlat_spec` (here)    — `a0 = a2`
-/

import EvmAsm.Codegen.GuestLayout
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.U256AddBeSAsm
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256AddBeAInPlaceSAsm

open U256AddBeSAsm

/-- Code surface: the deployed `u256_add_be` text and nothing else — the
    routine is a leaf, so there is no callee union.  Spelled with
    `u256AddBe_prog_of .zero`, exactly as `U256AddBeBInPlaceSAsm` spells it:
    `u256AddBe_prog_of` IGNORES its layout argument (`def … (_L : GuestLayout)`),
    and `U256.u256AddBe_prog := u256AddBe_prog_of guestLayout`, so this is the
    same Program `GuestImageEntries` pairs with `GuestAddrs.u256_add_be` and the
    same `CodeReq` `u256AddBeFlat_spec` uses.  `U256.lean` is deliberately not
    imported here, to keep this lift at the same layer as the mirror. -/
def u256AddBeAInPlaceCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.u256_add_be : Word) (u256AddBe_prog_of .zero)

/-- The caller-saved registers the routine may clobber, held as owned.  Same
    set as `addScratch` / `u256AddBeBInPlaceScratch`: one routine, one clobber
    set, whatever the aliasing. -/
def u256AddBeAInPlaceScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_u256AddA (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
        (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf u256AddBeAInPlaceScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [u256AddBeAInPlaceScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem u256AddA_args_notin_scratch :
    ∀ r ∈ u256AddBeAInPlaceScratch,
      r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) := by
  decide

/-- **`u256_add_be` with the output aliased onto the FIRST operand.**

    Whole routine, `GuestAddrs.u256_add_be` through its `ret`, over the
    deployed text.  `a0` and `a2` are the same pointer; the 32-byte window
    there holds `aBytes` on entry and `u256AddBeBytes aBytes bBytes aBytes` on
    exit, with the carry-out in `a0`.  The second operand's region is pinned
    INTACT.

    Domain: ABI hypotheses only — 32-byte lengths, region well-formedness, no
    address-space wraparound, and the second operand disjoint from the
    aliased window.  That last one is a real restriction and not a formality:
    `a1` overlapping `a0` is a THIRD aliasing this contract does not cover. -/
theorem u256AddBeAInPlaceFlat_spec (ret aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨aPtr, 32⟩)
    (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (hlenA : aBytes.length = 32)
    (hlenB : bBytes.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64)
    (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hdisj : bPtr.toNat + 32 ≤ aPtr.toNat ∨
      aPtr.toNat + 32 ≤ bPtr.toNat)
    (hsz : 4 * ((u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).body.size + 1)
      ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).body.steps + 1)
      (GuestAddrs.u256_add_be : Word) ret u256AddBeAInPlaceCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ aPtr) **
        (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ aPtr) **
        regOwns u256AddBeAInPlaceScratch ** bytesRegion aPtr aBytes **
        bytesRegion bPtr bBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        (.x10 ↦ᵣ u256AddBeCarry aBytes bBytes aBytes) **
        (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ aPtr) **
        regOwns u256AddBeAInPlaceScratch **
        bytesRegion aPtr (u256AddBeBytes aBytes bBytes aBytes) **
        bytesRegion bPtr bBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns u256AddBeAInPlaceScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ aPtr) **
        (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ aPtr) ** bytesRegion aPtr aBytes **
        bytesRegion bPtr bBytes)
      (fun vf => ?_))
  have hpre : (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).pre
      (fun r => if r = .x10 then aPtr else
        if r = .x11 then bPtr else if r = .x12 then aPtr else vf r)
      aBytes (bytesRegion bPtr bBytes) := by
    refine ⟨?_, ?_, ?_, rfl, hlenA, hlenB, hovA, hovB, hdisj, rfl⟩
    · show RegFile.get _ .x10 = aPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = bPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = aPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes)
    (GuestAddrs.u256_add_be : Word)
    (u256AddBeInPlace_spec aPtr bPtr aBytes bBytes hrw hroB
      (GuestAddrs.u256_add_be : Word))
    hsz ret halign
    (fun r => if r = .x10 then aPtr else
      if r = .x11 then bPtr else if r = .x12 then aPtr else vf r)
    aBytes (bytesRegion bPtr bBytes)
    (bytesRegion_pcFree bPtr bBytes)
    (by exact hlenA) hpre
    (Q := (((.x10 ↦ᵣ u256AddBeCarry aBytes bBytes aBytes) **
          (.x11 ↦ᵣ bPtr) ** (.x12 ↦ᵣ aPtr) **
          regOwns u256AddBeAInPlaceScratch) **
        bytesRegion aPtr (u256AddBeBytes aBytes bBytes aBytes)) **
      bytesRegion bPtr bBytes)
    (fun _ _ _ hpost => hpost.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hx10', hx11', hx12', hws', _hA⟩ := hpost
      subst ws'
      have g10 : rf' .x10 = u256AddBeCarry aBytes bBytes aBytes := by
        rw [← hx10', RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have g11 : rf' .x11 = bPtr := by
        rw [← hx11', RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      have g12 : rf' .x12 = aPtr := by
        rw [← hx12', RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_u256AddA, g10, g11, g12] at hh
      rw [show (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).rw.base = aPtr
        from rfl] at hh
      have hh1 :
          (((((((.x10 : Reg) ↦ᵣ u256AddBeCarry aBytes bBytes aBytes) **
            (.x11 ↦ᵣ bPtr)) ** (.x12 ↦ᵣ aPtr)) **
            bytesRegion aPtr (u256AddBeBytes aBytes bBytes aBytes)) **
            bytesRegion bPtr bBytes) **
            regAtomsOf (fun r => rf' r) u256AddBeAInPlaceScratch) hp := by
        xperm_hyp hh
      have hh2 := sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) u256AddBeAInPlaceScratch) hp hh1
      xperm_hyp hh2)
  rw [show (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).programRet
      (GuestAddrs.u256_add_be : Word) = u256AddBe_prog_of .zero from rfl] at had
  rw [show (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).region = Region.empty from rfl,
    show (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).rw.base = aPtr from rfl,
    show Region.empty.base = (0 : Word) from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_u256AddA,
    show (if (Reg.x10 : Reg) = .x10 then aPtr else _) = aPtr
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then aPtr else
      if (Reg.x11 : Reg) = .x11 then bPtr else _) = bPtr from by
      rw [if_neg (by decide), if_pos rfl],
    show (if (Reg.x12 : Reg) = .x10 then aPtr else
      if (Reg.x12 : Reg) = .x11 then bPtr else
      if (Reg.x12 : Reg) = .x12 then aPtr else _) = aPtr from by
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl],
    regAtomsOf_congr
      (fun r => if r = .x10 then aPtr else
        if r = .x11 then bPtr else if r = .x12 then aPtr else vf r)
      vf u256AddBeAInPlaceScratch
      (fun r hr => by
        obtain ⟨h10, h11, h12⟩ := u256AddA_args_notin_scratch r hr
        show (if r = .x10 then aPtr else
          if r = .x11 then bPtr else if r = .x12 then aPtr else vf r) = vf r
        rw [if_neg h10, if_neg h11, if_neg h12])] at had
  simp only [sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end U256AddBeAInPlaceSAsm

end EvmAsm.Codegen
