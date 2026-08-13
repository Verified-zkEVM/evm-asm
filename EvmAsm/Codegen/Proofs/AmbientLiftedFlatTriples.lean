/-
  EvmAsm.Codegen.Proofs.AmbientLiftedFlatTriples

  Harvest of the `--shape` model-only bucket via the ambient flat lift
  (#12244 ask 3). Companion to `Codegen/Proofs/U256BeFlatTriples.lean`, which
  did the first three by hand and is the template every entry here mirrors.

  ## The queue this module works from

  `scripts/ambient-triage.py` partitions the model-only bucket by the property
  that actually decides the cost — does the leaf `Fn`'s `post` PIN its ambient
  assertion? Every adapter in `Rv64/SAsm/FnFlat.lean` requires it
  (`Fn.retSpecFlat`'s `hpostEmp`, `Fn.retSpecFlatAmbient`'s `hpostAmb`), because
  pinning is the only way the fact survives out of the existentially-quantified
  `asrtOf` in `Fn.retSpec`'s conclusion. A post that ignores its ambient looks
  more general and is strictly LESS usable: unliftable, hence unrowable.

  At the time of writing the triage reports, over 53 model-only symbols:

      MECHANICAL   (post pins the ambient) : 12   <- mirror the template
      CONTRACT-1ST (post ignores it)       : 39   <- leaf contract change first
      READ         (post did not parse)    :  2
      of which NOT ANCHORED                :  7   <- liftable but NEVER rowable

  That last row is the reason "lift in in-degree order", as ask 3 originally
  proposed, is the wrong queue: seven of these symbols (the gas helpers
  `log_data_gas`, `keccak256_word_gas`, `copy_word_gas`, `init_code_cost` among
  them) have no `GuestAddrs` address and no `GuestImageEntries` pair at all, so
  no triple about them is a claim about the deployed image and no honest row can
  cite them. In-degree tells you the value; the triage tells you the cost and
  whether a row is even possible.
-/

import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Codegen.Programs.Secp256k1FieldEq32SAsm
import EvmAsm.Codegen.Programs.P256Eq32SAsm
import EvmAsm.Codegen.Programs.Bls12G1Eq48SAsm

namespace EvmAsm.Codegen.AmbientLifted

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- Exposed registers excluding `bnf_eq32`'s two ABI argument registers. -/
def eqArgScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Exposed registers excluding only the result register `a0`. -/
def eqResScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_a0_a1 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf eqArgScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [eqArgScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem exposedRegs_split_a0 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf eqResScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [eqResScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_eqArgScratch : (.x10 : Reg) ∉ eqArgScratch := by decide
private theorem x11_notin_eqArgScratch : (.x11 : Reg) ∉ eqArgScratch := by decide

/-! ## The `(a0, a1) → a0` compare family, lifted once

  Four linked routines — `bnf_eq32`, `secf_eq32`, `p256_eq32`, `blsg_eq48` — have
  **byte-identical `Fn` geometry**: `region = ⟨ptr1, bs1⟩`, `rw = RwRegion.empty`,
  a `pre` taking the two buffer pointers in `a0`/`a1` with the second buffer as
  the ambient, and a `post` that fixes `a0` and pins that ambient back. They
  differ only in name, buffer width (32 vs 48) and which `firstDiff` they call.

  So the lift is proved **once**, generically, and each routine is a
  ~10-line instantiation. `bnfEq32Flat_spec` — the hand proof from #12292 that
  this generalises — is re-derived from it below, which is the check that the
  abstraction is faithful rather than merely plausible: if the generic statement
  had drifted from what the hand proof established, that instantiation would not
  elaborate.

  ⚠️ The width does **not** appear in the generic statement. It is carried
  entirely inside `fn.pre`/`fn.post` and surfaces only through `res`, so a
  48-byte routine instantiates this exactly as a 32-byte one does. Do not add a
  width parameter "for clarity" — it would have to be threaded through
  hypotheses that never mention it. -/

/-- **The compare-family ambient flat lift.** Turns an `Fn.Spec` for a routine of
    the `(a0, a1) → a0` compare shape into a whole-routine `cpsTripleWithin` at
    `base`, over `CodeReq.ofProg base prog` alone.

    Both operand regions are pinned INTACT across the call: the first rides
    through as `Fn.region`, the second as the pinned ambient. A routine that
    scribbled on either input could not satisfy this.

    The three `hpost*` hypotheses are where the pinning requirement bites — see
    this module's header. `hpostAmb` is what `Fn.retSpecFlatAmbient` needs to get
    the ambient fact out of the existential in `Fn.retSpec`'s conclusion, and a
    leaf whose `post` ignores its ambient cannot supply it at any price. -/
theorem eqFamilyFlatSpec
    (fn : Fn) (prog : Program) (base ret ptr1 ptr2 : Word)
    (bs1 bs2 : List (BitVec 8)) (res : Word)
    (hspec : fn.Spec base)
    (hregion : fn.region = ⟨ptr1, bs1⟩)
    (hrwbase : fn.rw.base = (0 : Word))
    (hrwlen : fn.rw.len = 0)
    (hsz : 4 * (fn.body.size + 1) ≤ 2 ^ 64)
    (hprog : fn.programRet base = prog)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hpre : ∀ rf : RegFile, rf.get .x10 = ptr1 → rf.get .x11 = ptr2 →
      fn.pre rf [] (bytesRegion ptr2 bs2))
    (hpostAmb : ∀ rf' ws' A', fn.post rf' ws' A' → A' = bytesRegion ptr2 bs2)
    (hpostRes : ∀ rf' ws' A', fn.post rf' ws' A' → rf'.get .x10 = res) :
    cpsTripleWithin (fn.body.steps + 1) base ret
      (CodeReq.ofProg base prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        regOwns eqArgScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ res) **
        regOwns eqResScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns eqArgScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr1) **
        ((.x11 : Reg) ↦ᵣ ptr2) ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (fun vf => ?_))
  have hg10 : RegFile.get
      (fun r => if r = .x10 then ptr1 else if r = .x11 then ptr2 else vf r)
      .x10 = ptr1 := by
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have hg11 : RegFile.get
      (fun r => if r = .x10 then ptr1 else if r = .x11 then ptr2 else vf r)
      .x11 = ptr2 := by
    rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
    rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
    exact if_pos rfl
  have had := Fn.retSpecFlatAmbient fn base hspec hsz ret halign
    (fun r => if r = .x10 then ptr1 else if r = .x11 then ptr2 else vf r)
    [] (bytesRegion ptr2 bs2)
    (bytesRegion_pcFree _ _) (by simp [hrwlen]) (hpre _ hg10 hg11)
    (Q := (((.x10 : Reg) ↦ᵣ res) ** regOwns eqResScratch) ** bytesRegion ptr2 bs2)
    hpostAmb
    (fun rf' ws' hlenWs hpost hp hh => by
      have hws : ws' = [] :=
        List.eq_nil_of_length_eq_zero (by rw [hlenWs, hrwlen])
      subst hws
      have g10 : rf' .x10 = res := by
        have h := hpostRes rf' [] _ hpost
        rwa [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)] at h
      rw [hrwbase, bytesRegion_nil, sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_a0, g10] at hh
      refine sepConj_mono_left ?_ hp hh
      exact fun h hx =>
        sepConj_mono_right (regAtomsOf_to_regOwns (fun r => rf' r) eqResScratch) h hx)
  rw [hprog, hregion, hrwbase, bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_a0_a1,
    show (if (Reg.x10 : Reg) = .x10 then ptr1 else
        if (Reg.x10 : Reg) = .x11 then ptr2 else vf .x10) = ptr1 from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then ptr1 else
        if (Reg.x11 : Reg) = .x11 then ptr2 else vf .x11) = ptr2 from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then ptr1 else if r = .x11 then ptr2 else vf r)
      vf eqArgScratch
      (fun r hr => by
        show (if r = .x10 then ptr1 else if r = .x11 then ptr2 else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_eqArgScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_eqArgScratch (hc ▸ hr))])]
    at had
  -- `rw = RwRegion.empty` leaves an `empAssertion` where the writable window
  -- would be, on the PRE side only; clear it before permuting.
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

/-- **`bnf_eq32`, whole-routine flat triple at the guest entry.**

    Compares the two 32-byte BN254 field elements at `a0`/`a1` and returns `1`
    in `a0` iff they are byte-equal, else `0`.  Anchored at
    `GuestAddrs.bnf_eq32` over `CodeReq.ofProg … bnfEq32_prog` — the pairing
    recorded in `GuestImageEntries.lean` — so this is a statement about the
    deployed image.

    First harvest from the MECHANICAL queue (#12244 ask 3), and the validation
    that the queue is real: the proof is the `u256AddBeFlat_spec` template with
    the operand shapes swapped, no new insight.  Note the geometry differs from
    that template in two ways that the lift absorbs without comment — the
    read-only region is NON-empty (`region = ⟨ptr1, bs1⟩`, so it rides through
    as the trailing conjunct) while the writable window is EMPTY
    (`rw = RwRegion.empty`), the mirror image of `u256_add_be`.

    BOTH operand regions are pinned INTACT in the post: a routine that scribbled
    on its inputs could not satisfy this.  Domain: ABI hypotheses only (both
    regions well-formed, both lengths 32, no address-space wraparound, the two
    ranges disjoint, aligned `ra`). -/
theorem bnfEq32Flat_spec (ret ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hov1 : ptr1.toNat + 32 < 2 ^ 64) (hov2 : ptr2.toNat + 32 < 2 ^ 64)
    (hdisj : ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bnfEq32Fn ptr1 ptr2 bs1 bs2).body.steps + 1)
      (GuestAddrs.bnf_eq32 : Word) ret
      (CodeReq.ofProg (GuestAddrs.bnf_eq32 : Word) bnfEq32_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        regOwns eqArgScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ (if firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word))) **
        regOwns eqResScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2) :=
  eqFamilyFlatSpec (bnfEq32Fn ptr1 ptr2 bs1 bs2) bnfEq32_prog
    (GuestAddrs.bnf_eq32 : Word) ret ptr1 ptr2 bs1 bs2
    (if firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word))
    (bnfEq32Fn_spec ptr1 ptr2 bs1 bs2 hwf1 hwf2 (GuestAddrs.bnf_eq32 : Word))
    rfl rfl rfl (by show 4 * (14 + 1) ≤ 2 ^ 64; decide) rfl halign
    (fun _ h10 h11 => ⟨h10, h11, hlen1, hlen2, hov1, hov2, hdisj, rfl⟩)
    (fun _ _ _ hpost => hpost.2.2.2.2.2)
    (fun _ _ _ hpost => hpost.1)


/-! ## The rest of the compare family

  Three more instantiations of `eqFamilyFlatSpec`, each anchored at its own
  `GuestAddrs` entry with the `(GuestAddrs.<sym>, <sym>_prog)` pairing recorded in
  `GuestImageEntries.lean`, so each is a statement about the deployed image and
  not about a probe wrapper.

  These are `MECHANICAL` in `ambient-triage.py`'s sense and the whole cost is the
  instantiation — no proof reasoning at all now that the family lemma exists.
  `p256_eq32` is the extreme case: its body is *literally* `secfEq32Body`
  (`P256Eq32SAsm.lean:20`), so its post is stated with
  `Secp256k1FieldEq32SAsm.firstDiff`, not a `p256`-named copy. -/

/-- **`secf_eq32`, whole-routine flat triple at the guest entry.** Compares the
    two 32-byte secp256k1 field elements at `a0`/`a1`, returning `1` in `a0` iff
    byte-equal. -/
theorem secfEq32Flat_spec (ret ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hov1 : ptr1.toNat + 32 < 2 ^ 64) (hov2 : ptr2.toNat + 32 < 2 ^ 64)
    (hdisj : ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((Secp256k1FieldEq32SAsm.secfEq32Fn ptr1 ptr2 bs1 bs2).body.steps + 1)
      (GuestAddrs.secf_eq32 : Word) ret
      (CodeReq.ofProg (GuestAddrs.secf_eq32 : Word) Secp256k1FieldEq32SAsm.secfEq32_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        regOwns eqArgScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ (if Secp256k1FieldEq32SAsm.firstDiff bs1 bs2 32 = 32
          then (1 : Word) else (0 : Word))) **
        regOwns eqResScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2) :=
  eqFamilyFlatSpec (Secp256k1FieldEq32SAsm.secfEq32Fn ptr1 ptr2 bs1 bs2)
    Secp256k1FieldEq32SAsm.secfEq32_prog
    (GuestAddrs.secf_eq32 : Word) ret ptr1 ptr2 bs1 bs2
    (if Secp256k1FieldEq32SAsm.firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word))
    (Secp256k1FieldEq32SAsm.secfEq32Fn_spec ptr1 ptr2 bs1 bs2 hwf1 hwf2
      (GuestAddrs.secf_eq32 : Word))
    rfl rfl rfl (by show 4 * (14 + 1) ≤ 2 ^ 64; decide) rfl halign
    (fun _ h10 h11 => ⟨h10, h11, hlen1, hlen2, hov1, hov2, hdisj, rfl⟩)
    (fun _ _ _ hpost => hpost.2.2.2.2.2)
    (fun _ _ _ hpost => hpost.1)

/-- **`p256_eq32`, whole-routine flat triple at the guest entry.** Same 32-byte
    scan as `secf_eq32` — the body is shared, not merely similar. -/
theorem p256Eq32Flat_spec (ret ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hov1 : ptr1.toNat + 32 < 2 ^ 64) (hov2 : ptr2.toNat + 32 < 2 ^ 64)
    (hdisj : ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((P256Eq32SAsm.p256Eq32Fn ptr1 ptr2 bs1 bs2).body.steps + 1)
      (GuestAddrs.p256_eq32 : Word) ret
      (CodeReq.ofProg (GuestAddrs.p256_eq32 : Word) P256Eq32SAsm.p256Eq32_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        regOwns eqArgScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ (if Secp256k1FieldEq32SAsm.firstDiff bs1 bs2 32 = 32
          then (1 : Word) else (0 : Word))) **
        regOwns eqResScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2) :=
  eqFamilyFlatSpec (P256Eq32SAsm.p256Eq32Fn ptr1 ptr2 bs1 bs2)
    P256Eq32SAsm.p256Eq32_prog
    (GuestAddrs.p256_eq32 : Word) ret ptr1 ptr2 bs1 bs2
    (if Secp256k1FieldEq32SAsm.firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word))
    (P256Eq32SAsm.p256Eq32Fn_spec ptr1 ptr2 bs1 bs2 hwf1 hwf2
      (GuestAddrs.p256_eq32 : Word))
    rfl rfl rfl (by show 4 * (14 + 1) ≤ 2 ^ 64; decide) rfl halign
    (fun _ h10 h11 => ⟨h10, h11, hlen1, hlen2, hov1, hov2, hdisj, rfl⟩)
    (fun _ _ _ hpost => hpost.2.2.2.2.2)
    (fun _ _ _ hpost => hpost.1)

/-- **`blsg_eq48`, whole-routine flat triple at the guest entry.** The 48-byte
    member of the family: BLS12-381 G1 field elements. Note the generic lemma is
    instantiated identically to the 32-byte cases — the width lives entirely in
    `fn.pre`/`fn.post`. -/
theorem blsgEq48Flat_spec (ret ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8))
    (hwf1 : (Region.mk ptr1 bs1).wf) (hwf2 : (Region.mk ptr2 bs2).wf)
    (hlen1 : bs1.length = 48) (hlen2 : bs2.length = 48)
    (hov1 : ptr1.toNat + 48 < 2 ^ 64) (hov2 : ptr2.toNat + 48 < 2 ^ 64)
    (hdisj : ptr1.toNat + 48 ≤ ptr2.toNat ∨ ptr2.toNat + 48 ≤ ptr1.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((Bls12G1Eq48SAsm.blsgEq48Fn ptr1 ptr2 bs1 bs2).body.steps + 1)
      (GuestAddrs.blsg_eq48 : Word) ret
      (CodeReq.ofProg (GuestAddrs.blsg_eq48 : Word) Bls12G1Eq48SAsm.blsgEq48_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr1) ** ((.x11 : Reg) ↦ᵣ ptr2) **
        regOwns eqArgScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ (if Bls12G1Eq48SAsm.firstDiff bs1 bs2 48 = 48
          then (1 : Word) else (0 : Word))) **
        regOwns eqResScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2) :=
  eqFamilyFlatSpec (Bls12G1Eq48SAsm.blsgEq48Fn ptr1 ptr2 bs1 bs2)
    Bls12G1Eq48SAsm.blsgEq48_prog
    (GuestAddrs.blsg_eq48 : Word) ret ptr1 ptr2 bs1 bs2
    (if Bls12G1Eq48SAsm.firstDiff bs1 bs2 48 = 48 then (1 : Word) else (0 : Word))
    (Bls12G1Eq48SAsm.blsgEq48Fn_spec ptr1 ptr2 bs1 bs2 hwf1 hwf2
      (GuestAddrs.blsg_eq48 : Word))
    rfl rfl rfl (by show 4 * (14 + 1) ≤ 2 ^ 64; decide) rfl halign
    (fun _ h10 h11 => ⟨h10, h11, hlen1, hlen2, hov1, hov2, hdisj, rfl⟩)
    (fun _ _ _ hpost => hpost.2.2.2.2.2)
    (fun _ _ _ hpost => hpost.1)

/-! ## Non-vacuity

  The four theorems above are implications, so they would all hold trivially if
  their hypothesis bundle were unsatisfiable. This exhibits a witness.

  ⭐ Deliberately stated with **no guest address in it**. #12293 pinned
  anti-vacuity examples with fully numeric posts, and #12291 moved
  `GuestAddrs.stage_system_call` out from under them the same night — correct when
  written, then outrun by a layout regen. Nothing here needs an address: the
  hypotheses constrain only the operand pointers, buffers and return address, so
  this witness is immune to layout by construction rather than by luck. -/
private def vacWitBytes : List (BitVec 8) := List.replicate 48 (0 : BitVec 8)

/-- The compare family's ABI hypothesis bundle is satisfiable at both widths:
    two disjoint, non-wrapping, well-formed buffers and an aligned return
    address. Stated for width 48 and 32 by taking prefixes of one buffer. -/
private theorem eqFamily_hyps_satisfiable :
    ∀ n ∈ [32, 48],
      ((Region.mk (0x1000 : Word) (vacWitBytes.take n)).wf
        ∧ (Region.mk (0x2000 : Word) (vacWitBytes.take n)).wf
        ∧ (vacWitBytes.take n).length = n
        ∧ (0x1000 : Word).toNat + n < 2 ^ 64
        ∧ (0x2000 : Word).toNat + n < 2 ^ 64
        ∧ ((0x1000 : Word).toNat + n ≤ (0x2000 : Word).toNat
            ∨ (0x2000 : Word).toNat + n ≤ (0x1000 : Word).toNat)
        ∧ (((0x4 : Word)) &&& ~~~(1 : Word)) = (0x4 : Word)) := by
  decide

/-- An actual instance of the 48-byte conclusion. **This is what establishes
    non-vacuity**, and it does so on its own: every hypothesis is discharged by an
    independent `decide`, so none of them is being derived from the others and a
    contradictory bundle could not have produced them. `eqFamily_hyps_satisfiable`
    above states the same fact in one place for readers who want the bundle
    without the triple around it.

    `GuestAddrs.blsg_eq48` appears here as a SYMBOL, so a layout regen flows
    through it; no numeric address is pinned. -/
private theorem blsgEq48Flat_instance :
    cpsTripleWithin
      ((Bls12G1Eq48SAsm.blsgEq48Fn (0x1000 : Word) (0x2000 : Word)
        vacWitBytes vacWitBytes).body.steps + 1)
      (GuestAddrs.blsg_eq48 : Word) (0x4 : Word)
      (CodeReq.ofProg (GuestAddrs.blsg_eq48 : Word) Bls12G1Eq48SAsm.blsgEq48_prog)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x1000 : Word)) **
        ((.x11 : Reg) ↦ᵣ (0x2000 : Word)) ** regOwns eqArgScratch **
        bytesRegion (0x1000 : Word) vacWitBytes **
        bytesRegion (0x2000 : Word) vacWitBytes)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) **
        ((.x10 : Reg) ↦ᵣ (if Bls12G1Eq48SAsm.firstDiff vacWitBytes vacWitBytes 48 = 48
          then (1 : Word) else (0 : Word))) **
        regOwns eqResScratch **
        bytesRegion (0x1000 : Word) vacWitBytes **
        bytesRegion (0x2000 : Word) vacWitBytes) :=
  blsgEq48Flat_spec (0x4 : Word) (0x1000 : Word) (0x2000 : Word)
    vacWitBytes vacWitBytes (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end EvmAsm.Codegen.AmbientLifted
