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
        regOwns eqResScratch ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns eqArgScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr1) **
        ((.x11 : Reg) ↦ᵣ ptr2) ** bytesRegion ptr1 bs1 ** bytesRegion ptr2 bs2)
      (fun vf => ?_))
  have hpre : (bnfEq32Fn ptr1 ptr2 bs1 bs2).pre
      (fun r => if r = .x10 then ptr1 else if r = .x11 then ptr2 else vf r)
      [] (bytesRegion ptr2 bs2) := by
    refine ⟨?_, ?_, hlen1, hlen2, hov1, hov2, hdisj, rfl⟩
    · show RegFile.get _ .x10 = ptr1
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = ptr2
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (bnfEq32Fn ptr1 ptr2 bs1 bs2)
    (GuestAddrs.bnf_eq32 : Word)
    (bnfEq32Fn_spec ptr1 ptr2 bs1 bs2 hwf1 hwf2 (GuestAddrs.bnf_eq32 : Word))
    (by show 4 * (14 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then ptr1 else if r = .x11 then ptr2 else vf r)
    [] (bytesRegion ptr2 bs2)
    (bytesRegion_pcFree _ _) rfl hpre
    (Q := (((.x10 : Reg) ↦ᵣ
          (if firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word))) **
        regOwns eqResScratch) ** bytesRegion ptr2 bs2)
    -- `hpostAmb`: the post's last conjunct pins the ambient.
    (fun _ _ _ hpost => hpost.2.2.2.2.2)
    (fun rf' ws' hlenWs hpost hp hh => by
      obtain ⟨hc10, -, -, -, -, -⟩ := hpost
      have hws : ws' = [] := List.eq_nil_of_length_eq_zero hlenWs
      subst hws
      have g10 : rf' .x10
          = (if firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word)) := by
        rw [← hc10, RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      rw [show (bnfEq32Fn ptr1 ptr2 bs1 bs2).rw.base = (0 : Word) from rfl,
        bytesRegion_nil, sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_a0, g10] at hh
      refine sepConj_mono_left ?_ hp hh
      exact fun h hx =>
        sepConj_mono_right (regAtomsOf_to_regOwns (fun r => rf' r) eqResScratch) h hx)
  rw [show (bnfEq32Fn ptr1 ptr2 bs1 bs2).programRet (GuestAddrs.bnf_eq32 : Word)
      = bnfEq32_prog from rfl] at had
  rw [show (bnfEq32Fn ptr1 ptr2 bs1 bs2).region = ⟨ptr1, bs1⟩ from rfl,
      show (bnfEq32Fn ptr1 ptr2 bs1 bs2).rw.base = (0 : Word) from rfl,
      bytesRegion_nil] at had
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

end EvmAsm.Codegen.AmbientLifted
