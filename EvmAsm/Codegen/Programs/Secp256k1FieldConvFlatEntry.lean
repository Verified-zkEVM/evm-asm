/-
  EvmAsm.Codegen.Programs.Secp256k1FieldConvFlatEntry

  Whole-routine flat triples for the two secp256k1 BE↔LE field converters,
  anchored at their OWN single-program `CodeReq` — the `GuestImageEntries`
  pairing — rather than a caller's union (#12244).

  ## Why this module exists

  Flat contracts for `secf_be_to_le` / `secf_le_to_be` already existed, twice
  each, inside the two callers that use them:

  | theorem | `CodeReq` | programs it requires loaded |
  |---|---|---|
  | `Secp256k1FieldMulModPSAsm.secfBeToLeFlat_spec` | `mulCr` | 3 |
  | `Secp256k1PointDoubleSAsm.secfBeToLeFlat_spec`  | `pdCr`  | 5 |

  A union `CodeReq` is a caller-specific assumption: the triple holds only when
  every program in the union is loaded. That is STRONGER than the single-program
  claim `GuestImageEntries.lean` makes (`(GuestAddrs.secf_be_to_le,
  secfBeToLe_prog)`), so neither of those theorems is the image claim, and
  rowing one would attach a registry row whose hypothesis the image does not
  discharge. This is the second trap documented in
  `Codegen/Proofs/AmbientFreeFlatTriples.lean`: a pre-existing `<sym>Flat_spec`
  settles neither whether a lift exists NOR whether it is rowable.

  ## The entry triples are the primitive, not a fifth copy

  Both pre-existing proofs already went through this statement internally: each
  built the triple from `Fn.retSpecFlat` — whose `CodeReq` is
  `CodeReq.ofProg base (f.programRet base)`, i.e. the routine's own program —
  and then widened it with `liftCode … (by code_mem)`. The own-`CodeReq` triple
  was the load-bearing step all along; it was simply never named.

  So this module states it once, and the four caller-side theorems become
  one-line `cpsTripleWithin_extend_code` corollaries. That REMOVES the ~360
  lines of duplication rather than adding to it, and the direction is the sound
  one: `⊆`-monotonicity gives caller triples from the entry triple, never the
  reverse. (The follow-up deferred in `AmbientFreeFlatTriples`'s header — that
  collapsing `pdCr` needs its five ranges pairwise disjoint because
  `CodeReq.union` is left-biased — is a DIFFERENT question, about eliminating
  the union itself. It stays open and is not needed here.)

  ## Geometry

  Both converters are the both-regions-non-empty case that
  `AmbientFreeFlatTriples`'s geometry map did not yet cover:

  | | `region` (read-only) | `rw` (writable) | ambient | adapter |
  |---|---|---|---|---|
  | `secf_be_to_le` | non-empty (`srci`, 32 B) | non-empty (`dsti`, 32 B) | empty | `retSpecFlat` |
  | `secf_le_to_be` | non-empty (`srci`, 32 B) | non-empty (`dsti`, 32 B) | empty | `retSpecFlat` |

  Two live windows is what forces the `hdisj` hypothesis: with both a source and
  a destination in the footprint, the separating conjunction needs them apart, so
  unlike the single-window leaves these triples are NOT total over their argument
  types. `hdisj` is a genuine domain restriction, discharged at each call site by
  the arena layout — not a representability guard.

  The posts are existential in the written bytes and pin only the DECODE, which
  is the honest statement: the converters' functional content is
  `wsNat256 ws' 0 = beBytesToNat inb` (BE→LE) and its inverse (LE→BE), not any
  particular byte list.
-/

import EvmAsm.Codegen.Programs.Secp256k1FieldConvSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldLeToBeSAsm
import EvmAsm.Rv64.SAsm.FnFlat
-- `sepConj_exists_left`, to push the frame atoms inside the existential post.
import EvmAsm.Rv64.SAsm.RwSubwindow

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1FieldConvSAsm

/-! ## Register geometry

    Both converters take two pointers (`a0` source, `a1` destination) and
    clobber the rest of `exposedRegs`. The split below is the same one the two
    caller stage files each derived privately; it is stated once here so the
    corollaries can reuse it. -/

/-- The exposed registers the converter contracts clobber beyond `a0`/`a1`. -/
def convScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split2 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf convScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [convScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_convScratch : (.x10 : Reg) ∉ convScratch := by decide
private theorem x11_notin_convScratch : (.x11 : Reg) ∉ convScratch := by decide

/-- **`secf_be_to_le`, whole-routine flat triple at the guest entry.**

    Converts the 32-byte big-endian buffer at `a0` into four little-endian u64
    limbs at `a1`. The post is existential in the written bytes and pins their
    256-bit LE decode to the input's BE value — the functional content.

    Anchored over `CodeReq.ofProg (GuestAddrs.secf_be_to_le) secfBeToLe_prog`,
    exactly the pairing in `GuestImageEntries.lean`, so this IS the image claim
    and is rowable.

    Domain: ABI hypotheses plus `hdisj` — with a live source AND destination
    window the two must not overlap. Discharged at every call site by the arena
    layout. See the module header on why this is a real domain restriction.

    ⚠️ Distinct from `Secp256k1FieldMulModPSAsm.secfBeToLeFlat_spec` and
    `Secp256k1PointDoubleSAsm.secfBeToLeFlat_spec`, which agree on entry, exit,
    pre and post but are anchored over `mulCr` / `pdCr`. Both are now corollaries
    of this theorem; neither is the image claim. -/
theorem secfBeToLeFlatEntry_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 32) (holen : ob.length = 32)
    (hwfR : Region.wf ⟨srci, inb⟩) (hrww : RwRegion.wf ⟨dsti, 32⟩)
    (hso : srci.toNat + 32 < 2 ^ 64) (hdo : dsti.toNat + 32 < 2 ^ 64)
    (hdisj : srci.toNat + 32 ≤ dsti.toNat ∨ dsti.toNat + 32 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((secfBeToLeFn srci dsti inb ob).body.steps + 1)
      (GuestAddrs.secf_be_to_le : Word) ret
      (CodeReq.ofProg (GuestAddrs.secf_be_to_le : Word) secfBeToLe_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** regOwns convScratch ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun hp => ∃ ws',
        ((⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
          ** bytesRegion dsti ws' ** bytesRegion srci inb)) hp) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns convScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (secfBeToLeFn srci dsti inb ob)
    (GuestAddrs.secf_be_to_le : Word)
    (secfBeToLeFn_spec srci dsti inb ob hwfR hrww hilen (GuestAddrs.secf_be_to_le : Word))
    (by show 4 * (19 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
    ob
    (by show ob.length = 32; exact holen)
    (by
      refine ⟨?_, ?_, rfl, holen, hilen, hso, hdo, hdisj, rfl⟩
      · show RegFile.get _ .x10 = srci
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
        exact if_pos rfl
      · show RegFile.get _ .x11 = dsti
        rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
        rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl)
    (fun _ _ _ h => h.2.2)
    (Q := fun hp => ∃ ws',
      ((⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
    (fun rf' ws' hlen' hpost' hp hh => by
      refine ⟨ws', ?_⟩
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      have hh2 := sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh
      have hpure : (⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
          ** (regOwns exposedRegs ** bytesRegion dsti ws')) hp :=
        (sepConj_pure_left hp).mpr ⟨⟨hpost'.1, hlen'⟩, hh2⟩
      xperm_hyp hpure)
  -- ⛔ NO `liftCode` here. This is the whole point of the module: the triple
  -- `Fn.retSpecFlat` produces is already at the routine's own single-program
  -- `CodeReq`, and widening it to a caller's union is what made the four
  -- pre-existing copies unrowable.
  rw [show (secfBeToLeFn srci dsti inb ob).programRet (GuestAddrs.secf_be_to_le : Word)
      = secfBeToLe_prog from rfl] at had
  rw [show (secfBeToLeFn srci dsti inb ob).region = (⟨srci, inb⟩ : Region) from rfl,
      show (secfBeToLeFn srci dsti inb ob).rw.base = dsti from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split2,
    show (if (Reg.x10 : Reg) = .x10 then srci else
        if (Reg.x10 : Reg) = .x11 then dsti else vf .x10) = srci from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then srci else
        if (Reg.x11 : Reg) = .x11 then dsti else vf .x11) = dsti from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
      vf convScratch
      (fun r hr => by
        show (if r = .x10 then srci else if r = .x11 then dsti else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_convScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_convScratch (hc ▸ hr))])]
    at had
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) had
  -- push the frame atoms inside the existential
  have hq1 : ((fun hp => ∃ ws',
      ((⌜wsNat256 ws' 0 = beBytesToNat inb ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
      ** (((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb) : Assertion) h := by
    xperm_hyp hq
  obtain ⟨ws', hin⟩ := (sepConj_exists_left h).mp hq1
  exact ⟨ws', by xperm_hyp hin⟩

/-- **`secf_le_to_be`, whole-routine flat triple at the guest entry.**

    The inverse converter: four little-endian u64 limbs at `a0` → a 32-byte
    big-endian buffer at `a1`. The post pins the output's BE decode to the
    input's LE value.

    Anchored over `CodeReq.ofProg (GuestAddrs.secf_le_to_be) secfLeToBe_prog`,
    the `GuestImageEntries` pairing, so this is the rowable image claim.

    Same two-live-window geometry as its twin, hence the same `hdisj`. -/
theorem secfLeToBeFlatEntry_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 32) (holen : ob.length = 32)
    (hwfR : Region.wf ⟨srci, inb⟩) (hrww : RwRegion.wf ⟨dsti, 32⟩)
    (hso : srci.toNat + 32 < 2 ^ 64) (hdo : dsti.toNat + 32 < 2 ^ 64)
    (hdisj : srci.toNat + 32 ≤ dsti.toNat ∨ dsti.toNat + 32 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((secfLeToBeFn srci dsti inb ob).body.steps + 1)
      (GuestAddrs.secf_le_to_be : Word) ret
      (CodeReq.ofProg (GuestAddrs.secf_le_to_be : Word) secfLeToBe_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** regOwns convScratch ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun hp => ∃ ws',
        ((⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
          ** ((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
          ** bytesRegion dsti ws' ** bytesRegion srci inb)) hp) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns convScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (secfLeToBeFn srci dsti inb ob)
    (GuestAddrs.secf_le_to_be : Word)
    (secfLeToBeFn_spec srci dsti inb ob hwfR hrww hilen (GuestAddrs.secf_le_to_be : Word))
    (by show 4 * (18 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
    ob
    (by show ob.length = 32; exact holen)
    (by
      refine ⟨?_, ?_, rfl, holen, hilen, hso, hdo, hdisj, rfl⟩
      · show RegFile.get _ .x10 = srci
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
        exact if_pos rfl
      · show RegFile.get _ .x11 = dsti
        rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
        rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl)
    (fun _ _ _ h => h.2.2)
    (Q := fun hp => ∃ ws',
      ((⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
    (fun rf' ws' hlen' hpost' hp hh => by
      refine ⟨ws', ?_⟩
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      have hh2 := sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh
      have hpure : (⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
          ** (regOwns exposedRegs ** bytesRegion dsti ws')) hp :=
        (sepConj_pure_left hp).mpr ⟨⟨hpost'.1, hlen'⟩, hh2⟩
      xperm_hyp hpure)
  rw [show (secfLeToBeFn srci dsti inb ob).programRet (GuestAddrs.secf_le_to_be : Word)
      = secfLeToBe_prog from rfl] at had
  rw [show (secfLeToBeFn srci dsti inb ob).region = (⟨srci, inb⟩ : Region) from rfl,
      show (secfLeToBeFn srci dsti inb ob).rw.base = dsti from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split2,
    show (if (Reg.x10 : Reg) = .x10 then srci else
        if (Reg.x10 : Reg) = .x11 then dsti else vf .x10) = srci from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then srci else
        if (Reg.x11 : Reg) = .x11 then dsti else vf .x11) = dsti from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
      vf convScratch
      (fun r hr => by
        show (if r = .x10 then srci else if r = .x11 then dsti else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_convScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_convScratch (hc ▸ hr))])]
    at had
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) had
  have hq1 : ((fun hp => ∃ ws',
      ((⌜beBytesToNat ws' = wsNat256 inb 0 ∧ ws'.length = 32⌝
        ** regOwns exposedRegs ** bytesRegion dsti ws')) hp)
      ** (((.x1 : Reg) ↦ᵣ ret) ** bytesRegion srci inb) : Assertion) h := by
    xperm_hyp hq
  obtain ⟨ws', hin⟩ := (sepConj_exists_left h).mp hq1
  exact ⟨ws', by xperm_hyp hin⟩

end Secp256k1FieldConvSAsm

end EvmAsm.Codegen
