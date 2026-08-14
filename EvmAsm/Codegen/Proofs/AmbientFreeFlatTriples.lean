/-
  EvmAsm.Codegen.Proofs.AmbientFreeFlatTriples

  Whole-routine flat triples for leaves whose ambient is EMPTY, i.e. the
  `Fn.retSpecFlat` side of the harvest (#12318 / #12244). Companion to
  `AmbientLiftedFlatTriples.lean`, which handles the pinned-NON-empty-ambient
  side via `Fn.retSpecFlatAmbient`.

  ## Where these sit in the geometry map

  The lift is decided by three independent facts — read-only `region`, writable
  `rw`, and ambient — not by what the routine computes:

  | routine | `region` | `rw` | ambient | adapter |
  |---|---|---|---|---|
  | `u256_add_be`             | empty     | non-empty | non-empty, pinned | `retSpecFlatAmbient` |
  | `bnf_eq32` + compare family | non-empty | empty   | non-empty, pinned | `retSpecFlatAmbient` |
  | `u256_from_u64_be`        | empty     | non-empty | **empty** | `retSpecFlat` |
  | `call_frame_set_calldata` | empty     | non-empty | **empty** | `retSpecFlat` |
  | **`secf_get_bit_lsb`**    | non-empty | empty     | **empty** | `retSpecFlat` |
  | **`bah_u32le`**           | non-empty | empty     | **empty** | `retSpecFlat` |
  | **`secf_zero32`**         | empty     | non-empty | **empty** | `retSpecFlat` |

  The first two rows here are a geometry no previous batch covered: a non-empty
  read-only region with NO writable window and NO ambient. It is the read-only
  accessor shape — load something, return a value in `a0`, touch no memory.

  ## Why these were reachable at all

  `scripts/ambient-triage.py` decides liftability by whether the leaf's `post`
  PINS its ambient, because that is what `Fn.retSpecFlat`'s `hpostEmp` and
  `Fn.retSpecFlatAmbient`'s `hpostAmb` need. All three routines below already
  pin (`A = empAssertion` in the post), so no leaf contract change was required.

  ⚠️ Their nearest siblings do NOT, and that is worth knowing before anyone
  batches by name: `enrgU32leFn`, `spwU32leFn` and `swsU32leFn` are the same
  computation as `bahU32leFn` but their posts read `fun rf _ _ => …`, discarding
  the ambient binder entirely. Those are unliftable until their contracts are
  pinned — a leaf change, not a lift. **Family resemblance in the NAME does not
  predict liftability; only the `post` does.**
-/

import EvmAsm.Codegen.Proofs.AmbientLiftedFlatTriples
import EvmAsm.Codegen.Programs.Secp256k1FieldGetBitLsbSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldLeavesSAsm
import EvmAsm.Codegen.Programs.BlockAccessListHashSAsm

namespace EvmAsm.Codegen.AmbientFree

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ⚠️ `AmbientLifted`'s register-split lemmas are `private`, so they cannot be
    reused across modules even though the register geometry is identical. The
    splits are re-derived here rather than de-privatising them there: a `private`
    proof-local lemma is not an API, and widening one to share three lines would
    make it one. -/

/-- `exposedRegs` minus the two ABI argument registers `a0`/`a1`. -/
def argScratch2 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- `exposedRegs` minus only the result register `a0`. -/
def resScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem split_a0_a1 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf argScratch2) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [argScratch2, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem split_a0 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf resScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [resScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_argScratch2 : (.x10 : Reg) ∉ argScratch2 := by decide
private theorem x11_notin_argScratch2 : (.x11 : Reg) ∉ argScratch2 := by decide

/-! ## `secf_get_bit_lsb` — two arguments, read-only region, no writable window -/

/-- **`secf_get_bit_lsb`, whole-routine flat triple at the guest entry.**

    Returns in `a0` the LSB-indexed bit `a1` of the 32-byte secp256k1 field
    element at `a0`, as `secfGetBitLsbResult`. The operand region is pinned
    INTACT in the post and there is no writable window at all, so this routine
    provably touches no memory: a version that scribbled anywhere could not
    satisfy it.

    Anchored at `GuestAddrs.secf_get_bit_lsb` over
    `CodeReq.ofProg … secfGetBitLsb_prog`, the pairing in
    `GuestImageEntries.lean`, so this is a claim about the deployed image.

    Domain: ABI plus ONE genuine input condition — `Region.loadOk` for the byte
    the index selects. That is not an ABI formality: it is what makes the bit
    index in range, so unlike the compare family this triple is **not** total
    over its argument type. -/
theorem secfGetBitLsbFlat_spec (ret src bitIdx : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hlen : bs.length = 32)
    (hload : Region.loadOk ⟨src, bs⟩ (src + Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbOffset bitIdx) 1)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn src bitIdx bs).body.steps + 1)
      (GuestAddrs.secf_get_bit_lsb : Word) ret
      (CodeReq.ofProg (GuestAddrs.secf_get_bit_lsb : Word)
        secfGetBitLsb_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ bitIdx) **
        regOwns argScratch2 ** bytesRegion src bs)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbResult src bs bitIdx) **
        regOwns resScratch ** bytesRegion src bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns argScratch2 (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ bitIdx) ** bytesRegion src bs)
      (fun vf => ?_))
  have hg10 : RegFile.get
      (fun r => if r = .x10 then src else if r = .x11 then bitIdx else vf r)
      .x10 = src := by
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have hg11 : RegFile.get
      (fun r => if r = .x10 then src else if r = .x11 then bitIdx else vf r)
      .x11 = bitIdx := by
    rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
    rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
    exact if_pos rfl
  have had := Fn.retSpecFlat
    (Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn src bitIdx bs)
    (GuestAddrs.secf_get_bit_lsb : Word)
    (Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn_spec src bitIdx bs
      (GuestAddrs.secf_get_bit_lsb : Word) hwf)
    (by show 4 * (8 + 1) ≤ 2 ^ 64; decide)
    ret halign
    (fun r => if r = .x10 then src else if r = .x11 then bitIdx else vf r)
    [] rfl ⟨hg10, hg11, rfl, hlen, hload, rfl⟩
    (Q := ((.x10 : Reg) ↦ᵣ
        Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbResult src bs bitIdx) **
      regOwns resScratch)
    (fun _ _ _ hpost => hpost.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hc10, hws, -⟩ := hpost
      subst hws
      have g10 : rf' .x10
          = Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbResult src bs bitIdx := by
        rwa [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)] at hc10
      rw [show (Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn src bitIdx bs).rw.base
            = (0 : Word) from rfl,
        bytesRegion_nil, sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        split_a0, g10] at hh
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) resScratch) hp hh)
  rw [show (Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn src bitIdx bs).programRet
      (GuestAddrs.secf_get_bit_lsb : Word)
      = secfGetBitLsb_prog from rfl] at had
  rw [show (Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn src bitIdx bs).region
        = ⟨src, bs⟩ from rfl,
      show (Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn src bitIdx bs).rw.base
        = (0 : Word) from rfl,
      bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    split_a0_a1,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then bitIdx else vf .x10) = src from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then bitIdx else vf .x11) = bitIdx from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else if r = .x11 then bitIdx else vf r)
      vf argScratch2
      (fun r hr => by
        show (if r = .x10 then src else if r = .x11 then bitIdx else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_argScratch2 (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_argScratch2 (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

/-! ## `secf_zero32` — one argument, empty read-only region, writable window

    Geometry-wise this is NOT a new shape: it is `u256_from_u64_be`'s (empty
    `region`, non-empty `rw`, empty ambient) with one argument instead of two, so
    it reuses `resScratch`/`split_a0` above rather than introducing its own
    register split. It lives here rather than in `U256BeFlatTriples` because the
    grouping is by adapter, not by opcode family. -/

private theorem x10_notin_resScratch : (.x10 : Reg) ∉ resScratch := by decide

/-- **`secf_zero32`, whole-routine flat triple at the guest entry.**

    Zeroes the 32-byte window at `a0` with four dword stores. The post pins the
    window to `List.replicate 32 0` — the whole window, not a prefix — so a
    version that zeroed only part of it could not satisfy this.

    Anchored at `GuestAddrs.secf_zero32` over `CodeReq.ofProg … secfZero32_prog`,
    the pairing in `GuestImageEntries.lean`.

    Domain: ABI hypotheses only (writable region well-formed, 32 original bytes,
    aligned `ra`), so unlike `secf_get_bit_lsb` below this one IS total over its
    argument type — there is no input-domain side condition.

    ## ⚠️ Relationship to `Secp256k1PointDoubleSAsmStage.secfZero32Flat_spec`

    A near-identical theorem already exists in the point-double **caller's** stage
    file. The statements agree on entry, exit, pre and post; they differ in ONE
    place, the `CodeReq`:

    | | this theorem | the stage-file twin |
    |---|---|---|
    | `CodeReq` | `CodeReq.ofProg secf_zero32 secfZero32_prog` | `pdCr` |
    | code assumed present | this routine's program **only** | **five** programs (point-double + 4 leaves) |

    `pdCr` is a four-fold `.union`, so the twin only applies when all five
    programs are loaded — a caller-specific assumption. This one assumes strictly
    less, which is why it is the form that matches the `GuestImageEntries` pairing
    and the form worth rowing. The name is `…FlatEntry_spec` rather than
    `…Flat_spec` so the two do not read as interchangeable.

    The implication runs one way only: `cpsTripleWithin_extend_code` lifts a
    triple from a smaller `CodeReq` to a larger one, so the twin should follow
    from THIS theorem and not conversely. ⚠️ I have not proved that here, and it
    is not free: `CodeReq.union` is left-biased, so the bridge needs the five
    program ranges to be pairwise disjoint. Collapsing the duplication is a
    follow-up, not a claim of this PR. -/
theorem secfZero32FlatEntry_spec (ret dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 32⟩) (hlenOrig : orig.length = 32)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((Secp256k1FieldLeavesSAsm.secfZero32Fn dst orig).body.steps + 1)
      (GuestAddrs.secf_zero32 : Word) ret
      (CodeReq.ofProg (GuestAddrs.secf_zero32 : Word) secfZero32_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ dst) **
        regOwns resScratch ** bytesRegion dst orig)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst (List.replicate 32 (0 : BitVec 8))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns resScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ dst) ** bytesRegion dst orig)
      (fun vf => ?_))
  have hg10 : RegFile.get (fun r => if r = .x10 then dst else vf r) .x10 = dst := by
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlat
    (Secp256k1FieldLeavesSAsm.secfZero32Fn dst orig)
    (GuestAddrs.secf_zero32 : Word)
    (Secp256k1FieldLeavesSAsm.secfZero32Fn_spec dst orig hwf
      (GuestAddrs.secf_zero32 : Word))
    (by show 4 * (4 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then dst else vf r)
    orig hlenOrig ⟨hg10, rfl, hlenOrig, rfl⟩
    (Q := regOwns exposedRegs ** bytesRegion dst (List.replicate 32 (0 : BitVec 8)))
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hws, -⟩ := hpost
      subst ws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (Secp256k1FieldLeavesSAsm.secfZero32Fn dst orig).programRet
      (GuestAddrs.secf_zero32 : Word) = secfZero32_prog from rfl] at had
  rw [show (Secp256k1FieldLeavesSAsm.secfZero32Fn dst orig).region
        = Region.empty from rfl,
      show (Secp256k1FieldLeavesSAsm.secfZero32Fn dst orig).rw.base = dst from rfl,
      show Region.empty.base = (0 : Word) from rfl,
      show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    split_a0,
    show (if (Reg.x10 : Reg) = .x10 then dst else vf .x10) = dst from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then dst else vf r) vf resScratch
      (fun r hr => by
        show (if r = .x10 then dst else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_resScratch (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by
      rw [sepConj_emp_right'] at hq
      xperm_hyp hq) had

/-! ## `bah_u32le` — one argument, read-only region, no writable window

    Same geometry as `secf_get_bit_lsb` (non-empty `region`, empty `rw`, empty
    ambient), with one argument, so it too reuses `resScratch`/`split_a0`.

    ⚠️ Read the header note before extending this to its siblings. -/

/-- **`bah_u32le`, whole-routine flat triple at the guest entry.**

    Returns in `a0` the little-endian `u32` at `a0`, as `SgLoadU32leSAsm.leU32 bs 0`. As with
    `secf_get_bit_lsb`, `rw` is empty and the operand region is pinned intact, so
    the routine provably touches no memory.

    Anchored at `GuestAddrs.bah_u32le` over `CodeReq.ofProg … bahU32le_prog`.

    Domain: ABI plus `4 ≤ bs.length`. That length bound is a genuine input
    condition — the four `LBU`s read `bs[0..3]` — but it is a condition on the
    BUFFER, not on a numeric argument, so it is satisfied by every caller that
    passes a wide enough region. -/
theorem bahU32leFlat_spec (ret p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (hlen4 : 4 ≤ bs.length)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((BlockAccessListHashSAsm.bahU32leFn p bs).body.steps + 1)
      (GuestAddrs.bah_u32le : Word) ret
      (CodeReq.ofProg (GuestAddrs.bah_u32le : Word) bahU32le_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ p) **
        regOwns resScratch ** bytesRegion p bs)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 bs 0) **
        regOwns resScratch ** bytesRegion p bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns resScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ p) ** bytesRegion p bs)
      (fun vf => ?_))
  have hg10 : RegFile.get (fun r => if r = .x10 then p else vf r) .x10 = p := by
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlat
    (BlockAccessListHashSAsm.bahU32leFn p bs)
    (GuestAddrs.bah_u32le : Word)
    (BlockAccessListHashSAsm.bahU32leFn_spec p bs hwf (GuestAddrs.bah_u32le : Word))
    (by show 4 * (11 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then p else vf r)
    [] rfl ⟨hg10, hlen4, rfl⟩
    (Q := ((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 bs 0) ** regOwns resScratch)
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' hlen' hpost hp hh => by
      obtain ⟨hc10, -⟩ := hpost
      -- ⚠️ Unlike `secfGetBitLsbFn`, this leaf's post is `fun rf _ A => …` and
      -- does NOT pin `ws`, so emptiness of the written window comes from the
      -- length side condition instead: `rw` is empty, hence `ws'.length = 0`.
      have hws : ws' = [] := List.eq_nil_of_length_eq_zero hlen'
      subst hws
      have g10 : rf' .x10 = SgLoadU32leSAsm.leU32 bs 0 := by
        rwa [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)] at hc10
      rw [show (BlockAccessListHashSAsm.bahU32leFn p bs).rw.base = (0 : Word)
            from rfl,
        bytesRegion_nil, sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        split_a0, g10] at hh
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) resScratch) hp hh)
  rw [show (BlockAccessListHashSAsm.bahU32leFn p bs).programRet
      (GuestAddrs.bah_u32le : Word) = bahU32le_prog from rfl] at had
  rw [show (BlockAccessListHashSAsm.bahU32leFn p bs).region = ⟨p, bs⟩ from rfl,
      show (BlockAccessListHashSAsm.bahU32leFn p bs).rw.base = (0 : Word) from rfl,
      bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    split_a0,
    show (if (Reg.x10 : Reg) = .x10 then p else vf .x10) = p from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then p else vf r) vf resScratch
      (fun r hr => by
        show (if r = .x10 then p else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_resScratch (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

/-! ## Non-vacuity

    ⚠️ This section matters MORE here than it did for the compare family. That
    family's hypotheses are all ABI formalities, true for any caller that follows
    the calling convention. This routine's `hload` is a genuine constraint on
    `bitIdx`, so its bundle is one that CAN be contradicted — and a triple under
    contradictory hypotheses proves nothing at all. -/

private def vacBytes32 : List (BitVec 8) := List.replicate 32 (0 : BitVec 8)

/-! `Region.loadOk` is a bare `Prop` def with no `Decidable` instance (unlike
    `Region.wf`, which carries one), so it is unfolded before `decide`. -/

/-- The in-range load at `bitIdx = 0`: the offset `31 - (bitIdx >>> 3)` is 31,
    the last byte of the 32-byte buffer. -/
private theorem vacLoadOk :
    Region.loadOk ⟨(0x1000 : Word), vacBytes32⟩
      ((0x1000 : Word)
        + Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbOffset (0 : Word)) 1 := by
  unfold Region.loadOk
  decide

/-- The `secf_get_bit_lsb` hypothesis bundle is satisfiable: a well-formed
    32-byte buffer, an in-range bit index, and an aligned return address. -/
private theorem secfGetBitLsb_hyps_satisfiable :
    (Region.mk (0x1000 : Word) vacBytes32).wf
      ∧ vacBytes32.length = 32
      ∧ Region.loadOk ⟨(0x1000 : Word), vacBytes32⟩
          ((0x1000 : Word)
            + Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbOffset (0 : Word)) 1
      ∧ (((0x4 : Word)) &&& ~~~(1 : Word)) = (0x4 : Word) :=
  ⟨by decide, by decide, vacLoadOk, by decide⟩

/-- ⭐ Negative control for the above. At `bitIdx = 256` the offset
    `31 - (256 >>> 3) = 31 - 32` underflows to a huge `Word`, and `loadOk` is
    FALSE. So `hload` is load-bearing: it is not an ABI formality that could be
    dropped, and the satisfiability proof above is not a tautology. This is what
    makes the domain restriction in `secfGetBitLsbFlat_spec`'s docstring an
    honest statement rather than a hedge. -/
private theorem secfGetBitLsb_hload_is_load_bearing :
    ¬ Region.loadOk ⟨(0x1000 : Word), vacBytes32⟩
        ((0x1000 : Word)
          + Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbOffset (256 : Word)) 1 := by
  unfold Region.loadOk
  decide

/-- An actual instance of the conclusion, which is what establishes
    non-vacuity. Each hypothesis is discharged by an independent `decide`, so
    none is being derived from the others.

    `GuestAddrs.secf_get_bit_lsb` appears as a SYMBOL, so a layout regen flows
    through it; no numeric address is pinned. -/
private theorem secfGetBitLsbFlat_instance :
    cpsTripleWithin
      ((Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn (0x1000 : Word) (0 : Word)
        vacBytes32).body.steps + 1)
      (GuestAddrs.secf_get_bit_lsb : Word) (0x4 : Word)
      (CodeReq.ofProg (GuestAddrs.secf_get_bit_lsb : Word) secfGetBitLsb_prog)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x1000 : Word)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) ** regOwns argScratch2 **
        bytesRegion (0x1000 : Word) vacBytes32)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) **
        ((.x10 : Reg) ↦ᵣ Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbResult
          (0x1000 : Word) vacBytes32 (0 : Word)) **
        regOwns resScratch ** bytesRegion (0x1000 : Word) vacBytes32) :=
  secfGetBitLsbFlat_spec (0x4 : Word) (0x1000 : Word) (0 : Word) vacBytes32
    (by decide) (by decide) vacLoadOk (by decide)

/-- `secf_zero32`'s bundle is satisfiable: a well-formed 32-byte writable window
    and an aligned return address. ABI-only, so unlike `secf_get_bit_lsb` there
    is no negative control to give — there is no input-domain condition that
    could fail. -/
private theorem secfZero32_hyps_satisfiable :
    RwRegion.wf ⟨(0x1000 : Word), 32⟩
      ∧ vacBytes32.length = 32
      ∧ (((0x4 : Word)) &&& ~~~(1 : Word)) = (0x4 : Word) := by
  decide

private theorem secfZero32FlatEntry_instance :
    cpsTripleWithin
      ((Secp256k1FieldLeavesSAsm.secfZero32Fn (0x1000 : Word) vacBytes32).body.steps + 1)
      (GuestAddrs.secf_zero32 : Word) (0x4 : Word)
      (CodeReq.ofProg (GuestAddrs.secf_zero32 : Word) secfZero32_prog)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x1000 : Word)) **
        regOwns resScratch ** bytesRegion (0x1000 : Word) vacBytes32)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** regOwns exposedRegs **
        bytesRegion (0x1000 : Word) (List.replicate 32 (0 : BitVec 8))) :=
  secfZero32FlatEntry_spec (0x4 : Word) (0x1000 : Word) vacBytes32
    (by decide) (by decide) (by decide)

/-- `bah_u32le`'s bundle is satisfiable. The `4 ≤ bs.length` condition is on the
    BUFFER rather than a numeric argument, so any wide-enough region witnesses
    it; the 32-byte buffer here is comfortably wide. -/
private theorem bahU32le_hyps_satisfiable :
    (Region.mk (0x1000 : Word) vacBytes32).wf
      ∧ 4 ≤ vacBytes32.length
      ∧ (((0x4 : Word)) &&& ~~~(1 : Word)) = (0x4 : Word) := by
  decide

private theorem bahU32leFlat_instance :
    cpsTripleWithin
      ((BlockAccessListHashSAsm.bahU32leFn (0x1000 : Word) vacBytes32).body.steps + 1)
      (GuestAddrs.bah_u32le : Word) (0x4 : Word)
      (CodeReq.ofProg (GuestAddrs.bah_u32le : Word) bahU32le_prog)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x1000 : Word)) **
        regOwns resScratch ** bytesRegion (0x1000 : Word) vacBytes32)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) **
        ((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 vacBytes32 0) **
        regOwns resScratch ** bytesRegion (0x1000 : Word) vacBytes32) :=
  bahU32leFlat_spec (0x4 : Word) (0x1000 : Word) vacBytes32
    (by decide) (by decide) (by decide)

end EvmAsm.Codegen.AmbientFree
