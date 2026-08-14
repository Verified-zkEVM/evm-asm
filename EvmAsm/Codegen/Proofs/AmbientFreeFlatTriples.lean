/-
  EvmAsm.Codegen.Proofs.AmbientFreeFlatTriples

  Whole-routine flat triples for leaves whose ambient is EMPTY, i.e. the
  `Fn.retSpecFlat` side of the harvest (#12318 / #12244). Companion to
  `AmbientLiftedFlatTriples.lean`, which handles the pinned-NON-empty-ambient
  side via `Fn.retSpecFlatAmbient`.

  ## ⛔ READ THIS FIRST: search by SYMBOL before writing any flat triple

  Two of the four triples originally in this module were **pure duplicates** of
  lifts that were already in the tree — `secfGetBitLsbFlat_spec` (landed
  `de2fc7fe0`) and `bahU32leFlat_spec` (landed `a9c898904`), both already
  ancestors of this branch's base. They coexisted with mine only because the
  namespaces differ, so nothing failed to build. They have been removed.

  The check that would have caught it, run BEFORE proving anything:

  ```
  grep -rn "GuestAddrs.<symbol>" EvmAsm/ | grep -v GuestAddrs.lean
  ```

  ⚠️ Grepping for the NAME you intend to use is not enough, and grepping the
  allowlist is actively misleading — `bah_u32le`'s entry still read "needs
  `Fn.retSpecFlat` before a `.proven` row is honest" hours after the lift landed.
  A stale allowlist reason is not evidence of absence.

  ## But a pre-existing `<sym>Flat_spec` does NOT settle rowability either

  The complementary trap, and the reason this module still exists. Caller stage
  files define UNION `CodeReq`s — `pdCr` in `Secp256k1PointDoubleSAsmStage.lean`
  is a four-fold `.union` over five programs — and the flat triples there are
  anchored over those. Such a triple holds only when all five programs are
  loaded: a caller-specific assumption, NOT the single-program
  `GuestImageEntries` pairing. Rowing one attaches a row whose `CodeReq` is
  STRONGER than the image claim.

  So the two questions are independent, and both must be asked:

  | | is there an existing triple at the symbol? | is its `CodeReq` the symbol's own program? |
  |---|---|---|
  | `secf_get_bit_lsb` | **yes** (`secfGetBitLsbCr`) | yes ⇒ mine was redundant, removed |
  | `bah_u32le` | **yes** (`bahU32leCr`) | yes ⇒ mine was redundant, removed |
  | `secf_zero32` | yes, but only under `pdCr` | **no** ⇒ own-`CodeReq` sibling below |
  | `secf_is_zero32` | yes, but only under `pdCr` | **no** ⇒ own-`CodeReq` sibling below |

  `cpsTripleWithin_extend_code` lifts a triple from a smaller `CodeReq` to a
  larger one, so the siblings below imply the `pdCr` twins and not conversely.

  ⛔ **CORRECTION (#12244).** This header used to say that collapsing that
  duplication "needs the five program ranges pairwise disjoint, because
  `CodeReq.union` is left-biased". That is wrong: `liftCode … (by code_mem)`
  discharges own-`CodeReq` ⊆ `pdCr` on the nose, and
  `Secp256k1FieldConvFlatEntry` now does exactly that against `pdCr` itself for
  both converters, turning four ~90-line copies into four one-liners. Pairwise
  disjointness would only be needed to go the OTHER way (recover an own-`CodeReq`
  triple FROM a union), which nothing needs. What still blocks collapsing the two
  `zero32` twins below is narrower and purely syntactic: the `pdCr` copies
  quantify `(secfZero32Fn 0 []).body.steps` where these use
  `(secfZero32Fn dst orig).body.steps`, and name this very register list
  `a0Rest` instead of `resScratch`.

  The class is now CLOSED: `secf_be_to_le` and `secf_le_to_be` were its last two
  members, and both are rowed. Their both-regions-non-empty geometry lives in
  `Codegen/Programs/Secp256k1FieldConvFlatEntry.lean` (it must sit under
  `Programs/` so the two caller stage files can import it), which is why the
  geometry table below still shows no entry for it.

  ## The geometry map

  The adapter is decided by three independent facts — read-only `region`,
  writable `rw`, and ambient — not by what the routine computes:

  | routine | `region` | `rw` | ambient | adapter |
  |---|---|---|---|---|
  | `u256_add_be`             | empty     | non-empty | non-empty, pinned | `retSpecFlatAmbient` |
  | `bnf_eq32` + compare family | non-empty | empty   | non-empty, pinned | `retSpecFlatAmbient` |
  | `u256_from_u64_be`        | empty     | non-empty | **empty** | `retSpecFlat` |
  | `call_frame_set_calldata` | empty     | non-empty | **empty** | `retSpecFlat` |
  | `secf_is_zero32`          | non-empty | empty     | **empty** | `retSpecFlat` |
  | `secf_zero32`             | empty     | non-empty | **empty** | `retSpecFlat` |

  ⚠️ Family resemblance in the NAME does not predict liftability; only the `post`
  does. `enrgU32leFn`, `spwU32leFn` and `swsU32leFn` are the same computation as
  `bahU32leFn` but their posts read `fun rf _ _ => …`, discarding the ambient
  binder entirely. Those are unliftable until their contracts are pinned — a leaf
  change, not a lift.
-/

import EvmAsm.Codegen.Proofs.AmbientLiftedFlatTriples
import EvmAsm.Codegen.Programs.Secp256k1FieldGetBitLsbSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldLeavesSAsm
import EvmAsm.Codegen.Programs.BlockAccessListHashSAsm
import EvmAsm.Codegen.Programs.Secp256k1FieldIsZeroSAsm

namespace EvmAsm.Codegen.AmbientFree

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ⚠️ `AmbientLifted`'s register-split lemmas are `private`, so they cannot be
    reused across modules even though the register geometry is identical. The
    splits are re-derived here rather than de-privatising them there: a `private`
    proof-local lemma is not an API, and widening one to share three lines would
    make it one. -/

/-- `exposedRegs` minus only the result register `a0`. -/
def resScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem split_a0 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf resScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [resScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_resScratch : (.x10 : Reg) ∉ resScratch := by decide

/-! ## `secf_zero32` — one argument, empty read-only region, writable window

    Geometry-wise this is `u256_from_u64_be`'s (empty `region`, non-empty `rw`,
    empty ambient) with one argument, so it reuses `resScratch`/`split_a0` rather
    than introducing its own register split. It lives here rather than in
    `U256BeFlatTriples` because the grouping is by adapter, not by opcode family. -/

/-- **`secf_zero32`, whole-routine flat triple at the guest entry.**

    Zeroes the 32-byte window at `a0` with four dword stores. The post pins the
    window to `List.replicate 32 0` — the whole window, not a prefix — so a
    version that zeroed only part of it could not satisfy this.

    Anchored at `GuestAddrs.secf_zero32` over `CodeReq.ofProg … secfZero32_prog`,
    the pairing in `GuestImageEntries.lean`.

    Domain: ABI hypotheses only (writable region well-formed, 32 original bytes,
    aligned `ra`), so this one IS total over its argument type — there is no
    input-domain side condition.

    ⚠️ Distinct from `Secp256k1PointDoubleSAsmStage.secfZero32Flat_spec`, which
    agrees on entry, exit, pre and post but is anchored over `pdCr` — a four-fold
    `.union` requiring FIVE programs loaded. That one is not the image claim;
    see the module header. Hence `…FlatEntry_spec`, so the two do not read as
    interchangeable. -/
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

/-! ## `secf_is_zero32` — one argument, read-only region, no writable window

    The read-only accessor shape: load, return a value in `a0`, touch no memory.
    Second own-`CodeReq` sibling of the `pdCr` class. -/

/-- **`secf_is_zero32`, whole-routine flat triple at the guest entry.**

    Returns `a0 = 1` iff the 32-byte buffer at `a0` is all-zero, expressed as
    `if WhileBreakDemo.nlz bs 32 = 32 then 1 else 0`. `rw` is empty and the
    operand region is pinned intact, so the routine provably touches no memory:
    one that scribbled anywhere could not satisfy this.

    Anchored at `GuestAddrs.secf_is_zero32` over
    `CodeReq.ofProg … secfIsZero32_prog` — the routine's OWN program, matching the
    `GuestImageEntries` pairing, NOT the `pdCr` union of
    `Secp256k1PointDoubleSAsmStage.secfIsZero32Flat_spec`.

    Domain: ABI plus `bs.length = 32` and a no-wrap bound on the buffer. Both are
    conditions on the buffer rather than on a numeric argument, so every caller
    passing a well-formed 32-byte region satisfies them. -/
theorem secfIsZero32FlatEntry_spec (ret ptr : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk ptr bs).wf) (hlen : bs.length = 32)
    (hnw : ptr.toNat + 32 < 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((Secp256k1FieldIsZeroSAsm.secfIsZero32Fn ptr bs).body.steps + 1)
      (GuestAddrs.secf_is_zero32 : Word) ret
      (CodeReq.ofProg (GuestAddrs.secf_is_zero32 : Word) secfIsZero32_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) **
        regOwns resScratch ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ
          (if WhileBreakDemo.nlz bs 32 = 32 then (1 : Word) else (0 : Word))) **
        regOwns resScratch ** bytesRegion ptr bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns resScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) ** bytesRegion ptr bs)
      (fun vf => ?_))
  have hg10 : RegFile.get (fun r => if r = .x10 then ptr else vf r) .x10 = ptr := by
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  have had := Fn.retSpecFlat
    (Secp256k1FieldIsZeroSAsm.secfIsZero32Fn ptr bs)
    (GuestAddrs.secf_is_zero32 : Word)
    (Secp256k1FieldIsZeroSAsm.secfIsZero32Fn_spec ptr bs hwf
      (GuestAddrs.secf_is_zero32 : Word))
    (by show 4 * (11 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then ptr else vf r)
    [] rfl ⟨hg10, hlen, hnw, rfl⟩
    (Q := ((.x10 : Reg) ↦ᵣ
        (if WhileBreakDemo.nlz bs 32 = 32 then (1 : Word) else (0 : Word))) **
      regOwns resScratch)
    (fun _ _ _ hpost => hpost.2.2.2)
    (fun rf' ws' hlen' hpost hp hh => by
      obtain ⟨hc10, -, -, -⟩ := hpost
      have hws : ws' = [] := List.eq_nil_of_length_eq_zero hlen'
      subst hws
      have g10 : rf' .x10
          = (if WhileBreakDemo.nlz bs 32 = 32 then (1 : Word) else (0 : Word)) := by
        rwa [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)] at hc10
      rw [show (Secp256k1FieldIsZeroSAsm.secfIsZero32Fn ptr bs).rw.base = (0 : Word)
            from rfl,
        bytesRegion_nil, sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        split_a0, g10] at hh
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) resScratch) hp hh)
  rw [show (Secp256k1FieldIsZeroSAsm.secfIsZero32Fn ptr bs).programRet
      (GuestAddrs.secf_is_zero32 : Word) = secfIsZero32_prog from rfl] at had
  rw [show (Secp256k1FieldIsZeroSAsm.secfIsZero32Fn ptr bs).region = ⟨ptr, bs⟩ from rfl,
      show (Secp256k1FieldIsZeroSAsm.secfIsZero32Fn ptr bs).rw.base = (0 : Word)
        from rfl,
      bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    split_a0,
    show (if (Reg.x10 : Reg) = .x10 then ptr else vf .x10) = ptr from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then ptr else vf r) vf resScratch
      (fun r hr => by
        show (if r = .x10 then ptr else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_resScratch (hc ▸ hr))])]
    at had
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

/-! ## Non-vacuity

    A triple under contradictory hypotheses proves nothing, so each bundle here
    gets a satisfiability proof and an actual instance of its conclusion.

    ⭐ The two `…FlatEntry_spec` theorems above are covered, and so are the two
    PRE-EXISTING canonical lifts `Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFlat_spec`
    and `BlockAccessListHashSAsm.bahU32leFlat_spec` — neither of which shipped
    with any satisfiability proof. That matters most for `secf_get_bit_lsb`,
    whose `Region.loadOk` hypothesis is a genuine input-domain condition and
    therefore one that CAN be contradicted; see
    `secfGetBitLsb_hload_is_load_bearing`, the negative control. This is what
    remains of the duplicated work: the triples were redundant, the non-vacuity
    proofs were not. -/

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

/-- `secf_get_bit_lsb`'s hypothesis bundle is satisfiable. -/
private theorem secfGetBitLsb_hyps_satisfiable :
    (Region.mk (0x1000 : Word) vacBytes32).wf
      ∧ vacBytes32.length = 32
      ∧ Region.loadOk ⟨(0x1000 : Word), vacBytes32⟩
          ((0x1000 : Word)
            + Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbOffset (0 : Word)) 1
      ∧ (((0x4 : Word)) &&& ~~~(1 : Word)) = (0x4 : Word) :=
  ⟨by decide, by decide, vacLoadOk, by decide⟩

/-- ⭐ Negative control for the above, and the reason it is not a tautology. At
    `bitIdx = 256` the offset `31 - (256 >>> 3) = 31 - 32` underflows to a huge
    `Word`, and `loadOk` is FALSE. So `hload` is load-bearing: it is not an ABI
    formality that could be dropped, and `secf_get_bit_lsb` is genuinely NOT
    total over its argument type — unlike the compare family in
    `AmbientLiftedFlatTriples`, whose hypotheses are all ABI formalities. -/
private theorem secfGetBitLsb_hload_is_load_bearing :
    ¬ Region.loadOk ⟨(0x1000 : Word), vacBytes32⟩
        ((0x1000 : Word)
          + Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbOffset (256 : Word)) 1 := by
  unfold Region.loadOk
  decide

/-- Non-vacuity for the PRE-EXISTING canonical `secf_get_bit_lsb` lift. Each
    hypothesis is discharged independently, so none is derived from the others. -/
private theorem secfGetBitLsbFlat_instance :
    cpsTripleWithin
      ((Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFn (0x1000 : Word) (0 : Word)
        vacBytes32).body.steps + 1)
      (GuestAddrs.secf_get_bit_lsb : Word) (0x4 : Word)
      Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbCr
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x1000 : Word)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        regOwns Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbScratch **
        bytesRegion (0x1000 : Word) vacBytes32)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) **
        ((.x10 : Reg) ↦ᵣ Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbResult
          (0x1000 : Word) vacBytes32 (0 : Word)) **
        regOwn .x11 **
        regOwns Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbScratch **
        bytesRegion (0x1000 : Word) vacBytes32) :=
  Secp256k1FieldGetBitLsbSAsm.secfGetBitLsbFlat_spec
    (0x4 : Word) (0x1000 : Word) (0 : Word) vacBytes32
    (by decide) (by decide) vacLoadOk (by decide)

/-- `bah_u32le`'s bundle is satisfiable. The `4 ≤ bs.length` condition is on the
    BUFFER rather than a numeric argument, so any wide-enough region witnesses
    it; the 32-byte buffer here is comfortably wide. -/
private theorem bahU32le_hyps_satisfiable :
    (Region.mk (0x1000 : Word) vacBytes32).wf
      ∧ 4 ≤ vacBytes32.length
      ∧ (((0x4 : Word)) &&& ~~~(1 : Word)) = (0x4 : Word) := by
  decide

/-- Non-vacuity for the PRE-EXISTING canonical `bah_u32le` lift. -/
private theorem bahU32leFlat_instance :
    cpsTripleWithin
      ((BlockAccessListHashSAsm.bahU32leFn (0x1000 : Word) vacBytes32).body.steps + 1)
      (GuestAddrs.bah_u32le : Word) (0x4 : Word)
      BlockAccessListHashSAsm.bahU32leCr
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x1000 : Word)) **
        regOwns BlockAccessListHashSAsm.bahU32leScratch **
        bytesRegion (0x1000 : Word) vacBytes32)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) **
        ((.x10 : Reg) ↦ᵣ SgLoadU32leSAsm.leU32 vacBytes32 0) **
        regOwns BlockAccessListHashSAsm.bahU32leScratch **
        bytesRegion (0x1000 : Word) vacBytes32) :=
  BlockAccessListHashSAsm.bahU32leFlat_spec
    (0x4 : Word) (0x1000 : Word) vacBytes32
    (by decide) (by decide) (by decide) (by decide)

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

/-- `secf_is_zero32`'s bundle is satisfiable. Both non-ABI conditions are on the
    buffer (32 bytes, no address wrap), not on a numeric argument. -/
private theorem secfIsZero32_hyps_satisfiable :
    (Region.mk (0x1000 : Word) vacBytes32).wf
      ∧ vacBytes32.length = 32
      ∧ (0x1000 : Word).toNat + 32 < 2 ^ 64
      ∧ (((0x4 : Word)) &&& ~~~(1 : Word)) = (0x4 : Word) := by
  decide

private theorem secfIsZero32FlatEntry_instance :
    cpsTripleWithin
      ((Secp256k1FieldIsZeroSAsm.secfIsZero32Fn (0x1000 : Word) vacBytes32).body.steps + 1)
      (GuestAddrs.secf_is_zero32 : Word) (0x4 : Word)
      (CodeReq.ofProg (GuestAddrs.secf_is_zero32 : Word) secfIsZero32_prog)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x1000 : Word)) **
        regOwns resScratch ** bytesRegion (0x1000 : Word) vacBytes32)
      (((.x1 : Reg) ↦ᵣ (0x4 : Word)) **
        ((.x10 : Reg) ↦ᵣ
          (if WhileBreakDemo.nlz vacBytes32 32 = 32 then (1 : Word) else (0 : Word))) **
        regOwns resScratch ** bytesRegion (0x1000 : Word) vacBytes32) :=
  secfIsZero32FlatEntry_spec (0x4 : Word) (0x1000 : Word) vacBytes32
    (by decide) (by decide) (by decide) (by decide)

end EvmAsm.Codegen.AmbientFree
