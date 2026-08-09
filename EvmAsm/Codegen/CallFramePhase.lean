/-
  EvmAsm.Codegen.CallFramePhase

  The verified phase-ownership model for the `call_frame_arena` union —
  bead `evm-asm-4ch8f.6`'s deferred hard half, instantiating the generic
  machinery of `EvmAsm/Rv64/SAsm/PhaseSplit.lean` on the audited inventory
  of `EvmAsm/Codegen/RegionMap.lean`.

  ## What is being modeled

  `call_frame_arena` (`frameArrayBytes` ≈ 100.1 MiB, the Phase-D EVM
  call-frame overlay) physically coalesces five execution-dead Phase-H
  arenas into its front (`basr_values`, `basr_accounts`,
  `baap_storage_{desc,paths,values}`;
  `RegionMap.dataUnionChildren`).  The retired storage-log probe arenas are not
  part of this linked image.
  Until now the no-corruption argument was
  prose ("sequential, disjoint live windows",
  `docs/call-frame-memory-layout.md` §5).  This module replaces the prose
  with an ownership discipline:

  * The arena is ONE separation-logic resource
    (`phaseDView base = anyBytes base frameArrayBytes`), never two.
  * The Phase-H view is a *tiling* of that same resource
    (`phaseHView` = five havoc'd children + havoc'd pad), and
    `phaseD_eq_phaseH` proves the two views are THE SAME assertion.
  * Phase transitions are rewrites across that equality.  Both directions
    **forget contents by construction** (`anyBytes` carries ownership and
    length, nothing else): Phase D provably cannot depend on what Phase H
    left in the shared bytes, and a hypothetical post-dispatch Phase-H
    reader cannot recover its old buffers — re-partition havocs them.
    The unsoundness the prose worried about (a stale reader observing bytes
    the other phase scribbled) is now structurally unexpressible in any
    composed proof that frames the arena through these views.
  * On the consuming side, `SAsm.cpsTripleWithin_anyBytes_pre` forces every
    routine framed against a havoc'd range to be verified for all possible
    contents of that range.

  What routine beads must do: Phase-H routines (`.41`–`.48`) frame the
  individual child ranges (obtained by rewriting `phaseD_eq_phaseH` /
  `phaseD_children` left-to-right); Phase-D dispatch routines (`.49`,
  `.56`) frame `phaseDView`; the `block_verdict` composition (`.61`)
  performs each transition by a single rewrite, weakening any concrete
  buffer contents through `SAsm.bytesRegion_anyBytes` first.

  The absolute arena base stays a parameter (`base`) — the model is
  link-layout-independent; `RegionMap.callFrameArenaBase` pins this build's
  address, and `scripts/check-region-map.sh` guards it against the ELF.
-/

import EvmAsm.Codegen.RegionMap
import EvmAsm.Rv64.SAsm.PhaseSplit

namespace EvmAsm.Codegen
namespace CallFramePhase

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- Total bytes of the five coalesced Phase-H arenas (the union front). -/
def unionBytes : Nat := (RegionMap.dataUnionChildren.map (·.size)).sum

/-- Trailing pad: arena bytes past the union front, owned by neither Phase-H
    child (part of the Phase-D frame array only). -/
def unionPadBytes : Nat := frameArrayBytes - unionBytes

/-- The union front fits the arena (kernel recheck of
    `RegionMap.dataUnionChildren_fit_arena` at the summed granularity). -/
theorem unionBytes_le_arena : unionBytes ≤ frameArrayBytes := by decide

/-- Phase-H tiling segment sizes: the five children in layout order, then
    the pad. -/
def phaseHSegs : List Nat :=
  RegionMap.dataUnionChildren.map (·.size) ++ [unionPadBytes]

theorem phaseHSegs_sum : phaseHSegs.sum = frameArrayBytes := by decide

theorem phaseHSegs_dvd8 : ∀ s ∈ phaseHSegs, 8 ∣ s := by decide

-- ============================================================================
-- The two phase views and their equality
-- ============================================================================

/-- **Phase-D view**: the whole `call_frame_arena` as one havoc'd resource
    (the EVM call-frame overlay owns every byte, contents unspecified). -/
def phaseDView (base : Word) : Assertion := anyBytes base frameArrayBytes

/-- **Phase-H view**: the five coalesced arenas plus the pad, each a
    havoc'd tile of the same byte range. -/
def phaseHView (base : Word) : Assertion := anyTilesAt base 0 phaseHSegs

/-- **The phase-repartition theorem**: the two views are the SAME assertion.
    Rewriting across this equality is the phase transition; contents are
    forgotten in both directions by construction. -/
theorem phaseD_eq_phaseH (base : Word) : phaseDView base = phaseHView base := by
  rw [phaseDView, phaseHView, ← phaseHSegs_sum]
  exact anyBytes_eq_anyTiles base phaseHSegs phaseHSegs_dvd8

theorem pcFree_phaseDView (base : Word) : (phaseDView base).pcFree :=
  pcFree_anyBytes _ _

theorem pcFree_phaseHView (base : Word) : (phaseHView base).pcFree :=
  pcFree_anyTilesAt _ _ _

-- ============================================================================
-- The named-children form (offsets as accumulated sums)
-- ============================================================================

/-- Abbreviations for the audited segment sizes (`RegionMap.dataUnionChildren`):
    `S` = basr values/accounts stride, `D` = baap descriptors, `P` = one baap
    path arena. -/
private def S : Nat := RegionMap.basrArenaBytes
private def D : Nat := bsrMaxBalItems * baapStorageDescBytes
private def P : Nat := bsrMaxBalItems * bsrPathBytes

/-- The Phase-H view unfolded to the five named children plus the pad, each
    at its accumulated byte offset.  The offsets are stated as left-nested
    sums exactly as the tiling produces them;
    `children_offsets_match_regionMap` pins them to the audited
    `RegionMap.dataUnionChildren` offsets. -/
theorem phaseHView_children (base : Word) :
    phaseHView base
      = (anyBytes (base + BitVec.ofNat 64 0) S
        ** (anyBytes (base + BitVec.ofNat 64 S) S
        ** (anyBytes (base + BitVec.ofNat 64 (S + S)) D
        ** (anyBytes (base + BitVec.ofNat 64 (S + S + D)) P
        ** (anyBytes (base + BitVec.ofNat 64 (S + S + D + P)) P
        ** anyBytes (base + BitVec.ofNat 64 (S + S + D + P + P))
            unionPadBytes))))) := by
  show anyTilesAt base 0 phaseHSegs = _
  rw [show phaseHSegs = [S, S, D, P, P, unionPadBytes] from rfl]
  simp only [anyTilesAt, Nat.zero_add, sepConj_emp_right']

/-- The accumulated offsets above are exactly the audited
    `RegionMap.dataUnionChildren` offsets (and the pad starts at
    `unionBytes`). -/
theorem children_offsets_match_regionMap :
    [0, S, S + S, S + S + D, S + S + D + P]
      = RegionMap.dataUnionChildren.map (·.off)
    ∧ S + S + D + P + P = unionBytes := by
  constructor <;> decide

-- ============================================================================
-- Phase transitions
-- ============================================================================

/-- **Phase-H → Phase-D handoff, from concrete buffers**: the five child
    buffers with WHATEVER contents Phase H left in them, plus the untouched
    pad, assemble into the single arena resource Phase D owns.  Contents are
    forgotten here — this hypothesis shape is all a `block_verdict`-level
    composition needs at the dispatch boundary. -/
theorem phaseH_to_phaseD (base : Word) (h : PartialState)
    (bs₁ bs₂ bs₃ bs₄ bs₅ : List (BitVec 8))
    (hl₁ : bs₁.length = S) (hl₂ : bs₂.length = S) (hl₃ : bs₃.length = D)
    (hl₄ : bs₄.length = P) (hl₅ : bs₅.length = P)
    (hp : (bytesRegion (base + BitVec.ofNat 64 0) bs₁
        ** (bytesRegion (base + BitVec.ofNat 64 S) bs₂
        ** (bytesRegion (base + BitVec.ofNat 64 (S + S)) bs₃
        ** (bytesRegion (base + BitVec.ofNat 64 (S + S + D)) bs₄
        ** (bytesRegion (base + BitVec.ofNat 64 (S + S + D + P)) bs₅
        ** anyBytes (base + BitVec.ofNat 64 (S + S + D + P + P))
            unionPadBytes))))) h) :
    phaseDView base h := by
  have w : ∀ (b : Word) (n : Nat) (bs : List (BitVec 8)), bs.length = n →
      ∀ h', bytesRegion b bs h' → anyBytes b n h' :=
    fun b n bs hl h' hx => hl ▸ bytesRegion_anyBytes b bs h' hx
  rw [phaseD_eq_phaseH, phaseHView_children]
  refine sepConj_mono_left (w _ _ _ hl₁) h (sepConj_mono_right (fun h₁ hx₁ => ?_) h hp)
  refine sepConj_mono_left (w _ _ _ hl₂) h₁ (sepConj_mono_right (fun h₂ hx₂ => ?_) h₁ hx₁)
  refine sepConj_mono_left (w _ _ _ hl₃) h₂ (sepConj_mono_right (fun h₃ hx₃ => ?_) h₂ hx₂)
  refine sepConj_mono_left (w _ _ _ hl₄) h₃ (sepConj_mono_right (fun h₄ hx₄ => ?_) h₃ hx₃)
  exact sepConj_mono_left (w _ _ _ hl₅) h₄ hx₄

/-- **Phase-D → Phase-H re-entry** (stated for completeness; the guest's
    phase order is H then D with no post-dispatch Phase-H reader — this
    direction documents that even if one existed, it would receive its
    buffers HAVOC'D, not with their old contents): the arena resource
    re-partitions into the five child tiles + pad, contents unspecified. -/
theorem phaseD_to_phaseH (base : Word) (h : PartialState)
    (hp : phaseDView base h) : phaseHView base h :=
  (phaseD_eq_phaseH base) ▸ hp

end CallFramePhase
end EvmAsm.Codegen
