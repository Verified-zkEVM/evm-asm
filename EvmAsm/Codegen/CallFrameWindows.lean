/-
  EvmAsm.Codegen.CallFrameWindows

  Per-depth window algebra over the Phase-D `call_frame_arena`
  (bead `evm-asm-4ch8f.10.4`, strategy `docs/4ch8f-interp-strategy.md` §4).

  ## What this module is

  The Phase-D dispatcher is ONE flat loop; a CALL/CREATE does not recurse but
  MOVES a window over the 1025-slot frame arena
  (`CallFramePhase.phaseDView base = anyBytes base frameArrayBytes`).  Frame
  `d` lives at `base + d * frameStride` (`CallFrameLayout`).  This module is
  the pure separation-logic algebra those descend/return proofs (bead `.56`)
  splice: it carves `phaseDView` into per-depth windows, focuses/unfocuses one
  depth against the untouched rest, tiles a single window into its named
  sub-regions (`CallFrameLayout` offsets), and fixes the SHAPE of the
  depth-indexed `encodesFrame` relation for suspended parent frames.

  No machine code, no addresses pinned: everything is parameterized over the
  arena base `base : Word`, exactly like `CallFramePhase`.  The 1025-way tiling
  is stated once over `List.replicate frameSlotCount frameStride` and proved by
  induction over the generic replicated segment — never a 1025-case
  enumeration (see `anyTilesAt_replicate_focus_at`).

  Built on `EvmAsm/Rv64/SAsm/PhaseSplit.lean` (`anyBytes`, `anyBytes_add`,
  `anyTilesAt`, `anyBytes_eq_anyTiles`, `bytesRegion_anyBytes`) and the audited
  constants of `EvmAsm/Codegen/CallFrameLayout.lean`.  The worked example for
  the tiling proof pattern is `CallFramePhase.phaseHView_children`.
-/

import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.CallFramePhase
import EvmAsm.Rv64.SAsm.PhaseSplit

namespace EvmAsm.Codegen
namespace CallFrameWindows

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

-- ============================================================================
-- Generic replicated-segment tiling toolkit
-- ============================================================================

/-- Sum of a replicated `Nat` segment (kept generic so no 1025-case unfold is
    ever needed). -/
theorem sum_replicate (n s : Nat) : (List.replicate n s).sum = n * s := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

/-- Every element of a replicated `frameStride` list is dword-aligned. -/
theorem replicate_dvd8 (n : Nat) : ∀ s ∈ List.replicate n frameStride, 8 ∣ s := by
  intro s hs
  rw [List.eq_of_mem_replicate hs]
  decide

/-- Split a tiling over a list append into the two contiguous sub-tilings, the
    second shifted by the first list's byte sum.  The offset-threading engine
    of every window lemma below. -/
theorem anyTilesAt_append (base : Word) (l1 l2 : List Nat) (off : Nat) :
    anyTilesAt base off (l1 ++ l2)
      = (anyTilesAt base off l1 ** anyTilesAt base (off + l1.sum) l2) := by
  induction l1 generalizing off with
  | nil =>
      simp only [List.nil_append, anyTilesAt, List.sum_nil, Nat.add_zero, sepConj_emp_left']
  | cons n ns ih =>
      have hoff : off + (n + ns.sum) = (off + n) + ns.sum := by omega
      simp only [List.cons_append, anyTilesAt, List.sum_cons, hoff]
      rw [ih (off + n), sepConj_assoc']

/-- A single-element tiling is just the one havoc'd tile. -/
theorem anyTilesAt_singleton (base : Word) (off s : Nat) :
    anyTilesAt base off [s] = anyBytes (base + BitVec.ofNat 64 off) s := by
  simp only [anyTilesAt, sepConj_emp_right']

/-- **The one-tile focus for replicated segments** (generic over `n`, `off`, `j`
    — the discipline the reviewer checks: composed on `j`, never enumerated):
    a replicated tiling splits into the `j` tiles before, the focused tile at
    `off + j * s`, and the tail after.  All window lemmas descend from this. -/
theorem anyTilesAt_replicate_focus_at (base : Word) (s off n j : Nat) (hj : j < n) :
    anyTilesAt base off (List.replicate n s)
      = (anyTilesAt base off (List.replicate j s)
        ** anyBytes (base + BitVec.ofNat 64 (off + j * s)) s
        ** anyTilesAt base (off + (j + 1) * s) (List.replicate (n - (j + 1)) s)) := by
  have h1 : List.replicate n s = List.replicate j s ++ List.replicate (n - j) s := by
    rw [← List.replicate_add]; congr 1; omega
  have h2 : List.replicate (n - j) s = [s] ++ List.replicate (n - (j + 1)) s := by
    rw [List.singleton_append, ← List.replicate_succ]; congr 1; omega
  rw [h1, anyTilesAt_append, sum_replicate,
    h2, anyTilesAt_append, anyTilesAt_singleton]
  rw [show ([s] : List Nat).sum = s from by simp,
    show off + j * s + s = off + (j + 1) * s from by rw [Nat.succ_mul]; omega]

-- ============================================================================
-- 1. Equal-stride tiling of the arena into per-depth windows
-- ============================================================================

/-- Absolute base address of frame slot `d`. -/
def frameBase (base : Word) (d : Nat) : Word := base + BitVec.ofNat 64 (d * frameStride)

/-- **One per-depth window**: the `frameStride` bytes of frame slot `d`,
    havoc'd (contents unspecified).  The grow-down operand stack lives inside
    it exactly as the pilot's `x12` window. -/
def frameWindow (base : Word) (d : Nat) : Assertion := anyBytes (frameBase base d) frameStride

theorem pcFree_frameWindow (base : Word) (d : Nat) : (frameWindow base d).pcFree :=
  pcFree_anyBytes _ _

/-- **The equal-stride tiling**: the whole Phase-D arena IS the separating
    conjunction of the 1025 per-depth windows.  Stated the `anyTilesAt` way
    over `List.replicate frameSlotCount frameStride` (a replicated instance of
    `anyBytes_eq_anyTiles`); `phaseDView_focus` below extracts any single
    `frameWindow base d` from it. -/
theorem phaseDView_eq_framesTiling (base : Word) :
    CallFramePhase.phaseDView base
      = anyTilesAt base 0 (List.replicate frameSlotCount frameStride) := by
  unfold CallFramePhase.phaseDView
  rw [show frameArrayBytes = (List.replicate frameSlotCount frameStride).sum from
    by simp only [sum_replicate, frameArrayBytes]]
  exact anyBytes_eq_anyTiles base _ (replicate_dvd8 _)

-- ============================================================================
-- 2. Focus / unfocus one depth against the untouched rest
-- ============================================================================

/-- The frames below depth `d` (havoc'd, untouched by a descend/return at `d`). -/
def prefixFrames (base : Word) (d : Nat) : Assertion :=
  anyTilesAt base 0 (List.replicate d frameStride)

/-- The frames above depth `d` (havoc'd, untouched by a descend/return at `d`). -/
def suffixFrames (base : Word) (d : Nat) : Assertion :=
  anyTilesAt base ((d + 1) * frameStride) (List.replicate (frameSlotCount - (d + 1)) frameStride)

/-- **Focus depth `d`**: the arena splits into the frames below, the depth-`d`
    window, and the frames above — the rest framed off untouched.  This is the
    equality a descend/return proof rewrites through to work on one window. -/
theorem phaseDView_focus (base : Word) (d : Nat) (hd : d ≤ maxCallDepth) :
    CallFramePhase.phaseDView base
      = (prefixFrames base d ** frameWindow base d ** suffixFrames base d) := by
  rw [phaseDView_eq_framesTiling,
    anyTilesAt_replicate_focus_at base frameStride 0 frameSlotCount d
      (by unfold frameSlotCount; omega)]
  unfold prefixFrames frameWindow suffixFrames frameBase
  simp only [Nat.zero_add]

/-- **Extract depth `d`** (the descend/return direction): the arena resource
    yields the depth-`d` window separated from the untouched rest. -/
theorem focusFrame (base : Word) (d : Nat) (hd : d ≤ maxCallDepth) (h : PartialState)
    (hp : CallFramePhase.phaseDView base h) :
    (prefixFrames base d ** frameWindow base d ** suffixFrames base d) h :=
  (phaseDView_focus base d hd) ▸ hp

/-- **Re-absorb depth `d`** (the post-descend/return direction): whatever
    concrete `frameStride` bytes now sit in slot `d` weaken back into the arena
    resource (`bytesRegion → anyBytes` composed with the tiling), the rest
    still framed untouched. -/
theorem unfocusFrame (base : Word) (d : Nat) (hd : d ≤ maxCallDepth)
    (bs : List (BitVec 8)) (hlen : bs.length = frameStride) (h : PartialState)
    (hp : (prefixFrames base d ** bytesRegion (frameBase base d) bs
            ** suffixFrames base d) h) :
    CallFramePhase.phaseDView base h := by
  rw [phaseDView_focus base d hd]
  refine sepConj_mono_right (sepConj_mono_left (fun h' hx => ?_)) h hp
  have hw := bytesRegion_anyBytes _ bs h' hx
  rw [hlen] at hw
  exact hw

-- ============================================================================
-- 3. Intra-frame carving: one window into its named sub-regions
-- ============================================================================

/-- The operand-stack window including both guard bands
    (`frameStackGuardBytes + frameStackBytes + frameStackGuardBytes`). -/
def frameStackWindowBytes : Nat := frameStackGuardBytes + frameStackBytes + frameStackGuardBytes

/-- Trailing intra-frame pad: stride bytes past the used sub-regions. -/
def frameIntraPadBytes : Nat := frameStride - frameUsedBytes

/-- Intra-frame tiling segment sizes: memory / stack(+guards) / returndata /
    env / pc / codebase / meta, then the pad — summing to `frameStride`. -/
def frameSegs : List Nat :=
  [frameMemBytes, frameStackWindowBytes, frameReturndataBytes, frameEnvBytes,
    framePcBytes, frameCodebaseBytes, frameMetaBytes, frameIntraPadBytes]

theorem frameSegs_sum : frameSegs.sum = frameStride := by decide

theorem frameSegs_dvd8 : ∀ s ∈ frameSegs, 8 ∣ s := by decide

/-! ### Named per-component accessor assertions (offsets from `CallFrameLayout`).
    Bead `.56`'s descend/return contracts state their pre/posts directly in
    these. -/

def frameMemWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 frameMemOff) frameMemBytes

def frameStackWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 frameStackGuardLoOff) frameStackWindowBytes

def frameReturndataWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 frameReturndataOff) frameReturndataBytes

def frameEnvWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 frameEnvOff) frameEnvBytes

def framePcWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 framePcOff) framePcBytes

def frameCodebaseWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 frameCodebaseOff) frameCodebaseBytes

def frameMetaWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 frameMetaOff) frameMetaBytes

def framePadWindow (base : Word) (d : Nat) : Assertion :=
  anyBytes (frameBase base d + BitVec.ofNat 64 frameUsedBytes) frameIntraPadBytes

/-- The window at depth `d` as the `anyTilesAt` tiling of its sub-regions. -/
theorem frameWindow_intra (base : Word) (d : Nat) :
    frameWindow base d = anyTilesAt (frameBase base d) 0 frameSegs := by
  unfold frameWindow
  rw [show frameStride = frameSegs.sum from frameSegs_sum.symm]
  exact anyBytes_eq_anyTiles (frameBase base d) frameSegs frameSegs_dvd8

/-- **Intra-frame carving**: one per-depth window unfolds to its named
    sub-region windows at the `CallFrameLayout` offsets (plus the pad). -/
theorem frameWindow_components (base : Word) (d : Nat) :
    frameWindow base d
      = (frameMemWindow base d ** frameStackWindow base d
        ** frameReturndataWindow base d ** frameEnvWindow base d
        ** framePcWindow base d ** frameCodebaseWindow base d
        ** frameMetaWindow base d ** framePadWindow base d) := by
  rw [frameWindow_intra]
  simp only [frameSegs, anyTilesAt, sepConj_emp_right',
    frameMemWindow, frameStackWindow, frameReturndataWindow, frameEnvWindow,
    framePcWindow, frameCodebaseWindow, frameMetaWindow, framePadWindow,
    frameStackWindowBytes, frameMemOff, frameStackGuardLoOff, frameStackLowOff,
    frameStackTopOff, frameStackGuardHiOff, frameReturndataOff, frameEnvOff,
    framePcOff, frameCodebaseOff, frameMetaOff, frameUsedBytes,
    frameMemBytes, frameStackGuardBytes, frameStackBytes, frameReturndataBytes,
    frameEnvBytes, framePcBytes, frameCodebaseBytes, frameMetaBytes]

-- ============================================================================
-- 4. `encodesFrame`: the suspended-parent frame relation (SHAPE)
-- ============================================================================

/-- Minimal per-frame abstract state (strategy §4 names stack / pc / codebase).
    Bead `.56` will extend this (return offset/len, static/create flags, …). -/
structure FrameState where
  stack : List Word
  pc : Word
  codebase : Word

/-- Little-endian dword byte-split of a `Word` (length 8; `framePcBytes`). -/
def dwordBytes (w : Word) : List (BitVec 8) :=
  List.ofFn (fun i : Fin 8 => (w >>> (8 * i.val)).setWidth 8)

theorem dwordBytes_length (w : Word) : (dwordBytes w).length = 8 := by
  simp [dwordBytes]

/-- Placeholder stack-window serialization (SHAPE only; total, fixed length
    `frameStackWindowBytes`).  Bead `.56` fixes the concrete stack encoding —
    all this module needs is that a stack pins a `frameStackWindowBytes`-byte
    region so the encoded frame tiles the window. -/
def stackWindowBytes (stk : List Word) : List (BitVec 8) :=
  (stk.flatMap dwordBytes ++ List.replicate frameStackWindowBytes 0).take frameStackWindowBytes

theorem stackWindowBytes_length (stk : List Word) :
    (stackWindowBytes stk).length = frameStackWindowBytes := by
  simp only [stackWindowBytes, List.length_take, List.length_append, List.length_replicate]
  omega

/-- **The suspended-parent frame relation** (strategy §4): at depth `d`, the
    frame's saved pc/codebase dwords are PINNED as concrete `bytesRegion`s at
    `framePcOff`/`frameCodebaseOff` and its stack window is pinned to the
    encoded stack; everything else (memory, returndata, env, meta, pad) is
    havoc'd.  No existential over the frame state escapes — the fields are
    pinned through `bytesRegion`. -/
def encodesFrame (base : Word) (d : Nat) (fr : FrameState) : Assertion :=
  frameMemWindow base d
  ** bytesRegion (frameBase base d + BitVec.ofNat 64 frameStackGuardLoOff)
        (stackWindowBytes fr.stack)
  ** frameReturndataWindow base d
  ** frameEnvWindow base d
  ** bytesRegion (frameBase base d + BitVec.ofNat 64 framePcOff) (dwordBytes fr.pc)
  ** bytesRegion (frameBase base d + BitVec.ofNat 64 frameCodebaseOff) (dwordBytes fr.codebase)
  ** frameMetaWindow base d
  ** framePadWindow base d

/-- **An encoded frame is a focused window**: the pinned pc/codebase/stack
    bytes weaken (`bytesRegion → anyBytes`) into the havoc'd `frameWindow`, so a
    descend/return proof can splice an `encodesFrame` in wherever a
    `frameWindow` is framed.  This is the `⊸`-into-havoc lemma bead `.56` needs. -/
theorem encodesFrame_focus (base : Word) (d : Nat) (fr : FrameState) (h : PartialState)
    (henc : encodesFrame base d fr h) : frameWindow base d h := by
  have wkStack : ∀ h', bytesRegion (frameBase base d + BitVec.ofNat 64 frameStackGuardLoOff)
      (stackWindowBytes fr.stack) h' → frameStackWindow base d h' := by
    intro h' hx
    have hw := bytesRegion_anyBytes _ (stackWindowBytes fr.stack) h' hx
    rw [stackWindowBytes_length] at hw
    exact hw
  have wkPc : ∀ h', bytesRegion (frameBase base d + BitVec.ofNat 64 framePcOff)
      (dwordBytes fr.pc) h' → framePcWindow base d h' := by
    intro h' hx
    have hw := bytesRegion_anyBytes _ (dwordBytes fr.pc) h' hx
    rw [dwordBytes_length] at hw
    exact hw
  have wkCb : ∀ h', bytesRegion (frameBase base d + BitVec.ofNat 64 frameCodebaseOff)
      (dwordBytes fr.codebase) h' → frameCodebaseWindow base d h' := by
    intro h' hx
    have hw := bytesRegion_anyBytes _ (dwordBytes fr.codebase) h' hx
    rw [dwordBytes_length] at hw
    exact hw
  rw [frameWindow_components]
  exact sepConj_mono (fun _ hx => hx)
    (sepConj_mono wkStack (sepConj_mono (fun _ hx => hx) (sepConj_mono (fun _ hx => hx)
      (sepConj_mono wkPc (sepConj_mono wkCb (fun _ hx => hx)))))) h henc

/-- **Distinct depths are disjoint by construction** (free from the tiling;
    stated explicitly as the sanity lemma `.56` cites).  For `d < d' ≤ 1024`
    the two windows appear as separate `**`-conjoined tiles of the arena, so
    they own disjoint sub-states. -/
theorem frameWindows_separate (base : Word) (d d' : Nat) (hlt : d < d')
    (hd' : d' ≤ maxCallDepth) :
    ∃ A B C : Assertion,
      CallFramePhase.phaseDView base
        = (A ** frameWindow base d ** B ** frameWindow base d' ** C) := by
  refine ⟨prefixFrames base d,
    anyTilesAt base ((d + 1) * frameStride) (List.replicate (d' - (d + 1)) frameStride),
    anyTilesAt base ((d' + 1) * frameStride)
      (List.replicate (frameSlotCount - (d' + 1)) frameStride), ?_⟩
  rw [phaseDView_focus base d (by omega), suffixFrames,
    anyTilesAt_replicate_focus_at base frameStride ((d + 1) * frameStride)
      (frameSlotCount - (d + 1)) (d' - (d + 1)) (by unfold frameSlotCount; omega)]
  rw [show frameSlotCount - (d + 1) - (d' - (d + 1) + 1) = frameSlotCount - (d' + 1) from
      by omega,
    show (d + 1) * frameStride + (d' - (d + 1)) * frameStride = d' * frameStride from
      by rw [← Nat.add_mul]; congr 1; omega,
    show (d + 1) * frameStride + (d' - (d + 1) + 1) * frameStride = (d' + 1) * frameStride from
      by rw [← Nat.add_mul]; congr 1; omega]
  simp only [frameWindow, frameBase]

end CallFrameWindows
end EvmAsm.Codegen
