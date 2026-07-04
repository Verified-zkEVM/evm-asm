/-
  EvmAsm.Rv64.SAsm.HandleFocus

  Data-dependent writable-window embedding for `callRegS` dispatch
  (bead evm-asm-4ch8f.49.1).

  `Stmt.callRegS` soundness (`StmtSoundCall.lean`, via `Stmt.CalleesIn`)
  forces every callee handle to declare the *same* writable region as its
  caller: `h.rw = caller.rw`, FIXED.  But the interpreter dispatch site
  (`docs/4ch8f-interp-strategy.md`) runs the one `callRegS` at a *different*
  value-stack top `x12` every loop iteration, and the packaged opcode
  handles (`Codegen/Proofs/HandlerHandles*.lean`) are verified against a
  MINIMAL window `⟨sp, 64⟩` whose base `sp` is a fixed parameter.  A fixed
  window cannot sit at a per-iteration `x12`.

  `FnHandle.widenRw` (`HandleWiden.lean`) does not help: it embeds a
  sub-window at a *fixed* byte offset (`preB`/`sufB` are `def` parameters),
  and it is stated for the non-snapshot `FnHandle` — which cannot express a
  state-transforming callee's exit-as-a-function-of-entry post (strategy
  §0), the very reason the dispatch handles are `FnHandleS`.

  This module supplies the missing piece: **`FnHandleS.focus`** repackages a
  *family* of window handles — `family sp : FnHandleS` verified against
  `⟨sp, winLen⟩` for every `sp` — as ONE handle over a FIXED enclosing arena
  `arena`, whose `pre` focuses the operative `winLen`-byte sub-window at the
  register value `x12` (data-dependent *within* the fixed region), whose
  `post` pins the window results as a function of the entry snapshot and
  `x12`, and whose arena remainder (the bytes below `x12` and above
  `x12+winLen`) is FRAMED — pinned to its entry contents.  The varying
  quantity is now *data* (the register `x12`) inside a fixed `rw`, so
  `h.rw = caller.rw` holds; nothing weakens `callRegS`.

  The soundness reuses the `bytesRegion` window split `asrtM_window`
  (`HandleWiden.lean`) at a per-snapshot offset `(x12 - arena.base)`, plus a
  one-off bridge `Reach.exact = Reach.window (Reach.exact …)` so the family's
  `Reach.exact`-entry triple frames into the arena.

  `FocusDemo` composes `callRegS` to a `focus`-ed handle at TWO distinct
  `x12` in one `Fn.SpecR` (an `ite` picks the window base), discharging the
  real dispatch-site `.pre` VC at both — the anti-"secretly-fixed-window"
  witness.
-/

import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm

open Stmt

-- ============================================================================
-- List reassembly at a data-dependent split
-- ============================================================================

/-- Reassemble a list from a prefix, a mid-window, and a suffix cut at an
    arbitrary (data-dependent) offset — the list-level identity behind the
    focus embedding.  `take off ++ (drop off).take winLen ++ drop (off+winLen)`
    recovers the whole list whenever the window fits. -/
theorem take_take_drop_reassemble (xs : List (BitVec 8)) (off winLen : Nat) :
    xs.take off ++ ((xs.drop off).take winLen) ++ xs.drop (off + winLen) = xs := by
  rw [List.append_assoc, ← List.drop_drop,
    List.take_append_drop, List.take_append_drop]

-- ============================================================================
-- `Reach.exact` as a degenerate window
-- ============================================================================

/-- The one-point reach at a full byte list equals the window reach at the
    sub-list: pinning `ws₀` exactly is the same as framing the two ends and
    pinning the middle `winLen`-byte window.  This bridges the family's
    `Reach.exact`-entry triple (stated on the window) to the arena entry. -/
theorem reach_exact_eq_window (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (off winLen : Nat) (hle : off + winLen ≤ ws₀.length) :
    Reach.exact rf₀ ws₀ A₀
      = Reach.window (ws₀.take off) (ws₀.drop (off + winLen)) winLen
          (Reach.exact rf₀ ((ws₀.drop off).take winLen) A₀) := by
  have hwl : ((ws₀.drop off).take winLen).length = winLen := by
    rw [List.length_take, List.length_drop]; omega
  funext rf ws A
  apply propext
  constructor
  · rintro ⟨hrf, hws, hA⟩
    exact ⟨(ws₀.drop off).take winLen, hwl,
      by rw [hws]; exact (take_take_drop_reassemble ws₀ off winLen).symm,
      hrf, rfl, hA⟩
  · rintro ⟨win, hwinl, hws, hrf, hwin, hA⟩
    exact ⟨hrf, by rw [hws, hwin, take_take_drop_reassemble], hA⟩

-- ============================================================================
-- The data-dependent focus embedding
-- ============================================================================

/-- Byte offset of the value-stack top `x12` within the arena. -/
def focusOff (arena : RwRegion) (rf : RegFile) : Nat :=
  (rf.get .x12 - arena.base).toNat

/-- Call-site obligation of a `focus`-ed handle: the `winLen`-byte window at
    `x12` sits (dword-aligned) inside the arena, and the family member at
    `sp = x12` accepts the focused window.  Admits ANY in-arena `x12` — the
    window position is data, not a pinned constant. -/
def focusPre (family : Word → FnHandleS) (arena : RwRegion) (winLen : Nat) :
    Reach :=
  fun rf ws A =>
    focusOff arena rf + winLen ≤ arena.len ∧ 8 ∣ focusOff arena rf
    ∧ (family (rf.get .x12)).pre rf ((ws.drop (focusOff arena rf)).take winLen) A

/-- Snapshot-parameterized guarantee of a `focus`-ed handle: the window at
    `x12` is transformed exactly as the family member's post dictates
    (a function of the entry snapshot), while the arena bytes outside the
    window are pinned to their entry contents (`Reach.window` frames the
    ends). -/
def focusPost (family : Word → FnHandleS) (arena : RwRegion) (winLen : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ =>
    Reach.window (ws₀.take (focusOff arena rf₀))
      (ws₀.drop (focusOff arena rf₀ + winLen)) winLen
      ((family (rf₀.get .x12)).post rf₀
        ((ws₀.drop (focusOff arena rf₀)).take winLen) A₀)

/- Keep the focus pre/post folded during the big `isDefEq` steps of the
   soundness proof and of any consumer (`.49.d`): they carry the whole inner
   family post as a subterm. -/
attribute [irreducible] focusPre focusPost

/-- **Data-dependent window embedding.**  Given a family of window handles
    `family sp` — one code/entry, but each verified against its own
    `⟨sp, winLen⟩` window (the `.10.1` shape `evmAddHandle base ·`) — package
    ONE handle over the fixed enclosing arena `arena` that dispatches the
    same code at a per-call `x12`.  `h.rw = arena` is fixed (satisfying the
    `callRegS` constraint); the window position rides in the register `x12`.

    All family members must share code placement (`entry`/`code`/`nSteps`/
    read-only `region`) and differ only in their window base
    (`(family sp).rw = ⟨sp, winLen⟩`) and their `pre`/`post` — exactly how
    the `.10.1` handles are parameterized. -/
def FnHandleS.focus (family : Word → FnHandleS) (arena : RwRegion)
    (winLen : Nat) (entry : Word) (code : CodeReq) (nSteps : Nat)
    (region : Region)
    (hentry : ∀ sp, (family sp).entry = entry)
    (hcode : ∀ sp, (family sp).code = code)
    (hnsteps : ∀ sp, (family sp).nSteps = nSteps)
    (hregion : ∀ sp, (family sp).region = region)
    (hrw : ∀ sp, (family sp).rw = ⟨sp, winLen⟩)
    (hwin8 : 8 ∣ winLen) : FnHandleS where
  entry := entry
  code := code
  nSteps := nSteps
  region := region
  rw := arena
  pre := focusPre family arena winLen
  post := focusPost family arena winLen
  sound := by
    intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
    -- Unpack the focus precondition.
    rw [focusPre] at hpre
    obtain ⟨hfit, hoff8, hinner⟩ := hpre
    set v : Word := rf₀.get .x12 with hv
    set off : Nat := focusOff arena rf₀ with hoffdef
    set win₀ : List (BitVec 8) := (ws₀.drop off).take winLen with hwin0def
    have hwslen : ws₀.length = arena.len := hlen
    have hoffle : off + winLen ≤ ws₀.length := by rw [hwslen]; exact hfit
    have hwin0len : win₀.length = winLen := by
      rw [hwin0def, List.length_take, List.length_drop]; omega
    -- offset ↔ register identity: base + off = x12.
    have hvbase : v = arena.base + BitVec.ofNat 64 off := by
      rw [hoffdef, focusOff, ← hv]; bv_omega
    have hpreBlen : (ws₀.take off).length = off := by
      rw [List.length_take]; omega
    -- The family member at sp = v, on the focused window.
    have hsv := (family v).sound rf₀ win₀ A₀
      (by rw [hrw v]; exact hwin0len) hApc hinner ret halign
    rw [hnsteps v, hentry v, hcode v, hregion v, hrw v] at hsv
    -- Frame the two arena ends around the family triple.
    set preB : List (BitVec 8) := ws₀.take off with hpreBdef
    set sufB : List (BitVec 8) := ws₀.drop (off + winLen) with hsufBdef
    have hframe := cpsTripleWithin_frameR
      (bytesRegion arena.base preB **
        bytesRegion ((⟨v, winLen⟩ : RwRegion).base
          + BitVec.ofNat 64 (⟨v, winLen⟩ : RwRegion).len) sufB)
      (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
      hsv
    -- The window split, instantiated at the per-snapshot offset.
    have hbase : (⟨v, winLen⟩ : RwRegion).base
        = arena.base + BitVec.ofNat 64 preB.length := by
      show v = arena.base + BitVec.ofNat 64 preB.length
      rw [hpreBdef, hpreBlen]; exact hvbase
    have hlen' : preB.length + (⟨v, winLen⟩ : RwRegion).len + sufB.length
        = arena.len := by
      show preB.length + winLen + sufB.length = arena.len
      rw [hpreBdef, hsufBdef, hpreBlen, List.length_drop, ← hwslen]; omega
    have hpre8 : 8 ∣ preB.length := by rw [hpreBdef, hpreBlen]; exact hoff8
    have hwin8' : 8 ∣ (⟨v, winLen⟩ : RwRegion).len := hwin8
    refine cpsTripleWithin_weaken ?_ ?_ hframe
    · -- pre: arena `Reach.exact` = framed window `Reach.exact`
      intro hp hh
      rw [reach_exact_eq_window rf₀ ws₀ A₀ off winLen hoffle,
        ← hpreBdef, ← hsufBdef, ← hwin0def,
        asrtM_window region arena ⟨v, winLen⟩ preB sufB
          (Reach.exact rf₀ win₀ A₀) hbase hlen' hpre8 hwin8',
        ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret)
          (asrtM region ⟨v, winLen⟩ (Reach.exact rf₀ win₀ A₀))
          (bytesRegion arena.base preB **
            bytesRegion ((⟨v, winLen⟩ : RwRegion).base
              + BitVec.ofNat 64 (⟨v, winLen⟩ : RwRegion).len) sufB)] at hh
      exact hh
    · -- post: framed window post = arena `focusPost`
      intro hp hh
      rw [focusPost, ← hoffdef, ← hpreBdef, ← hsufBdef, ← hwin0def, ← hv,
        asrtM_window region arena ⟨v, winLen⟩ preB sufB
          ((family v).post rf₀ win₀ A₀) hbase hlen' hpre8 hwin8',
        ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret)
          (asrtM region ⟨v, winLen⟩ ((family v).post rf₀ win₀ A₀))
          (bytesRegion arena.base preB **
            bytesRegion ((⟨v, winLen⟩ : RwRegion).base
              + BitVec.ofNat 64 (⟨v, winLen⟩ : RwRegion).len) sufB)]
      exact hh

end SAsm
end EvmAsm.Rv64
