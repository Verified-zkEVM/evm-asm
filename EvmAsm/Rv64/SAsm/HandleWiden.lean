/-
  EvmAsm.Rv64.SAsm.HandleWiden

  Per-frame writable sub-regions for deep call trees (bead evm-asm-4ch8f.3).

  `Stmt.CalleesIn` requires a callee to declare the *same* writable region
  as its caller, so today a whole call tree shares one `RwRegion` and every
  callee's contract must thread the caller's private state (e.g. the
  ra-spill slot) as ghost data — `ExamplesVc.leafFn v` carries the caller's
  spilled return address `v` through its own pre/post for no reason of its
  own.  That coupling multiplies contract surface at every tree level and
  is the blocker called out in docs/sasm-design.md §3.6 ("per-frame
  sub-regions are future work").

  `FnHandle.widenRw` removes the coupling: a callee verified against its
  own *window* — a dword-aligned sub-range of the caller's writable region —
  is repackaged as a handle over the caller's full region.  The bytes
  outside the window (`preB`/`sufB`) ride along as a frame: the widened
  pre/postcondition pins them to their entry values *by construction*, so
  the caller's private slots survive every call without the callee's
  contract ever mentioning them.  The caller instantiates `preB`/`sufB`
  with its own ghost values at each call site (they are parameters of the
  widened handle, exactly like the ghost indices of `Fn.toHandleR`).

  `WidenDemo` re-plays the ra-spill two-level tree of `ExamplesVc` with the
  leaf owning only its own 8-byte window: the leaf's contract mentions
  neither the caller's slot address nor its contents, and the caller's
  `.post` VC recovers slot preservation from the window shape alone.
-/

import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Splitting a byte region at a dword boundary
-- ============================================================================

/-- Push a `+ ofNat` past a `+ ofNat` (word addition needs no overflow side
    conditions; `ofNat` is addition modulo `2^64`). -/
private theorem add_ofNat_add (b : Word) (m k : Nat) :
    (b + BitVec.ofNat 64 m) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (m + k) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  conv_rhs => rw [Nat.add_mod]

private theorem bytesRegion_append_aux (ys : List (BitVec 8)) :
    ∀ (n : Nat) (b : Word) (xs : List (BitVec 8)), xs.length = 8 * n →
      bytesRegion b (xs ++ ys)
        = (bytesRegion b xs ** bytesRegion (b + BitVec.ofNat 64 xs.length) ys)
  | 0, b, xs, hn => by
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp only [List.nil_append, bytesRegion_nil, sepConj_emp_left',
        List.length_nil]
      congr 1
      bv_omega
  | n + 1, b, xs, hn => by
      have hlen : xs.length = 8 * n + 8 := by omega
      have hne : xs ≠ [] := by
        intro h
        rw [h] at hlen
        simp at hlen
      have hnecat : xs ++ ys ≠ [] := by
        intro h
        exact hne (List.append_eq_nil_iff.mp h).1
      rw [bytesRegion_eq_cons b (xs ++ ys) hnecat,
        List.take_append_of_le_length (by omega),
        List.drop_append_of_le_length (by omega),
        bytesRegion_append_aux ys n (b + 8) (xs.drop 8)
          (by rw [List.length_drop]; omega),
        List.length_drop,
        show (b + 8) + BitVec.ofNat 64 (xs.length - 8)
            = b + BitVec.ofNat 64 xs.length from by
          rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, add_ofNat_add,
            show 8 + (xs.length - 8) = xs.length from by omega],
        ← sepConj_assoc',
        ← bytesRegion_eq_cons b xs hne]

/-- **Split a byte region at a dword boundary**: a region holding `xs ++ ys`
    with `8 ∣ xs.length` is the separating conjunction of the two
    sub-regions.  This is the frame seam for per-frame writable windows. -/
theorem bytesRegion_append (b : Word) (xs ys : List (BitVec 8))
    (h8 : 8 ∣ xs.length) :
    bytesRegion b (xs ++ ys)
      = (bytesRegion b xs ** bytesRegion (b + BitVec.ofNat 64 xs.length) ys) := by
  obtain ⟨n, hn⟩ := h8
  exact bytesRegion_append_aux ys n b xs hn

-- ============================================================================
-- The window view of a reachable set
-- ============================================================================

/-- The caller-side view of a callee reach: the writable bytes are the fixed
    `preB`/`sufB` sandwiching a `winLen`-byte window that the inner reach
    governs.  `preB`/`sufB` are chosen by the caller (typically its own
    ghost state — e.g. the spilled `ra`); the callee never sees them. -/
def Reach.window (preB sufB : List (BitVec 8)) (winLen : Nat) (r : Reach) : Reach :=
  fun rf ws A => ∃ win, win.length = winLen ∧ ws = preB ++ win ++ sufB ∧ r rf win A

/-- The heap decomposition behind `Reach.window`: the widened region's bytes
    split into the callee's window plus the two framed outside pieces. -/
private theorem window_heap_split (rw' rwC : RwRegion)
    (preB win sufB : List (BitVec 8)) (rf : RegFile) (A : Assertion)
    (hbase : rwC.base = rw'.base + BitVec.ofNat 64 preB.length)
    (hwl : win.length = rwC.len)
    (hpre8 : 8 ∣ preB.length) (hwin8 : 8 ∣ rwC.len) :
    ((regFileIs rf ** bytesRegion rw'.base (preB ++ win ++ sufB)) ** A)
      = ((((regFileIs rf) ** bytesRegion rwC.base win) ** A) **
         (bytesRegion rw'.base preB **
          bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB)) := by
  rw [bytesRegion_append rw'.base (preB ++ win) sufB
      (by rw [List.length_append, hwl]; exact Nat.dvd_add hpre8 hwin8),
    bytesRegion_append rw'.base preB win hpre8,
    List.length_append, hwl,
    show rw'.base + BitVec.ofNat 64 preB.length = rwC.base from hbase.symm,
    show rw'.base + BitVec.ofNat 64 (preB.length + rwC.len)
        = rwC.base + BitVec.ofNat 64 rwC.len from by
      rw [hbase, add_ofNat_add],
    sepConj_comm' (bytesRegion rw'.base preB) (bytesRegion rwC.base win),
    sepConj_assoc' (bytesRegion rwC.base win) (bytesRegion rw'.base preB)
      (bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB),
    ← sepConj_assoc' (regFileIs rf) (bytesRegion rwC.base win)
      (bytesRegion rw'.base preB
        ** bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB),
    sepConj_assoc' ((regFileIs rf) ** bytesRegion rwC.base win)
      (bytesRegion rw'.base preB
        ** bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB) A,
    sepConj_comm'
      (bytesRegion rw'.base preB
        ** bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB) A,
    ← sepConj_assoc' ((regFileIs rf) ** bytesRegion rwC.base win) A
      (bytesRegion rw'.base preB
        ** bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB)]

/-- `asrtOf` through a window: the widened region's embedding is the
    callee's own embedding with the outside bytes framed alongside. -/
theorem asrtOf_window (rw' rwC : RwRegion) (preB sufB : List (BitVec 8))
    (r : Reach)
    (hbase : rwC.base = rw'.base + BitVec.ofNat 64 preB.length)
    (hlen : preB.length + rwC.len + sufB.length = rw'.len)
    (hpre8 : 8 ∣ preB.length) (hwin8 : 8 ∣ rwC.len) :
    asrtOf rw' (Reach.window preB sufB rwC.len r)
      = ((asrtOf rwC r) **
         (bytesRegion rw'.base preB **
          bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB)) := by
  funext hp
  apply propext
  constructor
  · rintro ⟨rf, ws, A, hlws, hApc, ⟨win, hwl, rfl, hr⟩, hsts⟩
    rw [window_heap_split rw' rwC preB win sufB rf A hbase hwl hpre8 hwin8]
      at hsts
    exact sepConj_mono_left
      (fun hq hx => ⟨rf, win, A, hwl, hApc, hr, hx⟩) hp hsts
  · rintro ⟨h1, h2, hd, hu, ⟨rf, win, A, hwl, hApc, hr, hsts1⟩, hF⟩
    refine ⟨rf, preB ++ win ++ sufB, A, ?_, hApc, ⟨win, hwl, rfl, hr⟩, ?_⟩
    · simp only [List.length_append, hwl]
      omega
    · rw [window_heap_split rw' rwC preB win sufB rf A hbase hwl hpre8 hwin8]
      exact ⟨h1, h2, hd, hu, hsts1, hF⟩

/-- `asrtM` through a window (the read-only region rides along unchanged). -/
theorem asrtM_window (reg : Region) (rw' rwC : RwRegion)
    (preB sufB : List (BitVec 8)) (r : Reach)
    (hbase : rwC.base = rw'.base + BitVec.ofNat 64 preB.length)
    (hlen : preB.length + rwC.len + sufB.length = rw'.len)
    (hpre8 : 8 ∣ preB.length) (hwin8 : 8 ∣ rwC.len) :
    asrtM reg rw' (Reach.window preB sufB rwC.len r)
      = ((asrtM reg rwC r) **
         (bytesRegion rw'.base preB **
          bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB)) := by
  show (asrtOf rw' (Reach.window preB sufB rwC.len r)
      ** bytesRegion reg.base reg.bytes) = _
  rw [asrtOf_window rw' rwC preB sufB r hbase hlen hpre8 hwin8,
    sepConj_assoc' (asrtOf rwC r)
      (bytesRegion rw'.base preB
        ** bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB)
      (bytesRegion reg.base reg.bytes),
    sepConj_comm'
      (bytesRegion rw'.base preB
        ** bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB)
      (bytesRegion reg.base reg.bytes),
    ← sepConj_assoc' (asrtOf rwC r) (bytesRegion reg.base reg.bytes)
      (bytesRegion rw'.base preB
        ** bytesRegion (rwC.base + BitVec.ofNat 64 rwC.len) sufB)]
  rfl

-- ============================================================================
-- Widening a callee handle to the caller's writable region
-- ============================================================================

/-- **Per-frame writable sub-regions**: repackage a callee verified against
    its own writable window as a callee over the caller's full region
    `rw'`.  The window sits at byte offset `preB.length` (dword-aligned,
    dword-multiple length); the bytes outside it — `preB` before, `sufB`
    after — are framed across the call, so the widened postcondition pins
    them to their entry values without any cooperation from the callee's
    contract.

    The caller instantiates `preB`/`sufB` per call site with its own ghost
    state (e.g. `dwordBytes v` for its spilled return address), the same
    way `Fn.toHandleR` threads its ghost index. -/
def FnHandle.widenRw (h : FnHandle) (rw' : RwRegion)
    (preB sufB : List (BitVec 8))
    (hbase : h.rw.base = rw'.base + BitVec.ofNat 64 preB.length)
    (hlen : preB.length + h.rw.len + sufB.length = rw'.len)
    (hpre8 : 8 ∣ preB.length) (hwin8 : 8 ∣ h.rw.len) : FnHandle where
  entry := h.entry
  code := h.code
  nSteps := h.nSteps
  region := h.region
  rw := rw'
  pre := Reach.window preB sufB h.rw.len h.pre
  post := Reach.window preB sufB h.rw.len h.post
  sound := by
    intro ret halign
    have hf := cpsTripleWithin_frameR
      (bytesRegion rw'.base preB **
        bytesRegion (h.rw.base + BitVec.ofNat 64 h.rw.len) sufB)
      (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
      (h.sound ret halign)
    refine cpsTripleWithin_weaken ?_ ?_ hf
    · intro hp hh
      rw [asrtM_window h.region rw' h.rw preB sufB h.pre hbase hlen hpre8 hwin8,
        ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret) (asrtM h.region h.rw h.pre)
          (bytesRegion rw'.base preB
            ** bytesRegion (h.rw.base + BitVec.ofNat 64 h.rw.len) sufB)] at hh
      exact hh
    · intro hp hh
      rw [asrtM_window h.region rw' h.rw preB sufB h.post hbase hlen hpre8 hwin8,
        ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret) (asrtM h.region h.rw h.post)
          (bytesRegion rw'.base preB
            ** bytesRegion (h.rw.base + BitVec.ofNat 64 h.rw.len) sufB)]
      exact hh

-- ============================================================================
-- Widening a callee handle to the caller's read-only region
-- ============================================================================

/-- `asrtM` through a read-only sub-slice: the widened region's assertion is
    the callee's own with the outside bytes framed alongside.  Simpler than
    `asrtM_window` because ro contents live in the region descriptor, not
    the symbolic state — no existential moves. -/
theorem asrtM_widenRo (reg' regC : Region) (rw : RwRegion)
    (preR sufR : List (BitVec 8)) (r : Reach)
    (hbytes : reg'.bytes = preR ++ regC.bytes ++ sufR)
    (hbase : regC.base = reg'.base + BitVec.ofNat 64 preR.length)
    (hpre8 : 8 ∣ preR.length) (hmid8 : 8 ∣ regC.bytes.length) :
    asrtM reg' rw r
      = ((asrtM regC rw r) **
         (bytesRegion reg'.base preR **
          bytesRegion (regC.base + BitVec.ofNat 64 regC.bytes.length) sufR)) := by
  show (asrtOf rw r ** bytesRegion reg'.base reg'.bytes) = _
  rw [hbytes,
    bytesRegion_append reg'.base (preR ++ regC.bytes) sufR
      (by rw [List.length_append]; exact Nat.dvd_add hpre8 hmid8),
    bytesRegion_append reg'.base preR regC.bytes hpre8,
    List.length_append,
    show reg'.base + BitVec.ofNat 64 preR.length = regC.base from hbase.symm,
    show reg'.base + BitVec.ofNat 64 (preR.length + regC.bytes.length)
        = regC.base + BitVec.ofNat 64 regC.bytes.length from by
      rw [hbase, add_ofNat_add],
    sepConj_comm' (bytesRegion reg'.base preR)
      (bytesRegion regC.base regC.bytes),
    sepConj_assoc' (bytesRegion regC.base regC.bytes)
      (bytesRegion reg'.base preR)
      (bytesRegion (regC.base + BitVec.ofNat 64 regC.bytes.length) sufR),
    ← sepConj_assoc' (asrtOf rw r) (bytesRegion regC.base regC.bytes)
      (bytesRegion reg'.base preR
        ** bytesRegion (regC.base + BitVec.ofNat 64 regC.bytes.length) sufR)]
  rfl

/-- **Read-only sub-slices**: repackage a callee verified against its own
    ro slice — a dword-aligned, dword-multiple sub-range of the caller's
    read-only region — as a callee over the caller's full region.  The
    callee's pre/post pass through unchanged (ro contents live in the
    region descriptor); the bytes outside the slice are framed.

    Together with `widenRw` this lets every callee declare only the memory
    it touches: N callees reading different named slices of one buffer
    (e.g. sections of the SSZ input) compose under a single caller
    region. -/
def FnHandle.widenRo (h : FnHandle) (reg' : Region)
    (preR sufR : List (BitVec 8))
    (hbytes : reg'.bytes = preR ++ h.region.bytes ++ sufR)
    (hbase : h.region.base = reg'.base + BitVec.ofNat 64 preR.length)
    (hpre8 : 8 ∣ preR.length) (hmid8 : 8 ∣ h.region.bytes.length) : FnHandle where
  entry := h.entry
  code := h.code
  nSteps := h.nSteps
  region := reg'
  rw := h.rw
  pre := h.pre
  post := h.post
  sound := by
    intro ret halign
    have hf := cpsTripleWithin_frameR
      (bytesRegion reg'.base preR **
        bytesRegion (h.region.base + BitVec.ofNat 64 h.region.bytes.length) sufR)
      (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
      (h.sound ret halign)
    refine cpsTripleWithin_weaken ?_ ?_ hf
    · intro hp hh
      rw [asrtM_widenRo reg' h.region h.rw preR sufR h.pre hbytes hbase hpre8
          hmid8,
        ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret) (asrtM h.region h.rw h.pre)
          (bytesRegion reg'.base preR
            ** bytesRegion (h.region.base + BitVec.ofNat 64 h.region.bytes.length)
                sufR)] at hh
      exact hh
    · intro hp hh
      rw [asrtM_widenRo reg' h.region h.rw preR sufR h.post hbytes hbase hpre8
          hmid8,
        ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret) (asrtM h.region h.rw h.post)
          (bytesRegion reg'.base preR
            ** bytesRegion (h.region.base + BitVec.ofNat 64 h.region.bytes.length)
                sufR)]
      exact hh

-- ============================================================================
-- Demo: the ra-spill two-level tree with a per-frame callee window
-- ============================================================================

namespace WidenDemo

/-- The caller's writable region: its own ra-spill slot in the first dword,
    the callee's window in the second. -/
def wRw : RwRegion := ⟨0x10000, 16⟩

/-- The leaf's own writable window: the second dword of `wRw`.  The leaf is
    verified against this region ONLY — it never sees the caller's slot. -/
def wLeafRw : RwRegion := ⟨0x10008, 8⟩

/-- Leaf callee: store 5 into its window (pointer in `x13`).  Compare
    `ExamplesVc.leafFn v`: no ghost `v`, no caller slot in the contract. -/
def wLeafFn : Fn where
  name := "wleaf"
  rw := wLeafRw
  pre := fun rf _ _ => rf.get .x13 = 0x10008
  post := fun rf ws _ => rf.get .x10 = 5 ∧ rf.get .x13 = 0x10008
    ∧ ws = dwordBytes 5
  body := .block "store" [.LI .x10 5, .SD .x13 .x10 0]

private theorem wleaf_hidx : ∀ rf : RegFile, rf.get .x13 = 0x10008 →
    ((rf.get .x13 + signExtend12 (0 : BitVec 12)) - (0x10008 : Word)).toNat = 0 := by
  intro rf h
  rw [h, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  bv_omega

theorem wLeafFn_spec : wLeafFn.Spec 0x2000 := by
  have hx13' : ∀ rf : RegFile, rf.get .x13 = 0x10008 →
      (rf.set .x10 5).get .x13 = 0x10008 := by
    intro rf h
    rw [RegFile.get_set_ne rf .x10 .x13 5 (by decide)]
    exact h
  vcgen
  case wleaf.store.mem =>
    rintro rf ws A hws hx13
    have hws8 : ws.length = 8 := hws
    simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, wLeafFn,
      wLeafRw, inRw, wleaf_hidx _ (hx13' rf hx13)]
    exact ⟨trivial, ⟨by omega, by decide⟩, trivial⟩
  case wleaf.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, hx13, rfl, rfl⟩
    have hws8 : ws₀.length = 8 := hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
      storeSem, wLeafFn, wLeafRw, wleaf_hidx _ (hx13' rf₀ hx13)]
    refine ⟨?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · exact hx13' rf₀ hx13
    · rw [RegFile.get_set_self _ _ _ (by decide)]
      have hs := setBytes_slot ws₀ (dwordBytes 5) 0
        (by rw [length_dwordBytes]; omega)
      rw [List.drop_zero, length_dwordBytes] at hs
      conv_lhs => rw [← List.take_of_length_le
        (l := setBytes ws₀ 0 (dwordBytes 5)) (i := 8)
        (by rw [length_setBytes]; omega)]
      exact hs

/-- The leaf as a callee at `0x2000`, against its OWN window only. -/
def wLeafHandle : FnHandle :=
  wLeafFn.toHandle 0x2000 wLeafFn_spec
    ((by decide : 4 * (wLeafFn.body.size + 1) ≤ 2 ^ 64))

/-- The leaf widened to the caller's region: the caller's slot bytes
    (`dwordBytes v`, its spilled return address) are framed across the
    call.  Ghost `v` enters through the WIDENING, not the leaf. -/
def wLeafWide (v : Word) : FnHandle :=
  wLeafHandle.widenRw wRw (dwordBytes v) []
    (by rw [length_dwordBytes]; decide)
    (by rw [length_dwordBytes]; decide)
    (by rw [length_dwordBytes])
    (by decide)

/-- The mid-level caller: call the widened leaf.  Ghost `v` is its own
    spilled return address, living in the first dword (`x13 - 8`). -/
def wCallerRVFn (v : Word) : Fn where
  name := "wcaller"
  rw := wRw
  pre := fun rf ws _ => rf.get .x13 = 0x10008 ∧ ws.length = 16
    ∧ ws.take 8 = dwordBytes v
  post := fun rf ws _ => rf.get .x10 = 5 ∧ rf.get .x13 = 0x10008
    ∧ ws.length = 16 ∧ ws.take 8 = dwordBytes v
  body := .call "wleaf" (wLeafWide v)

/-- The handle-facing view: no ghost anywhere. -/
def wCallerRFn : Fn :=
  { wCallerRVFn 0 with
    pre := fun rf _ _ => rf.get .x13 = 0x10008
    post := fun rf _ _ => rf.get .x10 = 5 ∧ rf.get .x13 = 0x10008 }

/-- Ambient code: the caller's spill-wrapped code at `0x1000` plus the
    leaf's (the widened handle shares the leaf's code). -/
def wCallerRCr : CodeReq :=
  (CodeReq.ofProg 0x1000 (wCallerRFn.programRetR .x13 (-8) 0x1000)).union
    wLeafHandle.code

theorem wCallerRVFn_spec (v : Word) :
    (wCallerRVFn v).SpecR (0x1000 + 4) wCallerRCr := by
  vcgen
  case region =>
    exact ⟨Region.empty_wf, (by decide : wRw.wf)⟩
  case code =>
    intro a i h
    have h' : CodeReq.ofProg 0x1000 (wCallerRFn.programRetR .x13 (-8) 0x1000)
        a = some i := by
      show CodeReq.ofProg 0x1000 (Instr.SD .x13 .x1 (-8) ::
        (wCallerRFn.body.flatten (0x1000 + 4)
          ++ [Instr.LD .x1 .x13 (-8), Instr.JALR .x0 .x1 0])) a = some i
      apply ofProg_cons_tail
        ((by decide : 4 * ((wCallerRFn.body.flatten (0x1000 + 4)
          ++ [Instr.LD .x1 .x13 (-8), Instr.JALR .x0 .x1 0]).length + 1) ≤ 2 ^ 64))
      apply ofProg_mono_left
      exact h
    simp only [wCallerRCr, CodeReq.union, h']
  case callees =>
    refine ⟨?_, rfl, rfl⟩
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hlen : (wLeafFn.programRet 0x2000).length = 3 := by decide
    rw [hlen] at hk
    simp only [wCallerRCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000 (wCallerRFn.programRetR .x13 (-8) 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hlen' : (wCallerRFn.programRetR .x13 (-8) 0x1000).length = 4 := by
        decide
      rw [hlen'] at hk'
      bv_omega
  case calls =>
    have h0 : (wCallerRVFn 0).body.callsOk (0x1000 + 4) :=
      ⟨by decide, by decide, by decide⟩
    exact h0
  case wcaller.wleaf.pre =>
    rintro rf ws A ⟨hx13, hlen, htake⟩
    refine ⟨ws.drop 8, ?_, ?_, hx13⟩
    · rw [List.length_drop, hlen]
      rfl
    · rw [List.append_nil, ← htake, List.take_append_drop]
  case wcaller.post =>
    rintro rf ws A ⟨win, hwl, rfl, hx10, hx13, hwin⟩
    have hwl8 : win.length = 8 := hwl
    refine ⟨hx10, hx13, ?_, ?_⟩
    · simp only [List.append_nil, List.length_append, length_dwordBytes]
      omega
    · rw [List.append_nil,
        List.take_append_of_le_length (by rw [length_dwordBytes]),
        List.take_of_length_le (by rw [length_dwordBytes])]

private theorem wCallerR_hcode : ∀ a i,
    CodeReq.ofProg 0x1000 (wCallerRFn.programRetR .x13 (-8) 0x1000) a = some i →
    wCallerRCr a = some i := by
  intro a i h
  simp only [wCallerRCr, CodeReq.union, h]

private theorem wCallerR_haddr : ∀ rf ws A, wCallerRFn.pre rf ws A →
    rf.get .x13 + signExtend12 (-8) = wCallerRFn.rw.base + BitVec.ofNat 64 0 := by
  intro rf ws A h
  rw [show rf.get .x13 = 0x10008 from h]
  decide

private theorem wCallerR_haddrPost : ∀ (v : Word) rf ws A,
    (wCallerRVFn v).post rf ws A →
    rf.get .x13 + signExtend12 (-8) = wCallerRFn.rw.base + BitVec.ofNat 64 0 := by
  intro v rf ws A h
  rw [show rf.get .x13 = 0x10008 from h.2.1]
  decide

private theorem wCallerR_hspre : ∀ (v : Word) rf ws A, wCallerRFn.pre rf ws A →
    ws.length = wCallerRFn.rw.len →
    (wCallerRVFn v).pre rf (setBytes ws 0 (dwordBytes v)) A := by
  intro v rf ws A h hlen
  have hlen16 : ws.length = 16 := hlen
  refine ⟨h, by rw [length_setBytes]; exact hlen16, ?_⟩
  have hs := setBytes_slot ws (dwordBytes v) 0
    (by rw [length_dwordBytes]; omega)
  rw [List.drop_zero, length_dwordBytes] at hs
  exact hs

private theorem wCallerR_hspost : ∀ (v : Word) rf ws A,
    (wCallerRVFn v).post rf ws A → wCallerRFn.post rf ws A :=
  fun _ _ _ _ h => ⟨h.1, h.2.1⟩

private theorem wCallerR_hslot : ∀ (v : Word) rf ws A,
    (wCallerRVFn v).post rf ws A → ws.length = wCallerRFn.rw.len →
    (ws.drop 0).take 8 = dwordBytes v := by
  intro v rf ws A h hlen
  rw [List.drop_zero]
  exact h.2.2.2

/-- The caller packaged as a callee: `ra` spilled to ITS OWN dword — a slot
    the widened leaf provably cannot touch, with no ghost threading through
    the leaf's contract (compare `ExamplesVc.callerRHandle`). -/
def wCallerRHandle : FnHandle :=
  wCallerRFn.toHandleR 0x1000 wCallerRCr .x13 (-8) 0
    (fun v => (wCallerRVFn v).pre) (fun v => (wCallerRVFn v).post)
    (by decide)
    ((by decide : wRw.wf))
    (by decide) ((by decide : 0 + 8 ≤ wRw.len))
    ((by decide : 4 * (wCallerRFn.body.size + 3) ≤ 2 ^ 64))
    (fun v => wCallerRVFn_spec v)
    wCallerR_hcode wCallerR_haddr wCallerR_haddrPost
    wCallerR_hspre wCallerR_hspost wCallerR_hslot

end WidenDemo

-- ============================================================================
-- Demo: one leaf routine, two named read-only slices of one input buffer
-- ============================================================================

namespace RoWidenDemo

open Stmt

/-- Leaf: read the first byte of ITS OWN slice (pointer in `x11`).  The
    slice base and contents are ghosts — one code copy serves every call
    site, each instantiating the region at its own named slice (the SAsm
    answer to `la`-style per-arena addressing: the pointer is materialized
    by the caller, the contract is instantiated per slice). -/
def roLeafFn (b : Word) (xs : List (BitVec 8)) : Fn where
  name := "roleaf"
  region := ⟨b, xs⟩
  pre := fun rf _ _ => rf.get .x11 = b ∧ xs ≠ []
  post := fun rf _ _ => rf.get .x10 = (xs.getD 0 0).zeroExtend 64
  body := .block "load" [.LBU .x10 .x11 0]

private theorem roleaf_hidx (b : Word) : ∀ rf : RegFile, rf.get .x11 = b →
    ((rf.get .x11 + signExtend12 (0 : BitVec 12)) - b).toNat = 0 := by
  intro rf h
  rw [h, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  bv_omega

theorem roLeafFn_spec (b : Word) (xs : List (BitVec 8))
    (hwf : (Region.mk b xs).wf) : (roLeafFn b xs).Spec 0x2000 := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case roleaf.load.mem =>
    rintro rf ws A hws ⟨hx11, hne⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x11 + signExtend12 (0 : BitVec 12)) - b).toNat + 1
      ≤ xs.length
    rw [roleaf_hidx b rf hx11]
    have := List.length_pos_iff.mpr hne
    omega
  case roleaf.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hx11, hne⟩, rfl, rfl⟩
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    simp only [roLeafFn, execBlock_cons, execBlock_nil, execInstrRF_nil,
      aluSem, loadSem]
    rw [RegFile.get_set_self _ _ _ (by decide)]
    show (Region.byteAt ⟨b, xs⟩
        (rf₀.get .x11 + signExtend12 (0 : BitVec 12))).zeroExtend 64
      = (xs.getD 0 0).zeroExtend 64
    unfold Region.byteAt
    show (xs.getD ((rf₀.get .x11 + signExtend12 (0 : BitVec 12)) - b).toNat
        0).zeroExtend 64 = (xs.getD 0 0).zeroExtend 64
    rw [roleaf_hidx b rf₀ hx11]

/-- The one leaf routine at `0x2000`, contract instantiated per slice. -/
def roLeafHandle (b : Word) (xs : List (BitVec 8))
    (hwf : (Region.mk b xs).wf) : FnHandle :=
  (roLeafFn b xs).toHandle 0x2000 (roLeafFn_spec b xs hwf)
    ((by decide : 4 * ((roLeafFn 0 []).body.size + 1) ≤ 2 ^ 64))

/-- The caller's input buffer: two named 8-byte slices at `0x20000`. -/
def roBufBase : Word := 0x20000

variable (xsA xsB : List (BitVec 8))

/-- Slice A's leaf handle, widened to the full buffer (`sufR = xsB`). -/
def roLeafWideA (hwfA : (Region.mk roBufBase xsA).wf)
    (h8A : xsA.length = 8) : FnHandle :=
  (roLeafHandle roBufBase xsA hwfA).widenRo ⟨roBufBase, xsA ++ xsB⟩ [] xsB
    rfl
    (by show roBufBase = roBufBase
          + BitVec.ofNat 64 (List.length ([] : List (BitVec 8)))
        decide)
    (by decide)
    (by show (8 : Nat) ∣ xsA.length
        omega)

/-- Slice B's leaf handle, widened to the full buffer (`preR = xsA`). -/
def roLeafWideB (hwfB : (Region.mk (roBufBase + 8) xsB).wf)
    (h8A : xsA.length = 8) (h8B : xsB.length = 8) : FnHandle :=
  (roLeafHandle (roBufBase + 8) xsB hwfB).widenRo ⟨roBufBase, xsA ++ xsB⟩ xsA []
    (by show xsA ++ xsB = xsA ++ xsB ++ []
        rw [List.append_nil])
    (by show roBufBase + 8 = roBufBase + BitVec.ofNat 64 xsA.length
        rw [h8A]
        decide)
    (by show (8 : Nat) ∣ xsA.length
        omega)
    (by show (8 : Nat) ∣ xsB.length
        omega)

/-- The caller: read the head byte of slice A, then of slice B, against ONE
    region covering the whole buffer.  Each call site materializes its own
    slice pointer (the `la` shape) and uses the widened per-slice handle. -/
def roCallerFn (hwfA : (Region.mk roBufBase xsA).wf)
    (hwfB : (Region.mk (roBufBase + 8) xsB).wf)
    (h8A : xsA.length = 8) (h8B : xsB.length = 8) : Fn where
  name := "rocaller"
  region := ⟨roBufBase, xsA ++ xsB⟩
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x10 = (xsB.getD 0 0).zeroExtend 64
  body :=
    .block "goA" [.LI .x11 0x20000] ;;;
    .call "leafA" (roLeafWideA xsA xsB hwfA h8A) ;;;
    .block "goB" [.LI .x11 0x20008] ;;;
    .call "leafB" (roLeafWideB xsA xsB hwfB h8A h8B)

def roCallerCr (hwfA : (Region.mk roBufBase xsA).wf)
    (hwfB : (Region.mk (roBufBase + 8) xsB).wf)
    (h8A : xsA.length = 8) (h8B : xsB.length = 8) : CodeReq :=
  (CodeReq.ofProg 0x1000
      ((roCallerFn xsA xsB hwfA hwfB h8A h8B).body.flatten 0x1000)).union
    (roLeafHandle roBufBase xsA hwfA).code

theorem roCallerFn_spec (hwfA : (Region.mk roBufBase xsA).wf)
    (hwfB : (Region.mk (roBufBase + 8) xsB).wf)
    (h8A : xsA.length = 8) (h8B : xsB.length = 8) :
    (roCallerFn xsA xsB hwfA hwfB h8A h8B).SpecR 0x1000
      (roCallerCr xsA xsB hwfA hwfB h8A h8B) := by
  have hneA : xsA ≠ [] := by
    intro h
    rw [h] at h8A
    exact absurd h8A (by decide)
  have hneB : xsB ≠ [] := by
    intro h
    rw [h] at h8B
    exact absurd h8B (by decide)
  -- the two widened handles share one code copy; containment is proved once
  have hcode : ∀ a i, (roLeafHandle roBufBase xsA hwfA).code a = some i →
      roCallerCr xsA xsB hwfA hwfB h8A h8B a = some i := by
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hk2 : kk < 2 := hk
    simp only [roCallerCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000
      ((roCallerFn xsA xsB hwfA hwfB h8A h8B).body.flatten 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hk'2 : k' < 4 := hk'
      bv_omega
  -- normalize the target head so `vcgen` recognizes the `SpecR` shape
  show Fn.SpecR _ _ _
  vcgen
  case region =>
    refine ⟨⟨(by decide : (roBufBase : Word).toNat % 8 = 0), ?_, ?_⟩,
      RwRegion.empty_wf⟩
    · show (roBufBase : Word).toNat + (xsA ++ xsB).length < 2 ^ 64
      rw [List.length_append, h8A, h8B]
      decide
    · intro k hk
      have hk' : k < (xsA ++ xsB).length := hk
      rw [List.length_append, h8A, h8B] at hk'
      show isValidMemAddr (roBufBase + BitVec.ofNat 64 k) = true
      interval_cases k <;> decide
  case code =>
    intro a i h
    simp only [roCallerCr, CodeReq.union, h]
  case callees =>
    exact ⟨trivial, ⟨hcode, rfl, rfl⟩, trivial, hcode, rfl, rfl⟩
  case calls =>
    exact ⟨trivial,
      ⟨(by decide : (0x1004 : Word) + signExtend21 (BitVec.setWidth 21
          ((0x2000 : Word) - 0x1004)) = 0x2000),
       (by decide : (((0x1004 : Word) + 4) &&& ~~~(1 : Word)) = 0x1004 + 4),
       (by decide : CodeReq.ofProg 0x2000 ((roLeafFn 0 []).programRet 0x2000)
          (0x1004 : Word) = none)⟩,
      trivial,
      (by decide : (0x100c : Word) + signExtend21 (BitVec.setWidth 21
          ((0x2000 : Word) - 0x100c)) = 0x2000),
      (by decide : (((0x100c : Word) + 4) &&& ~~~(1 : Word)) = 0x100c + 4),
      (by decide : CodeReq.ofProg 0x2000 ((roLeafFn 0 []).programRet 0x2000)
          (0x100c : Word) = none)⟩
  case rocaller.leafA.pre =>
    rintro rf ws A ⟨rf₀, ws₀, hlen, -, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil]
    exact ⟨RegFile.get_set_self _ _ _ (by decide), hneA⟩
  case rocaller.leafB.pre =>
    rintro rf ws A ⟨rf₀, ws₀, hlen, -, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil]
    exact ⟨RegFile.get_set_self _ _ _ (by decide), hneB⟩
  case rocaller.post =>
    exact fun rf ws A h => h

end RoWidenDemo

end SAsm
end EvmAsm.Rv64
