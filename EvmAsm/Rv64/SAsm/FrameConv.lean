/-
  EvmAsm.Rv64.SAsm.FrameConv

  Register-preservation and frame-layout conventions for deep call trees
  (bead evm-asm-4ch8f.3, docs/sasm-design.md §3.6.2).

  `Stmt.sp` for a `.call` replaces the reachable set by the callee's
  postcondition: the callee owns the whole exposed register file, so any
  register the post does not mention is forgotten.  Exposed registers
  (t0–t6, a0–a7) are therefore *caller-saved*, with two conventions for
  keeping a value live across a call:

  * contract pinning (`Reach.pin`): when the callee provably does not
    touch the register, its contract family carries the entry value as a
    ghost and re-asserts it in the post — zero runtime cost (`PinDemo`);

  * spill/reload: the caller stores the value into a private dword of its
    own frame window — outside the callee's `FnHandle.widenRw` window, so
    the widened postcondition preserves the slot by construction — and
    reloads it after the call (`SpillDemo`).  Pointers are never spilled:
    they are re-materialized by `LI` from the static layout (§3.6.1).

  s-registers (and `sp`/`gp`/`tp`) are outside the exposed set: `blockOk`
  rejects any access, so verified SAsm code cannot clobber them and no
  preservation machinery is needed.  Frames are *static* windows of the
  stack arena — assigned by the global memory layout (bead evm-asm-4ch8f.6)
  and carved per call edge by `widenRw`; verified code contains no dynamic
  `addi sp` prologue.
-/

import EvmAsm.Rv64.SAsm.HandleWiden

namespace EvmAsm.Rv64
namespace SAsm

/-- Pin an exposed register through a reachable set: the contract family's
    ghost `v` records the entry value, and using `pin` in both pre and post
    states preservation.  Nest applications to pin several registers. -/
def Reach.pin (r : Reg) (v : Word) (reach : Reach) : Reach :=
  fun rf ws A => rf.get r = v ∧ reach rf ws A

-- ============================================================================
-- Demo: contract pinning — a value survives a call in a register
-- ============================================================================

namespace PinDemo

open Stmt

/-- Leaf callee: clobber `x10` but leave `x15` alone.  The contract family
    pins `x15` to ghost `g` through pre AND post; the leaf's own `.post` VC
    proves the preservation (the block never writes `x15`). -/
def pinLeafFn (g : Word) : Fn where
  name := "pinleaf"
  pre := Reach.pin .x15 g (fun _ _ _ => True)
  post := Reach.pin .x15 g (fun rf _ _ => rf.get .x10 = 99)
  body := .block "clob" [.LI .x10 99]

theorem pinLeafFn_spec (g : Word) : (pinLeafFn g).Spec 0x2000 := by
  vcgen
  case pinleaf.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hx15, -⟩, rfl, rfl⟩
    simp only [pinLeafFn, Reach.pin, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem]
    exact ⟨by rw [RegFile.get_set_ne rf₀ .x10 .x15 99 (by decide)]; exact hx15,
      RegFile.get_set_self rf₀ .x10 99 (by decide)⟩

/-- The leaf as a callee, contract instantiated per ghost `g`. -/
def pinLeafHandle (g : Word) : FnHandle :=
  (pinLeafFn g).toHandle 0x2000 (pinLeafFn_spec g)
    ((by decide : 4 * ((pinLeafFn 0).body.size + 1) ≤ 2 ^ 64))

/-- Caller: keep `w` live in `x15` across the call, then USE it after —
    the pinned contract carries it through. -/
def pinCallerFn (w : Word) : Fn where
  name := "pincaller"
  pre := fun rf _ _ => rf.get .x15 = w
  post := fun rf _ _ => rf.get .x11 = w ∧ rf.get .x10 = 99
  body := .call "leaf" (pinLeafHandle w) ;;;
    .block "use" [.ADDI .x11 .x15 0]

def pinCallerCr (w : Word) : CodeReq :=
  (CodeReq.ofProg 0x1000 ((pinCallerFn w).body.flatten 0x1000)).union
    (pinLeafHandle w).code

theorem pinCallerFn_spec (w : Word) :
    (pinCallerFn w).SpecR 0x1000 (pinCallerCr w) := by
  have hcode : ∀ a i, (pinLeafHandle w).code a = some i →
      pinCallerCr w a = some i := by
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hk2 : kk < 2 := hk
    simp only [pinCallerCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000 ((pinCallerFn w).body.flatten 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hk'2 : k' < 2 := hk'
      bv_omega
  show Fn.SpecR _ _ _
  vcgen
  case code =>
    intro a i h
    simp only [pinCallerCr, CodeReq.union, h]
  case callees =>
    exact ⟨⟨hcode, rfl, rfl⟩, trivial⟩
  case calls =>
    exact ⟨⟨(by decide : (0x1000 : Word) + signExtend21 (BitVec.setWidth 21
          ((0x2000 : Word) - 0x1000)) = 0x2000),
       (by decide : (((0x1000 : Word) + 4) &&& ~~~(1 : Word)) = 0x1000 + 4),
       (by decide : CodeReq.ofProg 0x2000 ((pinLeafFn 0).programRet 0x2000)
          (0x1000 : Word) = none)⟩,
      trivial⟩
  case pincaller.leaf.pre =>
    rintro rf ws A hx15
    exact ⟨hx15, trivial⟩
  case pincaller.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hx15, hx10⟩, rfl, rfl⟩
    simp only [pinCallerFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_⟩
    · rw [RegFile.get_set_self rf₀ .x11 _ (by decide), hx15,
        show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne rf₀ .x11 .x10 _ (by decide)]
      exact hx10

end PinDemo

-- ============================================================================
-- Demo: spill/reload — a value survives a clobbering call through memory
-- ============================================================================

namespace SpillDemo

open Stmt

/-- The caller's frame window: its private save slot in the first dword,
    the callee's window in the second. -/
def spRw : RwRegion := ⟨0x30000, 16⟩

/-- The leaf's own writable window: the second dword of `spRw`. -/
def spLeafRw : RwRegion := ⟨0x30008, 8⟩

/-- Leaf callee: CLOBBERS `x15` (and writes its own window via `x14`).
    Its contract says nothing about the caller's value. -/
def spLeafFn : Fn where
  name := "spleaf"
  rw := spLeafRw
  pre := fun rf _ _ => rf.get .x14 = 0x30008
  post := fun rf ws _ => rf.get .x15 = 7 ∧ ws = dwordBytes 7
  body := .block "clob" [.LI .x15 7, .SD .x14 .x15 0]

private theorem spleaf_hidx : ∀ rf : RegFile, rf.get .x14 = 0x30008 →
    ((rf.get .x14 + signExtend12 (0 : BitVec 12)) - (0x30008 : Word)).toNat
      = 0 := by
  intro rf h
  rw [h, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  bv_omega

theorem spLeafFn_spec : spLeafFn.Spec 0x2000 := by
  have hx14' : ∀ rf : RegFile, rf.get .x14 = 0x30008 →
      (rf.set .x15 7).get .x14 = 0x30008 := by
    intro rf h
    rw [RegFile.get_set_ne rf .x15 .x14 7 (by decide)]
    exact h
  vcgen
  case spleaf.clob.mem =>
    rintro rf ws A hws hx14
    have hws8 : ws.length = 8 := hws
    simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, spLeafFn,
      spLeafRw, inRw, spleaf_hidx _ (hx14' rf hx14)]
    exact ⟨trivial, ⟨by omega, by decide⟩, trivial⟩
  case spleaf.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, hx14, rfl, rfl⟩
    have hws8 : ws₀.length = 8 := hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
      storeSem, spLeafFn, spLeafRw, spleaf_hidx _ (hx14' rf₀ hx14)]
    refine ⟨?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
      have hs := setBytes_slot ws₀ (dwordBytes 7) 0
        (by rw [length_dwordBytes]; omega)
      rw [List.drop_zero, length_dwordBytes] at hs
      conv_lhs => rw [← List.take_of_length_le
        (l := setBytes ws₀ 0 (dwordBytes 7)) (i := 8)
        (by rw [length_setBytes]; omega)]
      exact hs

/-- The leaf as a callee at `0x2000`, against its OWN window only. -/
def spLeafHandle : FnHandle :=
  spLeafFn.toHandle 0x2000 spLeafFn_spec
    ((by decide : 4 * (spLeafFn.body.size + 1) ≤ 2 ^ 64))

/-- The leaf widened to the caller's frame: the caller's saved dword
    (`dwordBytes w`) is framed across the call by construction. -/
def spLeafWide (w : Word) : FnHandle :=
  spLeafHandle.widenRw spRw (dwordBytes w) []
    (by rw [length_dwordBytes]; decide)
    (by rw [length_dwordBytes]; decide)
    (by rw [length_dwordBytes])
    (by decide)

private theorem spcaller_hidx : ∀ rf : RegFile, rf.get .x13 = 0x30000 →
    ((rf.get .x13 + signExtend12 (0 : BitVec 12)) - (0x30000 : Word)).toNat
      = 0 := by
  intro rf h
  rw [h, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  bv_omega

private theorem sp_hidx0 :
    (((0x30000 : Word) + signExtend12 (0 : BitVec 12)) - (0x30000 : Word)).toNat
      = 0 := by decide

/-- Caller: save `w` (live in `x15`) to its own slot, call the clobbering
    leaf, re-materialize the pointer with `LI`, reload.  The callee's
    contract never mentions `w`; the widened window preserves the slot. -/
def spCallerFn (w : Word) : Fn where
  name := "spcaller"
  rw := spRw
  pre := fun rf _ _ => rf.get .x13 = 0x30000 ∧ rf.get .x15 = w
  post := fun rf _ _ => rf.get .x15 = w
  body :=
    .block "save" [.SD .x13 .x15 0, .LI .x14 0x30008] ;;;
    .call "spleaf" (spLeafWide w) ;;;
    .block "restore" [.LI .x13 0x30000, .LD .x15 .x13 0]

def spCallerCr (w : Word) : CodeReq :=
  (CodeReq.ofProg 0x1000 ((spCallerFn w).body.flatten 0x1000)).union
    spLeafHandle.code

theorem spCallerFn_spec (w : Word) :
    (spCallerFn w).SpecR 0x1000 (spCallerCr w) := by
  have hcode : ∀ a i, spLeafHandle.code a = some i →
      spCallerCr w a = some i := by
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hk3 : kk < 3 := hk
    simp only [spCallerCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000 ((spCallerFn w).body.flatten 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hk'5 : k' < 5 := hk'
      bv_omega
  show Fn.SpecR _ _ _
  vcgen
  case region =>
    exact ⟨Region.empty_wf, (by decide : spRw.wf)⟩
  case code =>
    intro a i h
    simp only [spCallerCr, CodeReq.union, h]
  case callees =>
    exact ⟨trivial, ⟨hcode, rfl, rfl⟩, trivial⟩
  case calls =>
    exact ⟨trivial,
      ⟨(by decide : (0x1008 : Word) + signExtend21 (BitVec.setWidth 21
          ((0x2000 : Word) - 0x1008)) = 0x2000),
       (by decide : (((0x1008 : Word) + 4) &&& ~~~(1 : Word)) = 0x1008 + 4),
       (by decide : CodeReq.ofProg 0x2000 (spLeafFn.programRet 0x2000)
          (0x1008 : Word) = none)⟩,
      trivial⟩
  case spcaller.save.mem =>
    rintro rf ws A hws ⟨hx13, hx15⟩
    have hws16 : ws.length = 16 := hws
    simp only [blockVCs, loadSem, storeSem, spCallerFn,
      spRw, inRw, spcaller_hidx rf hx13]
    exact ⟨⟨by omega, by decide⟩, trivial, trivial⟩
  case spcaller.spleaf.pre =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx13, hx15⟩, rfl, rfl⟩
    have hws16 : ws₀.length = 16 := hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
      storeSem, spCallerFn, spRw, spcaller_hidx rf₀ hx13, hx15]
    refine ⟨(setBytes ws₀ 0 (dwordBytes w)).drop 8, ?_, ?_, ?_⟩
    · show ((setBytes ws₀ 0 (dwordBytes w)).drop 8).length = 8
      rw [List.length_drop, length_setBytes]
      omega
    · rw [List.append_nil]
      conv_lhs => rw [← List.take_append_drop 8 (setBytes ws₀ 0 (dwordBytes w))]
      congr 1
      have hs := setBytes_slot ws₀ (dwordBytes w) 0
        (by rw [length_dwordBytes]; omega)
      rw [List.drop_zero, length_dwordBytes] at hs
      exact hs
    · exact RegFile.get_set_self rf₀ .x14 _ (by decide)
  case spcaller.restore.mem =>
    rintro rf ws A hws ⟨win, hwl, rfl, hpost⟩
    have hws16 : (dwordBytes w ++ win ++ []).length = 16 := hws
    simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, spCallerFn,
      spRw, inRw, Region.loadOk,
      RegFile.get_set_self rf .x13 (0x30000 : Word) (by decide), sp_hidx0]
    have hcond : (0 : Nat) + 8 ≤ (dwordBytes w ++ win ++ []).length := by
      rw [hws16]
      omega
    rw [if_pos hcond]
    exact ⟨trivial, ⟨by decide, hcond⟩, trivial⟩
  case spcaller.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, hreach, rfl, rfl⟩
    obtain ⟨win, hwl, rfl, hx15leaf, hwsleaf⟩ := hreach
    show RegFile.get _ .x15 = w
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
      spCallerFn, spRw,
      RegFile.get_set_self rf₀ .x13 (0x30000 : Word) (by decide)]
    rw [if_pos (show inRw (0x30000 : Word) (dwordBytes w ++ win ++ [])
        ((0x30000 : Word) + signExtend12 (0 : BitVec 12)) 8 from by
      unfold inRw
      rw [sp_hidx0]
      simp only [List.append_nil, List.length_append, length_dwordBytes]
      omega)]
    rw [RegFile.get_set_self _ .x15 _ (by decide)]
    show Region.dwordAt _ _ = w
    unfold Region.dwordAt
    rw [show ((⟨0x30000, dwordBytes w ++ win ++ []⟩ : Region).bytes.drop
        (((0x30000 : Word) + signExtend12 (0 : BitVec 12)
          - (⟨0x30000, dwordBytes w ++ win ++ []⟩ : Region).base).toNat))
        = dwordBytes w ++ win ++ [] from by
      show (dwordBytes w ++ win ++ []).drop _ = _
      rw [sp_hidx0, List.drop_zero]]
    rw [List.append_nil,
      List.take_append_of_le_length (by rw [length_dwordBytes]),
      List.take_of_length_le (by rw [length_dwordBytes]),
      packBytes_dwordBytes]

end SpillDemo

end SAsm
end EvmAsm.Rv64
