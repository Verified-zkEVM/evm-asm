/-
  EvmAsm.Rv64.SAsm.ExamplesVc

  End-to-end demos of the SAsm verification pipeline: define an `Fn`,
  state its `Spec`, run `vcgen`, and discharge the remaining named pure
  goals.  These double as regression tests for the tactic.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SAsm.AssertionSpec
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace ExamplesVc

open Stmt

/-- `min(a0, a1)` into a0: if a0 ≥u a1 then a0 := a1. -/
def clampFn (x y : Word) : Fn where
  name := "clamp"
  pre := fun rf _ _ => rf.get .x10 = x ∧ rf.get .x11 = y
  post := fun rf _ _ =>
    rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
  body := .when "cap" (.bgeu .x10 .x11) (.block "set" [.MV .x10 .x11])

theorem clampFn_spec (x y base : Word) : (clampFn x y).Spec base := by
  vcgen
  case clamp.post =>
    intro rf ws A h
    show rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
    rcases h with ⟨rf₀, ws₀, -, ⟨⟨hx, hy⟩, hge⟩, rfl, rfl⟩ | ⟨⟨hx, hy⟩, hlt⟩
    · -- took the branch: ¬ x <u y, a0 := a1
      simp only [Cond.holds] at hge
      rw [hx, hy] at hge
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      constructor
      · rw [RegFile.get_set_self _ _ _ (by decide), hy,
          if_neg (by simpa using hge)]
      · rw [RegFile.get_set_ne _ _ _ _ (by decide), hy]
    · -- fell through: x <u y, registers unchanged
      simp only [Cond.holds] at hlt
      rw [hx, hy] at hlt
      rw [if_pos (Decidable.of_not_not hlt)]
      exact ⟨hx, hy⟩

/-- Count up from 0 to 10 in t0: init; while (t0 <u t1) t0 += 1. -/
def countFn : Fn where
  name := "count"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x5 = 10
  body :=
    .block "init" [.LI .x5 0, .LI .x6 10] ;;;
    .«while» "loop" (.bltu .x5 .x6) 10
      (fun i rf _ _ => rf.get .x5 = BitVec.ofNat 64 i ∧ rf.get .x6 = 10 ∧ i ≤ 10)
      (.block "step" [.ADDI .x5 .x5 1])

theorem countFn_spec (base : Word) : countFn.Spec base := by
  vcgen
  case count.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, -, -, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case count.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx5, hx6, hle⟩, hlt⟩, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6
  case count.loop.exhausted =>
    rintro rf ws A ⟨hx5, hx6, -⟩
    simp only [Cond.holds]
    rw [hx5, hx6]
    decide
  case count.post =>
    intro rf ws A h
    show rf.get .x5 = 10
    obtain ⟨⟨i, hle, hx5, hx6, -⟩, hnc⟩ := h
    simp only [Cond.holds] at hnc
    rw [hx5, hx6] at hnc
    rw [hx5]
    have : i = 10 := by
      simp only [BitVec.ult, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
        decide_eq_true_eq] at hnc
      omega
    subst this
    decide

-- ============================================================================
-- Calls (Milestone M4): package a verified leaf as a handle, call it
-- ============================================================================

/-- The clamp routine as a callee at `0x2000`, instantiated at the ghost
    arguments `x := 5`, `y := 7`. -/
def clampHandle : FnHandle :=
  (clampFn 5 7).toHandle 0x2000 (clampFn_spec 5 7 0x2000) (by decide)

/-- Load arguments and call clamp: afterwards `a0 = min(5, 7) = 5`. -/
def callerFn : Fn where
  name := "caller"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x10 = 5
  body :=
    .block "args" [.LI .x10 5, .LI .x11 7] ;;;
    .call "clamp" clampHandle

/-- The canonical ambient code requirement: the caller's own code plus the
    callee's. -/
def callerCr : CodeReq :=
  (CodeReq.ofProg 0x1000 (callerFn.body.flatten 0x1000)).union clampHandle.code

theorem callerFn_spec : callerFn.SpecR 0x1000 callerCr := by
  vcgen
  case code =>
    intro a i h
    simp only [callerCr, CodeReq.union, h]
  case callees =>
    refine ⟨trivial, ?_, rfl, rfl⟩
    intro a i h
    obtain ⟨k, hk, rfl⟩ := ofProg_some_range h
    have hlen : ((clampFn 5 7).programRet 0x2000).length = 3 := by decide
    rw [hlen] at hk
    simp only [callerCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000 (callerFn.body.flatten 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hlen' : (callerFn.body.flatten 0x1000).length = 3 := by decide
      rw [hlen'] at hk'
      bv_omega
  case calls =>
    exact ⟨trivial, by decide, by decide, by decide⟩
  case caller.clamp.pre =>
    rintro rf ws A ⟨rf₀, ws₀, -, -, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    constructor
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case caller.post =>
    intro rf ws A h
    show rf.get .x10 = 5
    have h' : rf.get .x10 = (if BitVec.ult 5 7 then (5 : Word) else 7) := h.1
    rw [h', if_pos (by decide)]

-- ============================================================================
-- Read-only regions (Milestone M5a): RLP prefix classification
-- ============================================================================

/-- Classify the first byte of an RLP input: `a0 := 0` if the item is not a
    list (first byte `< 0xc0`), else `1`.  The input buffer is a *ghost*
    byte list `bs` at `inBase` — the check-heavy RLP decoding shape. -/
def rlpIsListFn (inBase : Word) (bs : List (BitVec 8)) : Fn where
  name := "rlpIsList"
  region := ⟨inBase, bs⟩
  pre := fun rf _ _ => rf.get .x10 = inBase ∧ bs ≠ []
  post := fun rf _ _ =>
    rf.get .x10 = (if (bs.headD 0).toNat < 0xc0 then 0 else 1)
  body :=
    .block "load" [.LBU .x5 .x10 0, .LI .x6 0xc0] ;;;
    .ite "classify" (.bltu .x5 .x6)
      (.block "notList" [.LI .x10 0])
      (.block "isList" [.LI .x10 1])

theorem rlpIsListFn_spec (inBase : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk inBase bs).wf) (base : Word) :
    (rlpIsListFn inBase bs).Spec base := by
  have haddr : ∀ rf : RegFile, rf.get .x10 = inBase →
      ((rf.get .x10 + signExtend12 (0 : BitVec 12)) - inBase).toNat = 0 := by
    intro rf h
    rw [h, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case rlpIsList.load.mem =>
    rintro rf ws A hws ⟨hx10, hne⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial, trivial⟩
    show ((rf.get .x10 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 1
      ≤ bs.length
    rw [haddr rf hx10]
    have := List.length_pos_iff.mpr hne
    omega
  case rlpIsList.post =>
    intro rf' ws' A' h
    show rf'.get .x10 = (if (bs.headD 0).toNat < 0xc0 then 0 else 1)
    obtain ⟨b, tl, rfl⟩ : ∃ b tl, bs = b :: tl := by
      rcases h with ⟨rf₀, ws₀, -, ⟨⟨rf₁, ws₁, -, ⟨-, hne⟩, -⟩, -⟩, -⟩
                  | ⟨rf₀, ws₀, -, ⟨⟨rf₁, ws₁, -, ⟨-, hne⟩, -⟩, -⟩, -⟩ <;>
        (cases bs with
         | nil => exact absurd rfl hne
         | cons b tl => exact ⟨b, tl, rfl⟩)
    have hz : (BitVec.zeroExtend 64 b).toNat = b.toNat := by
      have hb := b.isLt
      rw [show BitVec.zeroExtend 64 b = BitVec.setWidth 64 b from rfl,
        BitVec.toNat_setWidth]
      omega
    have hult : (BitVec.zeroExtend 64 b).ult (0xc0 : Word) = true ↔ b.toNat < 0xc0 := by
      simp only [BitVec.ult, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
        decide_eq_true_eq, hz]
    have hbyte : ∀ rf₀ : RegFile, rf₀.get .x10 = inBase →
        (rlpIsListFn inBase (b :: tl)).region.byteAt
          (rf₀.get .x10 + signExtend12 (0 : BitVec 12)) = b := by
      intro rf₀ h₀
      show Region.byteAt (Region.mk inBase (b :: tl)) _ = b
      unfold Region.byteAt
      rw [haddr rf₀ h₀]
      rfl
    rcases h with ⟨rf₀, ws₀, -, ⟨⟨rf₁, ws₁, hws₁, ⟨hx10, -⟩, rfl, rfl⟩, hcond⟩, rfl, rfl⟩
                | ⟨rf₀, ws₀, -, ⟨⟨rf₁, ws₁, hws₁, ⟨hx10, -⟩, rfl, rfl⟩, hcond⟩, rfl, rfl⟩ <;>
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₁
    · -- not a list: b <u 0xc0
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        Cond.holds, List.headD_cons] at hcond ⊢
      rw [RegFile.get_set_self _ .x10 _ (by decide)]
      rw [RegFile.get_set_ne _ .x6 .x5 _ (by decide),
        RegFile.get_set_self _ .x5 _ (by decide),
        RegFile.get_set_self _ .x6 _ (by decide),
        hbyte rf₁ hx10] at hcond
      rw [if_pos (hult.mp hcond)]
    · -- a list: ¬ (b <u 0xc0)
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        Cond.holds, List.headD_cons] at hcond ⊢
      rw [RegFile.get_set_self _ .x10 _ (by decide)]
      rw [RegFile.get_set_ne _ .x6 .x5 _ (by decide),
        RegFile.get_set_self _ .x5 _ (by decide),
        RegFile.get_set_self _ .x6 _ (by decide),
        hbyte rf₁ hx10] at hcond
      rw [if_neg (fun hlt => hcond (hult.mpr hlt))]

-- ============================================================================
-- Wider loads (Milestone M5b): SSZ-style u32 offset read
-- ============================================================================

/-- Read the little-endian u32 at byte offset 4 of an SSZ-style input into
    a1 — the shape of an SSZ offset-table walk (`decode_validation_bit`). -/
def sszReadOffsetFn (inBase : Word) (bs : List (BitVec 8)) : Fn where
  name := "sszReadOffset"
  region := ⟨inBase, bs⟩
  pre := fun rf _ _ => rf.get .x10 = inBase ∧ 8 ≤ bs.length
  post := fun rf _ _ => rf.get .x11
    = BitVec.zeroExtend 64
        (bs.getD 7 0 ++ bs.getD 6 0 ++ bs.getD 5 0 ++ bs.getD 4 0)
  body := .block "load" [.LWU .x11 .x10 4]

theorem sszReadOffsetFn_spec (inBase : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk inBase bs).wf) (base : Word) :
    (sszReadOffsetFn inBase bs).Spec base := by
  have haddr : ∀ rf : RegFile, rf.get .x10 = inBase →
      ((rf.get .x10 + signExtend12 (4 : BitVec 12)) - inBase).toNat = 4 := by
    intro rf h
    rw [h, show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide]
    bv_omega
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case sszReadOffset.load.mem =>
    rintro rf ws A hws ⟨hx10, hlen⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · show (4 : Nat) ∣ ((rf.get .x10 + signExtend12 (4 : BitVec 12)) - inBase).toNat
      rw [haddr rf hx10]
    · show ((rf.get .x10 + signExtend12 (4 : BitVec 12)) - inBase).toNat + 4
        ≤ bs.length
      rw [haddr rf hx10]
      omega
  case sszReadOffset.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hx10, hlen⟩, rfl, rfl⟩
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    show RegFile.get _ .x11 = _
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
    rw [RegFile.get_set_self _ .x11 _ (by decide)]
    rw [hx10, show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide]
    show BitVec.zeroExtend 64 (Region.word32At ⟨inBase, bs⟩ (inBase + 4)) = _
    unfold Region.word32At Region.byteAt
    rw [show inBase + 4 + 3 - inBase = (7 : Word) from by bv_omega,
      show inBase + 4 + 2 - inBase = (6 : Word) from by bv_omega,
      show inBase + 4 + 1 - inBase = (5 : Word) from by bv_omega,
      show inBase + 4 - inBase = (4 : Word) from by bv_omega]
    rfl

/-- Read the little-endian u16 at byte offset 2 of the input into a1 —
    exercises the LHU block leaf. -/
def readU16Fn (inBase : Word) (bs : List (BitVec 8)) : Fn where
  name := "readU16"
  region := ⟨inBase, bs⟩
  pre := fun rf _ _ => rf.get .x10 = inBase ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x11
    = BitVec.zeroExtend 64 (bs.getD 3 0 ++ bs.getD 2 0)
  body := .block "load" [.LHU .x11 .x10 2]

theorem readU16Fn_spec (inBase : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk inBase bs).wf) (base : Word) :
    (readU16Fn inBase bs).Spec base := by
  have haddr : ∀ rf : RegFile, rf.get .x10 = inBase →
      ((rf.get .x10 + signExtend12 (2 : BitVec 12)) - inBase).toNat = 2 := by
    intro rf h
    rw [h, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]
    bv_omega
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case readU16.load.mem =>
    rintro rf ws A hws ⟨hx10, hlen⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · show (2 : Nat) ∣ ((rf.get .x10 + signExtend12 (2 : BitVec 12)) - inBase).toNat
      rw [haddr rf hx10]
    · show ((rf.get .x10 + signExtend12 (2 : BitVec 12)) - inBase).toNat + 2
        ≤ bs.length
      rw [haddr rf hx10]
      omega
  case readU16.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hx10, hlen⟩, rfl, rfl⟩
    obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hws₀
    show RegFile.get _ .x11 = _
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem]
    rw [RegFile.get_set_self _ .x11 _ (by decide)]
    rw [hx10, show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide]
    show BitVec.zeroExtend 64 (Region.half16At ⟨inBase, bs⟩ (inBase + 2)) = _
    unfold Region.half16At Region.byteAt
    rw [show inBase + 2 + 1 - inBase = (3 : Word) from by bv_omega,
      show inBase + 2 - inBase = (2 : Word) from by bv_omega]
    rfl

-- ============================================================================
-- Writable regions (Milestone M5b-2): dword spill and reload
-- ============================================================================

/-- Store a0 to the writable scratch cell, clobber a0, load it back — the
    ra-spill shape, exercising SD + LD routed to the writable region. -/
def spillFn (scratch x : Word) : Fn where
  name := "spill"
  rw := ⟨scratch, 8⟩
  pre := fun rf _ _ => rf.get .x10 = x ∧ rf.get .x11 = scratch
  post := fun rf _ _ => rf.get .x10 = x
  body := .block "roundtrip" [.SD .x11 .x10 0, .LI .x10 0, .LD .x10 .x11 0]

theorem spillFn_spec (scratch x base : Word)
    (hwf : RwRegion.wf ⟨scratch, 8⟩) :
    (spillFn scratch x).Spec base := by
  have hidx : ∀ rf : RegFile, rf.get .x11 = scratch →
      ((rf.get .x11 + signExtend12 (0 : BitVec 12)) - scratch).toNat = 0 := by
    intro rf h
    rw [h, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case spill.roundtrip.mem =>
    rintro rf ws A hws ⟨hx10, hx11⟩
    have hws8 : ws.length = 8 := hws
    simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, spillFn,
      inRw, Region.loadOk, length_setBytes, hidx rf hx11,
      RegFile.get_set_ne rf .x10 .x11 0 (by decide)]
    rw [if_pos (show 0 + 8 ≤ ws.length from by omega)]
    exact ⟨⟨by omega, by decide⟩, trivial, ⟨by decide, by omega⟩, trivial⟩
  case spill.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11⟩, rfl, rfl⟩
    have hws8 : ws₀.length = 8 := hws₀
    show RegFile.get _ .x10 = x
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
      storeSem, spillFn, hidx rf₀ hx11,
      RegFile.get_set_ne rf₀ .x10 .x11 0 (by decide)]
    rw [if_pos (show inRw scratch (setBytes ws₀ 0 (dwordBytes (rf₀.get .x10)))
        (rf₀.get .x11 + signExtend12 0) 8 from by
      unfold inRw
      rw [length_setBytes, hidx rf₀ hx11]
      omega)]
    rw [RegFile.get_set_self _ .x10 _ (by decide)]
    show Region.dwordAt _ _ = x
    unfold Region.dwordAt
    rw [show ((⟨scratch, setBytes ws₀ 0 (dwordBytes (rf₀.get .x10))⟩ :
        Region).bytes.drop
          ((rf₀.get .x11 + signExtend12 0 - (⟨scratch,
            setBytes ws₀ 0 (dwordBytes (rf₀.get .x10))⟩ : Region).base).toNat))
        = setBytes ws₀ 0 (dwordBytes (rf₀.get .x10)) from by
      show (setBytes ws₀ 0 (dwordBytes (rf₀.get .x10))).drop
        ((rf₀.get .x11 + signExtend12 0 - scratch).toNat) = _
      rw [hidx rf₀ hx11, List.drop_zero]]
    rw [List.take_of_length_le (by rw [length_setBytes]; omega)]
    rw [hx10]
    exact (packBytes_setBytes_dword ws₀ x (by omega)).symm

-- ============================================================================
-- Callers as callees (ra-spill packaging): a two-level call tree
-- ============================================================================

/-- The demo call tree's shared writable region: one dword spill slot at
    `0x10000` (`CalleesIn` requires every function in the tree to declare
    the same writable region). -/
def spillRw : RwRegion := ⟨0x10000, 8⟩

/-- Leaf callee: set a0 := 5.  Ghost `v` is the caller's spilled return
    address: the leaf shares the writable region, so its contract records
    that it leaves the slot alone (its own `.post` VC proves it). -/
def leafFn (v : Word) : Fn where
  name := "leaf"
  rw := spillRw
  pre := fun rf ws _ => rf.get .x12 = 0x10000 ∧ ws = dwordBytes v
  post := fun rf ws _ => rf.get .x10 = 5 ∧ rf.get .x12 = 0x10000
    ∧ ws = dwordBytes v
  body := .block "set" [.LI .x10 5]

theorem leafFn_spec (v base : Word) : (leafFn v).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, (by decide : spillRw.wf)⟩
  case leaf.post =>
    rintro rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hx12, hslot⟩, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, hslot⟩
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx12

/-- The leaf as a callee at `0x2000`. -/
def leafHandle (v : Word) : FnHandle :=
  (leafFn v).toHandle 0x2000 (leafFn_spec v 0x2000)
    ((by decide : 4 * ((leafFn 0).body.size + 1) ≤ 2 ^ 64))

/-- The mid-level caller: call the leaf.  Ghost `v` is its own spilled
    return address, threaded through the whole call so the packaging can
    restore it. -/
def callerRVFn (v : Word) : Fn where
  name := "callerR"
  rw := spillRw
  pre := fun rf ws _ => rf.get .x12 = 0x10000 ∧ ws = dwordBytes v
  post := fun rf ws _ => rf.get .x10 = 5 ∧ rf.get .x12 = 0x10000
    ∧ ws = dwordBytes v
  body := .call "leaf" (leafHandle v)

/-- The handle-facing view of the caller: the spill slot's contents are
    nobody's business outside the wrapper. -/
def callerRFn : Fn :=
  { callerRVFn 0 with
    pre := fun rf _ _ => rf.get .x12 = 0x10000
    post := fun rf _ _ => rf.get .x10 = 5 ∧ rf.get .x12 = 0x10000 }

/-- Ambient code: the caller's spill-wrapped code at `0x1000` plus the
    leaf's. -/
def callerRCr : CodeReq :=
  (CodeReq.ofProg 0x1000 (callerRFn.programRetR .x12 0 0x1000)).union
    (leafHandle 0).code

theorem callerRVFn_spec (v : Word) :
    (callerRVFn v).SpecR (0x1000 + 4) callerRCr := by
  vcgen
  case region => exact ⟨Region.empty_wf, (by decide : spillRw.wf)⟩
  case code =>
    intro a i h
    have h' : CodeReq.ofProg 0x1000 (callerRFn.programRetR .x12 0 0x1000)
        a = some i := by
      show CodeReq.ofProg 0x1000 (Instr.SD .x12 .x1 0 ::
        (callerRFn.body.flatten (0x1000 + 4)
          ++ [Instr.LD .x1 .x12 0, Instr.JALR .x0 .x1 0])) a = some i
      apply ofProg_cons_tail
        ((by decide : 4 * ((callerRFn.body.flatten (0x1000 + 4)
          ++ [Instr.LD .x1 .x12 0, Instr.JALR .x0 .x1 0]).length + 1) ≤ 2 ^ 64))
      apply ofProg_mono_left
      exact h
    simp only [callerRCr, CodeReq.union, h']
  case callees =>
    refine ⟨?_, rfl, rfl⟩
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hlen0 : ((leafFn 0).programRet 0x2000).length = 2 := by decide
    have hlen : ((leafFn v).programRet 0x2000).length = 2 := hlen0
    rw [hlen] at hk
    simp only [callerRCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000 (callerRFn.programRetR .x12 0 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hlen' : (callerRFn.programRetR .x12 0 0x1000).length = 4 := by
        decide
      rw [hlen'] at hk'
      bv_omega
  case calls =>
    have h0 : (callerRVFn 0).body.callsOk (0x1000 + 4) :=
      ⟨by decide, by decide, by decide⟩
    exact h0
  case callerR.leaf.pre =>
    exact fun rf ws A h => h
  case callerR.post =>
    exact fun rf ws A h => h

private theorem callerR_hcode : ∀ a i,
    CodeReq.ofProg 0x1000 (callerRFn.programRetR .x12 0 0x1000) a = some i →
    callerRCr a = some i := by
  intro a i h
  simp only [callerRCr, CodeReq.union, h]

private theorem callerR_haddr : ∀ rf ws A, callerRFn.pre rf ws A →
    rf.get .x12 + signExtend12 0 = callerRFn.rw.base + BitVec.ofNat 64 0 := by
  intro rf ws A h
  rw [show rf.get .x12 = 0x10000 from h]
  decide

private theorem callerR_haddrPost : ∀ (v : Word) rf ws A,
    (callerRVFn v).post rf ws A →
    rf.get .x12 + signExtend12 0 = callerRFn.rw.base + BitVec.ofNat 64 0 := by
  intro v rf ws A h
  rw [show rf.get .x12 = 0x10000 from h.2.1]
  decide

private theorem callerR_hspre : ∀ (v : Word) rf ws A, callerRFn.pre rf ws A →
    ws.length = callerRFn.rw.len →
    (callerRVFn v).pre rf (setBytes ws 0 (dwordBytes v)) A := by
  intro v rf ws A h hlen
  refine ⟨h, ?_⟩
  have hlen8 : ws.length = 8 := hlen
  have h1 := setBytes_slot ws (dwordBytes v) 0
    (by rw [length_dwordBytes]; omega)
  rw [List.drop_zero, length_dwordBytes,
    List.take_of_length_le (by rw [length_setBytes]; omega)] at h1
  exact h1

private theorem callerR_hspost : ∀ (v : Word) rf ws A,
    (callerRVFn v).post rf ws A → callerRFn.post rf ws A :=
  fun _ _ _ _ h => ⟨h.1, h.2.1⟩

private theorem callerR_hslot : ∀ (v : Word) rf ws A,
    (callerRVFn v).post rf ws A → ws.length = callerRFn.rw.len →
    (ws.drop 0).take 8 = dwordBytes v := by
  intro v rf ws A h hlen
  rw [h.2.2, List.drop_zero,
    List.take_of_length_le (by rw [length_dwordBytes])]

/-- The caller, packaged as a callee: its `ra` is spilled to the scratch
    slot around the body.  This is the "callers as callees" milestone: the
    packaged handle can itself be called. -/
def callerRHandle : FnHandle :=
  callerRFn.toHandleR 0x1000 callerRCr .x12 0 0
    (fun v => (callerRVFn v).pre) (fun v => (callerRVFn v).post)
    (by decide)
    ((by decide : spillRw.wf))
    (by decide) ((by decide : 0 + 8 ≤ spillRw.len))
    ((by decide : 4 * (callerRFn.body.size + 3) ≤ 2 ^ 64))
    (fun v => callerRVFn_spec v)
    callerR_hcode callerR_haddr callerR_haddrPost
    callerR_hspre callerR_hspost callerR_hslot

/-- A top-level caller consuming the packaged handle: the mid-level caller
    really is a callee. -/
def topFn : Fn where
  name := "top"
  rw := spillRw
  pre := fun rf _ _ => rf.get .x12 = 0x10000
  post := fun rf _ _ => rf.get .x10 = 5 ∧ rf.get .x12 = 0x10000
  body := .call "callerR" callerRHandle

/-- Ambient code of the top-level caller at `0x3000`. -/
def topCr : CodeReq :=
  (CodeReq.ofProg 0x3000 (topFn.body.flatten 0x3000)).union callerRCr

theorem topFn_spec : topFn.SpecR 0x3000 topCr := by
  vcgen
  case code =>
    intro a i h
    simp only [topCr, CodeReq.union, h]
  case callees =>
    refine ⟨?_, rfl, rfl⟩
    intro a i h
    -- callerRHandle.code = callerRCr: two ofProg ranges, both away from 0x3000
    have h' : callerRCr a = some i := h
    simp only [topCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x3000 (topFn.body.flatten 0x3000)
      (fun k' hk' heq => ?_)]
    · exact h'
    · have hlen' : (topFn.body.flatten 0x3000).length = 1 := by decide
      rw [hlen'] at hk'
      have hk1 : k' = 0 := by omega
      subst hk1
      -- the address 0x3000 carries no code in callerRCr
      have hnone : callerRCr (0x3000 + BitVec.ofNat 64 (4 * 0)) = none := by
        decide
      rw [← heq, h'] at hnone
      cases hnone
  case calls =>
    exact ⟨by decide, by decide, by decide⟩
  case top.callerR.pre =>
    exact fun rf ws A h => h
  case top.post =>
    exact fun rf ws A h => h

-- ============================================================================
-- Packaging a hand-verified routine (atom-form triple) as a callee
-- ============================================================================

/-- A hand-written (non-SAsm) routine: `a0 := a0 + a1; ret`. -/
def handAddProg : Program := [.ADD .x10 .x10 .x11, .JALR .x0 .x1 0]

/-- The exposed registers `handAddProg` does not touch. -/
private def handAddRest : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The handle contract for `handAddProg`, proved from the routine's
    atom-form per-instruction specs — the template for packaging any
    existing hand-verified `cpsTripleWithin` as an SAsm callee: peel the
    touched registers off `regFileIs` (`regFileOn_perm` + `regFileOn_cons`),
    frame the rest, run the atom-form steps, and re-fold with
    `regFileOn_congr`. -/
theorem handAdd_sound (a b : Word) : ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
    cpsTripleWithin 2 0x4000 ret (CodeReq.ofProg 0x4000 handAddProg)
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
        (fun rf _ _ => rf.get .x10 = a ∧ rf.get .x11 = b))
      (((.x1 : Reg) ↦ᵣ ret) ** asrtM Region.empty RwRegion.empty
        (fun rf _ _ => rf.get .x10 = a + b)) := by
  intro ret halign
  rw [sepConj_comm' ((.x1 : Reg) ↦ᵣ ret) (asrtM Region.empty RwRegion.empty
    (fun rf _ _ => rf.get .x10 = a ∧ rf.get .x11 = b))]
  apply cpsTripleWithin_exists_pre_M_frame
  intro rf ws A hlen hApc hpre
  obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨hx10, hx11⟩ := hpre
  -- peel a0/a1 off the register-file atom
  have hsplit : ∀ rf' : RegFile, regFileIs rf'
      = (((.x10 : Reg) ↦ᵣ rf'.get .x10) ** (((.x11 : Reg) ↦ᵣ rf'.get .x11) **
          regFileOn handAddRest rf')) := by
    intro rf'
    rw [regFileIs_eq_regFileOn,
      regFileOn_perm exposedRegs (.x10 :: .x11 :: handAddRest) rf'
        (by intro r; cases r <;> simp [exposedRegs, handAddRest]),
      regFileOn_cons _ _ _ (by decide), regFileOn_cons _ _ _ (by decide)]
  -- the updated valuation (definitionally: a0 the sum, everything else rf)
  set rf' : RegFile := fun r => if r = .x10 then rf.get .x10 + rf.get .x11 else rf r
    with hrf'
  have hrest : regFileOn handAddRest rf = regFileOn handAddRest rf' :=
    regFileOn_congr _ _ _ (by intro r hr; fin_cases hr <;> rfl)
  -- ADD step, framed with the untouched remainder + ambient A + ra
  have hadd := add_spec_rd_eq_rs1_within .x10 .x11 (rf.get .x10) (rf.get .x11)
    0x4000 (by decide)
  have haddC := cpsTripleWithin_extend_code
    (fun a' i h => show CodeReq.ofProg 0x4000
        [Instr.ADD .x10 .x10 .x11, Instr.JALR .x0 .x1 0] a' = some i from
      ofProg_head a' i h) hadd
  have hFpc : (regFileOn handAddRest rf ** (A ** ((.x1 : Reg) ↦ᵣ ret))).pcFree :=
    pcFree_sepConj (pcFree_regFileOn _ _) (pcFree_sepConj hApc (by pcFree))
  have haddF := cpsTripleWithin_frameR
    (regFileOn handAddRest rf ** (A ** ((.x1 : Reg) ↦ᵣ ret))) hFpc haddC
  -- return step over the post-state atoms
  have hjal := Fn.jalr_ret_spec (0x4000 + 4) ret halign
    (P := ((.x10 : Reg) ↦ᵣ rf.get .x10 + rf.get .x11) **
      (((.x11 : Reg) ↦ᵣ rf.get .x11) ** (regFileOn handAddRest rf ** A)))
    (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree)
      (pcFree_sepConj (pcFree_regFileOn _ _) hApc)))
  have hjalC := cpsTripleWithin_extend_code
    (fun a' i h => by
      show CodeReq.ofProg 0x4000
        [Instr.ADD .x10 .x10 .x11, Instr.JALR .x0 .x1 0] a' = some i
      apply ofProg_cons_tail (by decide)
      rw [CodeReq.ofProg_singleton]
      exact h) hjal
  -- assemble
  have hseq := cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_weaken
      (P' := (((regFileIs rf) ** bytesRegion RwRegion.empty.base []) ** A) **
        (bytesRegion Region.empty.base Region.empty.bytes ** ((.x1 : Reg) ↦ᵣ ret)))
      (Q' := ((.x1 : Reg) ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ rf.get .x10 + rf.get .x11) **
          (((.x11 : Reg) ↦ᵣ rf.get .x11) ** (regFileOn handAddRest rf ** A))))
      (fun hp hh => by
        rw [show bytesRegion RwRegion.empty.base [] = empAssertion from rfl,
          show bytesRegion Region.empty.base Region.empty.bytes = empAssertion
            from rfl,
          sepConj_emp_right', sepConj_emp_left', hsplit rf] at hh
        xperm_hyp hh)
      (fun hp hh => by xperm_hyp hh)
      haddF)
    hjalC
  refine cpsTripleWithin_weaken (fun hp hh => hh) ?_ hseq
  intro hp hh
  refine sepConj_mono_right (fun hq hx => ?_) hp hh
  show (asrtOf RwRegion.empty (fun rf _ _ => rf.get .x10 = a + b) **
    bytesRegion Region.empty.base Region.empty.bytes) hq
  rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion from rfl,
    sepConj_emp_right']
  refine ⟨rf', [], A, rfl, hApc, ?_, ?_⟩
  · show rf.get .x10 + rf.get .x11 = a + b
    rw [hx10, hx11]
  · have hv10 : rf'.get .x10 = rf.get .x10 + rf.get .x11 := by rw [hrf']; rfl
    have hv11 : rf'.get .x11 = rf.get .x11 := by rw [hrf']; rfl
    rw [show bytesRegion RwRegion.empty.base [] = empAssertion from rfl,
      sepConj_emp_right', hsplit rf', hv10, hv11, ← hrest]
    xperm_hyp hx

/-- The packaged hand routine at `0x4000`. -/
def handAddHandle (a b : Word) : FnHandle where
  entry := 0x4000
  code := CodeReq.ofProg 0x4000 handAddProg
  nSteps := 2
  region := Region.empty
  rw := RwRegion.empty
  pre := fun rf _ _ => rf.get .x10 = a ∧ rf.get .x11 = b
  post := fun rf _ _ => rf.get .x10 = a + b
  sound := handAdd_sound a b

/-- An SAsm caller of the hand-verified routine. -/
def callerHFn : Fn where
  name := "callerH"
  pre := fun _ _ _ => True
  post := fun rf _ _ => rf.get .x10 = 12
  body :=
    .block "args" [.LI .x10 5, .LI .x11 7] ;;;
    .call "handAdd" (handAddHandle 5 7)

def callerHCr : CodeReq :=
  (CodeReq.ofProg 0x1000 (callerHFn.body.flatten 0x1000)).union
    (handAddHandle 5 7).code

theorem callerHFn_spec : callerHFn.SpecR 0x1000 callerHCr := by
  vcgen
  case code =>
    intro a i h
    simp only [callerHCr, CodeReq.union, h]
  case callees =>
    refine ⟨trivial, ?_, rfl, rfl⟩
    intro a i h
    obtain ⟨k, hk, rfl⟩ := ofProg_some_range h
    have hlen : (handAddProg : List Instr).length = 2 := by decide
    rw [hlen] at hk
    simp only [callerHCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000 (callerHFn.body.flatten 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hlen' : (callerHFn.body.flatten 0x1000).length = 3 := by decide
      rw [hlen'] at hk'
      bv_omega
  case calls =>
    exact ⟨trivial, by decide, by decide, by decide⟩
  case callerH.handAdd.pre =>
    rintro rf ws A ⟨rf₀, ws₀, -, -, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    constructor
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case callerH.post =>
    intro rf ws A h
    show rf.get .x10 = 12
    have h' : rf.get .x10 = 5 + 7 := h
    rw [h']
    decide

end ExamplesVc
end SAsm
end EvmAsm.Rv64
