/-
  EvmAsm.Rv64.SAsm.ExamplesVc

  End-to-end demos of the SAsm verification pipeline: define an `Fn`,
  state its `Spec`, run `vcgen`, and discharge the remaining named pure
  goals.  These double as regression tests for the tactic.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SAsm.AssertionSpec
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.MultiDword
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

-- ============================================================================
-- Assertion contracts + the call-granularity frame rule (frameA)
-- ============================================================================

/-- A callee whose contract owns an ambient separation-logic cell (ghost
    value `v`): the cell rides through the body untouched — blocks cannot
    reach the ambient assertion. -/
def cellKeepFn (v : Word) : Fn where
  name := "cellKeep"
  pre := fun _ _ A => A = ((0x10100 : Word) ↦ₘ v)
  post := fun rf _ A => rf.get .x10 = 1 ∧ A = ((0x10100 : Word) ↦ₘ v)
  body := .block "one" [.LI .x10 1]

theorem cellKeepFn_spec (v base : Word) : (cellKeepFn v).Spec base := by
  vcgen
  case cellKeep.post =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, hA, rfl, rfl⟩
    refine ⟨?_, hA⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_self _ _ _ (by decide)]

/-- The same contract published as a readable Assertion triple. -/
theorem cellKeepFn_specA (v base : Word) :
    (cellKeepFn v).SpecA base
      (SState Region.empty RwRegion.empty (fun _ _ => True)
        (fun _ _ => (0x10100 : Word) ↦ₘ v))
      (SState Region.empty RwRegion.empty (fun rf _ => rf.get .x10 = 1)
        (fun _ _ => (0x10100 : Word) ↦ₘ v)) := by
  refine Fn.specA_of_spec _ _ (cellKeepFn_spec v base) ?_ ?_
  · exact asrtM_mono (fun rf ws A h => h.2)
  · exact asrtM_mono (fun rf ws A h => ⟨h.1, h.2⟩)

/-- The cell-owning callee at `0x5000`. -/
def cellKeepHandle (v : Word) : FnHandle :=
  (cellKeepFn v).toHandle 0x5000 (cellKeepFn_spec v 0x5000)
    ((by decide : 4 * ((cellKeepFn 0).body.size + 1) ≤ 2 ^ 64))

/-- A caller owning TWO ambient cells: the callee needs only the first, so
    the call site frames the second with `FnHandle.frameA`. -/
def twoCellsFn (v w : Word) : Fn where
  name := "twoCells"
  pre := fun _ _ A =>
    A = (((0x10100 : Word) ↦ₘ v) ** ((0x10108 : Word) ↦ₘ w))
  post := fun rf _ A => rf.get .x10 = 1 ∧
    A = (((0x10100 : Word) ↦ₘ v) ** ((0x10108 : Word) ↦ₘ w))
  body := .call "cellKeep"
    ((cellKeepHandle v).frameA ((0x10108 : Word) ↦ₘ w) pcFree_memIs)

def twoCellsCr (v w : Word) : CodeReq :=
  (CodeReq.ofProg 0x1000 ((twoCellsFn v w).body.flatten 0x1000)).union
    (cellKeepHandle v).code

theorem twoCellsFn_spec (v w : Word) :
    (twoCellsFn v w).SpecR 0x1000 (twoCellsCr v w) := by
  vcgen
  case code =>
    intro a i h
    simp only [twoCellsCr, CodeReq.union, h]
  case callees =>
    refine ⟨?_, rfl, rfl⟩
    intro a i h
    obtain ⟨k, hk, rfl⟩ := ofProg_some_range h
    have hlen0 : ((cellKeepFn 0).programRet 0x5000).length = 2 := by decide
    have hlen : ((cellKeepFn v).programRet 0x5000).length = 2 := hlen0
    rw [hlen] at hk
    simp only [twoCellsCr, CodeReq.union]
    rw [CodeReq.ofProg_none_range 0x1000 ((twoCellsFn v w).body.flatten 0x1000)
      (fun k' hk' heq => ?_)]
    · exact h
    · have hlen0' : ((twoCellsFn 0 0).body.flatten 0x1000).length = 1 := by decide
      have hlen' : ((twoCellsFn v w).body.flatten 0x1000).length = 1 := hlen0'
      rw [hlen'] at hk'
      bv_omega
  case calls =>
    have h0 : (twoCellsFn 0 0).body.callsOk 0x1000 :=
      ⟨by decide, by decide, by decide⟩
    exact h0
  case twoCells.cellKeep.pre =>
    rintro rf ws A hA
    exact ⟨(0x10100 : Word) ↦ₘ v, pcFree_memIs, hA, rfl⟩
  case twoCells.post =>
    rintro rf ws A ⟨A₀, hA0pc, rfl, hx10, hA0eq⟩
    exact ⟨hx10, by rw [hA0eq]⟩

-- ============================================================================
-- Ghost steps: reshaping the ambient assertion mid-body
-- ============================================================================

/-- A ghost step commuting the two ambient cells: no code, one entailment
    VC.  (The stand-in for fold/unfold of recursive predicates.) -/
def swapCellsFn (v w : Word) : Fn where
  name := "swapCells"
  pre := fun _ _ A =>
    A = (((0x10100 : Word) ↦ₘ v) ** ((0x10108 : Word) ↦ₘ w))
  post := fun _ _ A =>
    A = (((0x10108 : Word) ↦ₘ w) ** ((0x10100 : Word) ↦ₘ v))
  body := .ghost "swap"
    (fun _ _ _ A' => A' = (((0x10108 : Word) ↦ₘ w) ** ((0x10100 : Word) ↦ₘ v)))

theorem swapCellsFn_spec (v w base : Word) : (swapCellsFn v w).Spec base := by
  vcgen
  case swapCells.swap =>
    rintro rf ws A hA hApc hsat
    refine ⟨_, rfl, ?_, pcFree_sepConj pcFree_memIs pcFree_memIs⟩
    intro hp hh
    rw [hA] at hh
    rw [sepConj_comm']
    exact hh
  case swapCells.post =>
    rintro rf ws A' ⟨A, hA, hsat, rfl⟩
    rfl

-- ============================================================================
-- Focus blocks: reading pointer-owned memory through the ambient assertion
-- ============================================================================

/-- Load the dword that the ambient assertion owns at the address in `a1`:
    the focus block opens the cell as the block's writable window (the
    annotation names the decomposition), the load routes into it, and a
    ghost step reseals the ambient assertion. -/
def focusReadFn (q v : Word) : Fn where
  name := "focusRead"
  pre := fun rf _ A => rf.get .x11 = q ∧ A = bytesRegion q (dwordBytes v)
  post := fun rf _ A => rf.get .x10 = v ∧ A = bytesRegion q (dwordBytes v)
  body :=
    .blockAt "win" .x11
      (fun _ _ _ win rest => win = dwordBytes v ∧ rest = empAssertion)
      [.LD .x10 .x11 0] ;;;
    .ghost "seal" (fun _ _ _ A' => A' = bytesRegion q (dwordBytes v))

theorem focusReadFn_spec (q v base : Word) (hwf : RwRegion.wf ⟨q, 8⟩) :
    (focusReadFn q v).Spec base := by
  have hidx : ∀ rf : RegFile, rf.get .x11 = q →
      ((rf.get .x11 + signExtend12 (0 : BitVec 12)) - rf.get .x11).toNat = 0 := by
    intro rf _
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  vcgen
  case focusRead.win.focus =>
    rintro rf ws A ⟨hx11, hA⟩ hApc hp hhp
    refine ⟨dwordBytes v, empAssertion, ⟨rfl, rfl⟩, ?_, pcFree_emp, ?_⟩
    · rw [sepConj_emp_right', hx11]
      rw [hA] at hhp
      exact hhp
    · rw [hx11, length_dwordBytes]
      exact hwf
  case focusRead.win.mem =>
    rintro rf ws A win rest hws ⟨hx11, hA⟩ ⟨rfl, rfl⟩ hsat
    simp only [blockVCs, loadSem, inRw, Region.loadOk,
      hidx rf hx11, length_dwordBytes]
    rw [if_pos (by omega)]
    exact ⟨⟨by omega, by omega⟩, trivial⟩
  case focusRead.seal =>
    rintro rf ws A ⟨rf₀, A₀, win, rest, hlen, ⟨hx11, hA₀⟩, hsat, ⟨rfl, rfl⟩,
      rfl, rfl⟩ hApc hsat'
    refine ⟨_, rfl, ?_, bytesRegion_pcFree _ _⟩
    intro hp hh
    rw [sepConj_emp_right'] at hh
    rw [← hx11]
    -- the window after a pure load is definitionally unchanged
    exact hh
  case focusRead.post =>
    rintro rf' ws' A' ⟨A1, ⟨rf₀, A₀, win, rest, hlen, ⟨hx11, hA₀⟩, hsat,
      ⟨rfl, rfl⟩, rfl, rfl⟩, hsat1, rfl⟩
    refine ⟨?_, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem]
    rw [if_pos (show inRw (rf₀.get .x11) (dwordBytes v)
        (rf₀.get .x11 + signExtend12 0) 8 from by
      unfold inRw
      rw [hidx rf₀ hx11, length_dwordBytes])]
    rw [RegFile.get_set_self _ _ _ (by decide)]
    show Region.dwordAt ⟨rf₀.get .x11, dwordBytes v⟩
      (rf₀.get .x11 + signExtend12 0) = v
    unfold Region.dwordAt
    rw [show ((rf₀.get .x11 + signExtend12 0)
        - (⟨rf₀.get .x11, dwordBytes v⟩ : Region).base).toNat = 0 from
      hidx rf₀ hx11]
    rw [List.drop_zero, List.take_of_length_le (by rw [length_dwordBytes])]
    exact packBytes_dwordBytes v

/-- Harvesting a pure fact trapped inside the ambient assertion: ghost
    steps receive satisfiability of the current `A`, so facts baked into
    predicates (`⌜…⌝` conjuncts: nil-pointers, node well-formedness) reach
    the pure VCs through the ghost relation. -/
def harvestFn (n : Word) : Fn where
  name := "harvest"
  pre := fun _ _ A => A = (⌜n = 7⌝ ** empAssertion)
  post := fun _ _ A => A = empAssertion ∧ n = 7
  body := .ghost "get" (fun _ _ _ A' => A' = empAssertion ∧ n = 7)

theorem harvestFn_spec (n base : Word) : (harvestFn n).Spec base := by
  vcgen
  case harvest.get =>
    rintro rf ws A hA hApc hsat
    have h7 : n = 7 := by
      obtain ⟨hp, hhp⟩ := hsat
      rw [hA] at hhp
      exact ((sepConj_pure_left hp).mp hhp).1
    refine ⟨empAssertion, ⟨rfl, h7⟩, ?_, pcFree_emp⟩
    intro hp hh
    rw [hA] at hh
    exact ((sepConj_pure_left hp).mp hh).2
  case harvest.post =>
    rintro rf ws A' ⟨A, hA, hsat, rfl, h7⟩
    exact ⟨rfl, h7⟩

-- ============================================================================
-- Multi-dword focus blocks: `revCellFn`
--
-- The worked example for docs/sasm-howto.md ("Multi-dword focus blocks"):
-- one focus block that loads all four dwords of a 32-byte cell and stores
-- them back reversed.  The recipe: per-step `execInstrRF_ld_dword` /
-- `execInstrRF_sd_dword` rewrites (Sym.lean) — each resolves its routing
-- `if` once and for all, so no nested `if` trees ever appear — plus the
-- MultiDword slice/splice algebra for the window contents.
-- ============================================================================

/-- A 32-byte cell of four dwords (LSB dword first). -/
def cell32 (l0 l1 l2 l3 : Word) : List (BitVec 8) :=
  dwordBytes l0 ++ (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3))

@[simp] theorem length_cell32 (l0 l1 l2 l3 : Word) :
    (cell32 l0 l1 l2 l3).length = 32 := by
  simp [cell32]

/-- The dword slices of a 32-byte cell, packed. -/
theorem cell32_dword0 (l0 l1 l2 l3 : Word) :
    packBytes (((cell32 l0 l1 l2 l3).drop 0).take 8) = l0 :=
  packDword_at0 ..

theorem cell32_drop8 (l0 l1 l2 l3 : Word) :
    (cell32 l0 l1 l2 l3).drop 8
      = dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3) := by
  have h := drop8_dword_append l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) 0
  simp only [Nat.add_zero, List.drop_zero] at h
  rw [cell32, h]

theorem cell32_dword1 (l0 l1 l2 l3 : Word) :
    packBytes (((cell32 l0 l1 l2 l3).drop 8).take 8) = l1 := by
  rw [cell32_drop8, take8_dword_append, packBytes_dwordBytes]

theorem cell32_drop16 (l0 l1 l2 l3 : Word) :
    (cell32 l0 l1 l2 l3).drop 16 = dwordBytes l2 ++ dwordBytes l3 := by
  have h1 := drop8_dword_append l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) 8
  have h2 := drop8_dword_append l1 (dwordBytes l2 ++ dwordBytes l3) 0
  simp only [Nat.reduceAdd] at h1
  simp only [Nat.add_zero, List.drop_zero] at h2
  rw [cell32, h1, h2]

theorem cell32_dword2 (l0 l1 l2 l3 : Word) :
    packBytes (((cell32 l0 l1 l2 l3).drop 16).take 8) = l2 := by
  rw [cell32_drop16, take8_dword_append, packBytes_dwordBytes]

theorem cell32_drop24 (l0 l1 l2 l3 : Word) :
    (cell32 l0 l1 l2 l3).drop 24 = dwordBytes l3 := by
  have h1 := drop8_dword_append l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) 16
  have h2 := drop8_dword_append l1 (dwordBytes l2 ++ dwordBytes l3) 8
  have h3 := drop8_dword_append l2 (dwordBytes l3) 0
  simp only [Nat.reduceAdd] at h1 h2
  simp only [Nat.add_zero, List.drop_zero] at h3
  rw [cell32, h1, h2, h3]

theorem cell32_dword3 (l0 l1 l2 l3 : Word) :
    packBytes (((cell32 l0 l1 l2 l3).drop 24).take 8) = l3 := by
  rw [cell32_drop24, List.take_of_length_le (by rw [length_dwordBytes]),
    packBytes_dwordBytes]

/-- Splicing a dword at each cell offset. -/
theorem cell32_set0 (l0 l1 l2 l3 v : Word) :
    setBytes (cell32 l0 l1 l2 l3) 0 (dwordBytes v) = cell32 v l1 l2 l3 := by
  rw [cell32, setBytes_dword_at0, cell32]

theorem cell32_set8 (l0 l1 l2 l3 v : Word) :
    setBytes (cell32 l0 l1 l2 l3) 8 (dwordBytes v) = cell32 l0 v l2 l3 := by
  have h1 := setBytes_dword_past l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) (dwordBytes v) 0
  simp only [Nat.add_zero] at h1
  rw [cell32, h1, setBytes_dword_at0, cell32]

theorem cell32_set16 (l0 l1 l2 l3 v : Word) :
    setBytes (cell32 l0 l1 l2 l3) 16 (dwordBytes v) = cell32 l0 l1 v l3 := by
  have h1 := setBytes_dword_past l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) (dwordBytes v) 8
  have h2 := setBytes_dword_past l1
    (dwordBytes l2 ++ dwordBytes l3) (dwordBytes v) 0
  simp only [Nat.reduceAdd] at h1
  simp only [Nat.add_zero] at h2
  rw [cell32, h1, h2, setBytes_dword_at0, cell32]

theorem cell32_set24 (l0 l1 l2 l3 v : Word) :
    setBytes (cell32 l0 l1 l2 l3) 24 (dwordBytes v) = cell32 l0 l1 l2 v := by
  have h1 := setBytes_dword_past l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) (dwordBytes v) 16
  have h2 := setBytes_dword_past l1
    (dwordBytes l2 ++ dwordBytes l3) (dwordBytes v) 8
  have h3 := setBytes_dword_past l2 (dwordBytes l3) (dwordBytes v) 0
  simp only [Nat.reduceAdd] at h1 h2
  simp only [Nat.add_zero] at h3
  rw [cell32, h1, h2, h3, setBytes_dword_full _ _ (length_dwordBytes l3),
    cell32]

/-- Load the four dwords of the cell at `a2`, store them back reversed. -/
def revCellBlock : List Instr :=
  [.LD .x5 .x12 0, .LD .x6 .x12 8, .LD .x7 .x12 16, .LD .x14 .x12 24,
   .SD .x12 .x14 0, .SD .x12 .x7 8, .SD .x12 .x6 16, .SD .x12 .x5 24]

/-- Focus annotation: window = the whole cell, remainder = its
    well-formedness (all four limbs are `Fn`-level binders, so nothing
    needs restating). -/
def revCellR (p l0 l1 l2 l3 : Word) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun _ _ _ win rest =>
    win = cell32 l0 l1 l2 l3 ∧ rest = ⌜RwRegion.wf ⟨p, 32⟩⌝

/-- Reverse the four dwords of the 32-byte cell at `a2`. -/
def revCellFn (p l0 l1 l2 l3 : Word) : Fn where
  name := "revCell"
  pre := fun rf _ A => rf.get .x12 = p ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (cell32 l0 l1 l2 l3))
  post := fun rf _ A => rf.get .x12 = p ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (cell32 l3 l2 l1 l0))
  body := .blockAt "rev" .x12 (revCellR p l0 l1 l2 l3) revCellBlock

/-- The signExtend12 address arithmetic, once per offset. -/
private theorem revCell_off (b : Word) (ofs : BitVec 12) (k : Nat)
    (hofs : signExtend12 ofs = BitVec.ofNat 64 k) (hk : k < 2 ^ 12) :
    ((b + signExtend12 ofs) - b).toNat = k := by
  rw [hofs]
  bv_omega

/-- The engine: the block loads `l0..l3` and rewrites the window to the
    reversed cell.  One `execInstrRF_ld_dword`/`execInstrRF_sd_dword`
    rewrite per instruction — the routing `if`s never appear. -/
private theorem revCell_engine (reg : Region) (rf : RegFile)
    (l0 l1 l2 l3 : Word) :
    execBlock reg (rf.get .x12) rf (cell32 l0 l1 l2 l3) revCellBlock
      = ((((rf.set .x5 l0).set .x6 l1).set .x7 l2).set .x14 l3,
         cell32 l3 l2 l1 l0) := by
  have h0 := revCell_off (rf.get .x12) 0 0 (by decide) (by decide)
  -- the base register is never a destination, so its value is stable
  have hx12a : (rf.set .x5 l0).get .x12 = rf.get .x12 :=
    RegFile.get_set_ne _ _ _ _ (by decide)
  have hx12b : ((rf.set .x5 l0).set .x6 l1).get .x12 = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12a]
  have hx12c : (((rf.set .x5 l0).set .x6 l1).set .x7 l2).get .x12
      = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12b]
  have hx12d : ((((rf.set .x5 l0).set .x6 l1).set .x7 l2).set .x14 l3).get .x12
      = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12c]
  rw [show revCellBlock
      = [.LD .x5 .x12 0, .LD .x6 .x12 8, .LD .x7 .x12 16, .LD .x14 .x12 24,
         .SD .x12 .x14 0, .SD .x12 .x7 8, .SD .x12 .x6 16, .SD .x12 .x5 24]
    from rfl]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 0 l0
    h0 (by simp) (cell32_dword0 ..)]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 8 l1
    (by rw [hx12a]; exact revCell_off _ 8 8 (by decide) (by decide))
    (by simp) (cell32_dword1 ..)]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 16 l2
    (by rw [hx12b]; exact revCell_off _ 16 16 (by decide) (by decide))
    (by simp) (cell32_dword2 ..)]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 24 l3
    (by rw [hx12c]; exact revCell_off _ 24 24 (by decide) (by decide))
    (by simp) (cell32_dword3 ..)]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 0
    (by rw [hx12d]; exact h0)]
  rw [RegFile.get_set_self _ _ _ (by decide), cell32_set0]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 8
    (by rw [hx12d]; exact revCell_off _ 8 8 (by decide) (by decide))]
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), cell32_set8]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 16
    (by rw [hx12d]; exact revCell_off _ 16 16 (by decide) (by decide))]
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), cell32_set16]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 24
    (by rw [hx12d]; exact revCell_off _ 24 24 (by decide) (by decide))]
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), cell32_set24]
  rfl

/-- The `.mem` VCs: rewrite each engine step with the same dword-step
    lemmas, then every routing condition is about the ORIGINAL `rf`/window
    and discharges by arithmetic. -/
private theorem revCell_blockVCs (reg : Region) (rf : RegFile)
    (l0 l1 l2 l3 : Word) :
    blockVCs reg (rf.get .x12) rf (cell32 l0 l1 l2 l3) revCellBlock := by
  have h0 := revCell_off (rf.get .x12) 0 0 (by decide) (by decide)
  have hx12a : (rf.set .x5 l0).get .x12 = rf.get .x12 :=
    RegFile.get_set_ne _ _ _ _ (by decide)
  have hx12b : ((rf.set .x5 l0).set .x6 l1).get .x12 = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12a]
  have hx12c : (((rf.set .x5 l0).set .x6 l1).set .x7 l2).get .x12
      = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12b]
  have hx12d : ((((rf.set .x5 l0).set .x6 l1).set .x7 l2).set .x14 l3).get .x12
      = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12c]
  have h8 := revCell_off (rf.get .x12) 8 8 (by decide) (by decide)
  have h16 := revCell_off (rf.get .x12) 16 16 (by decide) (by decide)
  have h24 := revCell_off (rf.get .x12) 24 24 (by decide) (by decide)
  simp only [revCellBlock, blockVCs, loadSem, storeSem,
    execInstrRF_ld_dword _ _ _ _ _ _ _ 0 l0
      h0 (by simp) (cell32_dword0 ..),
    execInstrRF_ld_dword _ _ _ _ _ _ _ 8 l1
      (by rw [hx12a]; exact h8) (by simp) (cell32_dword1 ..),
    execInstrRF_ld_dword _ _ _ _ _ _ _ 16 l2
      (by rw [hx12b]; exact h16) (by simp) (cell32_dword2 ..),
    execInstrRF_ld_dword _ _ _ _ _ _ _ 24 l3
      (by rw [hx12c]; exact h24) (by simp) (cell32_dword3 ..),
    execInstrRF_sd_dword _ _ _ _ _ _ _ 0 (by rw [hx12d]; exact h0),
    execInstrRF_sd_dword _ _ _ _ _ _ _ 8 (by rw [hx12d]; exact h8),
    execInstrRF_sd_dword _ _ _ _ _ _ _ 16 (by rw [hx12d]; exact h16),
    hx12a, hx12b, hx12c, hx12d, inRw, Region.loadOk,
    length_cell32, length_setBytes, h0, h8, h16, h24]
  and_intros <;> trivial

theorem revCellFn_spec (p l0 l1 l2 l3 base : Word) :
    (revCellFn p l0 l1 l2 l3).Spec base := by
  vcgen
  case revCell.rev.focus =>
    rintro rf ws A ⟨hx12, hA⟩ hApc hp hhp
    rw [hA] at hhp
    refine ⟨cell32 l0 l1 l2 l3, _, ⟨rfl, rfl⟩, ?_, pcFree_pure, ?_⟩
    · rw [hx12]
      xperm_hyp hhp
    · rw [hx12, length_cell32]
      exact ((sepConj_pure_left hp).mp hhp).1
  case revCell.rev.mem =>
    rintro rf ws A win rest - - ⟨rfl, rfl⟩ -
    exact revCell_blockVCs _ rf l0 l1 l2 l3
  case revCell.post =>
    rintro rf ws A ⟨rf₀, A₀, win, rest, -, ⟨hx12, hA⟩, -, ⟨rfl, rfl⟩, hrf, hA'⟩
    rw [revCell_engine] at hrf hA'
    rw [hrf, hA']
    constructor
    · show ((((rf₀.set .x5 l0).set .x6 l1).set .x7 l2).set .x14 l3).get .x12 = p
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx12
    · show (bytesRegion (rf₀.get .x12) (cell32 l3 l2 l1 l0) **
          ⌜RwRegion.wf ⟨p, 32⟩⌝) = _
      rw [hx12, sepConj_comm']

-- ============================================================================
-- Byte-granularity focus blocks: `rev4Fn`
--
-- The worked example for docs/sasm-howto.md ("Byte-granularity focus
-- blocks"): reverse a 4-byte cell in place with two unrolled
-- literal-offset swaps.  The recipe:
--   1. `execInstrRF_lbu_byte` / `execInstrRF_sb_byte` (Sym.lean) — one
--      rewrite per byte access, no routing `if`s;
--   2. `setBytes_singleton` + `truncate_zeroExtend_byte` (MultiDword) —
--      each store becomes a plain `List.set` of the original byte;
--   3. for a FIXED-SIZE window, explode the byte list into cons cells
--      (`w = [b0, b1, b2, b3]`) — `List.set`/`getD`/`reverse` then all
--      reduce definitionally, so the engine result and `w.reverse` match
--      by `rfl`-strength reasoning, with no take/drop invariants.
-- ============================================================================

/-- Swap the bytes at literal offsets `lo`/`hi` of the cell at `a2`. -/
def byteSwapAt (lo hi : BitVec 12) : List Instr :=
  [.LBU .x5 .x12 lo, .LBU .x6 .x12 hi, .SB .x12 .x6 lo, .SB .x12 .x5 hi]

def rev4Block : List Instr := byteSwapAt 0 3 ++ byteSwapAt 1 2

def rev4R (p : Word) (w : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    rf.get .x12 = p ∧ win = w ∧ rest = ⌜RwRegion.wf ⟨p, 4⟩⌝

/-- Reverse the 4-byte cell at `a2` in place. -/
def rev4Fn (p : Word) (w : List (BitVec 8)) : Fn where
  name := "rev4"
  pre := fun rf _ A => rf.get .x12 = p ∧ w.length = 4 ∧
    A = (⌜RwRegion.wf ⟨p, 4⟩⌝ ** bytesRegion p w)
  post := fun rf _ A => rf.get .x12 = p ∧
    A = (⌜RwRegion.wf ⟨p, 4⟩⌝ ** bytesRegion p w.reverse)
  body := .blockAt "rev" .x12 (rev4R p w) rev4Block

private theorem rev4_off (b : Word) (ofs : BitVec 12) (k : Nat)
    (hofs : signExtend12 ofs = BitVec.ofNat 64 k) (hk : k < 2 ^ 12) :
    ((b + signExtend12 ofs) - b).toNat = k := by
  rw [hofs]
  bv_omega

/-- The engine over the EXPLODED window: with the four bytes named, every
    `getD`/`set` computes, and the final window is literally the reversal
    (the closing `rfl` checks it by kernel reduction — no take/drop
    invariant anywhere). -/
private theorem rev4_engine (reg : Region) (rf : RegFile)
    (b0 b1 b2 b3 : BitVec 8) :
    execBlock reg (rf.get .x12) rf [b0, b1, b2, b3] rev4Block
      = ((((rf.set .x5 (b0.zeroExtend 64)).set .x6 (b3.zeroExtend 64)).set
            .x5 (b1.zeroExtend 64)).set .x6 (b2.zeroExtend 64),
         [b3, b2, b1, b0]) := by
  have h0 := rev4_off (rf.get .x12) 0 0 (by decide) (by decide)
  have h1 := rev4_off (rf.get .x12) 1 1 (by decide) (by decide)
  have h2 := rev4_off (rf.get .x12) 2 2 (by decide) (by decide)
  have h3 := rev4_off (rf.get .x12) 3 3 (by decide) (by decide)
  have hx12a : ∀ v : Word, (rf.set .x5 v).get .x12 = rf.get .x12 :=
    fun v => RegFile.get_set_ne _ _ _ _ (by decide)
  have hx12b : ∀ v w : Word, ((rf.set .x5 v).set .x6 w).get .x12
      = rf.get .x12 := fun v w => by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12a]
  rw [show rev4Block = [.LBU .x5 .x12 0, .LBU .x6 .x12 3, .SB .x12 .x6 0,
      .SB .x12 .x5 3, .LBU .x5 .x12 1, .LBU .x6 .x12 2, .SB .x12 .x6 1,
      .SB .x12 .x5 2] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 0 h0 (by simp)]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 3
    (by rw [hx12a]; exact h3) (by simp)]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 0
    (by rw [hx12b]; exact h0)]
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 3
    (by rw [hx12b]; exact h3)]
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 1
    (by rw [hx12b]; exact h1) (by simp)]
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ 2
    (by rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12b]; exact h2)
    (by simp)]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 1
    (by rw [RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide), hx12b]; exact h1)]
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ 2
    (by rw [RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide), hx12b]; exact h2)]
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rfl

/-- The `.mem` VCs: byte accesses only need the in-window bound. -/
private theorem rev4_blockVCs (reg : Region) (rf : RegFile)
    (b0 b1 b2 b3 : BitVec 8) :
    blockVCs reg (rf.get .x12) rf [b0, b1, b2, b3] rev4Block := by
  have h0 := rev4_off (rf.get .x12) 0 0 (by decide) (by decide)
  have h1 := rev4_off (rf.get .x12) 1 1 (by decide) (by decide)
  have h2 := rev4_off (rf.get .x12) 2 2 (by decide) (by decide)
  have h3 := rev4_off (rf.get .x12) 3 3 (by decide) (by decide)
  have hx12a : ∀ v : Word, (rf.set .x5 v).get .x12 = rf.get .x12 :=
    fun v => RegFile.get_set_ne _ _ _ _ (by decide)
  have hx12b : ∀ v w : Word, ((rf.set .x5 v).set .x6 w).get .x12
      = rf.get .x12 := fun v w => by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12a]
  rw [show rev4Block = [.LBU .x5 .x12 0, .LBU .x6 .x12 3, .SB .x12 .x6 0,
      .SB .x12 .x5 3, .LBU .x5 .x12 1, .LBU .x6 .x12 2, .SB .x12 .x6 1,
      .SB .x12 .x5 2] from rfl]
  simp only [blockVCs, loadSem, storeSem]
  rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 0 h0 (by simp)]
  dsimp only
  rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 3 (by rw [hx12a]; exact h3) (by simp)]
  dsimp only
  -- the SB steps never change the register file (`execInstrRF_sb_fst`,
  -- a simp lemma), so the later loads' side conditions normalize through
  -- them without resolving the stores
  rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 1
    (by simp only [execInstrRF_sb_fst]; rw [hx12b]; exact h1)
    (by simp [execInstrRF_sb_snd])]
  dsimp only
  rw [execInstrRF_lbu_byte _ _ _ _ _ _ _ 2
    (by simp only [execInstrRF_sb_fst]
        rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12b]; exact h2)
    (by simp [execInstrRF_sb_snd])]
  dsimp only
  simp only [execInstrRF_sb_fst, execInstrRF_sb_snd, hx12a, hx12b,
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
    h0, h1, h2, h3, setBytes_singleton, inRw, Region.loadOk,
    List.length_set, List.length_cons, List.length_nil]
  and_intros <;> trivial

theorem rev4Fn_spec (p : Word) (w : List (BitVec 8)) (base : Word) :
    (rev4Fn p w).Spec base := by
  vcgen
  case rev4.rev.focus =>
    rintro rf ws A ⟨hx12, hw, hA⟩ hApc hp hhp
    rw [hA] at hhp
    refine ⟨w, ⌜RwRegion.wf ⟨p, 4⟩⌝, ⟨hx12, rfl, rfl⟩, ?_, pcFree_pure, ?_⟩
    · rw [hx12]
      xperm_hyp hhp
    · rw [hx12, hw]
      exact ((sepConj_pure_left hp).mp hhp).1
  case rev4.rev.mem =>
    rintro rf ws A win rest - ⟨-, hw, -⟩ ⟨hptr, rfl, rfl⟩ -
    obtain ⟨b0, b1, b2, b3, rfl⟩ : ∃ b0 b1 b2 b3, win = [b0, b1, b2, b3] := by
      rcases win with - | ⟨b0, - | ⟨b1, - | ⟨b2, - | ⟨b3, - | ⟨b4, win⟩⟩⟩⟩⟩ <;>
        simp only [List.length_nil, List.length_cons] at hw <;>
        first
          | omega
          | exact ⟨b0, b1, b2, b3, rfl⟩
    exact rev4_blockVCs _ rf b0 b1 b2 b3
  case rev4.post =>
    rintro rf ws A ⟨rf₀, A₀, win, rest, -, ⟨hx12, hw, -⟩, -, ⟨hptr, rfl, rfl⟩,
      hrf, hA⟩
    obtain ⟨b0, b1, b2, b3, rfl⟩ : ∃ b0 b1 b2 b3, win = [b0, b1, b2, b3] := by
      rcases win with - | ⟨b0, - | ⟨b1, - | ⟨b2, - | ⟨b3, - | ⟨b4, win⟩⟩⟩⟩⟩ <;>
        simp only [List.length_nil, List.length_cons] at hw <;>
        first
          | omega
          | exact ⟨b0, b1, b2, b3, rfl⟩
    -- shrink the equations BEFORE substituting (howto §8)
    rw [rev4_engine] at hrf hA
    dsimp only at hrf hA
    subst hrf
    constructor
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx12
    · rw [hA, hx12, sepConj_comm',
        show ([b0, b1, b2, b3] : List (BitVec 8)).reverse
          = [b3, b2, b1, b0] from rfl]

end ExamplesVc
end SAsm
end EvmAsm.Rv64
