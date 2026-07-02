/-
  EvmAsm.Rv64.SAsm.ExamplesVc

  End-to-end demos of the SAsm verification pipeline: define an `Fn`,
  state its `Spec`, run `vcgen`, and discharge the remaining named pure
  goals.  These double as regression tests for the tactic.
-/

import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace ExamplesVc

open Stmt

/-- `min(a0, a1)` into a0: if a0 ≥u a1 then a0 := a1. -/
def clampFn (x y : Word) : Fn where
  name := "clamp"
  pre := fun rf _ => rf.get .x10 = x ∧ rf.get .x11 = y
  post := fun rf _ =>
    rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
  body := .when "cap" (.bgeu .x10 .x11) (.block "set" [.MV .x10 .x11])

theorem clampFn_spec (x y base : Word) : (clampFn x y).Spec base := by
  vcgen
  case clamp.post =>
    intro rf ws h
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
  pre := fun _ _ => True
  post := fun rf _ => rf.get .x5 = 10
  body :=
    .block "init" [.LI .x5 0, .LI .x6 10] ;;;
    .«while» "loop" (.bltu .x5 .x6) 10
      (fun i rf _ => rf.get .x5 = BitVec.ofNat 64 i ∧ rf.get .x6 = 10 ∧ i ≤ 10)
      (.block "step" [.ADDI .x5 .x5 1])

theorem countFn_spec (base : Word) : countFn.Spec base := by
  vcgen
  case count.loop.inv_init =>
    rintro rf ws ⟨rf₀, ws₀, -, -, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case count.loop.inv_step =>
    rintro i hi rf' ws' ⟨rf₀, ws₀, -, ⟨⟨hx5, hx6, hle⟩, hlt⟩, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6
  case count.loop.exhausted =>
    rintro rf ws ⟨hx5, hx6, -⟩
    simp only [Cond.holds]
    rw [hx5, hx6]
    decide
  case count.post =>
    intro rf ws h
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
  pre := fun _ _ => True
  post := fun rf _ => rf.get .x10 = 5
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
    rintro rf ws ⟨rf₀, ws₀, -, -, rfl, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    constructor
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case caller.post =>
    intro rf ws h
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
  pre := fun rf _ => rf.get .x10 = inBase ∧ bs ≠ []
  post := fun rf _ =>
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
    rintro rf ws hws ⟨hx10, hne⟩
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial, trivial⟩
    show ((rf.get .x10 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 1
      ≤ bs.length
    rw [haddr rf hx10]
    have := List.length_pos_iff.mpr hne
    omega
  case rlpIsList.post =>
    intro rf' ws' h
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
  pre := fun rf _ => rf.get .x10 = inBase ∧ 8 ≤ bs.length
  post := fun rf _ => rf.get .x11
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
    rintro rf ws hws ⟨hx10, hlen⟩
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
    rintro rf' ws' ⟨rf₀, ws₀, hws₀, ⟨hx10, hlen⟩, rfl, rfl⟩
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
  pre := fun rf _ => rf.get .x10 = inBase ∧ 4 ≤ bs.length
  post := fun rf _ => rf.get .x11
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
    rintro rf ws hws ⟨hx10, hlen⟩
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
    rintro rf' ws' ⟨rf₀, ws₀, hws₀, ⟨hx10, hlen⟩, rfl, rfl⟩
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
  pre := fun rf _ => rf.get .x10 = x ∧ rf.get .x11 = scratch
  post := fun rf _ => rf.get .x10 = x
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
    rintro rf ws hws ⟨hx10, hx11⟩
    have hws8 : ws.length = 8 := hws
    simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, spillFn,
      inRw, Region.loadOk, length_setBytes, hidx rf hx11,
      RegFile.get_set_ne rf .x10 .x11 0 (by decide)]
    rw [if_pos (show 0 + 8 ≤ ws.length from by omega)]
    exact ⟨⟨by omega, by decide⟩, trivial, ⟨by decide, by omega⟩, trivial⟩
  case spill.post =>
    rintro rf' ws' ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11⟩, rfl, rfl⟩
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

end ExamplesVc
end SAsm
end EvmAsm.Rv64
