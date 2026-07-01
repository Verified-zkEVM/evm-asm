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
  pre := fun rf => rf.get .x10 = x ∧ rf.get .x11 = y
  post := fun rf =>
    rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
  body := .when "cap" (.bgeu .x10 .x11) (.block "set" [.MV .x10 .x11])

theorem clampFn_spec (x y base : Word) : (clampFn x y).Spec base := by
  vcgen
  case clamp.post =>
    intro rf h
    show rf.get .x10 = (if BitVec.ult x y then x else y) ∧ rf.get .x11 = y
    rcases h with ⟨rf₀, ⟨⟨hx, hy⟩, hge⟩, rfl⟩ | ⟨⟨hx, hy⟩, hlt⟩
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
  pre := fun _ => True
  post := fun rf => rf.get .x5 = 10
  body :=
    .block "init" [.LI .x5 0, .LI .x6 10] ;;;
    .«while» "loop" (.bltu .x5 .x6) 10
      (fun i rf => rf.get .x5 = BitVec.ofNat 64 i ∧ rf.get .x6 = 10 ∧ i ≤ 10)
      (.block "step" [.ADDI .x5 .x5 1])

theorem countFn_spec (base : Word) : countFn.Spec base := by
  vcgen
  case count.loop.inv_init =>
    rintro rf ⟨rf₀, -, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case count.loop.inv_step =>
    rintro i hi rf' ⟨rf₀, ⟨⟨hx5, hx6, hle⟩, hlt⟩, rfl⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, by omega⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx6
  case count.loop.exhausted =>
    rintro rf ⟨hx5, hx6, -⟩
    simp only [Cond.holds]
    rw [hx5, hx6]
    decide
  case count.post =>
    intro rf h
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
  pre := fun _ => True
  post := fun rf => rf.get .x10 = 5
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
    refine ⟨trivial, ?_, rfl⟩
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
    rintro rf ⟨rf₀, -, rfl⟩
    show (clampFn 5 7).pre _
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, clampFn]
    constructor
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
  case caller.post =>
    intro rf h
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
  pre := fun rf => rf.get .x10 = inBase ∧ bs ≠ []
  post := fun rf =>
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
  case region => exact hwf
  case rlpIsList.load.mem =>
    rintro rf ⟨hx10, hne⟩
    refine ⟨⟨one_dvd _, ?_⟩, trivial, trivial⟩
    show ((rf.get .x10 + signExtend12 (0 : BitVec 12)) - inBase).toNat + 1
      ≤ bs.length
    rw [haddr rf hx10]
    have := List.length_pos_iff.mpr hne
    omega
  case rlpIsList.post =>
    intro rf' h
    show rf'.get .x10 = (if (bs.headD 0).toNat < 0xc0 then 0 else 1)
    obtain ⟨b, tl, rfl⟩ : ∃ b tl, bs = b :: tl := by
      rcases h with ⟨rf₀, ⟨⟨rf₁, ⟨-, hne⟩, -⟩, -⟩, -⟩ | ⟨rf₀, ⟨⟨rf₁, ⟨-, hne⟩, -⟩, -⟩, -⟩ <;>
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
    rcases h with ⟨rf₀, ⟨⟨rf₁, ⟨hx10, -⟩, rfl⟩, hcond⟩, rfl⟩
                | ⟨rf₀, ⟨⟨rf₁, ⟨hx10, -⟩, rfl⟩, hcond⟩, rfl⟩
    · -- not a list: b <u 0xc0
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
        Cond.holds, List.headD_cons] at hcond ⊢
      rw [RegFile.get_set_self _ .x10 _ (by decide)]
      rw [RegFile.get_set_ne _ .x6 .x5 _ (by decide),
        RegFile.get_set_self _ .x5 _ (by decide),
        RegFile.get_set_self _ .x6 _ (by decide),
        hbyte rf₁ hx10] at hcond
      rw [if_pos (hult.mp hcond)]
    · -- a list: ¬ (b <u 0xc0)
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
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
  pre := fun rf => rf.get .x10 = inBase ∧ 8 ≤ bs.length
  post := fun rf => rf.get .x11
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
  case region => exact hwf
  case sszReadOffset.load.mem =>
    rintro rf ⟨hx10, hlen⟩
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · show (4 : Nat) ∣ ((rf.get .x10 + signExtend12 (4 : BitVec 12)) - inBase).toNat
      rw [haddr rf hx10]
    · show ((rf.get .x10 + signExtend12 (4 : BitVec 12)) - inBase).toNat + 4
        ≤ bs.length
      rw [haddr rf hx10]
      omega
  case sszReadOffset.post =>
    rintro rf' ⟨rf₀, ⟨hx10, hlen⟩, rfl⟩
    show RegFile.get _ .x11 = _
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem]
    rw [RegFile.get_set_self _ .x11 _ (by decide)]
    rw [hx10, show signExtend12 (4 : BitVec 12) = (4 : Word) from by decide]
    show BitVec.zeroExtend 64 (Region.word32At ⟨inBase, bs⟩ (inBase + 4)) = _
    unfold Region.word32At Region.byteAt
    rw [show inBase + 4 + 3 - inBase = (7 : Word) from by bv_omega,
      show inBase + 4 + 2 - inBase = (6 : Word) from by bv_omega,
      show inBase + 4 + 1 - inBase = (5 : Word) from by bv_omega,
      show inBase + 4 - inBase = (4 : Word) from by bv_omega]
    rfl

end ExamplesVc
end SAsm
end EvmAsm.Rv64
