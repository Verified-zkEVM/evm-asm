/-
  EvmAsm.Rv64.MemSat

  Satisfiability witnesses for byte-range assertions (bead evm-asm-4ch8f.63).

  `GuestFraming.scratch_sat` (Stateless/EntrySpec.lean) demands an explicit
  heap satisfying `guestInputAssertion input ** scratch` for every admissible
  input — a `cpsHaltTripleWithin` with an unsatisfiable precondition holds
  vacuously, so the framing must come with a non-vacuity witness.  This file
  provides the generic construction: `SatWithin P lo hi` packages "P is
  satisfied by a heap owning ONLY memory dwords inside `[lo, hi)`", and the
  combinators build witnesses for `memIs` / `bytesRegion` / `anyBytes` and
  chain them across `**` for address-ascending, footprint-disjoint regions.

  The footprint bookkeeping is in `Nat` (not `Word`) so the disjointness of
  adjacent ranges is `omega`-territory and never wraps: every valid dword
  address is ≤ `RAM_MEM_END = 0xc0000000` (`isValidDwordAccess`), far below
  `2^64`.
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.PhaseSplit

namespace EvmAsm.Rv64

open EvmAsm.Rv64.SAsm (anyBytes)

/-! ## Footprint-bounded heaps -/

/-- `h` owns nothing except memory dwords whose address lies in `[lo, hi)`
    (as a `Nat`).  The non-memory resources are all unowned, so two heaps
    with disjoint footprint intervals are `Disjoint`. -/
structure PartialState.MemOnlyWithin (h : PartialState) (lo hi : Nat) : Prop where
  regs : ∀ r, h.regs r = none
  code : ∀ a, h.code a = none
  pc : h.pc = none
  publicValues : h.publicValues = none
  privateInput : h.privateInput = none
  inputBufBase : h.inputBufBase = none
  mem : ∀ a, h.mem a ≠ none → lo ≤ a.toNat ∧ a.toNat < hi

/-- `P` is satisfiable by a heap owning only memory dwords in `[lo, hi)`. -/
def Assertion.SatWithin (P : Assertion) (lo hi : Nat) : Prop :=
  ∃ h, P h ∧ h.MemOnlyWithin lo hi

theorem Assertion.SatWithin.sat {P : Assertion} {lo hi : Nat}
    (h : P.SatWithin lo hi) : ∃ hp, P hp :=
  h.elim fun hp hsat => ⟨hp, hsat.1⟩

theorem PartialState.MemOnlyWithin.mono {h : PartialState} {lo hi lo' hi' : Nat}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hw : h.MemOnlyWithin lo hi) :
    h.MemOnlyWithin lo' hi' where
  regs := hw.regs
  code := hw.code
  pc := hw.pc
  publicValues := hw.publicValues
  privateInput := hw.privateInput
  inputBufBase := hw.inputBufBase
  mem := fun a ha => ⟨Nat.le_trans hlo (hw.mem a ha).1,
                      Nat.lt_of_lt_of_le (hw.mem a ha).2 hhi⟩

theorem Assertion.SatWithin.mono {P : Assertion} {lo hi lo' hi' : Nat}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hs : P.SatWithin lo hi) :
    P.SatWithin lo' hi' :=
  hs.elim fun hp ⟨hsat, hw⟩ => ⟨hp, hsat, hw.mono hlo hhi⟩

/-! ## Atoms -/

theorem satWithin_emp (lo hi : Nat) : empAssertion.SatWithin lo hi :=
  ⟨PartialState.empty, rfl,
   { regs := fun _ => rfl, code := fun _ => rfl, pc := rfl,
     publicValues := rfl, privateInput := rfl, inputBufBase := rfl,
     mem := fun _ ha => absurd rfl ha }⟩

theorem satWithin_memIs {a : Word} (v : Word)
    (hvalid : isValidDwordAccess a = true) :
    (a ↦ₘ v).SatWithin a.toNat (a.toNat + 8) :=
  ⟨PartialState.singletonMem a v, ⟨rfl, hvalid⟩,
   { regs := fun _ => rfl, code := fun _ => rfl, pc := rfl,
     publicValues := rfl, privateInput := rfl, inputBufBase := rfl,
     mem := fun a' ha => by
       simp only [PartialState.singletonMem] at ha
       by_cases h : a' == a
       · rw [show a' = a from by simpa using h]; omega
       · simp [h] at ha }⟩

/-! ## Chaining across `**` -/

/-- The workhorse: adjacent (or gap-separated) footprints compose.  The
    left witness owns `[lo, mid)`, the right owns `[mid, hi)`, so they are
    `Disjoint` and their union satisfies `P ** Q` with footprint
    `[lo, hi)`. -/
theorem Assertion.SatWithin.sepConj {P Q : Assertion} {lo mid hi : Nat}
    (hP : P.SatWithin lo mid) (hQ : Q.SatWithin mid hi)
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    (P ** Q).SatWithin lo hi := by
  obtain ⟨h1, hp1, hw1⟩ := hP
  obtain ⟨h2, hp2, hw2⟩ := hQ
  have hdisj : h1.Disjoint h2 := by
    refine ⟨fun r => .inl (hw1.regs r),
            fun a => ?_,
            fun a => .inl (hw1.code a),
            .inl hw1.pc, .inl hw1.publicValues,
            .inl hw1.privateInput, .inl hw1.inputBufBase⟩
    by_cases h1a : h1.mem a = none
    · exact .inl h1a
    · by_cases h2a : h2.mem a = none
      · exact .inr h2a
      · have := (hw1.mem a h1a).2
        have := (hw2.mem a h2a).1
        omega
  refine ⟨h1.union h2, ⟨h1, h2, hdisj, rfl, hp1, hp2⟩, ?_⟩
  refine { regs := ?_, code := ?_, pc := ?_, publicValues := ?_,
           privateInput := ?_, inputBufBase := ?_, mem := ?_ }
  · intro r; simp [PartialState.union, hw1.regs r, hw2.regs r]
  · intro a; simp [PartialState.union, hw1.code a, hw2.code a]
  · simp [PartialState.union, hw1.pc, hw2.pc]
  · simp [PartialState.union, hw1.publicValues, hw2.publicValues]
  · simp [PartialState.union, hw1.privateInput, hw2.privateInput]
  · simp [PartialState.union, hw1.inputBufBase, hw2.inputBufBase]
  · intro a ha
    simp only [PartialState.union] at ha
    by_cases h1a : h1.mem a = none
    · rw [h1a] at ha
      have := hw2.mem a (by simpa using ha)
      omega
    · have := hw1.mem a h1a
      omega

/-- Rewrite the bounds of a witness (bounds are plain `Nat`s, so `omega`
    equalities transport). -/
theorem Assertion.SatWithin.congr_bounds {P : Assertion} {lo hi lo' hi' : Nat}
    (hs : P.SatWithin lo hi) (hlo : lo = lo') (hhi : hi = hi') :
    P.SatWithin lo' hi' := hlo ▸ hhi ▸ hs

/-! ## Valid-address arithmetic -/

/-- Every valid dword address is bounded by `RAM_MEM_END`, so `+ 8` never
    wraps in the constructions below. -/
theorem toNat_le_of_validDword {a : Word} (h : isValidDwordAccess a = true) :
    a.toNat ≤ 0xc0000000 := by
  simp only [isValidDwordAccess, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

theorem toNat_add_ofNat_of_le {a : Word} {k : Nat}
    (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  have ha := a.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Byte regions -/

private theorem satWithin_bytesRegionAux (n : Nat) :
    ∀ (base : Word) (bs : List (BitVec 8)),
    (∀ k, k < n → isValidDwordAccess (base + BitVec.ofNat 64 (8 * k)) = true) →
    (bytesRegionAux base n bs).SatWithin base.toNat (base.toNat + 8 * n) := by
  induction n with
  | zero => intro base bs _; exact satWithin_emp _ _
  | succ m ih =>
    intro base bs hvalid
    have hbase : isValidDwordAccess base = true := by
      have := hvalid 0 (Nat.succ_pos m)
      simpa using this
    have hbound : base.toNat + 8 < 2 ^ 64 := by
      have := toNat_le_of_validDword hbase; omega
    have hnext : (base + (8 : Word)).toNat = base.toNat + 8 := by
      rw [BitVec.toNat_add]
      have h8 : (8 : Word).toNat = 8 := rfl
      rw [h8, Nat.mod_eq_of_lt hbound]
    have hvalid' : ∀ k, k < m →
        isValidDwordAccess ((base + (8 : Word)) + BitVec.ofNat 64 (8 * k)) = true := by
      intro k hk
      have h8 : BitVec.ofNat 64 8 = (8 : Word) := rfl
      have heq : (base + (8 : Word)) + BitVec.ofNat 64 (8 * k)
           = base + BitVec.ofNat 64 (8 * (k + 1)) := by
        have h1 : 8 * (k + 1) = 8 + 8 * k := by omega
        rw [h1, BitVec.ofNat_add, h8, ← BitVec.add_assoc]
      rw [heq]
      exact hvalid (k + 1) (by omega)
    have hhead := satWithin_memIs (a := base) (packBytes (bs.take 8)) hbase
    have htail := ih (base + (8 : Word)) (bs.drop 8) hvalid'
    rw [hnext] at htail
    have := hhead.sepConj htail (by omega) (by omega)
    exact this.congr_bounds rfl (by omega)

/-- Satisfiability of a concrete byte region: the canonical heap owning
    exactly the `⌈|bs|/8⌉` dwords starting at `base`. -/
theorem satWithin_bytesRegion (base : Word) (bs : List (BitVec 8))
    (hvalid : ∀ k, k < (bs.length + 7) / 8 →
      isValidDwordAccess (base + BitVec.ofNat 64 (8 * k)) = true) :
    (bytesRegion base bs).SatWithin base.toNat
      (base.toNat + 8 * ((bs.length + 7) / 8)) :=
  satWithin_bytesRegionAux ((bs.length + 7) / 8) base bs hvalid

/-- Satisfiability of a havoc'd byte range (contents chosen all-zero). -/
theorem satWithin_anyBytes (base : Word) (n : Nat)
    (hvalid : ∀ k, k < (n + 7) / 8 →
      isValidDwordAccess (base + BitVec.ofNat 64 (8 * k)) = true) :
    (anyBytes base n).SatWithin base.toNat (base.toNat + 8 * ((n + 7) / 8)) := by
  have h := satWithin_bytesRegion base (List.replicate n 0)
    (by simpa using hvalid)
  obtain ⟨hp, hsat, hw⟩ := h
  exact ⟨hp, ⟨List.replicate n 0, List.length_replicate, hsat⟩,
         by simpa using hw⟩

/-- Zone-check discharger: a dword-aligned address inside one of the three
    valid zones is a valid dword access. -/
theorem isValidDwordAccess_of_toNat {a : Word}
    (halign : a.toNat % 8 = 0)
    (hzone : (0x20 ≤ a.toNat ∧ a.toNat ≤ 0x78000000) ∨
             (0x40000000 ≤ a.toNat ∧ a.toNat ≤ 0x40002000) ∨
             (0xa0000000 ≤ a.toNat ∧ a.toNat ≤ 0xc0000000)) :
    isValidDwordAccess a = true := by
  simp only [isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START,
    MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- `Nat`-base form of the zone-check discharger. -/
theorem isValidDwordAccess_ofNat (x : Nat) (hlt : x < 2 ^ 64)
    (halign : x % 8 = 0)
    (hzone : (0x20 ≤ x ∧ x ≤ 0x78000000) ∨
             (0x40000000 ≤ x ∧ x ≤ 0x40002000) ∨
             (0xa0000000 ≤ x ∧ x ≤ 0xc0000000)) :
    isValidDwordAccess (BitVec.ofNat 64 x) = true := by
  have hx : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  exact isValidDwordAccess_of_toNat (by omega) (by omega)

end EvmAsm.Rv64
