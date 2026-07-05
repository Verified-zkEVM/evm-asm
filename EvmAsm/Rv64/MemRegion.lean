/-
  EvmAsm.Rv64.MemRegion

  A contiguous multi-dword **byte region** in RISC-V memory: a `List (BitVec 8)`
  stored little-endian across consecutive 8-byte dwords, each named by `↦ₘ` with
  value `packBytes`. This is the separation-logic resource the RLP list decoder
  needs to read a payload spanning more than one dword — the existing decoder
  (`Phase2LongLoopGeneral`) reads only within a single dword.

  The base address is assumed dword-aligned (a payload at an unaligned pointer is
  read as a byte offset into a region whose base is the aligned input buffer).
-/

import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64

/-- Assert `n` consecutive 8-byte dwords starting at `base`, holding `bs`
    little-endian (`packBytes` per chunk). -/
def bytesRegionAux (base : Word) : Nat → List (BitVec 8) → Assertion
  | 0, _ => empAssertion
  | n + 1, bs => (base ↦ₘ packBytes (bs.take 8)) ** bytesRegionAux (base + 8) n (bs.drop 8)

/-- A contiguous byte region: `bs` stored in `⌈|bs|/8⌉` consecutive dwords from
    the (dword-aligned) `base`. -/
def bytesRegion (base : Word) (bs : List (BitVec 8)) : Assertion :=
  bytesRegionAux base ((bs.length + 7) / 8) bs

@[simp] theorem bytesRegion_nil (base : Word) : bytesRegion base [] = empAssertion := rfl

/-- Peel the first dword (8 bytes) off a nonempty region. -/
theorem bytesRegion_eq_cons (base : Word) (bs : List (BitVec 8)) (h : bs ≠ []) :
    bytesRegion base bs
      = ((base ↦ₘ packBytes (bs.take 8)) ** bytesRegion (base + 8) (bs.drop 8)) := by
  have hlen : 0 < bs.length := List.length_pos_of_ne_nil h
  have hchunks : (bs.length + 7) / 8 = ((bs.drop 8).length + 7) / 8 + 1 := by
    rw [List.length_drop]; omega
  unfold bytesRegion
  rw [hchunks]
  rfl

theorem bytesRegionAux_pcFree (n : Nat) (base : Word) (bs : List (BitVec 8)) :
    (bytesRegionAux base n bs).pcFree := by
  induction n generalizing base bs with
  | zero => exact pcFree_emp
  | succ k ih => exact pcFree_sepConj pcFree_memIs (ih _ _)

theorem bytesRegion_pcFree (base : Word) (bs : List (BitVec 8)) :
    (bytesRegion base bs).pcFree :=
  bytesRegionAux_pcFree _ base bs

/-! ## Address arithmetic for an aligned base + byte offset -/

private theorem nat_and_seven (n : Nat) : n &&& 7 = n % 8 := by
  have : (7 : Nat) = 2 ^ 3 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- For a dword-aligned `base` and an in-range offset `i`, the byte offset of
    `base + i` is `i % 8`. -/
theorem byteOffset_add_ofNat_of_aligned {base : Word} {i : Nat}
    (halign : base.toNat % 8 = 0) (hover : base.toNat + i < 2 ^ 64) :
    byteOffset (base + BitVec.ofNat 64 i) = i % 8 := by
  have hi : i < 2 ^ 64 := by omega
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hover]
  show (base.toNat + i) &&& 7 = i % 8
  rw [nat_and_seven]
  omega

/-- For a dword-aligned `base` and an in-range offset `i`, aligning `base + i`
    down to its dword gives `base + 8*(i/8)`. -/
theorem alignToDword_add_ofNat_of_aligned {base : Word} {i : Nat}
    (halign : base.toNat % 8 = 0) (hover : base.toNat + i < 2 ^ 64) :
    alignToDword (base + BitVec.ofNat 64 i) = base + BitVec.ofNat 64 (8 * (i / 8)) := by
  have hbo := byteOffset_add_ofNat_of_aligned halign hover
  have hdecomp := alignToDword_add_byteOffset (base + BitVec.ofNat 64 i)
  rw [hbo] at hdecomp
  -- hdecomp : alignToDword (base + ofNat i) + ofNat (i % 8) = base + ofNat i
  have hi : i < 2 ^ 64 := by omega
  have hi8 : i % 8 < 2 ^ 64 := by omega
  have haddr : (base + BitVec.ofNat 64 i).toNat = base.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hover]
  have hAle : (alignToDword (base + BitVec.ofNat 64 i)).toNat ≤ base.toNat + i := by
    unfold alignToDword; rw [BitVec.toNat_and, ← haddr]; exact Nat.and_le_left
  have hd := congrArg BitVec.toNat hdecomp
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi8, haddr] at hd
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hAlt := (alignToDword (base + BitVec.ofNat 64 i)).isLt
  omega

/-! ## Dword extraction -/

/-- Assertion-level (`=`) associativity, from the pointwise `sepConj_assoc`. -/
private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-- Assertion-level (`=`) left identity, from the pointwise `sepConj_emp_left`. -/
private theorem sepConj_emp_left_eq {P : Assertion} : (empAssertion ** P) = P := by
  funext h; exact propext (sepConj_emp_left h)

/-- Extract the `dw`-th dword cell from a region (the chunk may be the partial
    last one — `packBytes` zero-pads), framing the rest. -/
theorem bytesRegion_dword_at (regionBase : Word) (bs : List (BitVec 8)) (dw : Nat)
    (hdw : 8 * dw < bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegion regionBase bs
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * dw)) ↦ₘ
            packBytes ((bs.drop (8 * dw)).take 8)) ** rest)) := by
  induction dw generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hdw
    refine ⟨empAssertion, bytesRegion (regionBase + 8) (bs.drop 8),
      pcFree_emp, bytesRegion_pcFree _ _, ?_⟩
    rw [bytesRegion_eq_cons regionBase bs hne]
    simp [sepConj_emp_left_eq]
  | succ k ih =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hdw
    have hdw' : 8 * k < (bs.drop 8).length := by rw [List.length_drop]; omega
    obtain ⟨front', rest', hf', hr', heq'⟩ := ih (regionBase + 8) (bs.drop 8) hdw'
    have haddr : (regionBase + 8) + BitVec.ofNat 64 (8 * k)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]
      omega
    have hdrop : (bs.drop 8).drop (8 * k) = bs.drop (8 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    refine ⟨(regionBase ↦ₘ packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIs hf', hr', ?_⟩
    rw [bytesRegion_eq_cons regionBase bs hne, heq', haddr, hdrop, ← sepConj_assoc_eq]

/-- Extract two **adjacent** dword cells (`dw` and `dw + 1`) from a region,
    framing the rest. The second chunk may be the partial last one —
    `packBytes` zero-pads. Unaligned 8-byte window reads (CALLDATALOAD's
    per-quarter lo/hi source dwords) always touch an adjacent pair, so this
    is the extraction shape their preconditions need. -/
theorem bytesRegion_dword_pair_at (regionBase : Word) (bs : List (BitVec 8)) (dw : Nat)
    (hdw : 8 * dw + 8 < bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegion regionBase bs
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * dw)) ↦ₘ
            packBytes ((bs.drop (8 * dw)).take 8)) **
            (((regionBase + BitVec.ofNat 64 (8 * dw + 8)) ↦ₘ
              packBytes ((bs.drop (8 * dw + 8)).take 8)) ** rest))) := by
  induction dw generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hdw
    have hne' : bs.drop 8 ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [List.length_drop] at hlen
      simp at hlen
      omega
    refine ⟨empAssertion, bytesRegion (regionBase + 8 + 8) ((bs.drop 8).drop 8),
      pcFree_emp, bytesRegion_pcFree _ _, ?_⟩
    rw [sepConj_emp_left_eq]
    rw [bytesRegion_eq_cons regionBase bs hne,
        bytesRegion_eq_cons (regionBase + 8) (bs.drop 8) hne']
    have haddr0 : regionBase + BitVec.ofNat 64 (8 * 0) = regionBase := by
      rw [show (8 * 0 : Nat) = 0 from rfl]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := regionBase.isLt
      omega
    have haddr8 : regionBase + BitVec.ofNat 64 (8 * 0 + 8) = regionBase + 8 := by
      rw [show (8 * 0 + 8 : Nat) = 8 from rfl]
      congr 1
    rw [haddr0, haddr8, show (8 * 0 : Nat) = 0 from rfl, List.drop_zero,
        show (8 * 0 + 8 : Nat) = 8 from rfl]
  | succ k ih =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hdw
    have hdw' : 8 * k + 8 < (bs.drop 8).length := by rw [List.length_drop]; omega
    obtain ⟨front', rest', hf', hr', heq'⟩ := ih (regionBase + 8) (bs.drop 8) hdw'
    have haddr : (regionBase + 8) + BitVec.ofNat 64 (8 * k)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]
      omega
    have haddr' : (regionBase + 8) + BitVec.ofNat 64 (8 * k + 8)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1) + 8) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]
      omega
    have hdrop : (bs.drop 8).drop (8 * k) = bs.drop (8 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    have hdrop' : (bs.drop 8).drop (8 * k + 8) = bs.drop (8 * (k + 1) + 8) := by
      rw [List.drop_drop]; congr 1; omega
    refine ⟨(regionBase ↦ₘ packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIs hf', hr', ?_⟩
    rw [bytesRegion_eq_cons regionBase bs hne, heq', haddr, haddr', hdrop, hdrop',
        ← sepConj_assoc_eq]

/-! ## Reading a byte from the region (the keystone) -/

/-- **`LBU` reads byte `i` from the region.** Reading the byte at `regionBase + i`
    (`i < bs.length`, region base dword-aligned, no address overflow) yields
    `bs[i]` — the multi-dword read the single-`dwordAddr` loop could not express. -/
theorem bytesRegion_lbu_within (rd rs1 : Reg) (regionBase vOld : Word) (base : Word)
    (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (rd ↦ᵣ ((bs[i]'hi).zeroExtend 64)) ** bytesRegion regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegion_dword_at regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have hptr_eq : (regionBase + BitVec.ofNat 64 i) + signExtend12 (0 : BitVec 12)
      = regionBase + BitVec.ofNat 64 i := by show _ + (0 : Word) = _; bv_omega
  have halign' :
      alignToDword ((regionBase + BitVec.ofNat 64 i) + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [hptr_eq]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess ((regionBase + BitVec.ofNat 64 i) + signExtend12 (0 : BitVec 12)) = true := by
    rw [hptr_eq]; exact hvalid
  have lbu := generic_lbu_spec_within rd rs1 (regionBase + BitVec.ofNat 64 i) vOld 0 base
    dwordAddr wordVal hrd halign' hvalid'
  rw [hptr_eq] at lbu
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 i)) = bs[i]'hi := by
    rw [byteOffset_add_ofNat_of_aligned halign hover, hwv,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu
  rw [heq]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

/-- Cross-check: reading byte 9 of a 10-byte region (second dword, byte offset 1)
    — a cross-dword read the single-`dwordAddr` `hwin` model could not express. -/
example (base regionBase vOld : Word) (rd rs1 : Reg) (hrd : rd ≠ .x0)
    (bs : List (BitVec 8)) (hlen : bs.length = 10)
    (halign : regionBase.toNat % 8 = 0) (hover : regionBase.toNat + 9 < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 9) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 9)) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 9)) **
       (rd ↦ᵣ ((bs[9]'(by omega)).zeroExtend 64)) ** bytesRegion regionBase bs) :=
  bytesRegion_lbu_within rd rs1 regionBase vOld base bs 9 hrd halign (by omega) hover hvalid

end EvmAsm.Rv64


