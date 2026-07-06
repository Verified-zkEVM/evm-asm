/-
  EvmAsm.Rv64.BitAux

  Shared `Word` (= `BitVec 64`) bit-level helper lemmas distilled from the
  `bv_decide` elimination. Before this file, the small lemmas below were copied
  verbatim as `private` declarations into `Evm64/SDiv/Compose/Words.lean` and
  `Evm64/SMod/Compose/Words.lean`; they now live here once.

  Also exposes the 2-byte-alignment lemmas used to discharge the JALR low-bit
  masks (`… &&& ~~~1`, `… &&& 1 = 0`) that recur across the EXP / SDIV / SMOD /
  ADDMOD composition proofs. The forward `@[grind →]` tags let `grind` derive
  alignment from a `… &&& 1 = 0` hypothesis automatically.

  All proofs are kernel-checkable (no `bv_decide` / `native_decide`).
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Rv64.BitAux

open EvmAsm.Rv64

/-! ## Small `Word` simp helpers (shared; previously duplicated) -/

/-- A 64-bit word shifted right by 63 is either `0` or `1` (the sign bit). -/
theorem ushr63_bool (x : Word) : x >>> 63 = 0 ∨ x >>> 63 = 1 := by
  have h : (x >>> 63).toNat < 2 := by
    rw [BitVec.toNat_ushiftRight]; have := x.isLt; omega
  have h01 : (x >>> 63).toNat = 0 ∨ (x >>> 63).toNat = 1 := by omega
  rcases h01 with h0 | h1
  · left; exact BitVec.eq_of_toNat_eq (by simpa using h0)
  · right; exact BitVec.eq_of_toNat_eq (by simpa using h1)

theorem bv6_63_toNat : (63 : BitVec 6).toNat = 63 := rfl

theorem ult_zero_false (x : Word) : BitVec.ult x 0 = false := by
  simp [BitVec.ult, Nat.not_lt_zero]

theorem word_xor_zero (x : Word) : x ^^^ 0 = x := by simp

theorem word_add_zero (x : Word) : x + 0 = x := by simp

theorem word_if_false_zero : (if False then (1 : Word) else 0) = 0 := rfl

theorem word_if_false_eq_zero (x : Word) : (if false = true then x else 0) = 0 := rfl

theorem word_zero_sub_one : (0 : Word) - 1 = BitVec.allOnes 64 := by decide

theorem word_xor_allOnes (x : Word) : x ^^^ BitVec.allOnes 64 = ~~~x := by
  rw [BitVec.xor_allOnes]

/-! ## 2-byte alignment (JALR low-bit masks) -/

/-- `x &&& 1 = 0` is exactly "bit 0 of `x` is clear". -/
theorem getLsbD_zero_of_and_one {x : Word} (h : x &&& 1 = 0) :
    x.getLsbD 0 = false := by
  have h0 : (x &&& 1).getLsbD 0 = (0 : Word).getLsbD 0 := by rw [h]
  rw [BitVec.getLsbD_and] at h0
  rw [show BitVec.getLsbD (1 : Word) 0 = true from rfl,
      show BitVec.getLsbD (0 : Word) 0 = false from rfl, Bool.and_true] at h0
  exact h0

/-- Adding an even constant `K` (bit 0 clear) to a 2-byte-aligned `base`
    (`base &&& 1 = 0`) keeps bit 0 clear. -/
@[grind →] theorem word_add_even_and_one {base K : Word}
    (hbase : base &&& 1 = 0) (hK : K.getLsbD 0 = false) :
    (base + K) &&& 1 = 0 := by
  have hsum0 : (base + K).getLsbD 0 = false := by
    rw [BitVec.getLsbD_add (by omega), getLsbD_zero_of_and_one hbase, hK,
      BitVec.carry_zero]; rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  by_cases h0 : i = 0
  · subst h0; rw [hsum0]; simp
  · rw [show (1 : Word).getLsbD i = false from by simp [BitVec.getLsbD_one, h0]]; simp

/-- The JALR low-bit mask `&&& ~~~1` is the identity on a 2-byte-aligned word. -/
theorem word_andn_one_of_even {x : Word} (h : x &&& 1 = 0) :
    x &&& ~~~(1 : Word) = x := by
  have hx0 := getLsbD_zero_of_and_one h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0; rw [hx0]; simp
  · rw [show (1 : Word).getLsbD i = false from by simp [BitVec.getLsbD_one, h0]]; simp [hi]

/-- `base + K` (even `K`, aligned `base`) survives the JALR low-bit mask. -/
@[grind →] theorem word_add_even_andn_one {base K : Word}
    (hbase : base &&& 1 = 0) (hK : K.getLsbD 0 = false) :
    (base + K) &&& ~~~(1 : Word) = base + K :=
  word_andn_one_of_even (word_add_even_and_one hbase hK)

end EvmAsm.Rv64.BitAux
