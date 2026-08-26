/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1d

  The post-Phase-1b-1st-correction V5 quotient `algorithmQ1dV5` and
  remainder `algorithmRhatdV5`, plus the `< 2^32` bound that follows
  from the V5 cap.

  v5 analog of v4's `algorithmQ1dV4` / `algorithmRhatdV4`
  (Phase1bBound.lean:20-36) but with the V5 guard on the 1st correction
  (`rhatc >>> 32 = 0` extra precondition).

  Bead `evm-asm-wbc4i.4.6.5` (V5.4.0.6). Prerequisite for V5.4.1.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.NoWrap

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The V5 post-Phase-1b-1st-correction quotient. Either `Q1c` (no fire)
    or `Q1c + signExtend12 4095` (= `Q1c - 1` in Word arithmetic; fire). -/
@[irreducible]
def algorithmQ1dV5 (uHi uLo vTop : Word) : Word :=
  let q1c := algorithmQ1cV5 uHi vTop
  let rhatc := algorithmRhatcV5 uHi vTop
  let qDlo := q1c * divKTrialCallV5DLo vTop
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 uLo
  let fire := decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
  if fire then q1c + signExtend12 4095 else q1c

/-- The corresponding post-Phase-1b-1st-correction remainder. -/
@[irreducible]
def algorithmRhatdV5 (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let q1c := algorithmQ1cV5 uHi vTop
  let rhatc := algorithmRhatcV5 uHi vTop
  let qDlo := q1c * divKTrialCallV5DLo vTop
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 uLo
  let fire := decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
  if fire then rhatc + dHi else rhatc

theorem algorithmQ1dV5_unfold (uHi uLo vTop : Word) :
    algorithmQ1dV5 uHi uLo vTop =
      (let q1c := algorithmQ1cV5 uHi vTop
       let rhatc := algorithmRhatcV5 uHi vTop
       let qDlo := q1c * divKTrialCallV5DLo vTop
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 uLo
       let fire := decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
       if fire then q1c + signExtend12 4095 else q1c) := by
  delta algorithmQ1dV5; rfl

theorem algorithmRhatdV5_unfold (uHi uLo vTop : Word) :
    algorithmRhatdV5 uHi uLo vTop =
      (let dHi := divKTrialCallV5DHi vTop
       let q1c := algorithmQ1cV5 uHi vTop
       let rhatc := algorithmRhatcV5 uHi vTop
       let qDlo := q1c * divKTrialCallV5DLo vTop
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 uLo
       let fire := decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
       if fire then rhatc + dHi else rhatc) := by
  delta algorithmRhatdV5; rfl

/-- Q1d is < 2^32 unconditionally under V5: either equals Q1c (which is
    < 2^32 by `algorithmQ1cV5_lt_pow32`) or `Q1c + (-1)` which is
    `Q1c - 1` since Q1c ≥ 1 when the fire condition triggers. -/
theorem algorithmQ1dV5_lt_pow32 (uHi uLo vTop : Word) :
    (algorithmQ1dV5 uHi uLo vTop).toNat < 2^32 := by
  rw [algorithmQ1dV5_unfold]
  dsimp only
  set q1c := algorithmQ1cV5 uHi vTop with hq1c
  set rhatc := algorithmRhatcV5 uHi vTop with hrhatc
  have h_q1c : q1c.toNat < 2^32 := by rw [hq1c]; exact algorithmQ1cV5_lt_pow32 uHi vTop
  split_ifs with h_fire
  · -- fire case: result = q1c + signExtend12 4095 = q1c - 1 mod 2^64
    have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se]
    by_cases h_q_zero : q1c.toNat = 0
    · -- q1c = 0 ⇒ q1c * dLo = 0 ⇒ BLTU rhatUn1 0 is false ⇒ fire is false. Contradiction.
      exfalso
      have h_q_eq : q1c = 0 := BitVec.eq_of_toNat_eq h_q_zero
      have h_mul : q1c * divKTrialCallV5DLo vTop = 0 := by
        rw [h_q_eq]; exact BitVec.zero_mul
      rw [h_mul] at h_fire
      simp [BitVec.ult] at h_fire
    · have h_q_pos : q1c.toNat ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_q_zero
      have h_sum : q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 := by omega
      rw [h_sum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q1c.toNat - 1 < 2^64)]
      omega
  · -- no-fire case: result = q1c
    exact h_q1c

end EvmAsm.Evm64
