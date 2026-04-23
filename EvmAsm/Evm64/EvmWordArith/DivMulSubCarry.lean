/-
  EvmAsm.Evm64.EvmWordArith.DivMulSubCarry

  Strict carry bound for the multiply-subtract operation: the per-limb
  carry from mulsub is always strictly less than 2^64 (fits in a Word).

  This is the critical bridge between register-level carry propagation
  (Word addition) and Nat-level carry equations. Without this, the Word
  carry could wrap around, breaking the chain.

  Key results:
  - mulsub_limb_carry_strict_lt: per-limb carry < 2^64 (unconditional)
  - mulsub_limb_word_carry_eq: Word carry = Nat carry (corollary)
  - mulsub_limb_nat_word_eq: per-limb equation using Word carry directly
  - mulsub_register_4limb_val256: 4-limb register ops → val256 equation
-/

import EvmAsm.Evm64.EvmWordArith.DivMulSubLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_toNat_0)

namespace EvmWord

-- ============================================================================
-- Strict carry bound: carry < 2^64 (always)
-- ============================================================================

/-- Helper: when MULHU = 2^64 - 2 (maximum), the low product is at most 1.
    From (2^64-1)² = (2^64-2)·2^64 + 1, so MUL result ≤ 1. -/
private theorem prodLo_le_one_of_mulhu_max {q v_i : Word}
    (h : (rv64_mulhu q v_i).toNat = 2^64 - 2) :
    (q * v_i).toNat ≤ 1 := by
  have := partial_product_decompose q v_i
  have : q.toNat * v_i.toNat ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by omega : q.toNat ≤ 2^64 - 1) (by omega : v_i.toNat ≤ 2^64 - 1)
  -- q * v_i = (2^64 - 2) * 2^64 + (q * v_i).toNat
  -- q * v_i ≤ (2^64 - 1)^2 = (2^64 - 2) * 2^64 + 1
  -- Therefore (q * v_i).toNat ≤ 1
  have : (2 : Nat) ^ 64 - 1 = 18446744073709551615 := by norm_num
  have : (2 : Nat) ^ 64 - 2 = 18446744073709551614 := by norm_num
  have : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  nlinarith

/-- The per-limb mulsub carry is strictly less than 2^64.

    The carry is `borrowAdd + prodHi + borrowSub` where:
    - borrowAdd ∈ {0, 1} (from prodLo + carryIn overflow)
    - prodHi ≤ 2^64 - 2 (from MULHU bound)
    - borrowSub ∈ {0, 1} (from u_i < fullSub underflow)

    When prodHi ≤ 2^64 - 3: carry ≤ 1 + (2^64 - 3) + 1 = 2^64 - 1 < 2^64.
    When prodHi = 2^64 - 2: prodLo ≤ 1, and borrowAdd = 1 forces
    fullSub.toNat = 0 (modular wrap leaves 0), making borrowSub = 0. -/
theorem mulsub_limb_carry_strict_lt {q v_i u_i carryIn : Word} :
    let prodLo := q * v_i
    let prodHi := rv64_mulhu q v_i
    let fullSub := prodLo + carryIn
    let borrowAdd := if BitVec.ult fullSub carryIn then (1 : Word) else 0
    let borrowSub := if BitVec.ult u_i fullSub then (1 : Word) else 0
    borrowAdd.toNat + prodHi.toNat + borrowSub.toNat < 2^64 := by
  intro prodLo prodHi fullSub borrowAdd borrowSub
  have := mulhu_toNat_le q v_i
  -- Work with Nat-level values: ba_n, bs_n ∈ {0, 1}
  set ba_n := if fullSub.toNat < carryIn.toNat then 1 else 0 with h_ba_def
  set bs_n := if u_i.toNat < fullSub.toNat then 1 else 0 with h_bs_def
  -- Convert borrowAdd/borrowSub toNat to ba_n/bs_n
  have h_ba : borrowAdd.toNat = ba_n := by
    show (if BitVec.ult fullSub carryIn then (1 : Word) else 0).toNat = ba_n
    simp only [h_ba_def]; by_cases h : fullSub.toNat < carryIn.toNat <;> simp [BitVec.ult, h]
  have h_bs : borrowSub.toNat = bs_n := by
    show (if BitVec.ult u_i fullSub then (1 : Word) else 0).toNat = bs_n
    simp only [h_bs_def]; by_cases h : u_i.toNat < fullSub.toNat <;> simp [BitVec.ult, h]
  rw [h_ba, h_bs]
  -- Bridge let-defs so omega can connect them
  have : prodHi.toNat = (rv64_mulhu q v_i).toNat := rfl
  -- Now goal is: ba_n + prodHi.toNat + bs_n < 2^64
  have : ba_n ≤ 1 := by simp only [h_ba_def]; split <;> omega
  have : bs_n ≤ 1 := by simp only [h_bs_def]; split <;> omega
  -- Easy case: prodHi ≤ 2^64 - 3
  by_cases h_ph_max : (rv64_mulhu q v_i).toNat ≤ 2^64 - 3
  · -- ba_n ≤ 1, bs_n ≤ 1, ph ≤ 2^64 - 3 → sum ≤ 2^64 - 1
    omega
  -- Hard case: prodHi = 2^64 - 2
  push Not at h_ph_max
  have h_ph_eq : (rv64_mulhu q v_i).toNat = 2^64 - 2 := by omega
  have : (q * v_i).toNat ≤ 1 := prodLo_le_one_of_mulhu_max h_ph_eq
  -- Suffices: ba_n + bs_n ≤ 1
  suffices ba_n + bs_n ≤ 1 by omega
  have h_fs_val : fullSub.toNat = ((q * v_i).toNat + carryIn.toNat) % 2^64 :=
    BitVec.toNat_add (q * v_i) carryIn
  have := carryIn.isLt
  -- Case: ba_n = 0 → immediate
  by_cases h_ba_0 : ba_n = 0
  · omega
  -- Case: ba_n = 1 → overflow → fullSub = 0 → bs_n = 0
  have h_ba_1 : ba_n = 1 := by omega
  -- ba_n = 1 means fullSub.toNat < carryIn.toNat
  have h_ov : fullSub.toNat < carryIn.toNat := by
    simp only [h_ba_def] at h_ba_1; split at h_ba_1 <;> [assumption; omega]
  -- overflow: (q * v_i).toNat + carryIn.toNat ≥ 2^64
  have h_overflow : (q * v_i).toNat + carryIn.toNat ≥ 2^64 := by
    by_contra h_no; push Not at h_no
    rw [h_fs_val, Nat.mod_eq_of_lt h_no] at h_ov; omega
  -- (q * v_i).toNat = 1 and carryIn = 2^64 - 1
  have h_plo_1 : (q * v_i).toNat = 1 := by omega
  -- fullSub = 0
  have h_fs_0 : fullSub.toNat = 0 := by rw [h_fs_val]; omega
  -- bs_n = 0 (nothing is < 0)
  have : bs_n = 0 := by
    simp only [h_bs_def, show ¬(u_i.toNat < fullSub.toNat) from by omega, ite_false]
  omega

-- ============================================================================
-- Word carry = Nat carry (unconditional corollary)
-- ============================================================================

/-- The Word-level carry `(borrowAdd + prodHi) + borrowSub` equals the
    Nat sum `borrowAdd.toNat + prodHi.toNat + borrowSub.toNat`.

    This follows from `mulsub_limb_carry_strict_lt` (carry < 2^64 means
    the Word additions don't overflow) and `mulsub_carry_word_eq`. -/
theorem mulsub_limb_word_carry_eq {q v_i u_i carryIn : Word} :
    let prodLo := q * v_i
    let prodHi := rv64_mulhu q v_i
    let fullSub := prodLo + carryIn
    let borrowAdd := if BitVec.ult fullSub carryIn then (1 : Word) else 0
    let borrowSub := if BitVec.ult u_i fullSub then (1 : Word) else 0
    ((borrowAdd + prodHi) + borrowSub).toNat =
      borrowAdd.toNat + prodHi.toNat + borrowSub.toNat := by
  intro prodLo prodHi fullSub borrowAdd borrowSub
  exact mulsub_carry_word_eq mulsub_limb_carry_strict_lt

-- ============================================================================
-- Per-limb equation using Word carry directly
-- ============================================================================

/-- Per-limb mulsub Nat equation using the Word carryOut directly.
    Combines `mulsub_limb_nat_eq` and `mulsub_limb_word_carry_eq` so the
    carryOut can be passed directly as carryIn to the next limb. -/
theorem mulsub_limb_nat_word_eq (q v_i u_i carryIn : Word) :
    let prodLo := q * v_i
    let prodHi := rv64_mulhu q v_i
    let fullSub := prodLo + carryIn
    let borrowAdd := if BitVec.ult fullSub carryIn then (1 : Word) else 0
    let uNew := u_i - fullSub
    let borrowSub := if BitVec.ult u_i fullSub then (1 : Word) else 0
    let carryOut := (borrowAdd + prodHi) + borrowSub
    u_i.toNat + carryOut.toNat * 2^64 =
      uNew.toNat + q.toNat * v_i.toNat + carryIn.toNat := by
  intro prodLo prodHi fullSub borrowAdd uNew borrowSub carryOut
  rw [show carryOut = (borrowAdd + prodHi) + borrowSub from rfl,
      mulsub_limb_word_carry_eq]
  exact mulsub_limb_nat_eq

-- ============================================================================
-- 4-limb composition: register ops → val256 equation
-- ============================================================================

/-- 4-limb mulsub from register operations → val256 Euclidean equation.

    This connects the exact register-level computation from `divK_mulsub_full_spec`
    to the mathematical Euclidean equation. The let-bindings match those in the
    mulsub loop body: for each limb i, compute prodLo/hi, fullSub, borrows,
    updated uNew, and carryOut.

    The initial carry is 0 (first limb). Each subsequent limb uses the
    Word carry from the previous limb. -/
theorem mulsub_register_4limb_val256 {q v0 v1 v2 v3 u0 u1 u2 u3 : Word} :
    -- Limb 0 (carryIn = 0)
    let fs0 := q * v0 + (0 : Word)
    let ba0 := if BitVec.ult fs0 (0 : Word) then (1 : Word) else 0
    let un0 := u0 - fs0
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let c0 := (ba0 + rv64_mulhu q v0) + bs0
    -- Limb 1 (carryIn = c0)
    let fs1 := q * v1 + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let un1 := u1 - fs1
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let c1 := (ba1 + rv64_mulhu q v1) + bs1
    -- Limb 2 (carryIn = c1)
    let fs2 := q * v2 + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let un2 := u2 - fs2
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let c2 := (ba2 + rv64_mulhu q v2) + bs2
    -- Limb 3 (carryIn = c2)
    let fs3 := q * v3 + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let un3 := u3 - fs3
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let c3 := (ba3 + rv64_mulhu q v3) + bs3
    -- Result
    val256 u0 u1 u2 u3 + c3.toNat * 2^256 =
      val256 un0 un1 un2 un3 + q.toNat * val256 v0 v1 v2 v3 := by
  intro fs0 ba0 un0 bs0 c0
        fs1 ba1 un1 bs1 c1
        fs2 ba2 un2 bs2 c2
        fs3 ba3 un3 bs3 c3
  -- Per-limb equations from mulsub_limb_nat_word_eq
  have h0 := mulsub_limb_nat_word_eq q v0 u0 (0 : Word)
  have h1 := mulsub_limb_nat_word_eq q v1 u1 c0
  have h2 := mulsub_limb_nat_word_eq q v2 u2 c1
  have h3 := mulsub_limb_nat_word_eq q v3 u3 c2
  -- Simplify h0: carryIn = 0, so (0 : Word).toNat = 0
  have h0' : u0.toNat + c0.toNat * 2^64 = un0.toNat + q.toNat * v0.toNat := by
    have := h0; simp only [word_toNat_0] at this; linarith
  -- Chain via mulsub_chain_nat
  exact mulsub_chain_nat q.toNat u0 u1 u2 u3 v0 v1 v2 v3 un0 un1 un2 un3
    c0.toNat c1.toNat c2.toNat c3.toNat h0' h1 h2 h3

end EvmWord

end EvmAsm.Evm64
