/-
  EvmAsm.Evm64.EvmWordArith.DivAddbackCarry

  Register-level addback carry bridge: connects the per-limb addback
  operations (two-step ADD with OR carry) to the Nat-level addition
  equation needed by `addback_4limb_val256`.

  Key results:
  - or_toNat_eq_add_of_le_one: OR = ADD for {0,1}-valued Words
  - addback_limb_nat_word_eq: per-limb addback equation with Word OR carry
  - addback_register_4limb_val256: 4-limb addback → val256 equation
-/

import EvmAsm.Evm64.EvmWordArith.DivAddbackLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_toNat_0)

namespace EvmWord

-- ============================================================================
-- OR = ADD for {0, 1}-valued Words
-- ============================================================================

/-- When two Words are each 0 or 1, and their sum ≤ 1, OR equals ADD.
    This is used for the addback carry: the two overflow flags ac1, ac2
    can't both be 1 (proven by addback_limb_nat_eq), so OR correctly
    computes the carry. -/
theorem or_toNat_eq_add_of_le_one {a b : Word}
    (ha : a.toNat ≤ 1) (hb : b.toNat ≤ 1) (hab : a.toNat + b.toNat ≤ 1) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  have ha_eq : a = 0 ∨ a = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h]))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp [h]))
  have hb_eq : b = 0 ∨ b = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h]))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp [h]))
  rcases ha_eq with rfl | rfl <;> rcases hb_eq with rfl | rfl <;> simp_all

-- ============================================================================
-- Per-limb addback with Word OR carry
-- ============================================================================

/-- Helper: the two overflow flags from the two-step addition can't both be 1.
    If the first addition overflows (u + carryIn ≥ 2^64), the intermediate
    result is small, so the second addition (intermediate + v) can't also overflow
    when the total carry is ≤ 1. -/
private theorem addback_carries_exclusive (u_i v_i carryIn : Word)
    (hci : carryIn.toNat ≤ 1) :
    let uPlusCarry := u_i + carryIn
    let uNew := uPlusCarry + v_i
    let ac1 := if BitVec.ult uPlusCarry carryIn then (1 : Word) else 0
    let ac2 := if BitVec.ult uNew v_i then (1 : Word) else 0
    ac1.toNat + ac2.toNat ≤ 1 := by
  intro uPlusCarry uNew ac1 ac2
  -- Convert to Nat
  have h_ac1 : ac1.toNat = (u_i.toNat + carryIn.toNat) / 2^64 := by
    show (if BitVec.ult uPlusCarry carryIn then (1 : Word) else 0).toNat = _
    have := carryIn.isLt; have := u_i.isLt
    by_cases h : u_i.toNat + carryIn.toNat < 2^64
    · have : uPlusCarry.toNat ≥ carryIn.toNat := by
        show (u_i + carryIn).toNat ≥ _
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]; omega
      simp [BitVec.ult, show ¬(uPlusCarry.toNat < carryIn.toNat) from by omega]
      exact (Nat.div_eq_of_lt h).symm
    · push Not at h
      have : uPlusCarry.toNat < carryIn.toNat := by
        show (u_i + carryIn).toNat < _
        rw [BitVec.toNat_add]; omega
      simp [BitVec.ult, this]
      have : u_i.toNat + carryIn.toNat < 2 * 2^64 := by omega
      omega
  have h_ac2 : ac2.toNat = (uPlusCarry.toNat + v_i.toNat) / 2^64 := by
    show (if BitVec.ult uNew v_i then (1 : Word) else 0).toNat = _
    have := v_i.isLt; have := uPlusCarry.isLt
    by_cases h : uPlusCarry.toNat + v_i.toNat < 2^64
    · have : uNew.toNat ≥ v_i.toNat := by
        show (uPlusCarry + v_i).toNat ≥ _
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]; omega
      simp [BitVec.ult, show ¬(uNew.toNat < v_i.toNat) from by omega]
      exact (Nat.div_eq_of_lt h).symm
    · push Not at h
      have : uNew.toNat < v_i.toNat := by
        show (uPlusCarry + v_i).toNat < _
        rw [BitVec.toNat_add]; omega
      simp [BitVec.ult, this]
      have : uPlusCarry.toNat + v_i.toNat < 2 * 2^64 := by omega
      omega
  rw [h_ac1, h_ac2]
  -- Total: u_i + v_i + carryIn < 2 * 2^64 (since each < 2^64 and carryIn ≤ 1)
  have := u_i.isLt; have := v_i.isLt
  have : u_i.toNat + v_i.toNat + carryIn.toNat < 2 * 2^64 := by omega
  -- c1 + c2 = (u_i + ci) / B + (upc + v) / B where upc = (u_i + ci) % B
  have hupc : uPlusCarry.toNat = (u_i.toNat + carryIn.toNat) % 2^64 :=
    BitVec.toNat_add u_i carryIn
  -- Case split on c1
  have hc1_01 := add_carry_01 u_i carryIn
  rcases hc1_01 with hc1_0 | hc1_1
  · -- c1 = 0: no overflow in first add. Then c2 ≤ 1.
    rw [hc1_0]; simp
    have := add_carry_01 uPlusCarry v_i
    rcases this with h | h <;> omega
  · -- c1 = 1: first add overflowed. upc is small. Second add can't overflow.
    rw [hc1_1]
    have : uPlusCarry.toNat = u_i.toNat + carryIn.toNat - 2^64 := by rw [hupc]; omega
    have : uPlusCarry.toNat + v_i.toNat < 2^64 := by omega
    have : (uPlusCarry.toNat + v_i.toNat) / 2^64 = 0 := Nat.div_eq_of_lt (by omega)
    omega

/-- Per-limb addback Nat equation using the Word OR carry directly.
    The two-step addition `(u_i + carryIn) + v_i` with OR carry propagation
    satisfies the same Nat equation as standard add-with-carry. -/
theorem addback_limb_nat_word_eq (u_i v_i carryIn : Word) (hci : carryIn.toNat ≤ 1) :
    let uPlusCarry := u_i + carryIn
    let uNew := uPlusCarry + v_i
    let ac1 := if BitVec.ult uPlusCarry carryIn then (1 : Word) else 0
    let ac2 := if BitVec.ult uNew v_i then (1 : Word) else 0
    let carryOut := ac1 ||| ac2
    carryOut.toNat ≤ 1 ∧
    u_i.toNat + v_i.toNat + carryIn.toNat = carryOut.toNat * 2^64 + uNew.toNat := by
  intro uPlusCarry uNew ac1 ac2 carryOut
  have h_excl := addback_carries_exclusive u_i v_i carryIn hci
  have h_ac1_01 : ac1.toNat ≤ 1 := by
    show (if BitVec.ult uPlusCarry carryIn then (1 : Word) else 0).toNat ≤ 1
    split <;> simp_all
  have h_ac2_01 : ac2.toNat ≤ 1 := by
    show (if BitVec.ult uNew v_i then (1 : Word) else 0).toNat ≤ 1
    split <;> simp_all
  -- OR = ADD for the carry
  have h_or := or_toNat_eq_add_of_le_one h_ac1_01 h_ac2_01 h_excl
  constructor
  · -- carryOut ≤ 1
    rw [show carryOut = ac1 ||| ac2 from rfl, h_or]; omega
  · -- The addback equation: derive directly from two-step addition
    rw [show carryOut = ac1 ||| ac2 from rfl, h_or]
    -- Connect ac1, ac2 to division values
    have h_ac1_div : ac1.toNat = (u_i.toNat + carryIn.toNat) / 2^64 := by
      show (if BitVec.ult uPlusCarry carryIn then (1 : Word) else 0).toNat = _
      have := carryIn.isLt; have := u_i.isLt
      by_cases h : u_i.toNat + carryIn.toNat < 2^64
      · have : ¬(uPlusCarry.toNat < carryIn.toNat) := by
          have : uPlusCarry.toNat = (u_i.toNat + carryIn.toNat) % 2^64 :=
            BitVec.toNat_add u_i carryIn
          rw [this, Nat.mod_eq_of_lt h]; omega
        simp [BitVec.ult, this]; exact (Nat.div_eq_of_lt h).symm
      · push Not at h
        have : uPlusCarry.toNat < carryIn.toNat := by
          have : uPlusCarry.toNat = (u_i.toNat + carryIn.toNat) % 2^64 :=
            BitVec.toNat_add u_i carryIn
          rw [this]; omega
        simp [BitVec.ult, this]
        have : u_i.toNat + carryIn.toNat < 2 * 2^64 := by omega
        omega
    have h_ac2_div : ac2.toNat = (uPlusCarry.toNat + v_i.toNat) / 2^64 := by
      show (if BitVec.ult uNew v_i then (1 : Word) else 0).toNat = _
      have := v_i.isLt; have := uPlusCarry.isLt
      by_cases h : uPlusCarry.toNat + v_i.toNat < 2^64
      · have : ¬(uNew.toNat < v_i.toNat) := by
          have : uNew.toNat = (uPlusCarry.toNat + v_i.toNat) % 2^64 :=
            BitVec.toNat_add uPlusCarry v_i
          rw [this, Nat.mod_eq_of_lt h]; omega
        simp [BitVec.ult, this]; exact (Nat.div_eq_of_lt h).symm
      · push Not at h
        have : uNew.toNat < v_i.toNat := by
          have : uNew.toNat = (uPlusCarry.toNat + v_i.toNat) % 2^64 :=
            BitVec.toNat_add uPlusCarry v_i
          rw [this]; omega
        simp [BitVec.ult, this]
        have : uPlusCarry.toNat + v_i.toNat < 2 * 2^64 := by omega
        omega
    -- Step 1: u_i + carryIn = div1 * 2^64 + uPlusCarry
    have h1 := add_carry_nat u_i carryIn
    -- Step 2: uPlusCarry + v_i = div2 * 2^64 + uNew
    have h2 := add_carry_nat uPlusCarry v_i
    -- Combined with ac1 = div1, ac2 = div2:
    -- u_i + v_i + ci = (ac1 + ac2) * 2^64 + uNew
    nlinarith [h1, h2, h_ac1_div, h_ac2_div]

-- ============================================================================
-- 4-limb addback: register ops → val256 equation
-- ============================================================================

/-- 4-limb addback from register operations → val256 addition equation.

    This connects the register-level addback computation (two-step ADD with
    OR carry) to the val256 addition needed by `addback_correction_euclidean`.
    The let-bindings match the addback path in the loop body. -/
theorem addback_register_4limb_val256
    {v0 v1 v2 v3 un0 un1 un2 un3 : Word} :
    -- Limb 0 (carryIn = 0)
    let upc0 := un0 + (0 : Word)
    let aun0 := upc0 + v0
    let ac1_0 := if BitVec.ult upc0 (0 : Word) then (1 : Word) else 0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let co0 := ac1_0 ||| ac2_0
    -- Limb 1 (carryIn = co0)
    let upc1 := un1 + co0
    let aun1 := upc1 + v1
    let ac1_1 := if BitVec.ult upc1 co0 then (1 : Word) else 0
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let co1 := ac1_1 ||| ac2_1
    -- Limb 2 (carryIn = co1)
    let upc2 := un2 + co1
    let aun2 := upc2 + v2
    let ac1_2 := if BitVec.ult upc2 co1 then (1 : Word) else 0
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let co2 := ac1_2 ||| ac2_2
    -- Limb 3 (carryIn = co2)
    let upc3 := un3 + co2
    let aun3 := upc3 + v3
    let ac1_3 := if BitVec.ult upc3 co2 then (1 : Word) else 0
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let co3 := ac1_3 ||| ac2_3
    -- Result
    val256 un0 un1 un2 un3 + val256 v0 v1 v2 v3 =
      val256 aun0 aun1 aun2 aun3 + co3.toNat * 2^256 := by
  intro upc0 aun0 ac1_0 ac2_0 co0
        upc1 aun1 ac1_1 ac2_1 co1
        upc2 aun2 ac1_2 ac2_2 co2
        upc3 aun3 ac1_3 ac2_3 co3
  -- Per-limb equations
  have h0 := addback_limb_nat_word_eq un0 v0 (0 : Word) (by simp)
  have h1 := addback_limb_nat_word_eq un1 v1 co0 h0.1
  have h2 := addback_limb_nat_word_eq un2 v2 co1 h1.1
  have h3 := addback_limb_nat_word_eq un3 v3 co2 h2.1
  -- Simplify h0: carryIn = 0
  have h0' : un0.toNat + v0.toNat = co0.toNat * 2^64 + aun0.toNat := by
    have := h0.2; simp only [word_toNat_0] at this; linarith
  -- Chain via addback_4limb_val256
  exact addback_4limb_val256 un0 un1 un2 un3 v0 v1 v2 v3 aun0 aun1 aun2 aun3
    co0.toNat co1.toNat co2.toNat co3.toNat h0' h1.2 h2.2 h3.2

end EvmWord

end EvmAsm.Evm64
