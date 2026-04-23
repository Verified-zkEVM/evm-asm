/-
  EvmAsm.Evm64.EvmWordArith.DivAddbackLimb

  Per-limb addback correctness at the Nat level.
  When the multiply-subtract step in Knuth's Algorithm D underflows (borrow = 1),
  the addback step adds the divisor back to the remainder and decrements the
  quotient digit. These lemmas connect the register-level addback operations
  to the Nat-level carry equations.

  Key results:
  - addback_limb_nat_eq: per-limb carry equation for addback
  - addback_4limb_val256: 4-limb composition giving val256 addition equation
  - addback_correction_euclidean: end-to-end from mulsub underflow + addback → Euclidean
-/

import EvmAsm.Evm64.EvmWordArith.DivMulSubLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Per-limb addback: Nat-level carry equation
-- ============================================================================

/-- Per-limb addback Nat-level equation.

    The addback_limb operation does a two-step addition:
    - uPlusCarry = u_i + carryIn (with overflow detection)
    - uNew = uPlusCarry + v_i (with overflow detection)
    - carryOut = carry1 ||| carry2

    At the Nat level, this is simply:
      u_i + v_i + carryIn = carry_nat * 2^64 + uNew
    where carry_nat = (u_i + v_i + carryIn) / 2^64 ∈ {0, 1}.

    We state the equation at the Nat level without referencing the
    register-level carryOut Word, since the carries are used only
    to propagate between limbs (and the 4-limb composition telescopes). -/
theorem addback_limb_nat_eq (u_i v_i carryIn : Word) (hci : carryIn.toNat ≤ 1) :
    let uPlusCarry := u_i + carryIn
    let uNew := uPlusCarry + v_i
    ∃ (carry_nat : Nat), carry_nat ≤ 1 ∧
      u_i.toNat + v_i.toNat + carryIn.toNat = carry_nat * 2^64 + uNew.toNat := by
  intro uPlusCarry uNew
  -- Step 1: u_i + carryIn = c1 * 2^64 + uPlusCarry
  have h1 := add_carry_nat u_i carryIn
  -- Step 2: uPlusCarry + v_i = c2 * 2^64 + uNew
  have h2 := add_carry_nat uPlusCarry v_i
  -- Combined carry
  set c1 := (u_i.toNat + carryIn.toNat) / 2^64
  set c2 := (uPlusCarry.toNat + v_i.toNat) / 2^64
  have hc1_01 := add_carry_01 u_i carryIn
  have hc2_01 := add_carry_01 uPlusCarry v_i
  -- Total: u_i + v_i + carryIn = (c1 + c2) * 2^64 + uNew
  -- But c1 + c2 ≤ 1 (the two carries are exclusive)
  have := u_i.isLt; have := v_i.isLt
  have htot : u_i.toNat + v_i.toNat + carryIn.toNat < 2 * 2^64 := by omega
  have hupc : uPlusCarry.toNat = (u_i.toNat + carryIn.toNat) % 2^64 :=
    BitVec.toNat_add u_i carryIn
  -- If c1 = 1 then uPlusCarry is small, so c2 = 0
  have hexcl : c1 + c2 ≤ 1 := by
    rcases hc1_01 with h | h <;> rcases hc2_01 with h' | h'
    · omega
    · omega
    · -- c1 = 1: uPlusCarry = u_i + ci - 2^64, which is small
      have : uPlusCarry.toNat = u_i.toNat + carryIn.toNat - 2^64 := by rw [hupc]; omega
      have : uPlusCarry.toNat + v_i.toNat < 2^64 := by omega
      have : c2 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    · -- c1 = 1, c2 = 1: impossible since total < 2 * 2^64
      have : uPlusCarry.toNat = u_i.toNat + carryIn.toNat - 2^64 := by rw [hupc]; omega
      have : uPlusCarry.toNat + v_i.toNat < 2^64 := by omega
      omega
  refine ⟨c1 + c2, hexcl, ?_⟩
  nlinarith [h1, h2]

-- ============================================================================
-- 4-limb addback chain
-- ============================================================================

/-- 4-limb addback: adding the divisor back to the underflowed remainder.
    Given per-limb carry equations, the val256 result satisfies:
      val256 u + val256 v = val256 uNew + carryOut * 2^256
    where carryOut ∈ {0, 1}. -/
theorem addback_4limb_val256
    (u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 : Word)
    (c0 c1 c2 c3 : Nat)
    (h0 : u0.toNat + v0.toNat = c0 * 2^64 + r0.toNat)
    (h1 : u1.toNat + v1.toNat + c0 = c1 * 2^64 + r1.toNat)
    (h2 : u2.toNat + v2.toNat + c1 = c2 * 2^64 + r2.toNat)
    (h3 : u3.toNat + v3.toNat + c2 = c3 * 2^64 + r3.toNat) :
    val256 u0 u1 u2 u3 + val256 v0 v1 v2 v3 =
    val256 r0 r1 r2 r3 + c3 * 2^256 := by
  unfold val256; nlinarith

/-- Addback with carryIn for limb 0 (the initial carry is from the mulsub borrow).
    When the mulsub borrow is 0, the addback carry chain starts with 0.
    This variant takes a general initial carry for the first limb. -/
theorem addback_4limb_val256_with_carry
    (u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 : Word)
    (c_init c0 c1 c2 c3 : Nat)
    (h0 : u0.toNat + v0.toNat + c_init = c0 * 2^64 + r0.toNat)
    (h1 : u1.toNat + v1.toNat + c0 = c1 * 2^64 + r1.toNat)
    (h2 : u2.toNat + v2.toNat + c1 = c2 * 2^64 + r2.toNat)
    (h3 : u3.toNat + v3.toNat + c2 = c3 * 2^64 + r3.toNat) :
    val256 u0 u1 u2 u3 + val256 v0 v1 v2 v3 + c_init =
    val256 r0 r1 r2 r3 + c3 * 2^256 := by
  unfold val256; nlinarith

-- ============================================================================
-- End-to-end: mulsub underflow + addback → corrected Euclidean
-- ============================================================================

/-- When mulsub underflows (cb3 = 1) and addback produces carryOut = 1,
    the corrected result satisfies the Euclidean property with quotient q-1.

    This combines:
    1. mulsub_chain_nat with cb3 = 1: val256(u) + 2^256 = val256(r_ms) + q * val256(v)
    2. addback: val256(r_ms) + val256(v) = val256(r_ab) + carry * 2^256
    3. Carry = 1 (since r_ms is close to 2^256), cancelling: val256(u) = val256(r_ab) + (q-1)*val256(v) -/
theorem addback_correction_euclidean
    (uVal vVal rMsVal rAbVal : Nat) (qNat : Nat)
    (h_mulsub : uVal + 2^256 = rMsVal + qNat * vVal)
    (h_addback : rMsVal + vVal = rAbVal + 2^256)
    (hq : 0 < qNat) :
    uVal = rAbVal + (qNat - 1) * vVal := by
  nlinarith [mulsub_correction_eq uVal vVal rMsVal qNat h_mulsub hq]

end EvmWord

end EvmAsm.Evm64
