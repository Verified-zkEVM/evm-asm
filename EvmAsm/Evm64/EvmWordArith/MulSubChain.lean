/-
  EvmAsm.Evm64.EvmWordArith.MulSubChain

  Carry-chain arithmetic for multi-limb multiply-subtract.
  These lemmas establish the Nat-level correctness of the multiply-subtract
  loop body in Knuth's Algorithm D: `u -= q * v` across 4 limbs with
  carry/borrow propagation.
-/

import EvmAsm.Evm64.EvmWordArith.Div128Lemmas

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Single-step carry/borrow properties
-- ============================================================================

/-- Add-with-carry at the Nat level: `a + b = carry * 2^64 + (a + b) % 2^64`. -/
theorem add_carry_nat (a b : Word) :
    a.toNat + b.toNat =
    (a.toNat + b.toNat) / 2^64 * 2^64 + (a + b).toNat := by
  rw [BitVec.toNat_add]
  have := Nat.div_add_mod (a.toNat + b.toNat) (2^64)
  omega

/-- The carry from addition is 0 or 1. -/
theorem add_carry_01 (a b : Word) :
    (a.toNat + b.toNat) / 2^64 = 0 ∨ (a.toNat + b.toNat) / 2^64 = 1 := by
  have ha := a.isLt; have hb := b.isLt
  have : a.toNat + b.toNat < 2 * 2^64 := by omega
  have : (a.toNat + b.toNat) / 2^64 < 2 := Nat.div_lt_of_lt_mul this
  omega

/-- Sub-with-borrow at the Nat level:
    `a + borrow * 2^64 = (a - b).toNat + b.toNat`
    where `borrow = if a < b then 1 else 0`. -/
theorem sub_borrow_nat (a b : Word) :
    let borrow := if a.toNat < b.toNat then 1 else 0
    a.toNat + borrow * 2^64 = (a - b).toNat + b.toNat := by
  intro borrow
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · simp only [borrow, h, ite_true]; omega
  · simp only [borrow, h, ite_false, Nat.zero_mul, Nat.add_zero]; omega

-- ============================================================================
-- 4-limb multiply-subtract chain (telescoping)
-- ============================================================================

/-- 4-limb multiply-subtract chain: given per-limb carry equations,
    the combined result satisfies the 256-bit equation.

    Each step equation says: `u_i + cb_i * 2^64 = r_i + q * v_i + cb_{i-1}`
    where `cb_{-1} = 0` (initial carry is zero).

    The intermediate carries `cb_0, cb_1, cb_2` telescope, leaving only `cb_3`:
    `val256 u + cb_3 * 2^256 = val256 r + q * val256 v`

    - `cb_3 = 0`: no underflow, `val256 r = val256 u - q * val256 v`
    - `cb_3 > 0`: underflow occurred, correction needed (add v back, decrement q) -/
theorem mulsub_chain_nat (q_nat : Nat) (u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 : Word)
    (cb0 cb1 cb2 cb3 : Nat)
    (h0 : u0.toNat + cb0 * 2^64 = r0.toNat + q_nat * v0.toNat)
    (h1 : u1.toNat + cb1 * 2^64 = r1.toNat + q_nat * v1.toNat + cb0)
    (h2 : u2.toNat + cb2 * 2^64 = r2.toNat + q_nat * v2.toNat + cb1)
    (h3 : u3.toNat + cb3 * 2^64 = r3.toNat + q_nat * v3.toNat + cb2) :
    val256 u0 u1 u2 u3 + cb3 * 2^256 =
    val256 r0 r1 r2 r3 + q_nat * val256 v0 v1 v2 v3 := by
  unfold val256; nlinarith

/-- When the multiply-subtract has no underflow (`cb3 = 0`), the result is exact. -/
theorem mulsub_chain_no_underflow (q_nat : Nat)
    (u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 : Word)
    (cb0 cb1 cb2 : Nat)
    (h0 : u0.toNat + cb0 * 2^64 = r0.toNat + q_nat * v0.toNat)
    (h1 : u1.toNat + cb1 * 2^64 = r1.toNat + q_nat * v1.toNat + cb0)
    (h2 : u2.toNat + cb2 * 2^64 = r2.toNat + q_nat * v2.toNat + cb1)
    (h3 : u3.toNat = r3.toNat + q_nat * v3.toNat + cb2) :
    val256 u0 u1 u2 u3 = val256 r0 r1 r2 r3 + q_nat * val256 v0 v1 v2 v3 := by
  have := mulsub_chain_nat q_nat u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3
    cb0 cb1 cb2 0 h0 h1 h2 (by linarith)
  simp at this; exact this

-- ============================================================================
-- Correction step
-- ============================================================================

/-- After correction (add v back, decrement q), the equation holds.
    If `val256 u + 2^256 = val256 r + q * val256 v` with cb = 1 (underflow),
    then: `val256 u + 2^256 = (val256 r + val256 v) + (q - 1) * val256 v`. -/
theorem mulsub_correction_eq (u_nat v_nat r_nat q_nat : Nat)
    (hchain : u_nat + 2^256 = r_nat + q_nat * v_nat)
    (hq : 0 < q_nat) :
    u_nat + 2^256 = (r_nat + v_nat) + (q_nat - 1) * v_nat := by
  have hq1 : q_nat = 1 + (q_nat - 1) := by omega
  nlinarith [show q_nat * v_nat = v_nat + (q_nat - 1) * v_nat by nlinarith]

end EvmWord

end EvmAsm.Rv64
