/-
  EvmAsm.Evm64.EvmWordArith.MulHigh

  High 256 bits of the natural-number product of two `EvmWord`s.

  Provides:
  * `EvmWord.mulHigh a b` — the upper 256 bits of `a.toNat * b.toNat`,
    truncated to an `EvmWord`. Together with the truncated product
    `a * b` (which is the low 256 bits), this completely captures the
    full 512-bit schoolbook product.
  * `EvmWord.mulHigh_correct` — algebraic correctness:
    `(mulHigh a b).toNat = (a.toNat * b.toNat) / 2^256`.
  * `EvmWord.mulHigh_mul_split` — companion identity expressing the
    natural-number product as `high · 2^256 + low`.

  This is the slice-4a deliverable for GH issue #91 (ADDMOD/MULMOD)
  per `docs/91-addmod-mulmod-survey.md` §3 (lines 162–170): the
  algebraic high-half identity. The runtime bridge to the existing
  schoolbook column accumulators in `EvmAsm/Evm64/Multiply` lives in
  the wider slice 4 (beads `evm-asm-lxq4`), which composes this
  algebraic shape with `MulCorrect.lean`'s limb-level proofs.

  Beads: `evm-asm-8qht`. Authored by @pirapira; implemented by
  Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.EvmWord

namespace EvmAsm.Evm64

namespace EvmWord

-- ============================================================================
-- High 256 bits of the schoolbook product
-- ============================================================================

/-- Upper 256 bits of the natural-number product `a.toNat * b.toNat`,
    embedded back into an `EvmWord`. The full 512-bit product equals
    `(mulHigh a b).toNat * 2^256 + (a * b).toNat`. -/
def mulHigh (a b : EvmWord) : EvmWord :=
  BitVec.ofNat 256 ((a.toNat * b.toNat) / 2 ^ 256)

/-- Algebraic correctness of `EvmWord.mulHigh`: it is exactly the
    quotient of the natural-number product by `2^256`. The mod-`2^256`
    that `BitVec.ofNat` would normally apply is a no-op here, since
    each operand is bounded by `2^256` and so the product is bounded
    by `2^512`, making the quotient itself bounded by `2^256`. -/
theorem mulHigh_correct (a b : EvmWord) :
    (EvmWord.mulHigh a b).toNat = (a.toNat * b.toNat) / 2 ^ 256 := by
  unfold mulHigh
  rw [BitVec.toNat_ofNat]
  -- a.toNat < 2^256, b.toNat < 2^256 ⇒ product < 2^256 * 2^256 ⇒
  -- quotient < 2^256.
  have ha : a.toNat < 2 ^ 256 := a.isLt
  have hb : b.toNat < 2 ^ 256 := b.isLt
  have h2pos : 0 < (2 : Nat) ^ 256 := Nat.two_pow_pos 256
  have hprod : a.toNat * b.toNat < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) h2pos
  have hq : (a.toNat * b.toNat) / 2 ^ 256 < 2 ^ 256 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hprod)
  exact Nat.mod_eq_of_lt hq

/-- Companion identity: the natural-number product is faithfully
    represented as `high · 2^256 + low`, where `low = (a * b).toNat`
    is the truncated `EvmWord` product and `high = (mulHigh a b).toNat`.

    This is the form that `evm_mulmod_stack_spec` (slice 5) uses when
    bridging from the runtime schoolbook to `mulmod_correct`. -/
theorem mulHigh_mul_split (a b : EvmWord) :
    a.toNat * b.toNat =
      (EvmWord.mulHigh a b).toNat * 2 ^ 256 + (a * b).toNat := by
  rw [mulHigh_correct]
  -- (a * b).toNat = (a.toNat * b.toNat) % 2^256.
  have hlow : (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
    simp [BitVec.toNat_mul]
  rw [hlow, Nat.mul_comm _ (2 ^ 256)]
  exact (Nat.div_add_mod _ _).symm

end EvmWord

end EvmAsm.Evm64
