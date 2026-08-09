/-
  EvmAsm.Rv64.RemuNat

  `rv64_remu` as `Nat` remainder, and the divisibility test guest code actually
  writes (GH #11578).

  ## Why this file exists

  `rv64_divu` already had its `Nat` bridge — `rv64_divu_toNat`
  (`EvmAsm/Evm64/EvmWordArith/KnuthTheoremB.lean:101`). **`rv64_remu` had none**,
  anywhere in the tree: the only prior proof reasoning about a `DIVU`/`REMU` pair
  is `U256DivU64BeSAsm.lean`, and it keeps both **opaque** behind a mirror model
  (`divByteStep`, `:26-28`) rather than bridging to `Nat`.

  ⚠️ Homed here rather than beside its `divu` sibling on purpose. That sibling
  sits in a 600-line file about Knuth's Algorithm B, where a reader looking for a
  general remainder bridge will not find it — which is exactly the failure mode
  ("searching by name finds a name; only reading the statement finds the fact")
  that has now cost this project four rediscoveries. A one-purpose file with the
  statement in its name is the cheap fix.

  ## The shape callers want

  Guest code does not test divisibility as `a % b = 0` on `Nat`; it computes
  `remu` into a register and branches on `bnez`. So the load-bearing form is the
  **`= 0` iff**, not the `toNat` equation — `remu_eq_zero_iff_mod_eq_zero` below
  is what a `bnez` obligation reduces to in one rewrite.
-/

import EvmAsm.Rv64.Instructions

namespace EvmAsm.Rv64

/-- `rv64_remu` is `Nat` remainder on a non-zero divisor. The `b = 0` case
    returns `a` unchanged (RV64IM has no trap), and is excluded rather than
    folded in: every guest divisor this is used with is a non-zero literal, and
    silently absorbing the zero case would make the lemma true of a routine that
    never checked. -/
theorem rv64_remu_toNat (a b : Word) (hb : b ≠ 0) :
    (rv64_remu a b).toNat = a.toNat % b.toNat := by
  unfold rv64_remu
  split
  · rename_i hbeq
    exfalso; apply hb
    simp at hbeq
    exact hbeq
  · rw [BitVec.toNat_umod]

/-- **The divisibility test, in the polarity `bnez` branches on.** `remu a b` is
    the zero word exactly when `b` divides `a` as naturals. -/
theorem remu_eq_zero_iff_mod_eq_zero (a b : Word) (hb : b ≠ 0) :
    rv64_remu a b = 0 ↔ a.toNat % b.toNat = 0 := by
  constructor
  · intro h
    have := rv64_remu_toNat a b hb
    rw [h] at this
    simpa using this.symm
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [rv64_remu_toNat a b hb, h]
    simp

/-- The contrapositive, which is the arm a `bnez … , .Lfail` takes. Stated
    separately because a caller reasoning about the *rejecting* path should not
    have to push a negation through the iff at every branch. -/
theorem remu_ne_zero_iff_mod_ne_zero (a b : Word) (hb : b ≠ 0) :
    rv64_remu a b ≠ 0 ↔ a.toNat % b.toNat ≠ 0 :=
  not_congr (remu_eq_zero_iff_mod_eq_zero a b hb)

end EvmAsm.Rv64
