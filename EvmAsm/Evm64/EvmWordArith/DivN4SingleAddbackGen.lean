/-
  EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackGen

  U4-general "single addback resolves the borrow" fact.

  In the n=4 single-digit Knuth division, the inner `mulsubN4` is a four-limb
  mul-sub; the overflow limb `uTop` (= U4) is reconciled against the four-limb
  borrow `c3` afterwards.  On the single-overshoot addback branch the borrow is
  `c3 = uTop + 1`, and the first addback (with top input `uTop - c3`) produces a
  carry that cancels it: the resulting top limb is `(uTop - c3) + carry = -1 + 1 =
  0`, REGARDLESS of `uTop`.

  The existing `iterSingleAddbackBranch_ab_top_toNat_eq_zero` (DivN4Overestimate)
  proves this only for `uTop = 0` (it bakes in `c3 = 1`, derives `uTop = 0`).
  `addbackN4_single_top_zero_of_c3_uTop_plus_one` proves it for ANY `uTop` (under
  `c3 = uTop + 1` and `carry = 1`).  This removes the `U4 = 0` restriction at the
  addback-top level — a step toward a U4-general `iterWithDoubleAddback`
  conservation and hence a U4-general n=4 addback semantic.
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The single-addback top limb resolves to `0` for ANY `uTop`, given the
    single-overshoot borrow `c3 = uTop + 1` (no wrap) and a nonzero addback carry
    (`= 1`).  The addback top is `(uTop - c3) + carry = (uTop - (uTop+1)) + 1 = 0`. -/
theorem addbackN4_single_top_zero_of_c3_uTop_plus_one
    (un0 un1 un2 un3 v0 v1 v2 v3 uTop c3 : Word)
    (hc3 : c3 = uTop + 1)
    (hcarry_one : addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3 = 1) :
    (addbackN4 un0 un1 un2 un3 (uTop - c3) v0 v1 v2 v3).2.2.2.2 = 0 := by
  have htop := addbackN4_top_eq un0 un1 un2 un3 (uTop - c3) v0 v1 v2 v3
  simp only [] at htop
  rw [htop, hcarry_one, hc3]
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  have h0 : (0 : BitVec 64).toNat = 0 := by decide
  simp only [BitVec.toNat_add, BitVec.toNat_sub, h1, h0]
  omega

end EvmAsm.Evm64
