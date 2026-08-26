/-
  EvmAsm.Evm64.EvmWordArith.DivN4BorrowRemainderLtGen

  U4-general borrow-branch remainder bound: on the borrow branch with
  `c3 = uTop + 1`, the `iterWithDoubleAddback` output remainder is `< val256 v`,
  for ANY `uTop` (no `U4 = 0`).

  This is the U4-general counterpart of
  `iterWithDoubleAddback_borrow_remainder_lt_of_qhat_le_div_plus_one`
  (DivN4DoubleAddback), which is `c3 = 1` / `uTop = 0`-specific.

  Both branches are clean val256 bookkeeping (no overshoot / qTrue):
  * single (carry ≠ 0): `ab.top = 0` (#7649), and the addback identity gives
    `val256(ab.result) = val256(ms.result) + B - 2^256 < B` since
    `val256(ms.result) < 2^256`;
  * double (carry = 0, carry2 = 1): `ab'.top = 0` (#7649 on the 2nd addback),
    `val256(ab'.result) = val256(ab.result) + B - 2^256 < B` since
    `val256(ab.result) < 2^256`.

  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackGen

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- On the borrow branch with `c3 = uTop + 1`, the iterate output remainder is
    `< val256 v`, for ANY `uTop`. -/
theorem iterWithDoubleAddback_borrow_remainder_lt_gen
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hb : BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    (hc3 : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = uTop + 1)
    (hcarry2 : isAddbackCarry2Nz q v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2 ^ 256 <
      EvmWord.val256 v0 v1 v2 v3 := by
  intro out
  subst out
  have hout := iterWithDoubleAddback_borrow (qHat := q) (v0 := v0) (v1 := v1)
    (v2 := v2) (v3 := v3) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) (uTop := uTop) hb
  simp only [] at hout
  rw [hout]
  set ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3 with hmsdef
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    with habdef
  have hBb : val256 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 < 2 ^ 256 := val256_bound _ _ _ _
  by_cases hcarry_zero :
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0
  · rw [if_pos hcarry_zero]
    -- first addback top = uTop - c3 (carry = 0).
    have hab_top : ab.2.2.2.2 = uTop - ms.2.2.2.2 := by
      rw [habdef]
      have h := addbackN4_top_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
      simp only [] at h
      rw [h, hcarry_zero]; simp
    -- second addback carry = 1.
    have hcarry2_ne : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
      have := hcarry2 hcarry_zero; rw [habdef]; exact this
    have hcarry2_one : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 = 1 :=
      addbackN4_carry_eq_one_of_ne_zero _ _ _ _ v0 v1 v2 v3 hcarry2_ne
    -- second addback top = 0.
    have hab'_top0 := addbackN4_single_top_zero_of_c3_uTop_plus_one
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 uTop ms.2.2.2.2 hc3 hcarry2_one
    rw [← hab_top] at hab'_top0
    -- addback identities.
    have hid1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    simp only [] at hid1
    rw [← habdef, hcarry_zero] at hid1
    have hid2 := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    simp only [] at hid2
    rw [hcarry2_one] at hid2
    have habr : val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 < 2 ^ 256 := val256_bound _ _ _ _
    have h0 : (0 : Word).toNat = 0 := by decide
    have h1 : (1 : Word).toNat = 1 := by decide
    rw [hab'_top0, h0]
    rw [h0] at hid1
    rw [h1] at hid2
    linarith [hid1, hid2, habr]
  · rw [if_neg hcarry_zero]
    have hcarry_one : addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 1 :=
      addbackN4_carry_eq_one_of_ne_zero _ _ _ _ v0 v1 v2 v3 hcarry_zero
    have hab_top0 := addbackN4_single_top_zero_of_c3_uTop_plus_one
      ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 uTop ms.2.2.2.2 hc3 hcarry_one
    have hid1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    simp only [] at hid1
    rw [← habdef, hcarry_one] at hid1
    have h0 : (0 : Word).toNat = 0 := by decide
    have h1 : (1 : Word).toNat = 1 := by decide
    rw [← habdef] at hab_top0
    rw [hab_top0, h0]
    rw [h1] at hid1
    linarith [hid1, hBb]

end EvmAsm.Evm64
