/-
  EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddbackVal256

  U4-general double-addback value conservation for the n=4 double-addback iterate.

  The carry=0 branch of `iterWithDoubleAddback` performs TWO corrective addbacks,
  emitting quotient `qHat - 2` (= `qHat + signExtend12 4095 + signExtend12 4095`)
  and the second addback's result limbs.  Under the single-overshoot borrow
  `c3 = uTop + 1` (no wrap), a ZERO first addback carry, and a nonzero second
  addback carry, the dividend value is preserved for ANY `uTop`:

    val256 u + uTop·2^256 = (qHat-2)·val256 v + val256(ab'.result) + ab'.top·2^256.

  (The first addback's top is `(uTop - c3) + 0 = -1 = 2^64-1`, unresolved; the
  second addback's top is `(uTop - c3) + 1 = 0`, resolved.)  This is the U4≥1
  companion of `iterDoubleAddbackBranch_val256_conservation` (DivN4Overestimate,
  `uTop = 0`-only).

  Proof: pure val256 bookkeeping (`mulsubN4_val256_eq` + `addbackN4_val256_eq`
  twice) + the generalised addback-top-zero `addbackN4_single_top_zero_of_c3_uTop_plus_one`
  (#7649) for the second addback + `add_signExtend12_4095_add_signExtend12_4095_toNat`
  (`qOut = q - 2`).  Together with the single-addback version this completes the
  two branch generalisations needed for a U4-general `iterWithDoubleAddback`
  conservation.  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackGen

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Pure-`Nat` arithmetic core of the double-addback conservation (`2^256` kept as
    a variable `W` to keep `omega` away from large-literal recursion-depth). -/
private theorem double_addback_conservation_arith
    (A U MR B AB AB' QV W : Nat)
    (hms : A + (U + 1) * W = MR + QV)
    (hab1 : MR + B = AB)
    (hab2 : AB + B = AB' + W)
    (hQV : 2 * B ≤ QV) :
    A + U * W = QV - 2 * B + AB' := by
  rw [Nat.add_mul, Nat.one_mul] at hms
  omega

/-- U4-general double-addback value conservation (carry=0 branch), for ANY `uTop`
    under `c3 = uTop + 1` (no wrap), zero first carry, nonzero second carry. -/
theorem iterDoubleAddback_val256_conservation_gen
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (huTop : uTop.toNat + 1 < 2 ^ 64)
    (hc3 : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = uTop + 1)
    (hcarry_zero :
      addbackN4_carry
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0)
    (hcarry2_one :
      addbackN4_carry
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1
        v0 v1 v2 v3 = 1)
    (hq_ge_2 : 2 ≤ q.toNat) :
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256 =
      (q + signExtend12 (4095 : BitVec 12) + signExtend12 (4095 : BitVec 12)).toNat *
          EvmWord.val256 v0 v1 v2 v3 +
        EvmWord.val256
          (addbackN4
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2
            v0 v1 v2 v3).1
          (addbackN4
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2
            v0 v1 v2 v3).2.1
          (addbackN4
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2
            v0 v1 v2 v3).2.2.1
          (addbackN4
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1
            (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
              (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
              (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2
            v0 v1 v2 v3).2.2.2.1 +
        (addbackN4
          (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).1
          (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.1
          (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.1
          (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1
          (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2
          v0 v1 v2 v3).2.2.2.2.toNat * 2 ^ 256 := by
  -- Abbreviate the mulsub result and the first addback.
  set ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3 with hms_def
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    with hab_def
  -- The first addback's top limb is `uTop - c3` (carry = 0).
  have hab_top : ab.2.2.2.2 = uTop - ms.2.2.2.2 := by
    rw [hab_def]
    have h := addbackN4_top_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    simp only [] at h
    rw [h, hcarry_zero]
    simp
  -- The second addback (top input `uTop - c3`, carry = 1) resolves the top to 0.
  have hab'_top0 := addbackN4_single_top_zero_of_c3_uTop_plus_one
    ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 uTop ms.2.2.2.2 hc3 hcarry2_one
  rw [← hab_top] at hab'_top0
  set ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3 with hab'_def
  -- val256 identities.
  have hms := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hms
  rw [← hms_def] at hms
  have hab1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
  simp only [] at hab1
  rw [← hab_def, hcarry_zero] at hab1
  have hab2 := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  simp only [] at hab2
  rw [← hab'_def, hcarry2_one] at hab2
  -- numeric facts
  have h1 : (1 : Word).toNat = 1 := by decide
  have h0 : (0 : Word).toNat = 0 := by decide
  have hc3_toNat : ms.2.2.2.2.toNat = uTop.toNat + 1 := by
    rw [hc3, BitVec.toNat_add, h1]; omega
  have hqsub : (q + signExtend12 (4095 : BitVec 12) + signExtend12 (4095 : BitVec 12)).toNat
      = q.toNat - 2 :=
    add_signExtend12_4095_add_signExtend12_4095_toNat q hq_ge_2
  have hVle : 2 * val256 v0 v1 v2 v3 ≤ q.toNat * val256 v0 v1 v2 v3 :=
    Nat.mul_le_mul_right _ hq_ge_2
  rw [h0, Nat.zero_mul, Nat.add_zero] at hab1
  rw [h1, Nat.one_mul] at hab2
  rw [hc3_toNat] at hms
  rw [hab'_top0, h0, Nat.zero_mul, Nat.add_zero, hqsub, Nat.sub_mul]
  -- Discharge via the abstracted arithmetic core.
  exact double_addback_conservation_arith
    (val256 u0 u1 u2 u3) uTop.toNat
    (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1)
    (val256 v0 v1 v2 v3)
    (val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1)
    (val256 ab'.1 ab'.2.1 ab'.2.2.1 ab'.2.2.2.1)
    (q.toNat * val256 v0 v1 v2 v3) (2 ^ 256)
    hms hab1 hab2 hVle

end EvmAsm.Evm64
