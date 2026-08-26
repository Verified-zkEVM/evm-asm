/-
  EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackVal256

  U4-general single-addback value conservation for the n=4 double-addback iterate.

  The carry≠0 branch of `iterWithDoubleAddback` performs a single corrective
  addback, emitting quotient `qHat - 1` (= `qHat + signExtend12 4095`) and the
  addback result limbs.  Under the single-overshoot borrow `c3 = uTop + 1` (no
  wrap) and a nonzero addback carry, the dividend value is preserved for ANY
  `uTop`:

    val256 u + uTop·2^256 = (qHat-1)·val256 v + val256(ab.result) + ab.top·2^256.

  This generalises `iterSingleAddbackBranch_val256_conservation` (DivN4Overestimate),
  which is `uTop = 0`-only (it routes through `val256_conservation_of_low_eq_and_zero_tops`,
  requiring `uTop.toNat = 0`).  Pure val256 bookkeeping: `mulsubN4_val256_eq` +
  `addbackN4_val256_eq` + the generalised addback-top-zero
  `addbackN4_single_top_zero_of_c3_uTop_plus_one` (#7649).

  One of the two branch generalisations needed for a U4-general
  `iterWithDoubleAddback` conservation.  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackGen

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The pure-`Nat` arithmetic core of the single-addback conservation, with the
    large val256 / mulsub / addback terms abstracted to opaque atoms (keeps the
    `omega` call small, away from the deeply nested BitVec terms). -/
private theorem single_addback_conservation_arith
    (A U MR V QV AR W : Nat)
    (hms : A + (U + 1) * W = MR + QV)
    (hab : MR + V = AR + W)
    (hVle : V ≤ QV) :
    A + U * W = QV - V + AR := by
  rw [Nat.add_mul, Nat.one_mul] at hms
  omega

/-- U4-general single-addback value conservation (carry≠0 branch), for ANY `uTop`
    under `c3 = uTop + 1` (no wrap) and a nonzero addback carry. -/
theorem iterSingleAddback_val256_conservation_gen
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (huTop : uTop.toNat + 1 < 2 ^ 64)
    (hc3 : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = uTop + 1)
    (hcarry_one :
      addbackN4_carry
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 1)
    (hq_pos : 1 ≤ q.toNat) :
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256 =
      (q + signExtend12 (4095 : BitVec 12)).toNat * EvmWord.val256 v0 v1 v2 v3 +
        EvmWord.val256
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
            (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.1 +
        (addbackN4 (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
          (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3).2.2.2.2.toNat *
          2 ^ 256 := by
  -- ab top resolves to 0 (generalised, any uTop).
  have htop0 := addbackN4_single_top_zero_of_c3_uTop_plus_one
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
    v0 v1 v2 v3 uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 hc3 hcarry_one
  -- val256 identities (generic).
  have hms := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hms
  have hab := addbackN4_val256_eq
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
    (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) v0 v1 v2 v3
  simp only [] at hab
  rw [hcarry_one] at hab
  -- numeric facts
  have h1 : (1 : Word).toNat = 1 := by decide
  have h0 : (0 : Word).toNat = 0 := by decide
  have hc3_toNat : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = uTop.toNat + 1 := by
    rw [hc3, BitVec.toNat_add, h1]; omega
  have hqsub : (q + signExtend12 (4095 : BitVec 12)).toNat = q.toNat - 1 :=
    add_signExtend12_4095_toNat q hq_pos
  have hVle : val256 v0 v1 v2 v3 ≤ q.toNat * val256 v0 v1 v2 v3 :=
    Nat.le_mul_of_pos_left _ hq_pos
  -- Fold the large mulsub/addback terms into single atoms.
  set ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3 with hms_def
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    with hab_def
  rw [h1, one_mul] at hab
  rw [hc3_toNat] at hms
  rw [htop0, h0, hqsub, Nat.sub_one_mul, Nat.zero_mul, Nat.add_zero]
  -- Discharge via the abstracted arithmetic core (omega stays small).
  exact single_addback_conservation_arith
    (val256 u0 u1 u2 u3) uTop.toNat
    (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1)
    (val256 v0 v1 v2 v3) (q.toNat * val256 v0 v1 v2 v3)
    (val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1)
    (2 ^ 256)
    hms hab hVle

end EvmAsm.Evm64
