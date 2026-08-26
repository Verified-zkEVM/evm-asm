/-
  EvmAsm.Evm64.EvmWordArith.DivN4IterConservationGen

  U4-general value conservation for the full `iterWithDoubleAddback` iterate.

  Assembles the three branch conservations into a single statement that holds for
  ANY `uTop` (no `U4 = 0`), replacing the `c3 = 1` / `uTop = 0` machinery of
  `iterWithDoubleAddback_val256_conservation_of_carry2` (DivN4DoubleAddback):

    val256 u + uTop·2^256 = out.q·val256 v + val256(out.result) + out.top·2^256.

  Dispatch (mirrors `_of_carry2`):
  * no borrow → `iterWithDoubleAddback_no_borrow_val256_conservation` (already
    `uTop`-general);
  * borrow, first carry ≠ 0 → single addback `iterSingleAddback_val256_conservation_gen`
    (#7651);
  * borrow, first carry = 0 → double addback `iterDoubleAddback_val256_conservation_gen`
    (#7652), with the second carry `= 1` from `isAddbackCarry2Nz`.

  The single-overshoot borrow `c3 = uTop + 1` is taken as a hypothesis
  (`hc3_of_borrow`) — the U4-general analogue of the `_of_carry2` premise
  `hc3_one_of_borrow` (`c3 = 1`).  It is the remaining deferred obligation for the
  n=4 call path (discharged from the Knuth trial structure), exactly as the v4/v5
  `_of_carry2` defers its `c3 = 1` to the runtime-condition lemmas.
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddbackVal256
public import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackVal256

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- U4-general `iterWithDoubleAddback` value conservation: holds for ANY `uTop`,
    given the single-overshoot borrow `c3 = uTop + 1` (on borrow), the second-carry
    predicate `isAddbackCarry2Nz`, and `q ≥ 2`. -/
theorem iterWithDoubleAddback_val256_conservation_gen
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (huTop : uTop.toNat + 1 < 2 ^ 64)
    (hc3_of_borrow :
      BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 →
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = uTop + 1)
    (hcarry2 : isAddbackCarry2Nz q v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hq_ge_2 : 2 ≤ q.toNat) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256 =
      out.1.toNat * EvmWord.val256 v0 v1 v2 v3 +
        EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2 ^ 256 := by
  intro out
  subst out
  by_cases hb : BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  · have hout := iterWithDoubleAddback_borrow (qHat := q) (v0 := v0) (v1 := v1)
      (v2 := v2) (v3 := v3) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) (uTop := uTop) hb
    simp only [] at hout
    rw [hout]
    by_cases hcarry_zero :
        addbackN4_carry (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 v0 v1 v2 v3 = 0
    · rw [if_pos hcarry_zero]
      have hcarry2_one := addbackN4_carry_eq_one_of_ne_zero _ _ _ _ v0 v1 v2 v3
        (hcarry2 hcarry_zero)
      exact iterDoubleAddback_val256_conservation_gen q v0 v1 v2 v3 u0 u1 u2 u3 uTop
        huTop (hc3_of_borrow hb) hcarry_zero hcarry2_one hq_ge_2
    · rw [if_neg hcarry_zero]
      have hcarry_one := addbackN4_carry_eq_one_of_ne_zero _ _ _ _ v0 v1 v2 v3 hcarry_zero
      exact iterSingleAddback_val256_conservation_gen q v0 v1 v2 v3 u0 u1 u2 u3 uTop
        huTop (hc3_of_borrow hb) hcarry_one (by omega)
  · have hout := iterWithDoubleAddback_no_borrow (qHat := q) (v0 := v0) (v1 := v1)
      (v2 := v2) (v3 := v3) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) (uTop := uTop) hb
    simp only [] at hout
    rw [hout]
    exact iterWithDoubleAddback_no_borrow_val256_conservation
      q v0 v1 v2 v3 u0 u1 u2 u3 uTop hb

end EvmAsm.Evm64
