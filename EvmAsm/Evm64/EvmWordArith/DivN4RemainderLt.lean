/-
  EvmAsm.Evm64.EvmWordArith.DivN4RemainderLt

  Unified per-iteration remainder bound for `iterWithDoubleAddback` covering
  BOTH the borrow and the no-borrow branch.

  The existing `iterWithDoubleAddback_borrow_remainder_lt_of_qhat_le_div_plus_one`
  (`DivN4DoubleAddback.lean`) covers only the borrow branch (the active double
  addback), needing a quotient OVERestimate bound `q ≤ ⌊window/v⌋ + 1`.  The
  no-borrow branch needs the dual fact — the trial does not UNDERestimate, i.e.
  `window + uTop·2^256 < (q+1)·v` — and then the remainder is just
  `window + uTop·2^256 − q·v < v` directly from the no-borrow conservation.

  Together these give `iterWithDoubleAddback_remainder_lt`: from the standard
  Knuth trial bracket (`q` neither under- nor over-estimates by more than the
  allowed slack) the per-digit remainder is `< v` regardless of which branch the
  hardware took.  This is the version-agnostic core that the v5 n=2/n=3/n=4
  per-digit remainder bounds specialize (discharging the brackets from the
  resolved v5 trial `div128Quot_v5 = floor`, #7218–#7220).  Bead
  `evm-asm-wbc4i.9.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- **No-borrow branch remainder bound.** When the top limb does not borrow
    (`¬ ult uTop ms.c3`), the iteration output is exactly the `mulsub` result, so
    its value is `window + uTop·2^256 − q·v`.  If the trial does not
    underestimate (`window + uTop·2^256 < (q+1)·v`) this is `< v`. -/
theorem iterWithDoubleAddback_no_borrow_remainder_lt
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hb : ¬ BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    (hq_ge : EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 <
              (q.toNat + 1) * EvmWord.val256 v0 v1 v2 v3) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2^256 < EvmWord.val256 v0 v1 v2 v3 := by
  intro out
  subst out
  rw [iterWithDoubleAddback_no_borrow hb]
  dsimp only
  have hcons := iterWithDoubleAddback_no_borrow_val256_conservation
    q v0 v1 v2 v3 u0 u1 u2 u3 uTop hb
  rw [Nat.add_mul, Nat.one_mul] at hq_ge
  omega

/-- **Unified per-iteration remainder bound (both branches).** From the standard
    Knuth trial bracket — overestimate `q ≤ ⌊window/v⌋ + 1` (consumed on borrow)
    and no-underestimate `window + uTop·2^256 < (q+1)·v` (consumed on no-borrow)
    — the per-digit remainder is `< v` regardless of which branch fired. -/
theorem iterWithDoubleAddback_remainder_lt
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 →
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hq_over :
      q.toNat ≤ EvmWord.val256 u0 u1 u2 u3 / EvmWord.val256 v0 v1 v2 v3 + 1)
    (hq_ge : EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 <
              (q.toNat + 1) * EvmWord.val256 v0 v1 v2 v3) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2^256 < EvmWord.val256 v0 v1 v2 v3 := by
  intro out
  subst out
  by_cases hb : BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  · exact iterWithDoubleAddback_borrow_remainder_lt_of_qhat_le_div_plus_one
      q v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hb (hc3_one_of_borrow hb) hq_over
  · exact iterWithDoubleAddback_no_borrow_remainder_lt
      q v0 v1 v2 v3 u0 u1 u2 u3 uTop hb hq_ge

/-- **Borrow branch remainder bound with a `+2` overestimate.** The double
    addback corrects an overestimate of up to `2`, so the borrow branch
    tolerates `q ≤ ⌊window/v⌋ + 2` — which is exactly what the v5 multi-limb
    trial provides (`divKTrialCallV5QHat ≤ val256 u / val256 v + 2`, #7219).
    Same proof as the `…_plus_one` variant: the `+1` there is only used to derive
    `+2` internally, so the `+2` hypothesis is consumed directly. -/
theorem iterWithDoubleAddback_borrow_remainder_lt_of_qhat_le_div_plus_two
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hb : BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    (hc3_one : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hq_over :
      q.toNat ≤ EvmWord.val256 u0 u1 u2 u3 / EvmWord.val256 v0 v1 v2 v3 + 2) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2^256 < EvmWord.val256 v0 v1 v2 v3 := by
  intro out
  subst out
  have hout := iterWithDoubleAddback_borrow (qHat := q) (v0 := v0) (v1 := v1)
    (v2 := v2) (v3 := v3) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
    (uTop := uTop) hb
  simp only [] at hout
  rw [hout]
  let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  by_cases hcarry_zero : carry = 0
  · rw [if_pos hcarry_zero]
    have hq_ge_2 :=
      q_ge_two_of_mulsub_borrow_and_addback_carry_zero
        q v0 v1 v2 v3 u0 u1 u2 u3 hc3_one (by
          subst ms
          subst carry
          exact hcarry_zero)
    have hbranch : iterDoubleAddbackBranch q v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      subst ms
      subst carry
      exact iterDoubleAddbackBranch_of q v0 v1 v2 v3 u0 u1 u2 u3 uTop
        hb hc3_one hcarry_zero hbnz hq_over hq_ge_2
    have h := iterDoubleAddbackBranch_remainder_lt
      q v0 v1 v2 v3 u0 u1 u2 u3 uTop hbranch
    simp only [] at h
    exact h
  · rw [if_neg hcarry_zero]
    have hcarry_one : carry = 1 := by
      subst ms
      subst carry
      exact addbackN4_carry_eq_one_of_ne_zero
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 hcarry_zero
    have hq_pos := q_pos_of_mulsub_borrow q v0 v1 v2 v3 u0 u1 u2 u3 hc3_one
    have hbranch : iterSingleAddbackBranch q v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      subst ms
      subst carry
      exact iterSingleAddbackBranch_of q v0 v1 v2 v3 u0 u1 u2 u3 uTop
        hb hc3_one hcarry_one hq_pos
    have h := iterSingleAddbackBranch_remainder_lt
      q v0 v1 v2 v3 u0 u1 u2 u3 uTop hbranch
    simp only [] at h
    exact h

/-- **Unified per-iteration remainder bound with a `+2` overestimate.** As
    `iterWithDoubleAddback_remainder_lt`, but with the `+2` overestimate the v5
    multi-limb trial actually provides (the v5 n=2/n=3/n=4 specializations
    consume this form). -/
theorem iterWithDoubleAddback_remainder_lt_of_plus_two
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 →
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hq_over :
      q.toNat ≤ EvmWord.val256 u0 u1 u2 u3 / EvmWord.val256 v0 v1 v2 v3 + 2)
    (hq_ge : EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 <
              (q.toNat + 1) * EvmWord.val256 v0 v1 v2 v3) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2^256 < EvmWord.val256 v0 v1 v2 v3 := by
  intro out
  subst out
  by_cases hb : BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  · exact iterWithDoubleAddback_borrow_remainder_lt_of_qhat_le_div_plus_two
      q v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hb (hc3_one_of_borrow hb) hq_over
  · exact iterWithDoubleAddback_no_borrow_remainder_lt
      q v0 v1 v2 v3 u0 u1 u2 u3 uTop hb hq_ge

end EvmAsm.Evm64
