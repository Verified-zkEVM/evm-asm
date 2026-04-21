/-
  EvmAsm.Evm64.EvmWordArith.Val256ModBridge

  Nat-level val256 extractions for the MOD stack spec bridge:
  - `val256_ms_un_eq_val256_mod_max_skip`:
      `val256(mulsub_un) = val256(a) % val256(b)` at n=4 max+skip with c3=0.
  - `val256_ms_un_lt_val256_b_max_skip`:
      `val256(mulsub_un) < val256(b)` (Knuth remainder bound).

  Both facts follow from the val256-level Euclidean equation derivable from
  `mulsubN4_val256_eq` plus the max-trial overestimate bound. They extract
  the Nat-level content from `n4_max_skip_correct` in a form usable by the
  MOD denormalization bridge (Lemma C/D/E chain) without dragging
  `EvmWord.mod` / `fromLimbs` through the proof.
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_toNat_0)

namespace EvmWord

/-- The un-normalized mulsub output (at n=4 max+skip with `c3 = 0`) represents
    `val256(a) mod val256(b)` at the Nat level. Derived via the Euclidean
    uniqueness argument (`remainder_lt_of_ge_floor`) rather than going through
    the `EvmWord.mod` / `fromLimbs` encoding of `n4_max_skip_correct`. -/
theorem val256_ms_un_eq_val256_mod_max_skip
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hc3_zero : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0) :
    let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 =
    val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
  intro ms
  -- From `mulsubN4_val256_eq` with c3 = 0:
  --   val256(a) = qHat * val256(b) + val256(ms)
  have hmulsub_raw := mulsubN4_val256_eq (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at hmulsub_raw
  rw [show ms.2.2.2.2 = (0 : Word) from hc3_zero] at hmulsub_raw
  rw [word_toNat_0, Nat.zero_mul, Nat.add_zero]
    at hmulsub_raw
  -- Rearrange into the form expected by `remainder_lt_of_ge_floor`.
  have hmulsub : val256 a0 a1 a2 a3 =
      (signExtend12 (4095 : BitVec 12) : Word).toNat * val256 b0 b1 b2 b3 +
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := by linarith
  -- Overestimate: val256(a)/val256(b) ≤ qHat.
  have hge := max_trial_overestimate_n4 a0 a1 a2 a3 b0 b1 b2 b3 hb3nz
  have hv := val256_pos_of_or_ne_zero hbnz
  have ⟨hq, hr_lt⟩ := remainder_lt_of_ge_floor hv hmulsub hge
  -- Substitute `qHat = val256(a)/val256(b)` into the mulsub equation, then
  -- compare with `Nat.div_add_mod` to conclude.
  rw [hq] at hmulsub
  have hdam := Nat.div_add_mod (val256 a0 a1 a2 a3) (val256 b0 b1 b2 b3)
  have hmulcomm : val256 b0 b1 b2 b3 * (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) =
      (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) * val256 b0 b1 b2 b3 := Nat.mul_comm _ _
  omega

/-- The un-normalized mulsub output is bounded by the divisor (at n=4 max+skip
    with `c3 = 0`). Follows from `val256_ms_un_eq_val256_mod_max_skip` +
    `Nat.mod_lt`. -/
theorem val256_ms_un_lt_val256_b_max_skip
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hc3_zero : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0) :
    let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < val256 b0 b1 b2 b3 := by
  intro ms
  rw [val256_ms_un_eq_val256_mod_max_skip a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb3nz hc3_zero]
  exact Nat.mod_lt _ (val256_pos_of_or_ne_zero hbnz)

end EvmWord

end EvmAsm.Evm64
