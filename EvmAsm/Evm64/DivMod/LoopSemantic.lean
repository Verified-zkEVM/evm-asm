/-
  EvmAsm.Evm64.DivMod.LoopSemantic

  Semantic bridge: connect the mulsubN4/addbackN4 computation definitions
  (from LoopDefs.lean) to the val256 Euclidean equations (from EvmWordArith).

  These theorems are pure Nat-level facts about the Word computations,
  independent of separation logic. They form the link between the
  loop body bounded CPS specs and the final EvmWord.div/mod correctness.
-/

-- `LoopDefs → LoopDefs.Post → LoopDefs.Iter → Compose.Base → DivMod.AddrNorm`.
import EvmAsm.Evm64.DivMod.LoopDefs
import EvmAsm.Evm64.EvmWordArith.DivMulSubCarry
import EvmAsm.Evm64.EvmWordArith.DivAddbackCarry

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord
open EvmAsm.Evm64.DivMod.AddrNorm (se12_0)

-- ============================================================================
-- Mulsub: mulsubN4 satisfies the 4-limb val256 Euclidean equation
-- ============================================================================

/-- The mulsubN4 computation satisfies the 4-limb mulsub val256 equation:
    val256(u) + c3 * 2^256 = val256(un) + q * val256(v)
    where (un0, un1, un2, un3, c3) = mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3. -/
theorem mulsubN4_val256_eq (q v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2^256 =
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 + q.toNat * val256 v0 v1 v2 v3 := by
  simp only [mulsubN4, se12_0]
  exact mulsub_register_4limb_val256

-- ============================================================================
-- Addback: addbackN4 satisfies the 4-limb val256 addition equation
-- ============================================================================

-- addbackN4_carry is now defined in LoopDefs.lean (moved there to support
-- the double-addback iter definitions).

/-- The first 4 components of addbackN4 satisfy the val256 addition equation:
    val256(un) + val256(v) = val256(aun) + carry * 2^256
    where (aun0, aun1, aun2, aun3, _) = addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3. -/
theorem addbackN4_val256_eq (un0 un1 un2 un3 u4_new v0 v1 v2 v3 : Word) :
    let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
    let carry := addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3
    val256 un0 un1 un2 un3 + val256 v0 v1 v2 v3 =
      val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 + carry.toNat * 2^256 := by
  simp only [addbackN4_carry, se12_0]
  simp only [addbackN4, se12_0]
  exact addback_register_4limb_val256

/-- The low 4 components of addbackN4 are independent of the `u4_new`
    (carry-input) parameter. Useful when bridging a `addbackN4 ... 0 ...` form
    (carry-input-zero, used in the algorithm's pre-addback validation) to
    `addbackN4 ... u4_new ...` form (carry-input-from-mulsub, used in the
    runtime program's actual computation). -/
theorem addbackN4_low_limbs_indep_u4_new
    (un0 un1 un2 un3 u4_new v0 v1 v2 v3 : Word) :
    (addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3).1 =
      (addbackN4 un0 un1 un2 un3 0 v0 v1 v2 v3).1 ∧
    (addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3).2.1 =
      (addbackN4 un0 un1 un2 un3 0 v0 v1 v2 v3).2.1 ∧
    (addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3).2.2.1 =
      (addbackN4 un0 un1 un2 un3 0 v0 v1 v2 v3).2.2.1 ∧
    (addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3).2.2.2.1 =
      (addbackN4 un0 un1 un2 un3 0 v0 v1 v2 v3).2.2.2.1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The 5th component of addbackN4 is u4_new + carry. -/
theorem addbackN4_top_eq (un0 un1 un2 un3 u4_new v0 v1 v2 v3 : Word) :
    let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
    let carry := addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3
    ab.2.2.2.2 = u4_new + carry := by
  simp only [addbackN4, addbackN4_carry]

theorem addbackN4_carry_toNat_le_one (un0 un1 un2 un3 v0 v1 v2 v3 : Word) :
    (addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3).toNat ≤ 1 := by
  unfold addbackN4_carry
  simp only []
  split_ifs <;> decide

theorem addbackN4_carry_eq_one_of_ne_zero
    (un0 un1 un2 un3 v0 v1 v2 v3 : Word)
    (hcarry : addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3 ≠ 0) :
    addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [show (1 : Word).toNat = 1 by decide]
  have hne : (addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3).toNat ≠ 0 := by
    intro hzero
    exact hcarry (BitVec.eq_of_toNat_eq hzero)
  have hle := addbackN4_carry_toNat_le_one un0 un1 un2 un3 v0 v1 v2 v3
  omega

theorem word_sub_toNat_of_le (x y : Word) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  simp only [BitVec.toNat_sub]
  have hx : x.toNat < 2^64 := x.isLt
  have hy : y.toNat < 2^64 := y.isLt
  rw [show 2 ^ 64 - y.toNat + x.toNat = x.toNat - y.toNat + 2 ^ 64 by omega]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem val256_conservation_of_low_eq_and_zero_tops
    {uVal qVal vVal rVal uTop rTop : Nat}
    (huTop : uTop = 0) (hrTop : rTop = 0)
    (hlow : uVal = qVal * vVal + rVal) :
    uVal + uTop * 2^256 = qVal * vVal + rVal + rTop * 2^256 := by
  omega

theorem iterWithDoubleAddback_no_borrow_val256_conservation
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hb : ¬ BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
      q.toNat * EvmWord.val256 v0 v1 v2 v3 +
        EvmWord.val256
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 +
        (uTop - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2).toNat * 2^256 := by
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  have hc3_le : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ uTop.toNat := by
    rw [EvmWord.ult_iff] at hb
    omega
  rw [word_sub_toNat_of_le uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 hc3_le]
  have htop_split : uTop.toNat =
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat +
      (uTop.toNat - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat) := by
    omega
  calc
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
        (EvmWord.val256 u0 u1 u2 u3 +
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat * 2^256) +
          (uTop.toNat - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat) *
            2^256 := by
      nth_rw 1 [htop_split]
      ring
    _ = (EvmWord.val256
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 +
        q.toNat * EvmWord.val256 v0 v1 v2 v3) +
          (uTop.toNat - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat) *
            2^256 := by
      rw [hmulsub]
    _ = q.toNat * EvmWord.val256 v0 v1 v2 v3 +
        EvmWord.val256
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1 +
        (uTop.toNat - (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat) *
          2^256 := by
      ring

end EvmAsm.Evm64
