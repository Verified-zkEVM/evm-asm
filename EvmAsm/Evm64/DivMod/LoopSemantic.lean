/-
  EvmAsm.Evm64.DivMod.LoopSemantic

  Semantic bridge: connect the mulsubN4/addbackN4 computation definitions
  (from LoopDefs.lean) to the val256 Euclidean equations (from EvmWordArith).

  These theorems are pure Nat-level facts about the Word computations,
  independent of separation logic. They form the link between the
  loop body cpsTriple specs and the final EvmWord.div/mod correctness.
-/

import EvmAsm.Evm64.DivMod.LoopDefs
import EvmAsm.Evm64.EvmWordArith.DivMulSubCarry
import EvmAsm.Evm64.EvmWordArith.DivAddbackCarry

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

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
  have hsig : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  simp only [mulsubN4, hsig]
  exact mulsub_register_4limb_val256 q v0 v1 v2 v3 u0 u1 u2 u3

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
  have hsig : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  simp only [addbackN4_carry, hsig]
  simp only [addbackN4, hsig]
  exact addback_register_4limb_val256 v0 v1 v2 v3 un0 un1 un2 un3

/-- The 5th component of addbackN4 is u4_new + carry. -/
theorem addbackN4_top_eq (un0 un1 un2 un3 u4_new v0 v1 v2 v3 : Word) :
    let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
    let carry := addbackN4_carry un0 un1 un2 un3 v0 v1 v2 v3
    ab.2.2.2.2 = u4_new + carry := by
  simp only [addbackN4, addbackN4_carry]

end EvmAsm.Evm64
