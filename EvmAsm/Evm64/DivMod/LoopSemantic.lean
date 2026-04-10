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

/-- Extract the 4-limb carry-out from addbackN4's intermediate computation.
    This is the carry out of the 4th limb (aco3), before the u4_new addition. -/
def addbackN4_carry (un0 un1 un2 un3 v0 v1 v2 v3 : Word) : Word :=
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0
  let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0
  let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1
  let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1
  let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2
  let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2
  let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3
  let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  ac1_3 ||| ac2_3

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
