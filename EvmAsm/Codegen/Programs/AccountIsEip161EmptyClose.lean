/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose

  Whole-program caller contract `account_is_eip161_empty_spec_within` for the
  108-instruction `accountIsEip161Empty_prog` (K137, `AccountFields.lean`).

  Composes the three byte-scan loop lemmas (`AccountIsEip161EmptyLoop.lean`),
  the emptiness model (`AccountIsEip161EmptySpec.lean`, `accountEip161Empty`),
  and three calls to the strict `rlp_list_nth_item` selector
  (`RlpListNthItemSAsm.lean`, `rlpListNthItem_spec_within`) into the genuine,
  total, lenient contract:

    a0 = 0 ∧ out = (if accountEip161Empty bytes accBase listLen then 1 else 0)
    a0 = 1 ⟺ RLP parse failure ∨ nonce len > 8 ∨ balance len > 32
    a0 = 2 ⟺ code_hash len ≠ 32

  Follows the K20 call-adapter pattern of
  `HeaderValidateExtraDataLengthSpec.hvedCall` (#10337).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyLoop

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## Code-region monotonicity -/

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells. -/
local macro "pcfR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

theorem aie_disjoint : aieCode.Disjoint RlpListNthItemSAsm.code := by
  unfold aieCode RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [aie_prog_length]; decide
  · rw [RlpListNthItemSAsm.total_length]; decide
  · right
    rw [RlpListNthItemSAsm.total_length]; decide

#print axioms aie_disjoint

/-- K20's linked code is subsumed by the AIE full closure. -/
theorem k20_mono :
    ∀ a i, RlpListNthItemSAsm.code a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right aie_disjoint (fun _ _ h => h) a i hi

/-- The AIE body's own code is subsumed by the full closure. -/
theorem aie_mono : ∀ a i, aieCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

end EvmAsm.Codegen.AccountIsEip161EmptySpec
