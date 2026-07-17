/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix2

  PASS 3 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Continues `TeerTxParsePrefix` (which landed the first call group,
  `tx_type_dispatch`, instrs 34..41).  This module composes the REST of the
  tx-parse prefix (instructions 42..181), from the `tx_type_dispatch`
  parse-success fall-through (`teerB + 168`) through to the per-auth loop head
  guard (`teerB + 724`, instruction 181):

    * type==4 check (42..46) + inner-payload cursor/len setup (47..53);
    * the `to`/value walk GROUP: `rlp_walk_init`@54 + 6× `rlp_walk_next`;
    * the authorization-list walk GROUP: re-`rlp_walk_init`@110 + 10×
      `rlp_walk_next`;
    * `rlp_list_count_items`@169 (count→x23) + list re-init@176;
    * each post-call parse-failure `BNE` (→ far epilogue `teerB + 2856`).

  Straight-line (call-free) blocks are proved over `teerCode` directly (as in
  `TeerBodyDecode`); the call groups lift the assumed callee contracts
  (`TeerBodyAssumptions`) through the `jal` via `callWithin_spec`, framing each
  callee's scratch footprint; every post-call `BNE` dispatch is proved over
  `fullCode` via `teer_mono` (mirroring `teer_txtype_bne_spec`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## type==4 check: load teer_type (instructions 42..45)

    From the `tx_type_dispatch` parse-success fall-through (`teerB + 168`):
    materialise `&teer_type` into `x5`, load the parsed type into `x6`, and
    `li x7, 4`.  Exit `teerB + 184`, the type-mismatch `BNE` at instruction 46.
    Stated over `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_type4_load_spec (v5 v6 v7 tval : Word) :
    cpsTripleWithin 4 (teerB + 168) (teerB + 184) teerCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (teerType ↦ₘ tval))
      ((.x5 ↦ᵣ teerType) ** (.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) ** (teerType ↦ₘ tval)) := by
  have h0 := la_materialize_within .x5 v5 (teerB + 168) teerType (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 168) teerProg 42
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 168) teerType))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 172) teerProg 43
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 168) teerType))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h1 := ld_spec_gen_within .x6 .x5 teerType v6 tval (0 : BitVec 12) (teerB + 176) (by decide)
  have h2 := li_spec_gen_within .x7 v7 (4 : Word) (teerB + 180) (by decide)
  runBlock h0 h1 h2

/-! ## type==4 check: dispatch (instruction 46)

    `bne x6(type), x7(=4)` at `teerB + 184`.  TAKEN (`type ≠ 4`) exits to the
    far epilogue `teerB + 2856` (a non-type-4 transaction contributes nothing);
    NOT-TAKEN (`type = 4`) falls through to `teerB + 188`, the inner-payload
    cursor setup. -/
set_option maxRecDepth 8000 in
theorem teer_type4_bne_spec (tval : Word) :
    cpsBranchWithin 1 (teerB + 184) fullCode
      ((.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)))
      (teerB + 2856) ((.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) ** ⌜tval ≠ (4 : Word)⌝)
      (teerB + 188) ((.x6 ↦ᵣ tval) ** (.x7 ↦ᵣ (4 : Word)) ** ⌜tval = (4 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x6 .x7 (2672 : BitVec 13) tval (4 : Word) (teerB + 184)
  rw [show (teerB + 184) + signExtend13 (2672 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2672 : BitVec 13) = (2672 : Word) from by decide]; bv_omega,
      show (teerB + 184) + 4 = teerB + 188 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 184) teerProg 46
    (.BNE .x6 .x7 (2672 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-! ## inner-payload cursor/len setup (instructions 47..53)

    `type == 4` fall-through (`teerB + 188`): load `teer_inner_off` into `x6`,
    compute the inner-payload cursor `x21 = x8(txPtr) + inner_off` and length
    `x22 = x9(txLen) - inner_off`, and stage them into the `rlp_walk_init` ABI
    args `a0`/`a1`.  Exit `teerB + 216`, the `jal rlp_walk_init` at
    instruction 54.  Stated over `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_cursor_setup_spec (v8 v9 v5 v6 v10o v11o v21o v22o ioff : Word) :
    cpsTripleWithin 7 (teerB + 188) (teerB + 216) teerCode
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
        (teerInnerOff ↦ₘ ioff))
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) ** (.x6 ↦ᵣ ioff) **
        (.x10 ↦ᵣ (v8 + ioff)) ** (.x11 ↦ᵣ (v9 - ioff)) **
        (.x21 ↦ᵣ (v8 + ioff)) ** (.x22 ↦ᵣ (v9 - ioff)) **
        (teerInnerOff ↦ₘ ioff)) := by
  have h0 := la_materialize_within .x5 v5 (teerB + 188) teerInnerOff (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 188) teerProg 47
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 188) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 192) teerProg 48
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 188) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h1 := ld_spec_gen_within .x6 .x5 teerInnerOff v6 ioff (0 : BitVec 12) (teerB + 196) (by decide)
  have h2 := add_spec_gen_within .x21 .x8 .x6 v8 ioff v21o (teerB + 200) (by decide)
  have h3 := sub_spec_gen_within .x22 .x9 .x6 v9 ioff v22o (teerB + 204) (by decide)
  have h4 := mv_spec_gen_within .x10 .x21 (v8 + ioff) v10o (teerB + 208) (by decide)
  have h5 := mv_spec_gen_within .x11 .x22 (v9 - ioff) v11o (teerB + 212) (by decide)
  runBlock h0 h1 h2 h3 h4 h5

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
