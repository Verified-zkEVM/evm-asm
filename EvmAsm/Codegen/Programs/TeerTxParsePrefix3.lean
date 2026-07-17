/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix3

  PASS 3 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  Continues `TeerTxParsePrefix2` with the remaining building blocks of the
  tx-parse prefix: the MV-shuffle GLUE blocks that re-stage the walk cursor /
  end into the `rlp_walk_next` ABI args between successive walks, the
  authorization-list walk re-init cursor block (instrs 103..109), and every
  remaining post-call parse-failure `BNE` dispatch for the two walk groups.

    * `to`/value walk GROUP (x24 cursor, x25 end): glue 56..59 / 62..64 / …,
      BNEs at 66/71/76/81/86 and the past-`to` BNE at 98;
    * authorization-list walk GROUP (x21 cursor, x22 end): glue 112..115 /
      118..120 / …, BNEs at 117/122/…/162;
    * the re-init cursor block (103..109): cursor = txPtr + inner_off,
      len = txLen - inner_off, staged into a0/a1 for `rlp_walk_init`@110.

  Straight-line glue / re-init blocks are proved over `teerCode` directly (as
  in `TeerBodyDecode`); every `BNE` dispatch is proved over `fullCode` via
  `teer_mono` (mirroring `teer_walknext61_bne_spec`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix2

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## `to`/value walk GROUP — MV-shuffle glue blocks (x24 cursor, x25 end)

    The `to`/value walk re-stages the current cursor in the callee-saved `x24`
    and the (fixed) end pointer in `x25`, restaging both into the `rlp_walk_next`
    ABI args `a0`/`a1` before each advance.  The FIRST glue (instrs 56..59)
    snapshots BOTH the `rlp_walk_init` cursor (into `x24`) and end (into `x25`);
    the subsequent 3-MV glues (62..64, 67..69, 72..74, 77..79, 82..84) refresh
    only the cursor (the end `x25` is untouched). -/

set_option maxRecDepth 8000 in
/-- First `to`-walk glue (instrs 56..59, `teerB + 224 → teerB + 240`): snapshot
    cursor `x24 = a0`, end `x25 = a1`, restage `a0 = x24`, `a1 = x25`. -/
theorem teer_toglue0_spec (v10 v11 v24o v25o : Word) :
    cpsTripleWithin 4 (teerB + 224) (teerB + 240) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25o))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x24 ↦ᵣ v10) ** (.x25 ↦ᵣ v11)) := by
  have h0 := mv_spec_gen_within .x24 .x10 v10 v24o (teerB + 224) (by decide)
  have h1 := mv_spec_gen_within .x25 .x11 v11 v25o (teerB + 228) (by decide)
  have h2 := mv_spec_gen_within .x10 .x24 v10 v10 (teerB + 232) (by decide)
  have h3 := mv_spec_gen_within .x11 .x25 v11 v11 (teerB + 236) (by decide)
  runBlock h0 h1 h2 h3

set_option maxRecDepth 8000 in
/-- 3-MV `to`-walk glue (instrs 62..64, `teerB + 248 → teerB + 260`): refresh
    cursor `x24 = a0`, restage `a0 = x24`, `a1 = x25`. -/
theorem teer_toglue1_spec (v10 v11o v24o v25 : Word) :
    cpsTripleWithin 3 (teerB + 248) (teerB + 260) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ v10) ** (.x25 ↦ᵣ v25)) := by
  have h0 := mv_spec_gen_within .x24 .x10 v10 v24o (teerB + 248) (by decide)
  have h1 := mv_spec_gen_within .x10 .x24 v10 v10 (teerB + 252) (by decide)
  have h2 := mv_spec_gen_within .x11 .x25 v25 v11o (teerB + 256) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV `to`-walk glue (instrs 67..69, `teerB + 268 → teerB + 280`). -/
theorem teer_toglue2_spec (v10 v11o v24o v25 : Word) :
    cpsTripleWithin 3 (teerB + 268) (teerB + 280) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ v10) ** (.x25 ↦ᵣ v25)) := by
  have h0 := mv_spec_gen_within .x24 .x10 v10 v24o (teerB + 268) (by decide)
  have h1 := mv_spec_gen_within .x10 .x24 v10 v10 (teerB + 272) (by decide)
  have h2 := mv_spec_gen_within .x11 .x25 v25 v11o (teerB + 276) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV `to`-walk glue (instrs 72..74, `teerB + 288 → teerB + 300`). -/
theorem teer_toglue3_spec (v10 v11o v24o v25 : Word) :
    cpsTripleWithin 3 (teerB + 288) (teerB + 300) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ v10) ** (.x25 ↦ᵣ v25)) := by
  have h0 := mv_spec_gen_within .x24 .x10 v10 v24o (teerB + 288) (by decide)
  have h1 := mv_spec_gen_within .x10 .x24 v10 v10 (teerB + 292) (by decide)
  have h2 := mv_spec_gen_within .x11 .x25 v25 v11o (teerB + 296) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV `to`-walk glue (instrs 77..79, `teerB + 308 → teerB + 320`). -/
theorem teer_toglue4_spec (v10 v11o v24o v25 : Word) :
    cpsTripleWithin 3 (teerB + 308) (teerB + 320) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ v10) ** (.x25 ↦ᵣ v25)) := by
  have h0 := mv_spec_gen_within .x24 .x10 v10 v24o (teerB + 308) (by decide)
  have h1 := mv_spec_gen_within .x10 .x24 v10 v10 (teerB + 312) (by decide)
  have h2 := mv_spec_gen_within .x11 .x25 v25 v11o (teerB + 316) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV `to`-walk glue (instrs 82..84, `teerB + 328 → teerB + 340`). -/
theorem teer_toglue5_spec (v10 v11o v24o v25 : Word) :
    cpsTripleWithin 3 (teerB + 328) (teerB + 340) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x24 ↦ᵣ v24o) ** (.x25 ↦ᵣ v25))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v25) ** (.x24 ↦ᵣ v10) ** (.x25 ↦ᵣ v25)) := by
  have h0 := mv_spec_gen_within .x24 .x10 v10 v24o (teerB + 328) (by decide)
  have h1 := mv_spec_gen_within .x10 .x24 v10 v10 (teerB + 332) (by decide)
  have h2 := mv_spec_gen_within .x11 .x25 v25 v11o (teerB + 336) (by decide)
  runBlock h0 h1 h2

/-! ## `to`/value walk GROUP — post-call parse-failure BNEs (x11 = a1)

    `bne a1, zero` after each `rlp_walk_next`: TAKEN (`a1 ≠ 0`, a non-advance
    status ⇒ end-of-list / malformed) exits to the far epilogue `teerB + 2856`;
    NOT-TAKEN (`a1 = 0`, item advanced) falls through.  Mirrors
    `teer_walknext61_bne_spec`. -/

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@65 dispatch (instr 66, `teerB + 264`). -/
theorem teer_walknext66_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 264) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 268) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2592 : BitVec 13) a1 (0 : Word) (teerB + 264)
  rw [show (teerB + 264) + signExtend13 (2592 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2592 : BitVec 13) = (2592 : Word) from by decide]; bv_omega,
      show (teerB + 264) + 4 = teerB + 268 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 264) teerProg 66
    (.BNE .x11 .x0 (2592 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@70 dispatch (instr 71, `teerB + 284`). -/
theorem teer_walknext71_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 284) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 288) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2572 : BitVec 13) a1 (0 : Word) (teerB + 284)
  rw [show (teerB + 284) + signExtend13 (2572 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2572 : BitVec 13) = (2572 : Word) from by decide]; bv_omega,
      show (teerB + 284) + 4 = teerB + 288 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 284) teerProg 71
    (.BNE .x11 .x0 (2572 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@75 dispatch (instr 76, `teerB + 304`). -/
theorem teer_walknext76_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 304) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 308) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2552 : BitVec 13) a1 (0 : Word) (teerB + 304)
  rw [show (teerB + 304) + signExtend13 (2552 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2552 : BitVec 13) = (2552 : Word) from by decide]; bv_omega,
      show (teerB + 304) + 4 = teerB + 308 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 304) teerProg 76
    (.BNE .x11 .x0 (2552 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@80 dispatch (instr 81, `teerB + 324`). -/
theorem teer_walknext81_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 324) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 328) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2532 : BitVec 13) a1 (0 : Word) (teerB + 324)
  rw [show (teerB + 324) + signExtend13 (2532 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2532 : BitVec 13) = (2532 : Word) from by decide]; bv_omega,
      show (teerB + 324) + 4 = teerB + 328 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 324) teerProg 81
    (.BNE .x11 .x0 (2532 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- `rlp_walk_next`@85 dispatch (instr 86, `teerB + 344`). -/
theorem teer_walknext86_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 344) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 348) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2512 : BitVec 13) a1 (0 : Word) (teerB + 344)
  rw [show (teerB + 344) + signExtend13 (2512 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2512 : BitVec 13) = (2512 : Word) from by decide]; bv_omega,
      show (teerB + 344) + 4 = teerB + 348 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 344) teerProg 86
    (.BNE .x11 .x0 (2512 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- past-`to` `rlp_walk_next`@97 dispatch (instr 98, `teerB + 392`). -/
theorem teer_walknext98_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 392) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 396) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2464 : BitVec 13) a1 (0 : Word) (teerB + 392)
  rw [show (teerB + 392) + signExtend13 (2464 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2464 : BitVec 13) = (2464 : Word) from by decide]; bv_omega,
      show (teerB + 392) + 4 = teerB + 396 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 392) teerProg 98
    (.BNE .x11 .x0 (2464 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

/-! ## re-init cursor block (instructions 103..109)

    On the `value ≠ 0` fall-through (`teerB + 412`): reload `teer_inner_off`
    into `x6`, recompute the inner-payload cursor `x21 = x8(txPtr) + inner_off`
    and length `x22 = x9(txLen) - inner_off`, and stage them into the
    `rlp_walk_init` args `a0`/`a1`.  Exit `teerB + 440`, the `jal rlp_walk_init`
    at instruction 110.  Structurally identical to `teer_cursor_setup_spec`
    (instrs 47..53) at the re-init PC.  Over `teerCode` (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_reinit_cursor_spec (v8 v9 v5 v6 v10o v11o v21o v22o ioff : Word) :
    cpsTripleWithin 7 (teerB + 412) (teerB + 440) teerCode
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
        (teerInnerOff ↦ₘ ioff))
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x5 ↦ᵣ teerInnerOff) ** (.x6 ↦ᵣ ioff) **
        (.x10 ↦ᵣ (v8 + ioff)) ** (.x11 ↦ᵣ (v9 - ioff)) **
        (.x21 ↦ᵣ (v8 + ioff)) ** (.x22 ↦ᵣ (v9 - ioff)) **
        (teerInnerOff ↦ₘ ioff)) := by
  have h0 := la_materialize_within .x5 v5 (teerB + 412) teerInnerOff (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 412) teerProg 103
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (teerB + 412) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 416) teerProg 104
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (teerB + 412) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h1 := ld_spec_gen_within .x6 .x5 teerInnerOff v6 ioff (0 : BitVec 12) (teerB + 420) (by decide)
  have h2 := add_spec_gen_within .x21 .x8 .x6 v8 ioff v21o (teerB + 424) (by decide)
  have h3 := sub_spec_gen_within .x22 .x9 .x6 v9 ioff v22o (teerB + 428) (by decide)
  have h4 := mv_spec_gen_within .x10 .x21 (v8 + ioff) v10o (teerB + 432) (by decide)
  have h5 := mv_spec_gen_within .x11 .x22 (v9 - ioff) v11o (teerB + 436) (by decide)
  runBlock h0 h1 h2 h3 h4 h5

/-! ## authorization-list walk GROUP — MV-shuffle glue blocks (x21 cursor, x22 end)

    Identical shape to the `to`-walk glue, using the callee-saved `x21` (cursor)
    / `x22` (end).  The FIRST glue (instrs 112..115) snapshots both; the
    subsequent 3-MV glues (118..120, …, 158..160) refresh only the cursor. -/

set_option maxRecDepth 8000 in
/-- First auth-list-walk glue (instrs 112..115, `teerB + 448 → teerB + 464`). -/
theorem teer_alglue0_spec (v10 v11 v21o v22o : Word) :
    cpsTripleWithin 4 (teerB + 448) (teerB + 464) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v11)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 448) (by decide)
  have h1 := mv_spec_gen_within .x22 .x11 v11 v22o (teerB + 452) (by decide)
  have h2 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 456) (by decide)
  have h3 := mv_spec_gen_within .x11 .x22 v11 v11 (teerB + 460) (by decide)
  runBlock h0 h1 h2 h3

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue at `teerB + A → teerB + A + 12`, refreshing cursor
    `x21 = a0` and restaging `a0 = x21`, `a1 = x22`.  Instantiated below at each
    concrete site (118..120, …, 158..160) via `teerProg` membership. -/
theorem teer_alglue1_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 472) (teerB + 484) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 472) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 476) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 480) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 123..125, `teerB + 492 → teerB + 504`). -/
theorem teer_alglue2_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 492) (teerB + 504) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 492) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 496) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 500) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 128..130, `teerB + 512 → teerB + 524`). -/
theorem teer_alglue3_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 512) (teerB + 524) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 512) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 516) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 520) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 133..135, `teerB + 532 → teerB + 544`). -/
theorem teer_alglue4_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 532) (teerB + 544) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 532) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 536) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 540) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 138..140, `teerB + 552 → teerB + 564`). -/
theorem teer_alglue5_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 552) (teerB + 564) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 552) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 556) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 560) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 143..145, `teerB + 572 → teerB + 584`). -/
theorem teer_alglue6_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 572) (teerB + 584) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 572) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 576) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 580) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 148..150, `teerB + 592 → teerB + 604`). -/
theorem teer_alglue7_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 592) (teerB + 604) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 592) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 596) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 600) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 153..155, `teerB + 612 → teerB + 624`). -/
theorem teer_alglue8_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 612) (teerB + 624) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 612) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 616) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 620) (by decide)
  runBlock h0 h1 h2

set_option maxRecDepth 8000 in
/-- 3-MV auth-list-walk glue (instrs 158..160, `teerB + 632 → teerB + 644`). -/
theorem teer_alglue9_spec (v10 v11o v21o v22 : Word) :
    cpsTripleWithin 3 (teerB + 632) (teerB + 644) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11o) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v22) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 632) (by decide)
  have h1 := mv_spec_gen_within .x10 .x21 v10 v10 (teerB + 636) (by decide)
  have h2 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 640) (by decide)
  runBlock h0 h1 h2

/-! ## authorization-list walk GROUP — post-call parse-failure BNEs (x11 = a1)

    `bne a1, zero` after each auth-list `rlp_walk_next`: TAKEN → far epilogue
    `teerB + 2856`; NOT-TAKEN falls through.  Mirrors `teer_walknext61_bne_spec`. -/

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 117, `teerB + 468`). -/
theorem teer_walknext117_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 468) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 472) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2388 : BitVec 13) a1 (0 : Word) (teerB + 468)
  rw [show (teerB + 468) + signExtend13 (2388 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2388 : BitVec 13) = (2388 : Word) from by decide]; bv_omega,
      show (teerB + 468) + 4 = teerB + 472 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 468) teerProg 117
    (.BNE .x11 .x0 (2388 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 122, `teerB + 488`). -/
theorem teer_walknext122_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 488) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 492) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2368 : BitVec 13) a1 (0 : Word) (teerB + 488)
  rw [show (teerB + 488) + signExtend13 (2368 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2368 : BitVec 13) = (2368 : Word) from by decide]; bv_omega,
      show (teerB + 488) + 4 = teerB + 492 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 488) teerProg 122
    (.BNE .x11 .x0 (2368 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 127, `teerB + 508`). -/
theorem teer_walknext127_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 508) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 512) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2348 : BitVec 13) a1 (0 : Word) (teerB + 508)
  rw [show (teerB + 508) + signExtend13 (2348 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2348 : BitVec 13) = (2348 : Word) from by decide]; bv_omega,
      show (teerB + 508) + 4 = teerB + 512 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 508) teerProg 127
    (.BNE .x11 .x0 (2348 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 132, `teerB + 528`). -/
theorem teer_walknext132_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 528) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 532) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2328 : BitVec 13) a1 (0 : Word) (teerB + 528)
  rw [show (teerB + 528) + signExtend13 (2328 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2328 : BitVec 13) = (2328 : Word) from by decide]; bv_omega,
      show (teerB + 528) + 4 = teerB + 532 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 528) teerProg 132
    (.BNE .x11 .x0 (2328 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 137, `teerB + 548`). -/
theorem teer_walknext137_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 548) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 552) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2308 : BitVec 13) a1 (0 : Word) (teerB + 548)
  rw [show (teerB + 548) + signExtend13 (2308 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2308 : BitVec 13) = (2308 : Word) from by decide]; bv_omega,
      show (teerB + 548) + 4 = teerB + 552 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 548) teerProg 137
    (.BNE .x11 .x0 (2308 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 142, `teerB + 568`). -/
theorem teer_walknext142_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 568) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 572) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2288 : BitVec 13) a1 (0 : Word) (teerB + 568)
  rw [show (teerB + 568) + signExtend13 (2288 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2288 : BitVec 13) = (2288 : Word) from by decide]; bv_omega,
      show (teerB + 568) + 4 = teerB + 572 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 568) teerProg 142
    (.BNE .x11 .x0 (2288 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 147, `teerB + 588`). -/
theorem teer_walknext147_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 588) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 592) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2268 : BitVec 13) a1 (0 : Word) (teerB + 588)
  rw [show (teerB + 588) + signExtend13 (2268 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2268 : BitVec 13) = (2268 : Word) from by decide]; bv_omega,
      show (teerB + 588) + 4 = teerB + 592 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 588) teerProg 147
    (.BNE .x11 .x0 (2268 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 152, `teerB + 608`). -/
theorem teer_walknext152_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 608) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 612) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2248 : BitVec 13) a1 (0 : Word) (teerB + 608)
  rw [show (teerB + 608) + signExtend13 (2248 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2248 : BitVec 13) = (2248 : Word) from by decide]; bv_omega,
      show (teerB + 608) + 4 = teerB + 612 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 608) teerProg 152
    (.BNE .x11 .x0 (2248 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 157, `teerB + 628`). -/
theorem teer_walknext157_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 628) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 632) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2228 : BitVec 13) a1 (0 : Word) (teerB + 628)
  rw [show (teerB + 628) + signExtend13 (2228 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2228 : BitVec 13) = (2228 : Word) from by decide]; bv_omega,
      show (teerB + 628) + 4 = teerB + 632 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 628) teerProg 157
    (.BNE .x11 .x0 (2228 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne

set_option maxRecDepth 8000 in
/-- auth-list `rlp_walk_next` dispatch (instr 162, `teerB + 648`). -/
theorem teer_walknext162_bne_spec (a1 : Word) :
    cpsBranchWithin 1 (teerB + 648) fullCode
      ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      (teerB + 2856) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 ≠ (0 : Word)⌝)
      (teerB + 652) ((.x11 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜a1 = (0 : Word)⌝) := by
  have hbne := bne_spec_gen_within .x11 .x0 (2208 : BitVec 13) a1 (0 : Word) (teerB + 648)
  rw [show (teerB + 648) + signExtend13 (2208 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2208 : BitVec 13) = (2208 : Word) from by decide]; bv_omega,
      show (teerB + 648) + 4 = teerB + 652 from by bv_omega] at hbne
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 648) teerProg 162
    (.BNE .x11 .x0 (2208 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code (fun a i h => teer_mono a i (hmem a i h)) hbne


end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
