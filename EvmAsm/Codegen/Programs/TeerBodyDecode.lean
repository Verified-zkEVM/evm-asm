/-
  EvmAsm.Codegen.Programs.TeerBodyDecode

  PASS 2 of the `tx_eip7702_existing_authority_refund` Fn.Spec development
  (continues `TeerExistingAuthorityRefundSpec`, which established the model, the
  `fullCode` closure + 7 callee monos, the 4 assumed string-only callee
  contracts, and the prologue through the BAL-ptr guard `beq`).

  This module maps the AUTH-ITERATION body (instructions 34..744, the bulk) and
  lands the call-free STRUCTURAL blocks that establish the framing pattern for
  the two entry points a later pass composes the callee triples around:

    * `teer_body_entry_spec`    — the tx-type-dispatch argument setup (instrs
                                  34..39), the first block after the BAL guard;
    * `teer_loop_init_spec`     — the per-auth loop counter/cursor init
                                  (instrs 178..180);
    * `teer_loop_head_spec`     — the per-auth loop guard `beq i, count`
                                  (instr 181), the per-iteration dispatch;
    * `teer_iter_body_entry_spec` — the first-action arg setup of one iteration
                                  (instrs 182..183), parameterised by the list
                                  cursor / end so it is reusable per iteration;
    * a handful of decidable LAYOUT facts pinning the loop back-edge and the
      epilogue boundary with their concrete immediates.

  The callee-laden interior of the prefix and the per-auth body is deferred:
  the `fullCode` callees (`tx_type_dispatch`, `rlp_list_count_items`,
  `eip7702_authorization_recover_address`, `bal_find_account_by_address`,
  `bal_account_nonstorage_finals`, `code_at_header_state_root`,
  `account_at_header_state_root`) do not yet have proven Program-level
  `cpsTripleWithin` specs on this branch (only the `_mono` image-subsumption
  lemmas exist), and the four string-only callees enter via the assumed
  contracts.  Composing the straight-line-with-calls sequence is the NEXT pass.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.

  ## Decode control-flow map (instruction indices; PC = teerB + 4·index)

  The concrete `decode : txBytes → balBytes → chainId → bai →
  (rolledBack, List TeerAuthOutcome)` that `teerAppliedOf` is instantiated with
  is exactly what the body computes.  Its control flow:

  ### tx-parse prefix (instrs 34..181)
    34..39  : arg setup for `tx_type_dispatch` (a0=txPtr, a1=txLen,
              a2=&teer_type, a3=&teer_inner_off).                [this module]
    40      : `jal tx_type_dispatch`.
    41      : `bne a0,0` → far epilogue (parse fail ⇒ rolledBack path).
    42..46  : load teer_type; require type == 4 else → epilogue.
    47..54  : cursor = txPtr+inner_off, len = txLen-inner_off; `jal rlp_walk_init`.
    55      : `bne a2,0` → epilogue.
    56..96  : 6× `jal rlp_walk_next` walking to the `to` field; capture the
              recipient content ptr/len (teer_recipient_ptr / _len).
    97..98  : `jal rlp_walk_next` past `to`; `bne` → epilogue.
    99..102 : teer_value_nonzero = (value len > 0).
    103..111: re-init the inner-payload walk (`jal rlp_walk_init`).
    112..162: 10× `jal rlp_walk_next` to the authorization_list field.
    163..170: auth-list content ptr/len; `jal rlp_list_count_items`
              (teer_auth_count); `bne a0,0` → epilogue.
    171..177: load teer_auth_count → x23; `jal rlp_walk_init` over the list;
              `bne a2,0` → epilogue.
    178..180: x21 = list cursor, x22 = list end, x24 = i = 0.       [this module]
    181     : `beq i, count` → loop-EXIT (epilogue) / fall to loop body.
                                                                    [this module]

  ### per-auth iteration (instrs 182..713), back-edge at 713 → head 181
    182..183: a0 = list cursor, a1 = list end.                      [this module]
    184..190: `jal rlp_walk_next` (next auth tuple); advance x21; tuple ptr x25,
              tuple len @sp+136.
    191..192: `jal rlp_walk_init` over the tuple; `bne` → epilogue.
    193..206: field 1 chain_id: `jal rlp_walk_next` + `jal rlp_content_to_u64`;
              if chain_id≠0 and ≠ our chain id (a4=x20) ⇒ skip auth (→ i++).
    207..214: field 2 address (delegation target): require len==20 else skip;
              target content ptr → x27.
    215..227: field 3 nonce: `jal rlp_walk_next` + `jal rlp_content_to_u64`;
              nonce==2^64-1 ⇒ skip; store nonce @sp+144.
    228..235: `jal eip7702_authorization_recover_address` → teer_authority;
              recover fail ⇒ skip auth.
    236..277: PRIOR-set scan: reset teer_prior_count / teer_prior_set_flag;
              loop over teer_success_table[0..success_count) byte-comparing the
              recovered authority; on a hit bump teer_prior_count and, if that
              row wrote a non-NULL indicator, set teer_prior_set_flag.
    281..297: `jal bal_find_account_by_address`; `jal bal_account_nonstorage_finals`.
    299..317: teer_acct_absent from the block-access is_insert record.
    319..461: pre-state delegation inference — two `code_at_header_state_root`
              paths (delegation-marker `0xef 0x01 0x00` byte check) and an
              `account_at_header_state_root` path; sets teer_acct_absent /
              teer_rolled_back on the witnessed-absent branches; instr 461 is a
              far `jal` skip-trampoline to the loop continuation (i++).
    462..500: `jal bal_account_nonce_before_index` + `account_at_header_state_root`
              pre-state nonce/delegation resolution.
    505..518: byte-compare authority vs bv_stx_sender_addr (written_accounts
              seed); adjust the prior-write count.
    519..533: prior-count / finals bookkeeping (teer_finals rows 40/48).
    534..541: teer_rolled_back set when the BAL nonce advance is missing
              (`bltu bai, finals[48]`).
    542..605: NEW_ACCOUNT accumulation: iff teer_prior_count==0 and
              teer_acct_absent≠0 add teerNewAccount (`lui 45; addiw -720`) to the
              state accumulator x26; else re-derive is_insert vs sender.
    566..605: ACCOUNT_WRITE / recipient bookkeeping; teer_value_nonzero +
              recipient-address compares.
    589..596: teer_regular_refund += teerAccountWrite (`lui 2; addiw -192`).
    597..660: AUTH_BASE decision: OR-reduce the 20 target bytes (net-new
              indicator), teer_prior_set_flag, pre-state delegation
              (`code_at_header_state_root` at 636, `bal_account_nonce_before_index`
              at 671); iff net-new add teerAuthBase (`lui 9; addiw -1674`) to x26.
    677..846: record success: append the authority (+ set flag/nonce) into
              teer_success_table, bump teer_success_count.
    847     : i = i + 1.
    848(=713 index): `jal x0, -2128` back-edge → loop head (instr 181).

  ### epilogue (instrs 714..744), entry teerB + 2856
    714     : a0 = x26 (would-be state accumulator).
    715..723: a1 = teer_regular_refund; publish teer_wouldbe_state /
              teer_wouldbe_regular.
    724..727: `beq teer_rolled_back, 0` skip the zeroing.
    728..729: rolled back ⇒ a0 = a1 = 0 (APPLIED = `teerAppliedState true _`).
    730..744: restore ra/s0..s11/a5, `addi sp,+160`, `jalr` return.

  The APPLIED return (post rolled-back zeroing) is `teerAppliedState rolledBack
  auths`; the would-be fold is published separately — exactly the model in
  `TeerExistingAuthorityRefundSpec`.
-/

import EvmAsm.Codegen.Programs.TeerExistingAuthorityRefundSpec

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64

/-! ### Body scratch globals used by the entry block -/

/-- Guest `.bss` cell holding the parsed EIP-2718 transaction type. -/
abbrev teerType : Word := (GuestAddrs.teer_type : Word)
/-- Guest `.bss` cell holding the type-4 inner-payload byte offset. -/
abbrev teerInnerOff : Word := (GuestAddrs.teer_inner_off : Word)

/-! ## Layout facts

    Decidable checks pinning the per-auth loop back-edge and the epilogue
    boundary with their concrete immediates — machine-checked confirmation of
    the control-flow map above. -/

set_option maxRecDepth 8000 in
/-- The per-auth loop GUARD: `beq x24(i), x23(count)` lives at instruction 181
    (PC `teerB + 724`) in `teerCode`. -/
theorem teerProg_loop_head :
    ∀ a i, CodeReq.singleton (teerB + 724) (Instr.BEQ .x24 .x23 (2132 : BitVec 13)) a = some i →
      teerCode a = some i :=
  CodeReq.ofProg_mem_at teerB (teerB + 724) teerProg 181
    (Instr.BEQ .x24 .x23 (2132 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)

set_option maxRecDepth 8000 in
/-- The per-auth loop BACK-EDGE: `jal x0, -2128` at instruction 713 (PC
    `teerB + 2852`), targeting the loop head at `teerB + 724`. -/
theorem teerProg_loop_backedge :
    ∀ a i, CodeReq.singleton (teerB + 2852) (Instr.JAL .x0 (-2128 : BitVec 21)) a = some i →
      teerCode a = some i :=
  CodeReq.ofProg_mem_at teerB (teerB + 2852) teerProg 713
    (Instr.JAL .x0 (-2128 : BitVec 21))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)

set_option maxRecDepth 8000 in
/-- The EPILOGUE entry: `mv a0, x26` (APPLIED state = would-be accumulator) at
    instruction 714 (PC `teerB + 2856`), the far target of both the BAL-ptr
    guard and every parse-failure `bne`. -/
theorem teerProg_epilogue_entry :
    ∀ a i, CodeReq.singleton (teerB + 2856) (Instr.MV .x10 .x26) a = some i →
      teerCode a = some i :=
  CodeReq.ofProg_mem_at teerB (teerB + 2856) teerProg 714 (Instr.MV .x10 .x26)
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)

set_option maxRecDepth 8000 in
/-- The RETURN: `jalr x0, x1, 0` at instruction 744 (the last instruction, PC
    `teerB + 2976`). -/
theorem teerProg_ret :
    ∀ a i, CodeReq.singleton (teerB + 2976) (Instr.JALR .x0 .x1 (0 : BitVec 12)) a = some i →
      teerCode a = some i :=
  CodeReq.ofProg_mem_at teerB (teerB + 2976) teerProg 744 (Instr.JALR .x0 .x1 (0 : BitVec 12))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)

/-! ## tx-parse prefix: body entry (instructions 34..39)

    From the body entry PC `teerB + 136` (the BAL-ptr guard's not-taken exit),
    set up the four `tx_type_dispatch` arguments: `a0 = x8` (tx ptr, saved from
    the ABI a0), `a1 = x9` (tx len), `a2 = &teer_type`, `a3 = &teer_inner_off`.
    Two `mv` + two `la`; exit `teerB + 160`, the `jal tx_type_dispatch` at
    instruction 40.  Stated over `teerCode` directly (call-free). -/
set_option maxRecDepth 8000 in
theorem teer_body_entry_spec (v8 v9 v10o v11o v12o v13o : Word) :
    cpsTripleWithin 6 (teerB + 136) (teerB + 160) teerCode
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o) **
        (.x12 ↦ᵣ v12o) ** (.x13 ↦ᵣ v13o))
      ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v8) ** (.x11 ↦ᵣ v9) **
        (.x12 ↦ᵣ teerType) ** (.x13 ↦ᵣ teerInnerOff)) := by
  have h0 := mv_spec_gen_within .x10 .x8 v8 v10o (teerB + 136) (by decide)
  have h1 := mv_spec_gen_within .x11 .x9 v9 v11o (teerB + 140) (by decide)
  have h2 := la_materialize_within .x12 v12o (teerB + 144) teerType (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 144) teerProg 36
      (.AUIPC .x12 (EvmAsm.Rv64.laHi (teerB + 144) teerType))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 148) teerProg 37
      (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (teerB + 144) teerType))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  have h3 := la_materialize_within .x13 v13o (teerB + 152) teerInnerOff (by decide) (by decide)
    (CodeReq.ofProg_mem_at teerB (teerB + 152) teerProg 38
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (teerB + 152) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
    (CodeReq.ofProg_mem_at teerB (teerB + 156) teerProg 39
      (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (teerB + 152) teerInnerOff))
      (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide))
  runBlock h0 h1 h2 h3

/-! ## per-auth loop: counter / cursor init (instructions 178..180)

    After the authorization-list `rlp_walk_init` returns (`a0` = list cursor,
    `a1` = list end), stash the cursor/end in the callee-saved `x21`/`x22` and
    zero the iteration counter `x24 = i`.  Exit `teerB + 724`, the loop guard
    `beq` at instruction 181. -/
set_option maxRecDepth 8000 in
theorem teer_loop_init_spec (v10 v11 v21o v22o v24o : Word) :
    cpsTripleWithin 3 (teerB + 712) (teerB + 724) teerCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o) **
        (.x24 ↦ᵣ v24o))
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v10) ** (.x22 ↦ᵣ v11) **
        (.x24 ↦ᵣ (0 : Word))) := by
  have h0 := mv_spec_gen_within .x21 .x10 v10 v21o (teerB + 712) (by decide)
  have h1 := mv_spec_gen_within .x22 .x11 v11 v22o (teerB + 716) (by decide)
  have h2 := li_spec_gen_within .x24 v24o (0 : Word) (teerB + 720) (by decide)
  runBlock h0 h1 h2

/-! ## per-auth loop: guard (instruction 181)

    `beq x24(i), x23(count)`.  TAKEN (`i = count`) exits the loop to the
    epilogue at `teerB + 2856`; NOT-TAKEN (`i ≠ count`) falls to the iteration
    body at `teerB + 728`.  This is the per-iteration dispatch — the entry of
    the first (and every) authorization iteration, parameterised by the current
    index `i` and the authorization count. -/
set_option maxRecDepth 8000 in
theorem teer_loop_head_spec (i cnt : Word) :
    cpsBranchWithin 1 (teerB + 724) teerCode
      ((.x24 ↦ᵣ i) ** (.x23 ↦ᵣ cnt))
      (teerB + 2856) ((.x24 ↦ᵣ i) ** (.x23 ↦ᵣ cnt) ** ⌜i = cnt⌝)
      (teerB + 728) ((.x24 ↦ᵣ i) ** (.x23 ↦ᵣ cnt) ** ⌜i ≠ cnt⌝) := by
  have hbeq := beq_spec_gen_within .x24 .x23 (2132 : BitVec 13) i cnt (teerB + 724)
  rw [show (teerB + 724) + signExtend13 (2132 : BitVec 13) = teerB + 2856 from by
        rw [show signExtend13 (2132 : BitVec 13) = (2132 : Word) from by decide]; bv_omega,
      show (teerB + 724) + 4 = teerB + 728 from by bv_omega] at hbeq
  have hmem := CodeReq.ofProg_mem_at teerB (teerB + 724) teerProg 181
    (.BEQ .x24 .x23 (2132 : BitVec 13))
    (by bv_omega) (by rw [teer_length]; decide) (by decide) (by rw [teer_length]; decide)
  exact cpsBranchWithin_extend_code hmem hbeq

/-! ## per-auth iteration: body entry (instructions 182..183)

    The first action of one iteration: load the list cursor (`x21`) and end
    (`x22`) into the ABI argument registers for the tuple-fetch
    `jal rlp_walk_next` at instruction 184.  Parameterised by the cursor / end,
    so it is the reusable per-iteration head-of-body block.  Exit `teerB + 736`. -/
set_option maxRecDepth 8000 in
theorem teer_iter_body_entry_spec (v21 v22 v10o v11o : Word) :
    cpsTripleWithin 2 (teerB + 728) (teerB + 736) teerCode
      ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x10 ↦ᵣ v10o) ** (.x11 ↦ᵣ v11o))
      ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x10 ↦ᵣ v21) ** (.x11 ↦ᵣ v22)) := by
  have h0 := mv_spec_gen_within .x10 .x21 v21 v10o (teerB + 728) (by decide)
  have h1 := mv_spec_gen_within .x11 .x22 v22 v11o (teerB + 732) (by decide)
  runBlock h0 h1

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
