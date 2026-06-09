/-
  EvmAsm.Codegen.Programs.BlockVerdictDispatchTx

  `dispatch_tx_runtime_code`: the contract-recipient runtime gas-measurement tail
  extracted from `block_verdict` (BlockVerdict.lean, the former inline
  `.Lbv_contract_dispatch` block) into a reusable callable so the multi-transaction
  dispatch loop (evm-asm-fhsxz.2.4.2.57.11.6.2.2.2) can measure each transaction's
  runtime gas the same way the single-transaction path does.

  The body is a faithful lift of the inline contract-dispatch sequence: it stages
  the recipient's bytecode + the BAL recipient storage preload through
  `stage_runtime_payload_code`, runs the callable runtime dispatcher, and reads the
  resulting `gas_left` (evm_env[568]) and calldata floor. The only changes versus
  the inline form are (1) the witness-state ptr/len and the context-record ptr are
  passed in registers instead of read from the block_verdict input frame (`s0`), and
  (2) every conservative bail (`.Lbv_after_tx_gas_precharge` in the inline form)
  becomes a non-zero status return, while the success fall-through returns the gas
  result. The single-transaction call site stores the result into the existing
  `bv_runtime_*` cells exactly as before, so the verdict is byte-identical.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## dispatch_tx_runtime_code

    Measure one contract-recipient transaction's runtime gas by staging its
    bytecode + recipient storage preload and running the callable runtime
    dispatcher. Reaches the dispatcher only when execution is exact (the recipient
    code is self-contained — own storage only, no un-staged state); any miss or
    unsupported shape returns a non-zero status so the caller stays conservative
    (leaves `bvgr_runtime_count` short of the transaction count).

    Calling convention:
      a0 = context record ptr (192-byte simple_transfer_tx_context /
           multi_tx_nth_context layout; recipient address at +72)
      a1 = witness.state ptr   (block_verdict input frame +80)
      a2 = witness.state len   (block_verdict input frame +88)

    Reads the block-global data labels populated by block_verdict before any
    dispatch: `sv_this_rlp`/`sv_this_rlp_len`, `svf_codes_ptr`/`svf_codes_len`,
    `bv_bal_start`/`bv_bal_len`, `bv_exec_p`, plus the `bvcd_*` scratch cells,
    `cahsr_*`, `sahsr_u256`, `bv_runtime_payload`, `runtime_dispatcher_input_ptr`,
    `evm_env`, `runtime_tx_calldata_floor`.

    Returns:
      a0 = status: 0 = supported, gas measured; non-zero = unsupported / lookup
           miss / not self-contained (caller should stay conservative)
      a1 = gas_left (evm_env[568]) on status 0
      a2 = calldata_floor (runtime_tx_calldata_floor) on status 0

    Preserves the caller's s0..s3 (block_verdict holds its input frame in s0). -/
/-! ## seed_callee_storage (bmvmx.1.6.4.2.b)

    Enumerate EVERY non-recipient BAL account's storage and seed it into the
    persistent exec log (via `callee_seed_table` / `callee_seed_count`, consumed by
    the callable dispatcher's inert seed loop) so a nested CALLEE's SLOAD reads its
    witness value instead of cold 0. Mirrors `dispatch_tx_runtime_code`'s recipient
    slot-loop, wrapped in a BAL-account loop, keyed per account on the callee
    exec-log key (`bal_addr_to_exec_log_key`, LE stack-word — the recipient keys BE
    and is handled separately by the existing recipient preload).

    Calling convention:
      a0 = witness.state ptr   a1 = witness.state len   a2 = recipient 20-byte addr ptr
    Reads globals `bv_bal_start`/`bv_bal_len`, `sv_this_rlp`/`sv_this_rlp_len`.
    Writes `callee_seed_count` + `callee_seed_table` (count × 96 B: addrHash, key,
    value). Caps at 128 entries (table size); preserves s0..s3. A seeded slot has
    original==current==value (no net change), matching the recipient preload. -/
def seedCalleeStorageFunction : String :=
  "seed_callee_storage:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                    # witness ptr\n" ++
  "  mv s1, a1                    # witness len\n" ++
  "  mv s2, a2                    # recipient 20B addr ptr\n" ++
  "  la t0, callee_seed_count; sd zero, 0(t0)\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0); la a2, csce_acct_n\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lscs_done                # BAL parse error -> seed nothing (conservative)\n" ++
  "  la t0, csce_acct_i; sd zero, 0(t0)\n" ++
  ".Lscs_acct_loop:\n" ++
  "  la t0, csce_acct_i; ld t1, 0(t0); la t2, csce_acct_n; ld t3, 0(t2); beq t1, t3, .Lscs_done\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la t0, csce_acct_i; ld a2, 0(t0); la a3, csce_aoff; la a4, csce_alen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lscs_acct_next\n" ++
  "  la t0, bv_bal_start; ld t1, 0(t0); la t0, csce_aoff; ld t2, 0(t0); add s3, t1, t2   # s3 = AccountChanges ptr\n" ++
  "  mv a0, s3; la t0, csce_alen; ld a1, 0(t0); li a2, 0; la a3, csce_doff; la a4, csce_dlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lscs_acct_next\n" ++
  "  la t0, csce_dlen; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lscs_acct_next   # item0 not a 20B address\n" ++
  "  la t0, csce_doff; ld t1, 0(t0); add t1, s3, t1; la t0, csce_addrp; sd t1, 0(t0)   # addr ptr (BE)\n" ++
  -- Skip the recipient (already preloaded BE by dispatch_tx_runtime_code).
  "  li t3, 0\n" ++
  ".Lscs_rcmp:\n" ++
  "  li t4, 20; beq t3, t4, .Lscs_acct_next       # 20/20 equal -> recipient -> skip\n" ++
  "  la t0, csce_addrp; ld t5, 0(t0); add t5, t5, t3; lbu t5, 0(t5)\n" ++
  "  add t6, s2, t3; lbu t6, 0(t6)\n" ++
  "  bne t5, t6, .Lscs_not_recip\n" ++
  "  addi t3, t3, 1; j .Lscs_rcmp\n" ++
  ".Lscs_not_recip:\n" ++
  "  la t0, csce_addrp; ld a0, 0(t0); la a1, csce_addrkey\n" ++
  "  jal ra, bal_addr_to_exec_log_key                # csce_addrkey = LE callee exec-log key\n" ++
  "  mv a0, s3; la t0, csce_alen; ld a1, 0(t0); la a2, csce_keys\n" ++
  "  jal ra, bal_recipient_storage_keys              # csce_keys[] (own buffer, 128 cap)\n" ++
  "  la t0, csce_key_n; sd a0, 0(t0)\n" ++
  "  la t0, csce_key_i; sd zero, 0(t0)\n" ++
  ".Lscs_slot_loop:\n" ++
  "  la t0, csce_key_i; ld t1, 0(t0); la t2, csce_key_n; ld t3, 0(t2); beq t1, t3, .Lscs_acct_next\n" ++
  "  la t0, callee_seed_count; ld t2, 0(t0); li t3, 128; bgeu t2, t3, .Lscs_done   # table cap\n" ++
  "  slli t4, t1, 5; la t5, csce_keys; add a3, t5, t4   # slot key ptr\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  la t0, csce_addrp; ld a2, 0(t0)\n" ++
  "  mv a4, s0; mv a5, s1; mv a6, s0; mv a7, s1\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  li t2, 5; beq a0, t2, .Lscs_slot_vzero\n" ++
  "  bnez a0, .Lscs_slot_next                        # lookup error -> skip this slot\n" ++
  -- entry ptr = callee_seed_table + count*96
  "  la t0, callee_seed_count; ld t1, 0(t0); slli t2, t1, 6; slli t3, t1, 5; add t2, t2, t3\n" ++
  "  la t4, callee_seed_table; add t4, t4, t2\n" ++
  "  la t5, csce_addrkey\n" ++
  "  ld t6, 0(t5); sd t6, 0(t4); ld t6, 8(t5); sd t6, 8(t4); ld t6, 16(t5); sd t6, 16(t4); ld t6, 24(t5); sd t6, 24(t4)\n" ++
  "  la t0, csce_key_i; ld t1, 0(t0); slli t2, t1, 5; la t5, csce_keys; add t5, t5, t2\n" ++
  "  ld t6, 0(t5); sd t6, 32(t4); ld t6, 8(t5); sd t6, 40(t4); ld t6, 16(t5); sd t6, 48(t4); ld t6, 24(t5); sd t6, 56(t4)\n" ++
  "  la t5, sahsr_u256\n" ++
  "  ld t6, 0(t5); sd t6, 64(t4); ld t6, 8(t5); sd t6, 72(t4); ld t6, 16(t5); sd t6, 80(t4); ld t6, 24(t5); sd t6, 88(t4)\n" ++
  "  j .Lscs_slot_commit\n" ++
  ".Lscs_slot_vzero:\n" ++
  "  la t0, callee_seed_count; ld t1, 0(t0); slli t2, t1, 6; slli t3, t1, 5; add t2, t2, t3\n" ++
  "  la t4, callee_seed_table; add t4, t4, t2\n" ++
  "  la t5, csce_addrkey\n" ++
  "  ld t6, 0(t5); sd t6, 0(t4); ld t6, 8(t5); sd t6, 8(t4); ld t6, 16(t5); sd t6, 16(t4); ld t6, 24(t5); sd t6, 24(t4)\n" ++
  "  la t0, csce_key_i; ld t1, 0(t0); slli t2, t1, 5; la t5, csce_keys; add t5, t5, t2\n" ++
  "  ld t6, 0(t5); sd t6, 32(t4); ld t6, 8(t5); sd t6, 40(t4); ld t6, 16(t5); sd t6, 48(t4); ld t6, 24(t5); sd t6, 56(t4)\n" ++
  "  sd zero, 64(t4); sd zero, 72(t4); sd zero, 80(t4); sd zero, 88(t4)\n" ++
  ".Lscs_slot_commit:\n" ++
  "  la t0, callee_seed_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lscs_slot_next:\n" ++
  "  la t0, csce_key_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lscs_slot_loop\n" ++
  ".Lscs_acct_next:\n" ++
  "  la t0, csce_acct_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lscs_acct_loop\n" ++
  ".Lscs_done:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def dispatchTxRuntimeCodeFunction : String :=
  "dispatch_tx_runtime_code:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a1                    # witness.state ptr\n" ++
  "  mv s1, a2                    # witness.state len\n" ++
  "  mv s2, a0                    # context record ptr\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72\n" ++
  "  mv a3, s0; mv a4, s1\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add a0, t1, t3\n" ++
  "  la t2, cahsr_code_length; ld a1, 0(t2)\n" ++
  "  la t0, bvcd_code_ptr; sd a0, 0(t0); la t0, bvcd_code_len; sd a1, 0(t0)\n" ++
  "  jal ra, bytecode_is_self_contained\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72; la a3, bvcd_acct_ptr; la a4, bvcd_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  li t0, 2; beq a0, t0, .Ldtrc_unsupported\n" ++
  "  bnez a0, .Ldtrc_zero_storage\n" ++
  "  la t0, bvcd_acct_ptr; ld a0, 0(t0); la t0, bvcd_acct_len; ld a1, 0(t0); la a2, bvcd_keys\n" ++
  "  jal ra, bal_recipient_storage_keys\n" ++
  "  la t0, bvcd_key_count; sd a0, 0(t0); j .Ldtrc_read_storage\n" ++
  ".Ldtrc_zero_storage:\n" ++
  "  la t0, bvcd_key_count; sd zero, 0(t0)\n" ++
  ".Ldtrc_read_storage:\n" ++
  "  la t0, bvcd_i; sd zero, 0(t0)\n" ++
  ".Ldtrc_sloop:\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); la t2, bvcd_key_count; ld t3, 0(t2); beq t1, t3, .Ldtrc_stage\n" ++
  "  slli t4, t1, 5; la t5, bvcd_keys; add a3, t5, t4\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72\n" ++
  "  mv a4, s0; mv a5, s1; mv a6, s0; mv a7, s1\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 6; la t3, bvcd_preload; add t4, t3, t2\n" ++
  "  slli t2, t1, 5; la t3, bvcd_keys; add t5, t3, t2\n" ++
  "  li t6, 0\n" ++
  ".Ldtrc_kcopy:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_kdone\n" ++
  "  add t2, t5, t6; lbu t3, 0(t2); add t2, t4, t6; sb t3, 0(t2); addi t6, t6, 1; j .Ldtrc_kcopy\n" ++
  ".Ldtrc_kdone:\n" ++
  "  li t2, 5; beq a0, t2, .Ldtrc_vzero\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  "  la t5, sahsr_u256; li t6, 0\n" ++
  ".Ldtrc_vcopy:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_vdone\n" ++
  "  add t2, t5, t6; lbu t3, 0(t2); add t2, t4, t6; addi t2, t2, 32; sb t3, 0(t2); addi t6, t6, 1; j .Ldtrc_vcopy\n" ++
  ".Ldtrc_vzero:\n" ++
  "  li t6, 0\n" ++
  ".Ldtrc_vzloop:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_vdone\n" ++
  "  add t2, t4, t6; addi t2, t2, 32; sb zero, 0(t2); addi t6, t6, 1; j .Ldtrc_vzloop\n" ++
  ".Ldtrc_vdone:\n" ++
  -- fhsxz.2.4.2.57.11.6.3.2 cross-tx threading: if a prior tx in this block committed a
  -- value for (recipient, slotKey), stage that committed value as this slot's preload
  -- (original==current) instead of the block-pre witness value, so this tx's SSTORE gas/
  -- refund uses the in-block committed original. bv_mtx_committed_count is 0 for tx0 /
  -- single-tx / independent blocks -> no match -> byte-identical. Recipient key = ctx+72
  -- (20B, zero-padded to 32) — the same re-keying the snapshot uses.
  "  la t0, bv_mtx_committed_count; ld a3, 0(t0); beqz a3, .Ldtrc_nothread\n" ++
  "  la t0, dtrc_recipkey; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  addi t1, s2, 72; li t2, 0\n" ++
  ".Ldtrc_rkey:\n" ++
  "  li t3, 20; beq t2, t3, .Ldtrc_rkeyd\n" ++
  "  add t3, t1, t2; lbu t4, 0(t3); la t5, dtrc_recipkey; add t5, t5, t2; sb t4, 0(t5); addi t2, t2, 1; j .Ldtrc_rkey\n" ++
  ".Ldtrc_rkeyd:\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 5; la t3, bvcd_keys; add a1, t3, t2   # a1 = slotKey ptr\n" ++
  "  la a0, dtrc_recipkey; la a2, bv_mtx_committed; la t0, bv_mtx_committed_count; ld a3, 0(t0); la a4, dtrc_threadval\n" ++
  "  jal ra, exec_log_latest_value\n" ++
  "  beqz a0, .Ldtrc_nothread                       # no prior-tx committed value -> keep witness value\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 6; la t3, bvcd_preload; add t4, t3, t2   # preload entry i\n" ++
  "  la t5, dtrc_threadval\n" ++
  "  ld t6, 0(t5);  sd t6, 32(t4); ld t6, 8(t5);  sd t6, 40(t4)\n" ++
  "  ld t6, 16(t5); sd t6, 48(t4); ld t6, 24(t5); sd t6, 56(t4)\n" ++
  ".Ldtrc_nothread:\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Ldtrc_sloop\n" ++
  ".Ldtrc_stage:\n" ++
  "  mv a0, s2; la a1, bv_runtime_payload; la t2, bv_exec_p; ld a2, 0(t2)\n" ++
  "  la t0, bvcd_code_ptr; ld a3, 0(t0); la t0, bvcd_code_len; ld a4, 0(t0)\n" ++
  "  la a5, bvcd_preload; la t0, bvcd_key_count; ld a6, 0(t0)\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  -- bmvmx.1.6.4.2.b: seed every non-recipient BAL account's storage into the exec log
  -- so nested callees SLOAD witness values (not 0). Fills callee_seed_table/count, which
  -- the callable dispatcher's seed loop drains during runtime_dispatcher_call's setup.
  "  mv a0, s0; mv a1, s1; addi a2, s2, 72\n" ++
  "  jal ra, seed_callee_storage\n" ++
  "  la t4, runtime_dispatcher_input_ptr; la t5, bv_runtime_payload; addi t5, t5, 8; sd t5, 0(t4)\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp)\n" ++
  "  jal ra, runtime_dispatcher_call\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  la t4, runtime_dispatcher_input_ptr; sd zero, 0(t4)\n" ++
  "  la t2, evm_env; ld t3, 568(t2)\n" ++
  "  la t4, runtime_tx_calldata_floor; ld t5, 0(t4)\n" ++
  "  mv a1, t3                    # gas_left\n" ++
  "  mv a2, t5                    # calldata_floor\n" ++
  "  li a0, 0\n" ++
  "  j .Ldtrc_ret\n" ++
  ".Ldtrc_unsupported:\n" ++
  "  li a0, 1\n" ++
  ".Ldtrc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

end EvmAsm.Codegen
