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
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.CommittedStorageLookup

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
      a1 = effective gas_left on status 0: env[568] + evm_state_gas_left with
           the spec's tx-level error rules folded in by dispatcher_tx_gas_settle
           (exceptional halt → regular gas burnt; any error → state-gas restore)
      a2 = calldata_floor (runtime_tx_calldata_floor) on status 0
      a3 = effective refund counter on status 0 (evm_refund_acc, or 0 when the
           tx erred — interpreter.py discards the refund counter on error)
      a4 = tx success bit on status 0 (1 for STOP/RETURN/SELFDESTRUCT halts,
           0 for REVERT/exceptional — the receipt `succeeded` field)

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
    value). Caps at 512 entries (table size); preserves s0..s3. A seeded slot has
    original==current==value (no net change), matching the recipient preload. -/
def seedCalleeStorageFunction : String :=
  "seed_callee_storage:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++   -- lv44p: s4 holds the changes-slot count across the reads-keys call
  "  mv s0, a0                    # witness ptr\n" ++
  "  mv s1, a1                    # witness len\n" ++
  "  mv s2, a2                    # recipient 20B addr ptr\n" ++
  "  la t0, callee_seed_count; sd zero, 0(t0)\n" ++
  "  la t0, callee_balance_count; sd zero, 0(t0)\n" ++   -- 1ipxd.1: reset per-account SELFBALANCE table
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
  -- 1ipxd.1: pre-resolve this BAL account's balance into callee_balance_table (clean
  -- pre-execution context; the witness MPT walk returns absent if run mid-EVM-execution
  -- inside call_frame_descend). Covers the recipient too (it IS a BAL account; the recipient
  -- skip below is storage-only). Key = canonical-BE 20-byte addr (csce_addrp); value = balance
  -- stored LE-limb so the descend copies it verbatim to the LE EVM stack (odq06 byte-order).
  -- Header = svf_parent_rlp (parent/witness root; the single-tx POST header bails). The verdict
  -- witness.state = s0/s1 (= bv_witness_state). account_at_header_state_root preserves s0-s7.
  "  la t0, callee_balance_count; ld t1, 0(t0); li t2, 512; bgeu t1, t2, .Lscs_bal_done\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la t0, csce_addrp; ld a2, 0(t0); li a3, 20; mv a4, s0; mv a5, s1; la a6, csce_bal_struct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lscs_bal_done\n" ++                  -- absent/error -> skip (descend default 0)
  "  la t0, callee_balance_count; ld t1, 0(t0); slli t2, t1, 6; la t3, callee_balance_table; add t3, t3, t2\n" ++
  -- addr (canonical BE, csce_addrp) -> entry+0..19, zero-pad +20..31
  "  la t0, csce_addrp; ld t0, 0(t0)\n" ++
  "  ld t4, 0(t0); sd t4, 0(t3); ld t4, 8(t0); sd t4, 8(t3); lwu t4, 16(t0); sw t4, 16(t3); sw zero, 20(t3); sd zero, 24(t3)\n" ++
  -- balance: csce_bal_struct+8..40 is BE; byte-reverse the 32 bytes into entry+32 (LE-limb).
  "  la t4, csce_bal_struct; addi t4, t4, 39; addi t5, t3, 32; li t6, 32\n" ++
  ".Lscs_bal_rev:\n" ++
  "  lbu t0, 0(t4); sb t0, 0(t5); addi t4, t4, -1; addi t5, t5, 1; addi t6, t6, -1; bnez t6, .Lscs_bal_rev\n" ++
  "  la t0, callee_balance_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lscs_bal_done:\n" ++
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
  "  li t0, 128; bgtu a0, t0, .Lscs_acct_next        # bmvmx.1.7.3: >128 changes wouldn't fit csce_keys -> skip this account (seed nothing)\n" ++
  -- lv44p / coc3g.5: ALSO enumerate the account's storage_READS keys (AccountChanges item 2) and
  -- seed them from the witness pre-state. A user contract that CALLs the EIP-2935 / EIP-4788
  -- predeploy READS a slot the begin-of-block system tx wrote in a PRIOR block (e.g. BLOCKHASH /
  -- parent-beacon-root): that slot is a storage_READ (not a storage_change) in THIS block's BAL, so
  -- a changes-only seed left it cold -> the nested SLOAD returned 0 -> the recipient SSTORE'd 0 ->
  -- bv_fail=34. The read value lives in the parent-state witness (the prior block's begin-of-block
  -- write is committed to the parent state root that roots the witness), so slot_at_header_state_root
  -- (dtrc_hdr_ptr = sv_pre_rlp under the coc3g flip) reads the AUTHENTICATED value. Mirrors the
  -- end-of-block stage_predeploy_storage_preload's Fix2 (which also appends reads keys). A slot that
  -- is BOTH read and changed (changes seeded first) is harmless: the seed only supplies the cold
  -- value, and the runtime SSTORE/last-write-wins overlay overrides it.
  "  mv s4, a0                                        # s4 = changes-slot count\n" ++
  "  mv a0, s3; la t0, csce_alen; ld a1, 0(t0)\n" ++
  "  slli t0, s4, 5; la t1, csce_keys; add a2, t1, t0  # a2 = &csce_keys[changes_count]\n" ++
  "  li t0, 128; sub a3, t0, s4                       # remaining capacity to 128\n" ++
  "  jal ra, bal_recipient_storage_reads_keys         # append storage_reads keys after the changes keys\n" ++
  "  add a0, a0, s4                                   # total = changes + reads\n" ++
  "  li t0, 128; bgtu a0, t0, .Lscs_acct_next        # combined > 128 -> skip this account (reads wrote nothing)\n" ++
  "  la t0, csce_key_n; sd a0, 0(t0)\n" ++
  "  la t0, csce_key_i; sd zero, 0(t0)\n" ++
  ".Lscs_slot_loop:\n" ++
  "  la t0, csce_key_i; ld t1, 0(t0); la t2, csce_key_n; ld t3, 0(t2); beq t1, t3, .Lscs_acct_next\n" ++
  "  la t0, callee_seed_count; ld t2, 0(t0); li t3, 128; bgeu t2, t3, .Lscs_done   # table cap\n" ++
  "  slli t4, t1, 5; la t5, csce_keys; add a3, t5, t4   # slot key ptr\n" ++
  "  la t0, dtrc_hdr_ptr; ld a0, 0(t0); la t0, dtrc_hdr_len; ld a1, 0(t0)\n" ++   -- .57.11.6.5: mtx-gated witness-lookup header (resolved at dispatch entry: sv_this_rlp single-tx / sv_pre_rlp mtx)
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
  -- .57.11.6.5.3 (d'): slot key (csce_keys, BIG-endian) + value (sahsr_u256, u256 BIG-endian)
  -- must be byte-reversed to little-endian-limb to match the exec-log scan / SSTORE-append order
  -- (same convention BalStorageReadsExecLog already reverses BE keys into). Verbatim limb-copy
  -- left non-zero seeded slots invisible to a nested callee's SLOAD/SSTORE.
  "  la t0, csce_key_i; ld t1, 0(t0); slli t2, t1, 5; la t5, csce_keys; add t5, t5, t2\n" ++   -- t5 = csce_keys[i] (BE)
  "  li t6, 0\n" ++
  ".Lscs_krev:\n" ++
  "  li t0, 32; beq t6, t0, .Lscs_krevd\n" ++
  "  add t0, t5, t6; lbu t1, 0(t0)\n" ++                              -- BE key byte i
  "  li t0, 63; sub t0, t0, t6; add t0, t4, t0; sb t1, 0(t0)\n" ++    -- -> entry slotKey byte 32+(31-i)=63-i (entry[32..63])
  "  addi t6, t6, 1; j .Lscs_krev\n" ++
  ".Lscs_krevd:\n" ++
  "  la t5, sahsr_u256; li t6, 0\n" ++
  ".Lscs_vrev:\n" ++
  "  li t0, 32; beq t6, t0, .Lscs_vrevd\n" ++
  "  add t0, t5, t6; lbu t1, 0(t0)\n" ++                              -- BE value byte i
  "  li t0, 95; sub t0, t0, t6; add t0, t4, t0; sb t1, 0(t0)\n" ++    -- -> entry value byte 64+(31-i)=95-i (entry[64..95])
  "  addi t6, t6, 1; j .Lscs_vrev\n" ++
  ".Lscs_vrevd:\n" ++
  "  j .Lscs_slot_commit\n" ++
  ".Lscs_slot_vzero:\n" ++
  "  la t0, callee_seed_count; ld t1, 0(t0); slli t2, t1, 6; slli t3, t1, 5; add t2, t2, t3\n" ++
  "  la t4, callee_seed_table; add t4, t4, t2\n" ++
  "  la t5, csce_addrkey\n" ++
  "  ld t6, 0(t5); sd t6, 0(t4); ld t6, 8(t5); sd t6, 8(t4); ld t6, 16(t5); sd t6, 16(t4); ld t6, 24(t5); sd t6, 24(t4)\n" ++
  -- slot key BE->LE byte-reverse (see .Lscs_krev); value is zero (slot absent at this state root).
  "  la t0, csce_key_i; ld t1, 0(t0); slli t2, t1, 5; la t5, csce_keys; add t5, t5, t2\n" ++
  "  li t6, 0\n" ++
  ".Lscs_kzrev:\n" ++
  "  li t0, 32; beq t6, t0, .Lscs_kzrevd\n" ++
  "  add t0, t5, t6; lbu t1, 0(t0)\n" ++
  "  li t0, 63; sub t0, t0, t6; add t0, t4, t0; sb t1, 0(t0)\n" ++   -- -> entry slotKey byte 32+(31-i)=63-i (entry[32..63])
  "  addi t6, t6, 1; j .Lscs_kzrev\n" ++
  ".Lscs_kzrevd:\n" ++
  "  sd zero, 64(t4); sd zero, 72(t4); sd zero, 80(t4); sd zero, 88(t4)\n" ++
  ".Lscs_slot_commit:\n" ++
  "  la t0, callee_seed_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lscs_slot_next:\n" ++
  "  la t0, csce_key_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lscs_slot_loop\n" ++
  ".Lscs_acct_next:\n" ++
  "  la t0, csce_acct_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lscs_acct_loop\n" ++
  ".Lscs_done:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def dispatchTxRuntimeCodeFunction : String :=
  "dispatch_tx_runtime_code:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a1                    # witness.state ptr\n" ++
  "  mv s1, a2                    # witness.state len\n" ++
  "  mv s2, a0                    # context record ptr\n" ++
  -- fhsxz.2.4.2.57.11.6.5: resolve the witness-lookup header ONCE (mtx-gated). Default
  -- (dtrc_use_pre_header=0, single-tx) = sv_this_rlp (this block's POST-state header,
  -- whose root is NOT in the pre-rooted witness -> lookups bail -> conservative, byte-
  -- identical to #8686). The mtx loop sets the flag=1 to use the PRE-state (parent)
  -- header whose root IS the witness root, enabling real multi-tx contract dispatch.
  "  la t0, dtrc_use_pre_header; ld t0, 0(t0); bnez t0, .Ldtrc_hdr_pre\n" ++
  "  la t1, sv_this_rlp; la t2, dtrc_hdr_ptr; sd t1, 0(t2)\n" ++
  "  la t0, sv_this_rlp_len; ld t1, 0(t0); la t2, dtrc_hdr_len; sd t1, 0(t2)\n" ++
  "  j .Ldtrc_hdr_done\n" ++
  ".Ldtrc_hdr_pre:\n" ++
  "  la t0, sv_pre_rlp_ptr; ld t1, 0(t0); la t2, dtrc_hdr_ptr; sd t1, 0(t2)\n" ++
  "  la t0, sv_pre_rlp_len; ld t1, 0(t0); la t2, dtrc_hdr_len; sd t1, 0(t2)\n" ++
  ".Ldtrc_hdr_done:\n" ++
  "  addi a0, s2, 72; mv a1, s0; mv a2, s1; li a3, 0\n" ++
  "  jal ra, bal_same_block_delegation_code_resolve\n" ++
  "  beqz a0, .Ldtrc_same_block_delegation_code\n" ++
  "  la t0, dtrc_hdr_ptr; ld a0, 0(t0); la t0, dtrc_hdr_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72\n" ++
  "  mv a3, s0; mv a4, s1\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Ldtrc_code_lookup_unsupported\n" ++
  -- coc3g.5: EIP-7702 prior-block delegation follow. The DIRECT recipient code lookup
  -- (this path, taken when the recipient was NOT delegated in THIS block) may return a
  -- 0xef0100||target marker (23 bytes) — a prior-block-delegated EOA whose pre/post-state
  -- code is the delegation designator. The spec (interpreter.py process_message) runs the
  -- DELEGATED TARGET's code while keeping current_target = the delegating EOA, so
  -- env.ADDRESS (stage_runtime_payload_code ADDRESS@0 = ctx+72 = the EOA) is UNCHANGED and
  -- SSTORE keys the EOA's own storage; only message.code is re-pointed at the target's
  -- code. Without this the marker bytes ran as bytecode (no SSTORE), so the EOA's BAL
  -- storage_change was absent from the exec log -> bv_fail=34. Follow is applied ONLY here
  -- (not on the same-block-delegation path below, which already resolved the one-hop
  -- target code): EIP-7702 delegation is single-hop, never recursively chained.
  "  la t0, cahsr_code_length; ld t2, 0(t0); li t3, 23; bne t2, t3, .Ldtrc_have_code\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3\n" ++
  "  lbu t2, 0(t4); li t3, 0xef; bne t2, t3, .Ldtrc_have_code\n" ++
  "  lbu t2, 1(t4); li t3, 0x01; bne t2, t3, .Ldtrc_have_code\n" ++
  "  lbu t2, 2(t4); bnez t2, .Ldtrc_have_code\n" ++
  -- Copy the 20-byte target address (marker bytes 3..22) into dtrc_deleg_target.
  "  la t1, dtrc_deleg_target; addi t5, t4, 3; li t6, 20\n" ++
  ".Ldtrc_deleg_copy:\n" ++
  "  beqz t6, .Ldtrc_deleg_copied\n" ++
  "  lbu t2, 0(t5); sb t2, 0(t1); addi t5, t5, 1; addi t1, t1, 1; addi t6, t6, -1; j .Ldtrc_deleg_copy\n" ++
  ".Ldtrc_deleg_copied:\n" ++
  -- Re-resolve the TARGET's code against the same header the recipient resolved under.
  "  la t0, dtrc_hdr_ptr; ld a0, 0(t0); la t0, dtrc_hdr_len; ld a1, 0(t0)\n" ++
  "  la a2, dtrc_deleg_target\n" ++
  "  mv a3, s0; mv a4, s1\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Ldtrc_code_lookup_unsupported\n" ++
  -- Warm the delegated target (EIP-2929 accessed_addresses.add(delegated_address)).
  "  la a0, dtrc_deleg_target; la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_seed\n" ++
  "  j .Ldtrc_have_code\n" ++
  ".Ldtrc_same_block_delegation_code:\n" ++
  "  la t0, sv_pre_rlp_ptr; ld t1, 0(t0); la t2, dtrc_hdr_ptr; sd t1, 0(t2)\n" ++
  "  la t0, sv_pre_rlp_len; ld t1, 0(t0); la t2, dtrc_hdr_len; sd t1, 0(t2)\n" ++
  ".Ldtrc_have_code:\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add a0, t1, t3\n" ++
  "  la t2, cahsr_code_length; ld a1, 0(t2)\n" ++
  "  la t0, bvcd_code_ptr; sd a0, 0(t0); la t0, bvcd_code_len; sd a1, 0(t0)\n" ++
  "  jal ra, bytecode_is_self_contained\n" ++
  "  bnez a0, .Ldtrc_self_contained_unsupported\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72; la a3, bvcd_acct_ptr; la a4, bvcd_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  li t0, 2; beq a0, t0, .Ldtrc_bal_unsupported\n" ++
  "  bnez a0, .Ldtrc_zero_storage\n" ++
  "  la t0, bvcd_acct_ptr; ld a0, 0(t0); la t0, bvcd_acct_len; ld a1, 0(t0); la a2, bvcd_keys\n" ++
  "  jal ra, bal_recipient_storage_keys\n" ++
  "  li t0, " ++ toString bsrAccountSlotCap ++ "; bgtu a0, t0, .Ldtrc_bal_unsupported   # 4jczt class-B lift: storage_changes capped at the gas-derived bsrAccountSlotCap; bvcd_keys/bvcd_preload sized to match (was 128)\n" ++
  "  la t0, bvcd_sc_count; sd a0, 0(t0)\n" ++
  -- fhsxz.2.4.2.57.11.6.5 (revert fix): also preload the recipient's storage_READS slots
  -- (accessed-but-not-net-changed). A reverting tx has empty storage_changes (its writes
  -- roll back) but lists the touched slots in storage_reads; without these the SSTORE-clears
  -- find no preloaded slot and undercharge (missing-slot path) -> block_regular undercount
  -- (bv_fail=41). Append the storage_reads keys after the storage_changes keys; cap total at
  -- bsrAccountSlotCap (the gas-derived bvcd_keys/bvcd_preload buffer size; 4jczt lift, was 128).
  "  la t0, bvcd_acct_ptr; ld a0, 0(t0); la t0, bvcd_acct_len; ld a1, 0(t0)\n" ++
  "  la t0, bvcd_sc_count; ld t1, 0(t0); slli t2, t1, 5; la a2, bvcd_keys; add a2, a2, t2\n" ++
  "  li a3, " ++ toString bsrAccountSlotCap ++ "; sub a3, a3, t1\n" ++
  "  jal ra, bal_recipient_storage_reads_keys\n" ++
  "  la t0, bvcd_sc_count; ld t1, 0(t0); add a0, a0, t1   # total = storage_changes + storage_reads\n" ++
  "  li t0, " ++ toString bsrAccountSlotCap ++ "; bgtu a0, t0, .Ldtrc_bal_unsupported\n" ++
  "  la t0, bvcd_key_count; sd a0, 0(t0); j .Ldtrc_read_storage\n" ++
  ".Ldtrc_zero_storage:\n" ++
  "  la t0, bvcd_key_count; sd zero, 0(t0)\n" ++
  ".Ldtrc_read_storage:\n" ++
  "  la t0, bvcd_i; sd zero, 0(t0)\n" ++
  ".Ldtrc_sloop:\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); la t2, bvcd_key_count; ld t3, 0(t2); beq t1, t3, .Ldtrc_stage\n" ++
  "  slli t4, t1, 5; la t5, bvcd_keys; add a3, t5, t4\n" ++
  "  la t0, dtrc_hdr_ptr; ld a0, 0(t0); la t0, dtrc_hdr_len; ld a1, 0(t0)\n" ++   -- .57.11.6.5: mtx-gated witness-lookup header (resolved at dispatch entry)
  "  addi a2, s2, 72\n" ++
  "  mv a4, s0; mv a5, s1; mv a6, s0; mv a7, s1\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 6; la t3, bvcd_preload; add t4, t3, t2\n" ++
  "  slli t2, t1, 5; la t3, bvcd_keys; add t5, t3, t2\n" ++
  "  li t6, 0\n" ++
  -- fhsxz.2.4.2.57.11.6.5.3 (d'): the BAL slot key (bvcd_keys) is 32-byte BIG-ENDIAN
  -- (left-padded), but the EVM stack / exec-log scan (Storage.lean h_SLOAD/h_SSTORE) and the
  -- runtime SSTORE-appended entries are LITTLE-ENDIAN-limb. Copying the key verbatim left
  -- preloaded non-zero slots INVISIBLE to the scan (only slot 0 matched, identical in both
  -- orders) -> SLOAD-of-preload returned 0 and SSTORE saw a missing slot, undercharging gas.
  -- Byte-REVERSE the key (dst byte 31-i <- src byte i) so the preload entry's slotKey matches
  -- the stack/append LE order. Validated: with LE preload the 10x SSTORE-clear repro charges
  -- the full 5000 each (gas_left 25200 -> 0).
  ".Ldtrc_kcopy:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_kdone\n" ++
  "  add t2, t5, t6; lbu t3, 0(t2)\n" ++                              -- t3 = BE key byte i
  "  li t2, 31; sub t2, t2, t6; add t2, t4, t2; sb t3, 0(t2)\n" ++    -- -> dst byte (31-i): BE->LE
  "  addi t6, t6, 1; j .Ldtrc_kcopy\n" ++
  ".Ldtrc_kdone:\n" ++
  "  li t2, 5; beq a0, t2, .Ldtrc_vzero\n" ++
  "  bnez a0, .Ldtrc_storage_unsupported\n" ++
  "  la t5, sahsr_u256; li t6, 0\n" ++
  -- The witness slot value (sahsr_u256) is also u256 BIG-ENDIAN (StateCompose.lean:519);
  -- byte-REVERSE it into the value field [entry+32..64] (dst byte 63-i <- src byte i) so
  -- original==current read back as LE limbs match the SSTORE handler's clean/dirty test.
  -- (The cross-tx threaded value below is already LE — it limb-copies dtrc_threadval from the
  -- exec log — so it is left as-is.)
  ".Ldtrc_vcopy:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_vdone\n" ++
  "  add t2, t5, t6; lbu t3, 0(t2)\n" ++                              -- t3 = BE value byte i
  "  li t2, 63; sub t2, t2, t6; add t2, t4, t2; sb t3, 0(t2)\n" ++    -- -> dst byte 32+(31-i)=63-i: BE->LE
  "  addi t6, t6, 1; j .Ldtrc_vcopy\n" ++
  ".Ldtrc_vzero:\n" ++
  "  li t6, 0\n" ++
  ".Ldtrc_vzloop:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_vdone\n" ++
  "  add t2, t4, t6; addi t2, t2, 32; sb zero, 0(t2); addi t6, t6, 1; j .Ldtrc_vzloop\n" ++
  ".Ldtrc_vdone:\n" ++
  -- fhsxz.2.4.2.57.11.6.3.2 cross-tx threading: if a prior tx in this block committed a
  -- value for (recipient, slotKey), stage that committed value as this slot's preload
  -- (original==current). The helper bounds the table count by the named committed-storage
  -- capacity, prepares recipient/slot scratch, and preserves latest matching entry semantics.
  "  la t0, bv_mtx_committed_chunk_count; ld a3, 0(t0); beqz a3, .Ldtrc_nothread\n" ++
  "  addi a0, s2, 72                                  # recipient 20B ptr\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 5; la a1, bvcd_keys; add a1, a1, t2  # BE slot key ptr\n" ++
  "  la a2, bv_mtx_committed_chunked; li a4, " ++ toString bvMtxCommittedChunkCapacity ++ "; la a5, dtrc_threadval; la a6, dtrc_recipkey; la a7, dtrc_slotkey_le\n" ++
  "  jal ra, bv_mtx_committed_chunked_latest_value\n" ++
  "  li t0, 2; beq a0, t0, .Ldtrc_storage_unsupported # over-capacity table count -> conservative\n" ++
  "  li t0, 1; bne a0, t0, .Ldtrc_nothread            # no prior-tx value -> keep witness value\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 6; la t3, bvcd_preload; add t4, t3, t2   # preload entry i\n" ++
  "  la t5, dtrc_threadval\n" ++
  "  ld t6, 0(t5);  sd t6, 32(t4); ld t6, 8(t5);  sd t6, 40(t4)\n" ++
  "  ld t6, 16(t5); sd t6, 48(t4); ld t6, 24(t5); sd t6, 56(t4)\n" ++
  ".Ldtrc_nothread:\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Ldtrc_sloop\n" ++
  ".Ldtrc_stage:\n" ++
  -- 3vc2p.3b sub-step B: reconstruct the M29 recent-blockhash table from the witness headers
  -- (cur = exec NUMBER, count = contiguous recent ancestors, count*32 hashes) into the staging
  -- globals BEFORE staging, so stage_runtime_payload_code writes the M29 block + shifts env_base.
  -- stage_blockhash_m29 (#8655) preserves s-regs (s2 = ctx survives); svf_headers_len = 0 yields
  -- count = 0 (inert / byte-identical). Execution-inert until 3vc2p.4 flips the BLOCKHASH gate.
  "  la t0, bv_exec_p; ld a0, 0(t0)\n" ++
  "  la t0, svf_headers_ptr; ld a1, 0(t0)\n" ++
  "  la t0, svf_headers_len; ld a2, 0(t0)\n" ++
  "  la a3, m29_stage_table\n" ++
  "  la a4, m29_stage_cur; la a5, m29_stage_count\n" ++
  "  jal ra, stage_blockhash_m29\n" ++
  -- BLOBHASH: extract blob versioned hashes from type-3 txs into the M28 staging
  -- globals, so stage_runtime_payload_code writes blob_hash_count + blob_hashes
  -- into the runtime payload trailer. Non-type-3 txs leave count=0 (inert).
  -- Each blob versioned hash is a fixed 32-byte string (RLP prefix 0xa0 + 32 bytes
  -- = 33 bytes per item), so the list payload start = list_start + (list_len - count*33).
  "  la t0, m28_blob_stage_count; sd zero, 0(t0)\n" ++
  "  ld t0, 160(s2); li t1, 3; bne t0, t1, .Ldtrc_no_blob_hash\n" ++
  "  ld a0, 176(s2); ld a1, 184(s2); la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ldtrc_no_blob_hash\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  ld t0, 176(s2); add t0, t0, t1\n" ++
  "  mv a0, t0; mv a1, t2; la a2, m28_blob_stage_count; jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Ldtrc_no_blob_hash\n" ++
  -- t0/t1/t2 clobbered by call — recompute list_start and blob_len
  "  la t0, tcbg_struct; lwu t4, 168(t0); lwu t2, 172(t0)\n" ++
  "  ld t0, 176(s2); add t0, t0, t4\n" ++
  "  la t1, m28_blob_stage_count; ld t1, 0(t1)\n" ++
  "  li t3, 33; mul t3, t1, t3; sub t3, t2, t3; add t0, t0, t3\n" ++
  "  la t2, m28_blob_stage_table\n" ++
  ".Ldtrc_blob_extract:\n" ++
  "  beqz t1, .Ldtrc_blob_extract_done\n" ++
  "  addi t0, t0, 1\n" ++
  -- Byte-reverse the 32-byte BE blob hash into LE-limb order (same fix
  -- class as GASPRICE odq06.3 / SELFBALANCE odq06.2). The EVM stack
  -- stores U256 in LE-limb order (low limb at +0), but the RLP source
  -- is big-endian; a raw dword copy reverses the limb order.
  "  li t3, 0\n" ++
  ".Ldtrc_blob_rev:\n" ++
  "  li t4, 32; beq t3, t4, .Ldtrc_blob_rev_done\n" ++
  "  add t4, t0, t3; lbu t5, 0(t4)\n" ++
  "  li t4, 31; sub t4, t4, t3; add t4, t2, t4; sb t5, 0(t4)\n" ++
  "  addi t3, t3, 1; j .Ldtrc_blob_rev\n" ++
  ".Ldtrc_blob_rev_done:\n" ++
  "  addi t0, t0, 32; addi t2, t2, 32; addi t1, t1, -1; j .Ldtrc_blob_extract\n" ++
  ".Ldtrc_blob_extract_done:\n" ++
  ".Ldtrc_no_blob_hash:\n" ++
  -- bmvmx.1.7.2: conservative payload-size guard. stage_runtime_payload_code writes
  -- round8(codelen)+round8(calldata)+storage*64+584 bytes into bv_runtime_payload; if that
  -- exceeds the buffer (bsrAccountSlotCap*64+65536, the 4jczt-lifted size) the write would
  -- overflow into adjacent .data (gas result + bvcd_* scratch). EIP-170 bounds code to 24576;
  -- storage now fits the gas-derived BAL cap, but calldata/witness are still unbounded, so bail
  -- conservatively (route to the safe path) instead of corrupting state.
  "  la t0, bvcd_code_len; ld t1, 0(t0); addi t1, t1, 7; andi t1, t1, -8\n" ++   -- round8(codelen)
  "  ld t2, 64(s2); addi t2, t2, 7; andi t2, t2, -8; add t1, t1, t2\n" ++         -- + round8(calldata)
  "  la t0, bvcd_key_count; ld t2, 0(t0); slli t2, t2, 6; add t1, t1, t2\n" ++   -- + storage_count*64
  "  la t0, m28_blob_stage_count; ld t2, 0(t0); slli t2, t2, 5; add t1, t1, t2\n" ++  -- + blob hashes (count*32)
  "  la t0, m29_stage_count; ld t2, 0(t0); slli t2, t2, 5; add t1, t1, t2\n" ++  -- 3vc2p.3b: + M29 hashes (count*32)
  "  la t0, dtrc_hdr_len; ld t2, 0(t0); add t1, t1, t2\n" ++        -- nested-CALL account-witness header bytes
  "  add t1, t1, s1\n" ++                                             -- witness.state bytes
  "  la t0, svf_codes_len; ld t2, 0(t0); add t1, t1, t2\n" ++       -- witness.codes bytes
  "  addi t1, t1, 584; li t2, " ++ toString (bsrAccountSlotCap * 64 + 65536) ++ "; bgtu t1, t2, .Ldtrc_payload_cap_unsupported\n" ++       -- payload > buffer (4jczt-lifted) -> conservative bail
  "  mv a0, s2; la a1, bv_runtime_payload; la t2, bv_exec_p; ld a2, 0(t2)\n" ++
  "  la t0, bvcd_code_ptr; ld a3, 0(t0); la t0, bvcd_code_len; ld a4, 0(t0)\n" ++
  "  la a5, bvcd_preload; la t0, bvcd_key_count; ld a6, 0(t0)\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Ldtrc_stage_unsupported\n" ++
  -- 6121j/coc3g.12.1: stage BLOBBASEFEE for the contract-recipient payload too.
  -- stage_runtime_payload_code leaves the 32-byte M28 blob-base-fee slot zeroed; compute the
  -- Amsterdam blob gas price from exec_payload.excess_blob_gas, then reverse the helper's BE
  -- output into the EVM stack-word layout expected by h_BLOBBASEFEE (limb0 at +0).
  "  la t0, bv_exec_p; ld a0, 0(t0); addi a0, a0, 520; jal ra, bgv_u64le\n" ++
  "  addi a1, sp, 48; jal ra, amsterdam_blob_gas_price_u256\n" ++
  "  bnez a0, .Ldtrc_stage_unsupported\n" ++
  "  la t0, bv_runtime_payload\n" ++
  "  la t1, srpc_env_base; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t2, m28_blob_stage_count; ld t2, 0(t2); slli t2, t2, 5; addi t2, t2, 56\n" ++
  "  la t3, m29_stage_count; ld t3, 0(t3); slli t3, t3, 5; add t2, t2, t3; sub t0, t0, t2\n" ++
  "  addi t1, sp, 48; li t2, 0\n" ++
  ".Ldtrc_blobbasefee_rev:\n" ++
  "  li t3, 32; beq t2, t3, .Ldtrc_blobbasefee_done\n" ++
  "  add t4, t1, t2; lbu t5, 0(t4); li t3, 31; sub t3, t3, t2; add t4, t0, t3; sb t5, 0(t4)\n" ++
  "  addi t2, t2, 1; j .Ldtrc_blobbasefee_rev\n" ++
  ".Ldtrc_blobbasefee_done:\n" ++
  -- bmvmx/gcylw: stage the same account-witness context used by the top-level
  -- recipient lookup into the callable runtime trailer, so nested CALL/EXTCODE
  -- lookups read the pre-header/state/codes context instead of zero lengths.
  "  la t0, bv_runtime_payload\n" ++
  "  la t5, srpc_env_base; ld t1, 0(t5); add t0, t0, t1\n" ++
  "  la t2, dtrc_hdr_len; ld t3, 0(t2); sd t3, 472(t0)\n" ++
  "  sd s1, 480(t0)\n" ++
  "  la t2, svf_codes_len; ld t4, 0(t2); sd t4, 488(t0)\n" ++
  "  addi t5, t0, 496\n" ++
  "  la t2, dtrc_hdr_ptr; ld t2, 0(t2); mv t6, t3\n" ++
  ".Ldtrc_ctx_hdr_copy:\n" ++
  "  beqz t6, .Ldtrc_ctx_state_copy_start\n" ++
  "  lbu a0, 0(t2); sb a0, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Ldtrc_ctx_hdr_copy\n" ++
  ".Ldtrc_ctx_state_copy_start:\n" ++
  "  mv t2, s0; mv t6, s1\n" ++
  ".Ldtrc_ctx_state_copy:\n" ++
  "  beqz t6, .Ldtrc_ctx_codes_copy_start\n" ++
  "  lbu a0, 0(t2); sb a0, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Ldtrc_ctx_state_copy\n" ++
  ".Ldtrc_ctx_codes_copy_start:\n" ++
  "  la t2, svf_codes_ptr; ld t2, 0(t2); mv t6, t4\n" ++
  ".Ldtrc_ctx_codes_copy:\n" ++
  "  beqz t6, .Ldtrc_ctx_done\n" ++
  "  lbu a0, 0(t2); sb a0, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Ldtrc_ctx_codes_copy\n" ++
  ".Ldtrc_ctx_done:\n" ++
  -- 3vc2p.1: stage CALLER (env+64) + ORIGIN (env+128) = tx'sender into the runtime
  -- payload's env words, so CALLER/ORIGIN resolve once 3vc2p.4 activates them (for a
  -- top-level tx, CALLER == ORIGIN == tx'sender). The sender is derived from the
  -- selected pubkey (ctx+24, 64-byte x||y) via address_from_pubkey. env_base (in the
  -- payload) = round8(codelen) + 80; CALLER = env_base+64, ORIGIN = env_base+128 (the
  -- same word slots stage_runtime_payload_code wrote ADDRESS@+0 / CALLVALUE@+96 to).
  -- INERT until 3vc2p.4: self-contained recipients reaching here never read CALLER/
  -- ORIGIN (the opcodes are still bytecode_is_self_contained-rejected). address_from_pubkey
  -- preserves s-regs (s0-s3 survive its keccak); guarded on a non-null pubkey ptr.
  "  ld a0, 24(s2)\n" ++
  "  beqz a0, .Ldtrc_no_sender\n" ++
  "  la a1, srpc_sender_addr\n" ++
  "  jal ra, address_from_pubkey\n" ++
  "  la t0, bv_runtime_payload\n" ++
  "  la t5, srpc_env_base; ld t1, 0(t5)\n" ++                -- 3vc2p.5: env_base from stage_runtime_payload_code
  "  add t2, t0, t1\n" ++                                    -- t2 = &env_words
  "  la t3, srpc_sender_addr; addi t4, t2, 64; li t5, 0\n" ++   -- CALLER (word 2 -> +64), BE address -> stack-word layout
  ".Ldtrc_caller:\n" ++
  "  li t6, 20; beq t5, t6, .Ldtrc_caller_d\n" ++
  "  li a5, 19; sub a5, a5, t5; add a5, t3, a5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Ldtrc_caller\n" ++
  ".Ldtrc_caller_d:\n" ++
  "  addi t4, t2, 128; li t5, 0\n" ++                        -- ORIGIN (word 4 -> +128); t3 still = srpc_sender_addr
  ".Ldtrc_origin:\n" ++
  "  li t6, 20; beq t5, t6, .Ldtrc_origin_d\n" ++
  "  li a5, 19; sub a5, a5, t5; add a5, t3, a5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Ldtrc_origin\n" ++
  ".Ldtrc_origin_d:\n" ++
  ".Ldtrc_no_sender:\n" ++
  -- 3vc2p.2: GASPRICE (word 5 -> env_base+160) = effective_gas_price. Computed via
  -- tx_effective_gas_pricing(a0=tx ptr, a1=tx len, a2=base_fee ptr -> a3=egp 32B BE,
  -- a4=prio) from the context (ctx+8 tx ptr / ctx+16 tx len / ctx+32 base_fee ptr), then
  -- copied verbatim into the gasPrice env word — mirroring the CALLVALUE staging
  -- (ctx+96 value, also 32B BE, copied direct), the already-active u256 env word, so the
  -- byte order matches a word GASPRICE pushes. INERT until 3vc2p.4 (self-contained
  -- recipients don't read GASPRICE). Conservative: a pricing failure leaves gasPrice 0.
  "  ld a0, 8(s2); ld a1, 16(s2); ld a2, 32(s2)\n" ++
  -- fhsxz.2.4.2.57.11.6.5: skip gas-pricing when base_fee ptr (ctx+32) is null. The
  -- multi-tx context (multi_tx_nth_context) leaves +32 zero (base_fee is a per-call
  -- input the loop doesn't supply); tx_effective_gas_pricing would then deref a null
  -- base_fee (u256_sub_be max_fee - base_fee reads addr 0 -> ziskemu mem panic). GASPRICE
  -- is INERT for self-contained recipients, so leaving it 0 here is correct (same as the
  -- existing pricing-failure path). Mirrors the .Ldtrc_no_sender guard on the pubkey (+24).
  "  beqz a2, .Ldtrc_no_gasprice\n" ++
  "  la a3, gp_egp; la a4, gp_prio\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  bnez a0, .Ldtrc_no_gasprice\n" ++
  "  la t0, bv_runtime_payload\n" ++
  "  la t5, srpc_env_base; ld t1, 0(t5)\n" ++                -- 3vc2p.5: env_base from stage_runtime_payload_code
  "  add t2, t0, t1; addi t2, t2, 160\n" ++                  -- t2 = &gasPrice word (env_base+160)
  -- odq06.3: byte-reverse the 32B BE gp_egp into env+160 so the low limb lands
  -- at env+160 (LE-limb order, matching how h_GASPRICE copies env+160..191
  -- dword-for-dword onto the stack). A verbatim BE copy put the low byte at
  -- env+191, so limb 0 was all-zero -> GASPRICE pushed 0 -> SSTORE(0,0) ->
  -- bv_fail=34 (blob_tx_attribute_gasprice_opcode). Same fix as odq06.2 SELFBALANCE.
  "  la t3, gp_egp; addi t3, t3, 31; mv t4, t2; li t5, 32\n" ++
  ".Ldtrc_gp_rev:\n" ++
  "  lbu t6, 0(t3); sb t6, 0(t4); addi t3, t3, -1; addi t4, t4, 1; addi t5, t5, -1; bnez t5, .Ldtrc_gp_rev\n" ++
  ".Ldtrc_no_gasprice:\n" ++
  -- yisv8.1: SELFBALANCE (word 1 -> env_base+32) = the recipient's own balance from the
  -- witness (account_at_header_state_root over env.ADDRESS=recipient, ctx+72), copied
  -- verbatim (BE) into the env word — mirroring the CALLVALUE/GASPRICE u256 staging (the
  -- ACTIVE CALLVALUE proves the contract-recipient path's u256 env words are BE-direct).
  -- INERT until yisv8.2 removes SELFBALANCE(0x47) from the self-contained reject set.
  -- Conservative: a lookup miss/error leaves SELFBALANCE 0. account_at_header_state_root
  -- preserves s-regs (s0=state ptr, s1=state len, s2=ctx survive); clobbers only dead a/t-regs.
  -- Use the raw account lookup here instead of balance_at_header_state_root: the BALANCE helper
  -- intentionally overlays the live nonstorage-effect log, but at top-level dispatch time that
  -- log may already contain transaction settlement effects. SELFBALANCE staging needs the
  -- execution-start account balance, then credits only tx.value below.
  -- odq06.1: use the PARENT/witness-root header (svf_parent_rlp), NOT dtrc_hdr_ptr (= sv_this_rlp
  -- POST header for single-tx, whose root is not in the pre-rooted witness -> bails -> SELFBALANCE 0).
  -- svf_parent_rlp's stateRoot IS the witness root; == sv_pre_rlp so multi-tx is unchanged.
  "  la t0, svf_parent_rlp; ld a0, 0(t0)\n  la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72\n" ++                       -- recipient addr (ctx+72)
  "  li a3, 20; mv a4, s0; mv a5, s1\n" ++       -- addr len + witness state ptr/len
  "  la a6, csce_bal_struct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Ldtrc_no_selfbal\n" ++             -- lookup miss/error -> leave SELFBALANCE 0
  "  la t0, bv_runtime_payload\n" ++
  "  la t5, srpc_env_base; ld t1, 0(t5)\n" ++                -- 3vc2p.5: env_base from stage_runtime_payload_code
  "  add t2, t0, t1; addi t2, t2, 32\n" ++                   -- t2 = &SELFBALANCE word (env_base+32)
  -- odq06.2: stage SELFBALANCE in stack-word (LE-limb) order, NOT big-endian. h_SELFBALANCE
  -- (0x47) copies env+32..63 dword-for-dword onto the EVM stack, which is LE-limb (low limb
  -- first); SSTORE then logs that order and the BAL comparator reverses the BE post-value to
  -- match. account_at_header_state_root outputs BE balance at account+8 (csce_bal_struct+8), so a verbatim copy put the
  -- balance's low byte in env+63 -> SELFBALANCE pushed a low-word of 0 -> SSTORE logged 0 (bv_fail=34
  -- self_code_on_set_code balance_1). Byte-reverse the 32-byte BE balance into env+32 so the low
  -- limb lands at env+32. (CALLVALUE@96 was never SSTORE'd+checked, so its order went unvalidated.)
  "  la t3, csce_bal_struct; addi t3, t3, 39; mv t4, t2; li t5, 32\n" ++
  ".Ldtrc_selfbal_rev:\n" ++
  "  lbu t6, 0(t3); sb t6, 0(t4); addi t3, t3, -1; addi t4, t4, 1; addi t5, t5, -1; bnez t5, .Ldtrc_selfbal_rev\n" ++
  -- Stage the top-level recipient value credit into the live non-storage log after
  -- runtime setup resets it. This lets BALANCE(recipient) observe tx.value during
  -- recipient execution. Self-transfers are already represented by the sender
  -- upfront-debit record, so do not overwrite that latest balance with pre+value.
  "  ld t0, 96(s2); ld t1, 104(s2); or t0, t0, t1; ld t1, 112(s2); or t0, t0, t1; ld t1, 120(s2); or t0, t0, t1; beqz t0, .Ldtrc_recipient_credit_done\n" ++
  "  addi t0, s2, 72; la t1, srpc_sender_addr; li t2, 20\n" ++
  ".Ldtrc_recipient_sender_cmp:\n" ++
  "  beqz t2, .Ldtrc_recipient_credit_done\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Ldtrc_recipient_distinct\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Ldtrc_recipient_sender_cmp\n" ++
  ".Ldtrc_recipient_distinct:\n" ++
  "  la t0, bv_pending_recipient_addr; sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  addi t1, s2, 72; li t2, 20\n" ++
  ".Ldtrc_recipient_addr_copy:\n" ++
  "  beqz t2, .Ldtrc_recipient_addr_done\n" ++
  "  lbu t3, 0(t1); sb t3, 0(t0); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Ldtrc_recipient_addr_copy\n" ++
  ".Ldtrc_recipient_addr_done:\n" ++
  "  la t0, csce_bal_struct; addi t0, t0, 8; la t1, bv_pending_recipient_pre\n" ++
  "  ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  la a0, bv_pending_recipient_pre; addi a1, s2, 96; la a2, bv_pending_recipient_post\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Ldtrc_recipient_credit_done\n" ++
  "  la t0, csce_bal_struct; ld t2, 0(t0); la t1, bv_pending_recipient_nonce; sd t2, 0(t1)\n" ++
  "  li t2, 1; la t1, bv_pending_recipient_credit_flag; sd t2, 0(t1)\n" ++
  ".Ldtrc_recipient_credit_done:\n" ++
  ".Ldtrc_no_selfbal:\n" ++
  -- coc3g.1: credit the recipient's live balance with the tx value, on BOTH the SELFBALANCE-lookup
  -- SUCCESS path (env+32 = staged pre-balance) AND the MISS path (env+32 ~ 0 for a fresh/unresolved
  -- recipient that the witness lookup couldn't stage). The EVM transfers tx.value to the recipient
  -- before its code runs, so SELFBALANCE / the creator's CREATE value-check see pre + tx.value.
  -- Recompute the env+32 pointer (the miss path jumped here without t2 set). env+96 = CALLVALUE (LE).
  -- 256-bit LE add; 0-value txs add 0. Preserves s0/s1/s2 (seed_callee_storage below needs them).
  "  la t0, bv_runtime_payload\n  la t1, srpc_env_base\n  ld t1, 0(t1)\n  add t2, t0, t1\n  addi t2, t2, 32\n" ++
  "  ld t3, 0(t2); ld t4, 64(t2); add t5, t3, t4; sltu t6, t5, t3; sd t5, 0(t2)\n" ++
  "  ld t3, 8(t2); ld t4, 72(t2); add t5, t3, t4; sltu a0, t5, t3; add t5, t5, t6; sltu a1, t5, t6; or t6, a0, a1; sd t5, 8(t2)\n" ++
  "  ld t3, 16(t2); ld t4, 80(t2); add t5, t3, t4; sltu a0, t5, t3; add t5, t5, t6; sltu a1, t5, t6; or t6, a0, a1; sd t5, 16(t2)\n" ++
  "  ld t3, 24(t2); ld t4, 88(t2); add t5, t3, t4; add t5, t5, t6; sd t5, 24(t2)\n" ++

  -- bmvmx.1.6.4.2.b: seed every non-recipient BAL account's storage into the exec log
  -- so nested callees SLOAD witness values (not 0). Fills callee_seed_table/count, which
  -- the callable dispatcher's seed loop drains during runtime_dispatcher_call's setup.
  "  mv a0, s0; mv a1, s1; addi a2, s2, 72\n" ++
  "  jal ra, seed_callee_storage\n" ++
  -- fhsxz.2.4.2.57.18.10: pass access-list cardinalities into the runtime
  -- dispatcher's tx-gas validator so the captured calldata floor and regular
  -- intrinsic gas include tokens_in_access_list. Type 0 has no access list,
  -- type 1 uses field 7, and EIP-1559/blob/7702 typed txs use field 8 of the
  -- inner RLP payload. Parse failures bail conservatively instead of undercounting.
  "  la t0, runtime_tx_access_list_address_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_storage_key_count; sd zero, 0(t0)\n" ++
  -- nxio8.5.2b: pass the same access-list span to the callable setup so it can
  -- seed EIP-2929 storage warmth after evm_storage_access_count is reset.
  "  la t0, runtime_tx_access_list_ptr; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_len; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_seed_fn; sd zero, 0(t0)\n" ++
  "  ld t0, 160(s2); beqz t0, .Ldtrc_access_done\n" ++
  "  li a2, 7; li t1, 1; beq t0, t1, .Ldtrc_access_field\n" ++
  "  li a2, 8; li t1, 2; beq t0, t1, .Ldtrc_access_field\n" ++
  "  li t1, 3; beq t0, t1, .Ldtrc_access_field\n" ++
  "  li t1, 4; bne t0, t1, .Ldtrc_access_list_unsupported\n" ++
  ".Ldtrc_access_field:\n" ++
  "  ld a0, 176(s2); ld a1, 184(s2); la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ldtrc_access_list_unsupported\n" ++
  "  ld t0, 176(s2); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, bsg_access_len; ld a1, 0(t1)\n" ++
  "  la a2, runtime_tx_access_list_address_count; la a3, runtime_tx_access_list_storage_key_count\n" ++
  "  jal ra, access_list_count\n" ++
  "  bnez a0, .Ldtrc_access_list_unsupported\n" ++
  "  ld t0, 176(s2); la t1, bsg_access_off; ld t1, 0(t1); add t2, t0, t1\n" ++
  "  la t0, runtime_tx_access_list_ptr; sd t2, 0(t0)\n" ++
  "  la t1, bsg_access_len; ld t2, 0(t1); la t0, runtime_tx_access_list_len; sd t2, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_seed_fn; la t1, seed_tx_access_list; sd t1, 0(t0)\n" ++
  ".Ldtrc_access_done:\n" ++
  -- coc3g.5 multi-hop: prepare the EIP-7702 authorization_list span so the callable
  -- setup can warm the recovered authorities after evm_access_account_count is reset
  -- (the spec validate_authorization adds each recovered authority to accessed_addresses;
  -- the pre-reset verdict-phase resolutions are wiped, so a CALL into a same-block-
  -- delegated authority would charge it COLD without this -> bv_fail=53 receipt over-count).
  -- type-4 only; authorization_list = inner field index 9. Parse failure leaves the
  -- globals zero (inert -> conservative over-charge, never a false-accept).
  "  la t0, runtime_tx_auth_list_ptr; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_list_len; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_warm_fn; sd zero, 0(t0)\n" ++
  "  ld t0, 160(s2); li t1, 4; bne t0, t1, .Ldtrc_auth_done\n" ++
  "  ld a0, 176(s2); ld a1, 184(s2); li a2, 9; la a3, dtrc_auth_off; la a4, dtrc_auth_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ldtrc_auth_done\n" ++
  "  ld t0, 176(s2); la t1, dtrc_auth_off; ld t1, 0(t1); add t2, t0, t1\n" ++
  "  la t0, runtime_tx_auth_list_ptr; sd t2, 0(t0)\n" ++
  "  la t1, dtrc_auth_len; ld t2, 0(t1); la t0, runtime_tx_auth_list_len; sd t2, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_warm_fn; la t1, eip7702_warm_recovered_authorities; sd t1, 0(t0)\n" ++
  ".Ldtrc_auth_done:\n" ++
  "  la t4, ecc_same_block_hit; sd zero, 0(t4)\n" ++
  "  la t4, runtime_dispatcher_input_ptr; la t5, bv_runtime_payload; addi t5, t5, 8; sd t5, 0(t4)\n" ++
  "  la t4, bv_bal_start; ld t5, 0(t4); la t4, runtime_current_bal_ptr; sd t5, 0(t4)\n" ++
  "  la t4, bv_bal_len; ld t5, 0(t4); la t4, runtime_current_bal_len; sd t5, 0(t4)\n" ++
  -- .62.2.5: arm the ECRECOVER backend for this dispatch (the guest closure
  -- links secp256k1_recover_pubkey_staged; standalone dispatch probes leave
  -- the pointer 0 and keep the legacy empty-returndata success).
  "  la t4, ecrecover_backend_ptr; la t5, secp256k1_recover_pubkey_staged; sd t5, 0(t4)\n" ++
  -- EIP-7702 `set_delegation` refunds the NEW_ACCOUNT state component into the
  -- message state-gas reservoir when the recovered authority already exists.
  -- The callable dispatcher resets its state-gas cells during setup, so compute
  -- the refund here and hand it to setup through `runtime_tx_auth_state_refund`.
  "  la t4, teer_records_ptr; la t5, basr_records; sd t5, 0(t4)\n" ++
  "  la t4, runtime_tx_auth_state_refund; sd zero, 0(t4)\n" ++
  "  ld a0, 8(s2); ld a1, 16(s2)\n" ++
  "  la t4, bv_bal_start; ld a2, 0(t4); la t4, bv_bal_len; ld a3, 0(t4)\n" ++
  "  la t4, bv_chain_id; ld a4, 0(t4); la t4, current_block_access_index; ld a5, 0(t4)\n" ++
  "  jal ra, tx_eip7702_existing_authority_refund\n" ++
  "  la t4, runtime_tx_auth_state_refund; sd a0, 0(t4)\n" ++
  -- The callable dispatcher will reread calldata_len at payload+8+round8(code_len)
  -- before it has any verdict-side bounds context. If later staging accidentally
  -- clobbers that word, ziskemu panics on the derived slot-count address instead
  -- of returning a conservative unsupported status. Recheck the exact word here.
  "  la t0, bv_runtime_payload\n" ++
  "  ld t1, 0(t0); addi t1, t1, 7; andi t1, t1, -8\n" ++
  "  add t2, t0, t1; addi t2, t2, 8; ld t3, 0(t2)\n" ++
  "  ld t4, 64(s2); bne t3, t4, .Ldtrc_stage_unsupported\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp)\n" ++
  "  jal ra, runtime_dispatcher_call\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  la t4, runtime_dispatcher_input_ptr; sd zero, 0(t4)\n" ++
  "  la t4, runtime_current_bal_ptr; sd zero, 0(t4)\n" ++
  "  la t4, runtime_current_bal_len; sd zero, 0(t4)\n" ++
  -- The callable staged payload carries the account-witness header length in
  -- the trailer word that overlaps env.eventLogLength in the live env layout.
  -- If execution produced no log data and the live count is exactly that header
  -- length, normalize it back to the empty receipt-log window before materializing
  -- receipts. Real LOG/EIP-7708 paths either advance the count or capture data.
  "  la t0, evm_log_data_used; ld t0, 0(t0); bnez t0, .Ldtrc_log_count_ready\n" ++
  "  la t0, evm_env; ld t1, 472(t0); la t2, dtrc_hdr_len; ld t2, 0(t2); bne t1, t2, .Ldtrc_log_count_ready\n" ++
  "  sd x0, 472(t0); sd x0, 480(t0)\n" ++
  ".Ldtrc_log_count_ready:\n" ++
  -- nxio8: spec-exact per-tx settlement fold (EIP-8037). dispatcher_tx_gas_settle
  -- returns a0 = gas_left + state_gas_left with the tx-error rules applied
  -- (exceptional halt burns regular gas; any error restores state gas and
  -- discards refunds) and a1 = the effective refund counter — so the bvgr
  -- consumers' `tx.gas - gas_left` formula matches
  -- `tx.gas - gas_left - state_gas_left` from fork.py process_transaction.
  "  jal ra, dispatcher_tx_gas_settle\n" ++
  "  mv s0, a0                    # effective gas_left\n" ++
  "  mv s1, a1                    # effective refund_counter\n" ++
  "  mv s2, a2                    # tx success bit (receipt status, .63.1.6.2.1)\n" ++
  "  la t4, runtime_tx_calldata_floor; ld s3, 0(t4)\n" ++
  -- .63.1.6.2.1: snapshot this tx's event-log window into the block log arena
  -- after settlement has classified the top-level tx status. A failed top-level
  -- transaction rolls back all LOGs, even logs committed by successful child calls.
  "  bnez s2, .Ldtrc_snapshot_logs\n" ++
  "  la t0, evm_env; sd x0, 472(t0); sd x0, 480(t0)\n" ++
  ".Ldtrc_snapshot_logs:\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  "  mv t3, s0                    # effective gas_left\n" ++
  "  mv a3, s1                    # effective refund_counter\n" ++
  "  mv a4, s2                    # tx success bit (receipt status, .63.1.6.2.1)\n" ++
  "  mv a1, t3                    # gas_left\n" ++
  "  mv a2, s3                    # calldata_floor\n" ++
  "  li a0, 0\n" ++
  "  j .Ldtrc_ret\n" ++
  -- Structured unsupported reason codes. Callers continue to treat any nonzero
  -- value as a conservative dispatch bail, but the code now distinguishes where
  -- the unsupported path came from for verdict/debug triage.
  ".Ldtrc_code_lookup_unsupported:\n" ++
  "  li a0, 1; j .Ldtrc_ret\n" ++
  ".Ldtrc_self_contained_unsupported:\n" ++
  "  li a0, 2; j .Ldtrc_ret\n" ++
  ".Ldtrc_bal_unsupported:\n" ++
  "  li a0, 3; j .Ldtrc_ret\n" ++
  ".Ldtrc_storage_unsupported:\n" ++
  "  li a0, 4; j .Ldtrc_ret\n" ++
  ".Ldtrc_payload_cap_unsupported:\n" ++
  "  li a0, 5; j .Ldtrc_ret\n" ++
  ".Ldtrc_stage_unsupported:\n" ++
  "  li a0, 6; j .Ldtrc_ret\n" ++
  ".Ldtrc_access_list_unsupported:\n" ++
  "  li a0, 7\n" ++
  ".Ldtrc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

end EvmAsm.Codegen
