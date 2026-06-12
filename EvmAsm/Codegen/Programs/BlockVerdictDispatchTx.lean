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
  "  li t0, 128; bgtu a0, t0, .Lscs_acct_next        # bmvmx.1.7.3: >128 slots wouldn't fit csce_keys -> skip this account (seed nothing)\n" ++
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
  "  li t0, 31; sub t0, t0, t6; add t0, t4, t0; sb t1, 0(t0)\n" ++    -- -> entry slotKey byte (31-i)
  "  addi t6, t6, 1; j .Lscs_krev\n" ++
  ".Lscs_krevd:\n" ++
  "  la t5, sahsr_u256; li t6, 0\n" ++
  ".Lscs_vrev:\n" ++
  "  li t0, 32; beq t6, t0, .Lscs_vrevd\n" ++
  "  add t0, t5, t6; lbu t1, 0(t0)\n" ++                              -- BE value byte i
  "  li t0, 63; sub t0, t0, t6; add t0, t4, t0; sb t1, 0(t0)\n" ++    -- -> entry value byte 32+(31-i)=63-i
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
  "  li t0, 31; sub t0, t0, t6; add t0, t4, t0; sb t1, 0(t0)\n" ++
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
  "  la t0, dtrc_hdr_ptr; ld a0, 0(t0); la t0, dtrc_hdr_len; ld a1, 0(t0)\n" ++
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
  "  li t0, 128; bgtu a0, t0, .Ldtrc_unsupported   # bmvmx.1.7.3: >128 storage slots wouldn't fit bvcd_keys/preload -> bail\n" ++
  "  la t0, bvcd_sc_count; sd a0, 0(t0)\n" ++
  -- fhsxz.2.4.2.57.11.6.5 (revert fix): also preload the recipient's storage_READS slots
  -- (accessed-but-not-net-changed). A reverting tx has empty storage_changes (its writes
  -- roll back) but lists the touched slots in storage_reads; without these the SSTORE-clears
  -- find no preloaded slot and undercharge (missing-slot path) -> block_regular undercount
  -- (bv_fail=41). Append the storage_reads keys after the storage_changes keys; cap total at
  -- 128 (the bvcd_keys/bvcd_preload buffer size).
  "  la t0, bvcd_acct_ptr; ld a0, 0(t0); la t0, bvcd_acct_len; ld a1, 0(t0)\n" ++
  "  la t0, bvcd_sc_count; ld t1, 0(t0); slli t2, t1, 5; la a2, bvcd_keys; add a2, a2, t2\n" ++
  "  li a3, 128; sub a3, a3, t1\n" ++
  "  jal ra, bal_recipient_storage_reads_keys\n" ++
  "  la t0, bvcd_sc_count; ld t1, 0(t0); add a0, a0, t1   # total = storage_changes + storage_reads\n" ++
  "  li t0, 128; bgtu a0, t0, .Ldtrc_unsupported\n" ++
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
  "  bnez a0, .Ldtrc_unsupported\n" ++
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
  -- ogjan: bvcd_keys[i] is 32B BIG-endian (RLP), but bv_mtx_committed's slotKey@32 is LITTLE-
  -- endian (EVM-stack limb order, preload-fed post-#8694/C.1). Byte-reverse it into dtrc_slotkey_le
  -- so exec_log_latest_value's slotKey compare (a1 vs entry@32) matches the LE snapshot; else this
  -- interacting-mtx committed-value threading silently no-ops (BE!=LE -> never found). The addrHash
  -- (a0=dtrc_recipkey) stays BE-left-aligned -- it matches the snapshot addrHash@0 (env.ADDRESS,
  -- BE, SLOAD self-match); reversing it too would BREAK the addrHash match.
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 5; la t3, bvcd_keys; add t3, t3, t2  # &bvcd_keys[i] (BE)\n" ++
  "  addi t3, t3, 31; la a1, dtrc_slotkey_le; li t4, 32\n" ++
  ".Ldtrc_klr:\n  beqz t4, .Ldtrc_klrd\n  lbu t5, 0(t3); sb t5, 0(a1); addi t3, t3, -1; addi a1, a1, 1; addi t4, t4, -1; j .Ldtrc_klr\n" ++
  ".Ldtrc_klrd:\n" ++
  "  la a1, dtrc_slotkey_le                          # a1 = LE slotKey ptr\n" ++
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
  -- bmvmx.1.7.2: conservative payload-size guard. stage_runtime_payload_code writes
  -- round8(codelen)+round8(calldata)+storage*64+584 bytes into bv_runtime_payload; if that
  -- exceeds the buffer (65536) the write would overflow into adjacent .data (gas result +
  -- bvcd_* scratch). EIP-170 bounds code to 24576 but calldata/storage are unbounded, so bail
  -- conservatively (route to the safe path) instead of corrupting state.
  "  la t0, bvcd_code_len; ld t1, 0(t0); addi t1, t1, 7; andi t1, t1, -8\n" ++   -- round8(codelen)
  "  ld t2, 64(s2); addi t2, t2, 7; andi t2, t2, -8; add t1, t1, t2\n" ++         -- + round8(calldata)
  "  la t0, bvcd_key_count; ld t2, 0(t0); slli t2, t2, 6; add t1, t1, t2\n" ++   -- + storage_count*64
  "  la t0, m29_stage_count; ld t2, 0(t0); slli t2, t2, 5; add t1, t1, t2\n" ++  -- 3vc2p.3b: + M29 hashes (count*32)
  "  addi t1, t1, 584; li t2, 65536; bgtu t1, t2, .Ldtrc_unsupported\n" ++       -- payload > buffer -> conservative bail
  "  mv a0, s2; la a1, bv_runtime_payload; la t2, bv_exec_p; ld a2, 0(t2)\n" ++
  "  la t0, bvcd_code_ptr; ld a3, 0(t0); la t0, bvcd_code_len; ld a4, 0(t0)\n" ++
  "  la a5, bvcd_preload; la t0, bvcd_key_count; ld a6, 0(t0)\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  -- 3vc2p.1: stage CALLER (env+64) + ORIGIN (env+128) = tx.sender into the runtime
  -- payload's env words, so CALLER/ORIGIN resolve once 3vc2p.4 activates them (for a
  -- top-level tx, CALLER == ORIGIN == tx.sender). The sender is derived from the
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
  "  la t3, srpc_sender_addr; addi t4, t2, 64; li t5, 0\n" ++   -- CALLER (word 2 -> +64)
  ".Ldtrc_caller:\n" ++
  "  li t6, 20; beq t5, t6, .Ldtrc_caller_d\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Ldtrc_caller\n" ++
  ".Ldtrc_caller_d:\n" ++
  "  addi t4, t2, 128; li t5, 0\n" ++                        -- ORIGIN (word 4 -> +128); t3 still = srpc_sender_addr
  ".Ldtrc_origin:\n" ++
  "  li t6, 20; beq t5, t6, .Ldtrc_origin_d\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Ldtrc_origin\n" ++
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
  "  la t3, gp_egp\n" ++
  "  ld t4, 0(t3); sd t4, 0(t2); ld t4, 8(t3); sd t4, 8(t2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(t2); ld t4, 24(t3); sd t4, 24(t2)\n" ++
  ".Ldtrc_no_gasprice:\n" ++
  -- yisv8.1: SELFBALANCE (word 1 -> env_base+32) = the recipient's own balance from the
  -- witness (balance_at_header_state_root over env.ADDRESS=recipient, ctx+72), copied
  -- verbatim (BE) into the env word — mirroring the CALLVALUE/GASPRICE u256 staging (the
  -- ACTIVE CALLVALUE proves the contract-recipient path's u256 env words are BE-direct).
  -- INERT until yisv8.2 removes SELFBALANCE(0x47) from the self-contained reject set.
  -- Conservative: a lookup miss/error leaves SELFBALANCE 0. balance_at_header_state_root
  -- preserves s-regs (s0=state ptr, s1=state len, s2=ctx survive); clobbers only dead a/t-regs.
  "  la t0, dtrc_hdr_ptr; ld a0, 0(t0)\n  la t0, dtrc_hdr_len; ld a1, 0(t0)\n" ++   -- .57.11.6.5: mtx-gated witness-lookup header (resolved at dispatch entry)
  "  addi a2, s2, 72\n" ++                       -- recipient addr (ctx+72)
  "  mv a3, s0; mv a4, s1\n" ++                   -- witness state ptr/len
  "  la a5, yisv8_self_bal\n" ++
  "  jal ra, balance_at_header_state_root\n" ++
  "  bnez a0, .Ldtrc_no_selfbal\n" ++             -- lookup miss/error -> leave SELFBALANCE 0
  "  la t0, bv_runtime_payload\n" ++
  "  la t5, srpc_env_base; ld t1, 0(t5)\n" ++                -- 3vc2p.5: env_base from stage_runtime_payload_code
  "  add t2, t0, t1; addi t2, t2, 32\n" ++                   -- t2 = &SELFBALANCE word (env_base+32)
  "  la t3, yisv8_self_bal\n" ++
  "  ld t4, 0(t3); sd t4, 0(t2); ld t4, 8(t3); sd t4, 8(t2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(t2); ld t4, 24(t3); sd t4, 24(t2)\n" ++
  ".Ldtrc_no_selfbal:\n" ++
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
  -- nxio8: spec-exact per-tx settlement fold (EIP-8037). dispatcher_tx_gas_settle
  -- returns a0 = gas_left + state_gas_left with the tx-error rules applied
  -- (exceptional halt burns regular gas; any error restores state gas and
  -- discards refunds) and a1 = the effective refund counter — so the bvgr
  -- consumers' `tx.gas - gas_left` formula matches
  -- `tx.gas - gas_left - state_gas_left` from fork.py process_transaction.
  "  jal ra, dispatcher_tx_gas_settle\n" ++
  "  mv t3, a0                    # effective gas_left\n" ++
  "  mv a3, a1                    # effective refund_counter\n" ++
  "  mv a4, a2                    # tx success bit (receipt status, .63.1.6.2.1)\n" ++
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
