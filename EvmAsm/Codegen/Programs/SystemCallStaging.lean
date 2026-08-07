/-
  EvmAsm.Codegen.Programs.SystemCallStaging

  `stage_system_call_payload` (bead evm-asm-8uld3.2.1.2, EIP-7002/7251/2935/4788) —
  stage the runtime payload for an Amsterdam system call
  (process_unchecked_system_transaction / process_checked_system_transaction):
  caller = origin = SYSTEM_ADDRESS (0xff..fe), value 0, gas 30M, the target
  predeploy's code. Optional calldata comes from globals `ssc_calldata_ptr` /
  `ssc_calldata_len` (ctx@56/64); 7002/7251 leave both zero (empty data).
  Reuses `stage_runtime_payload_code` with a synthesized SYSTEM context record,
  then overwrites CALLER (env_base+64) + ORIGIN (env_base+128) with
  SYSTEM_ADDRESS.

  This is the staging half of the shared system-call harness (8uld3.2.1); the depth-0
  RETURN-data capture (8uld3.2.1a, #8681) + the compose step (8uld3.2.1c) close the loop.
  Request-predeploy storage is resolved by the authenticated state path; this stage passes
  no BAL-sourced storage rows. The caller looks up the predeploy code
  (code_at_header_state_root) and provides the block exec payload.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.BlockVerdictContractStage
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_system_call_payload
    a0 = target (predeploy) address ptr (20-byte canonical)
    a1 = predeploy code ptr        a2 = predeploy code length
    a3 = block exec payload ptr (stage_runtime_payload_code's env source)
    a4 = output payload buffer ptr
    a0 (output) = 0 ok / 1 unsupported (stage_runtime_payload_code rejected).
    Stages caller=origin=SYSTEM_ADDRESS, value 0, gas 30M, code=predeploy.
    Calldata: `ssc_calldata_ptr` / `ssc_calldata_len` (default 0 = empty). -/
def stageSystemCallPayloadFunction : String :=
  "stage_system_call_payload:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                    # target addr\n" ++
  "  mv s1, a1                    # code ptr\n" ++
  "  mv s2, a2                    # code len\n" ++
  "  mv s3, a3                    # exec payload\n" ++
  "  mv s4, a4                    # out payload\n" ++
  -- Build the SYSTEM context record in scc_ctx (192 B): status@0=0, gas@40=30M,
  -- is_creation@48=0, calldata from ssc_calldata_*, recipient@72=target, value@96=0.
  "  la t0, scc_ctx\n" ++
  "  mv t1, t0; li t2, 24\n" ++
  ".Lscc_zero:\n" ++
  "  sd zero, 0(t1); addi t1, t1, 8; addi t2, t2, -1; bnez t2, .Lscc_zero\n" ++
  liAmsterdamSystemTransactionGas "t1" ++           -- t1 = 30000000
  "  sd t1, 40(t0)\n" ++                            -- gas@40
  -- Optional system-tx calldata (EIP-2935 parent_hash / EIP-4788 parent_beacon_root).
  -- 7002/7251 leave ssc_calldata_len=0 so ctx@56/64 stay zero (empty data).
  "  la t1, ssc_calldata_ptr; ld t1, 0(t1); sd t1, 56(t0)\n" ++
  "  la t1, ssc_calldata_len; ld t1, 0(t1); sd t1, 64(t0)\n" ++
  "  addi t1, t0, 72; mv t2, s0; li t3, 20\n" ++    -- recipient@72 = target (20B)
  ".Lscc_recip:\n" ++
  "  beqz t3, .Lscc_recip_d\n" ++
  "  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, 1; addi t1, t1, 1; addi t3, t3, -1; j .Lscc_recip\n" ++
  ".Lscc_recip_d:\n" ++
  -- fhsxz.2.4.2.66.1: conservative payload-size guard (mirrors bmvmx.1.7.2 in
  -- dispatch_tx_runtime_code). stage_runtime_payload_code zeroes + writes
  -- round8(codelen) + round8(calldata) + m29_count*32 + 584 bytes into the output
  -- buffer with no bound of its own; every verdict call site passes c1_staging
  -- (c1StagingBytes, BlockVerdictParams.lean — shared constant, .66.1.2). Predeploy
  -- code is read from the witness and NOT EIP-170-bounded (the system_contract_errors
  -- EEST predeploys are 72946 B), so an unchecked copy clobbers the .data globals
  -- above c1_staging. Bail (a0=1, unsupported -> requests-hash fail) instead of
  -- corrupting .data.
  "  addi t1, s2, 7; andi t1, t1, -8\n" ++                                         -- round8(codelen)
  "  la t0, ssc_calldata_len; ld t2, 0(t0); addi t2, t2, 7; andi t2, t2, -8; add t1, t1, t2\n" ++
  "  la t0, m29_stage_count; ld t2, 0(t0); slli t2, t2, 5; add t1, t1, t2\n" ++    -- + M29 hashes (count*32)
  -- Account-witness trailer (header+state+codes) is staged after the code body
  -- via stage_runtime_payload_witness_context; include its byte count so a
  -- large multi-block witness cannot overrun c1_staging (DispatchTx does the
  -- same sum before its user-tx staging).
  "  la t0, svf_parent_rlp_len; ld t2, 0(t0); add t1, t1, t2\n" ++
  "  la t0, svf_witness_len; ld t2, 0(t0); add t1, t1, t2\n" ++
  "  la t0, svf_codes_len; ld t2, 0(t0); add t1, t1, t2\n" ++
  "  addi t1, t1, 584; li t2, " ++ toString c1StagingBytes ++ "; bgtu t1, t2, .Lscc_toobig\n" ++              -- payload > buffer -> bail
  -- stage_runtime_payload_code(ctx, out, exec, code, codelen, null, 0)
  -- GH #11176: request-predeploy storage is read through the authenticated,
  -- demand-driven state path. Do not seed ordinary execution-log rows from
  -- BAL data before the call; both storage arguments are intentionally empty.
  -- This literal-zero production contract is pinned by the guard below.
  "  la a0, scc_ctx\n  mv a1, s4\n  mv a2, s3\n  mv a3, s1\n  mv a4, s2\n" ++
  "  li a5, 0; li a6, 0\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Lscc_ret\n" ++                        -- unsupported -> propagate
  -- Stage the same parent-header + witness.state/codes trailer user txs get
  -- (DispatchTx → stage_runtime_payload_witness_context). Without it,
  -- runtime_dispatcher leaves env+584 header_len=0 and every cold SLOAD's
  -- tier-3 slot_at_header_state_root returns status 4 (header parse fail) →
  -- value 0. Same-block prior-tx writes mask this via tier-2; multi-block
  -- empty-tx blocks (7002 queue from parent) fail → #11547 state-root.
  "  mv a0, s4\n" ++
  "  la t0, svf_parent_rlp; ld a1, 0(t0); la t0, svf_parent_rlp_len; ld a2, 0(t0)\n" ++
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, stage_runtime_payload_witness_context\n" ++
  -- CALLER (env_base+64) + ORIGIN (env_base+128) = SYSTEM_ADDRESS (mirror 3vc2p.1).
  -- 8uld3.2.3.3.1 Fix4: write the 20 address bytes BYTE-REVERSED (dst byte 19-i <- src byte i).
  -- `evm_env_load` copies the env word VERBATIM as 4 little-endian limbs to the EVM stack, so an
  -- address must sit in env in little-endian (LSB at +0), right-aligned. The big-endian write
  -- (mirrored from 3vc2p.1, which is INERT — self-contained mtx recipients never run CALLER) made
  -- the 7002/7251 predeploy see caller != SYSTEM and return the fee-getter result instead of
  -- processing the queue. Same BE->LE class as the storage preload (#8694).
  "  la t5, srpc_env_base; ld t1, 0(t5)\n" ++
  "  add t2, s4, t1\n" ++                            -- t2 = &env_words
  "  la t3, scc_system_addr; addi t4, t2, 64; li t5, 0\n" ++
  ".Lscc_caller:\n" ++
  "  li t6, 20; beq t5, t6, .Lscc_caller_d\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); li a5, 19; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lscc_caller\n" ++
  ".Lscc_caller_d:\n" ++
  "  addi t4, t2, 128; li t5, 0\n" ++
  ".Lscc_origin:\n" ++
  "  li t6, 20; beq t5, t6, .Lscc_origin_d\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); li a5, 19; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lscc_origin\n" ++
  ".Lscc_origin_d:\n" ++
  "  li a0, 0\n" ++
  "  j .Lscc_ret\n" ++
  ".Lscc_toobig:\n" ++
  "  li a0, 1\n" ++
  ".Lscc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! Production system-call staging keeps both generic preload arguments empty.
    The retained nonzero input path is standalone/probe-only. -/
#guard (stageSystemCallPayloadFunction.splitOn "  li a5, 0; li a6, 0\n").length = 2

/-! ## stage_system_call (8uld3.2.1c) — compose the full system call -> return_data.
    a0 = target (predeploy) addr ptr   a1 = predeploy code ptr   a2 = code length
    a3 = block exec payload ptr        a4 = output payload buffer ptr
    Returns: a0 = system_call_returndata ptr, a1 = system_call_returndata_len,
             a2 = 0 ok / 1 staging unsupported (no dispatch run).
    Stages the SYSTEM payload, runs the callable runtime dispatcher with
    system_call_mode=1 so the predeploy's depth-0 RETURN is captured (NoopHalt
    #8681) into system_call_returndata, then clears the flag. -/
def stageSystemCallFunction : String :=
  "stage_system_call:\n" ++
  -- runtime_dispatcher_call sets sp = lp64_sp_top and grows its own stack down from
  -- there, clobbering any caller-frame this function might keep on the stack across
  -- the call. So save ra + the scratch s0 in GLOBALS (ssc_saved_ra/ssc_saved_s0), not
  -- on the stack. Non-reentrant, which is fine (the dispatched predeploy never re-enters).
  "  la t0, ssc_saved_ra; sd ra, 0(t0)\n" ++
  "  la t0, ssc_saved_s0; sd s0, 0(t0)\n" ++
  -- `process_checked_system_transaction` reads its target through the real
  -- TransactionState before it calls `process_unchecked_system_transaction`.
  -- Its four request-predeploy callers enter this shared dispatch seam with the
  -- canonical 20-byte target in a0, so record the matching access here rather than
  -- duplicating four per-predeploy hooks.  t1 is restored by account_read_record,
  -- preserving the target for the staging ABI.
  "  mv t1, a0; jal ra, account_read_record; mv a0, t1\n" ++
  "  mv s0, a4                    # out payload ptr (used only pre-dispatch)\n" ++
  -- 87gow: reset the captured return-data length to 0 BEFORE each system call. The capture
  -- (NoopHalt) writes system_call_returndata_len ONLY on a depth-0 RETURN within
  -- systemCallReturndataMaxBytes; a
  -- predeploy that ends in a clean STOP (empty return_data, spec fork.py:976-997) or an
  -- oversized return does NOT write it. Without this reset the consolidation system call would
  -- inherit the withdrawal call's stale length -> a spurious consolidation request body ->
  -- wrong header.requests_hash -> false-reject/accept. Spec: each return_data is a SEPARATE
  -- MessageCallOutput; empty == len 0.
  "  li t0, 0; la t1, system_call_returndata_len; sd t0, 0(t1)\n" ++
  "  li t0, 1; la t1, system_call_mode; sd t0, 0(t1)\n" ++       -- enable depth-0 RETURN capture
  -- Drop any leftover user-tx auth callback before re-entering the dispatcher
  -- (code44: system path must not re-run eip7702_auth_state_prepare).
  "  la t1, runtime_tx_auth_exec_fn; sd zero, 0(t1)\n" ++
  "  jal ra, stage_system_call_payload\n" ++                     -- a0..a4 already set by caller
  "  bnez a0, .Lssc_fail\n" ++                                   -- staging rejected -> bail (no dispatch)
  "  addi t1, s0, 8; la t0, runtime_dispatcher_input_ptr; sd t1, 0(t0)\n" ++   -- input = out + 8 (skip codelen header)
  "  jal ra, runtime_dispatcher_call\n" ++                       -- run predeploy; RETURN -> system_call_returndata
  "  la t0, runtime_dispatcher_input_ptr; sd zero, 0(t0)\n" ++   -- clear input ptr
  "  li t0, 0; la t1, system_call_mode; sd t0, 0(t1)\n" ++       -- disable capture
  "  la a0, system_call_returndata\n" ++
  "  la t0, system_call_returndata_len; ld a1, 0(t0)\n" ++
  "  li a2, 0\n" ++
  "  j .Lssc_ret\n" ++
  ".Lssc_fail:\n" ++
  "  li t0, 0; la t1, system_call_mode; sd t0, 0(t1)\n" ++       -- restore flag on the staging-fail path
  "  la a0, system_call_returndata; li a1, 0; li a2, 1\n" ++
  ".Lssc_ret:\n" ++
  "  la t0, ssc_saved_s0; ld s0, 0(t0)\n" ++
  "  la t0, ssc_saved_ra; ld ra, 0(t0)\n" ++
  "  ret"

/-! ## process_block_start_system_transactions (GH #11431)

    Spec pin `amsterdam/forks/.../fork.py:897-910` `apply_body`:
      process_unchecked_system_transaction(BEACON_ROOTS, parent_beacon_block_root)
      process_unchecked_system_transaction(HISTORY_STORAGE, parent_hash)
      track_ancestor_access(1)
    before the user-tx loop. BAI = 0 for both (`block_access_index` starts at 0).

    Replaces the formula path (`system_write_descriptors` +
    `append_modeled_system_storage_tuple_rows` seed-only + identity fail-65):
    each contract is looked up via `code_at_header_state_root`, executed through
    `stage_system_call` with the real 32-byte calldata, then
    `account_writes_emit_builder_tx` + `write_sets_incorporate_tx` (which emits
    BAL storage changes at `current_block_access_index` and merges into the
    block map for tier-2 SLOAD) + `read_sets_incorporate_tx`.

    Unchecked semantics: code_at miss / empty code → skip dispatch (no write),
    still mark OAO. Staging failure → a0=1 (conservative bail).

    Calldata layout (SystemWrites.lean / SSZ):
      parent_beacon_block_root @ SSZ_BASE+24 = bv_exec_p - 36
      parent_hash             @ SSZ_BASE+60 = bv_exec_p + 0
    a0 (out) = 0 ok / 1 fail. -/
def processBlockStartSystemTransactionsFunction : String :=
  "process_block_start_system_transactions:\n" ++
  "  la t0, pbsst_saved_ra; sd ra, 0(t0)\n" ++
  -- BAI=0 for both startup system transactions (fork.py apply_body before loop).
  "  la t0, current_block_access_index; sd zero, 0(t0)\n" ++
  -- Clear optional calldata; each arm installs its own 32B blob.
  "  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)\n" ++
  -- Witness cells for cold SLOAD / code_at (same as deferred 7002 path).
  "  la t0, svf_witness; ld t1, 0(t0); la t2, bv_witness_state_ptr; sd t1, 0(t2)\n" ++
  "  la t0, svf_witness_len; ld t1, 0(t0); la t2, bv_witness_state_len; sd t1, 0(t2)\n" ++
  -- == EIP-4788 BEACON_ROOTS (first in apply_body) ==
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bsr_addr_4788\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  -- The spec records the target read before resolving its code. Keep this outside
  -- the executable-code gate so an absent/codeless predeploy still contributes its
  -- empty AccountChanges row while the unchecked system call itself is skipped.
  "  mv t0, a0; mv t1, a1; mv a0, a2; jal ra, account_read_record; mv a0, t0; mv a1, t1\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  -- process_unchecked (fork.py:788): no code → run nothing, continue. Distinguishes
  -- EMPTY_CODE_HASH (case A no-op) from status-5 missing preimage of a real hash
  -- (case B reject). Pattern: BlockVerdictDispatchTx materialize (#11520 gate).
  "  li t0, 1; beq a0, t0, .Lpbs_4788_skip\n" ++
  "  li t0, 5; bne a0, t0, .Lpbs_4788_lookup_done\n" ++
  "  la t0, cahsr_acct_struct; addi t0, t0, 72; la t1, chahsr_empty_code_hash\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lpbs_4788_lookup_done\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lpbs_4788_lookup_done\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lpbs_4788_lookup_done\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lpbs_4788_lookup_done\n" ++
  "  j .Lpbs_4788_skip\n" ++
  ".Lpbs_4788_lookup_done:\n" ++
  "  bnez a0, .Lpbs_fail\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Lpbs_4788_skip\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3\n" ++
  "  la t0, pbsst_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, pbsst_code_len; sd t3, 0(t0)\n" ++
  -- calldata = parent_beacon_block_root @ bv_exec_p - 36
  "  la t0, bv_exec_p; ld t1, 0(t0); addi t1, t1, -36\n" ++
  "  la t0, ssc_calldata_ptr; sd t1, 0(t0); li t1, 32; la t0, ssc_calldata_len; sd t1, 0(t0)\n" ++
  "  la a0, bsr_addr_4788\n" ++
  "  la t0, pbsst_code_ptr; ld a1, 0(t0); la t0, pbsst_code_len; ld a2, 0(t0)\n" ++
  "  la t0, bv_exec_p; ld a3, 0(t0); la a4, c1_staging\n" ++
  "  jal ra, stage_system_call\n" ++
  "  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)\n" ++
  "  bnez a2, .Lpbs_fail\n" ++
  -- Storage map + BAL BAI=0 via write_sets_incorporate_tx (bal_emit inside).
  -- Account-write map: clear any tx-local rows without block merge — system
  -- contracts are storage-authority only here (formula path never seeded AW);
  -- merging TOUCHED-only AW rows for 2935/4788 regressed CREATE Present-None
  -- on 01114 (optionalState flipped 0→1).
  "  la t0, tx_account_writes_count; sd zero, 0(t0)\n" ++
  "  jal ra, write_sets_incorporate_tx\n" ++
  "  jal ra, read_sets_incorporate_tx\n" ++
  ".Lpbs_4788_skip:\n" ++
  -- == EIP-2935 HISTORY_STORAGE ==
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bsr_addr_2935\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  -- As above, record the lookup even when the target is absent or codeless.
  "  mv t0, a0; mv t1, a1; mv a0, a2; jal ra, account_read_record; mv a0, t0; mv a1, t1\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  -- Same EMPTY_CODE_HASH vs missing-preimage split as 4788 (fork.py:788; #11520).
  "  li t0, 1; beq a0, t0, .Lpbs_2935_skip\n" ++
  "  li t0, 5; bne a0, t0, .Lpbs_2935_lookup_done\n" ++
  "  la t0, cahsr_acct_struct; addi t0, t0, 72; la t1, chahsr_empty_code_hash\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lpbs_2935_lookup_done\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lpbs_2935_lookup_done\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lpbs_2935_lookup_done\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lpbs_2935_lookup_done\n" ++
  "  j .Lpbs_2935_skip\n" ++
  ".Lpbs_2935_lookup_done:\n" ++
  "  bnez a0, .Lpbs_fail\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Lpbs_2935_skip\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3\n" ++
  "  la t0, pbsst_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, pbsst_code_len; sd t3, 0(t0)\n" ++
  -- calldata = parent_hash @ bv_exec_p + 0
  "  la t0, bv_exec_p; ld t1, 0(t0)\n" ++
  "  la t0, ssc_calldata_ptr; sd t1, 0(t0); li t1, 32; la t0, ssc_calldata_len; sd t1, 0(t0)\n" ++
  "  la a0, bsr_addr_2935\n" ++
  "  la t0, pbsst_code_ptr; ld a1, 0(t0); la t0, pbsst_code_len; ld a2, 0(t0)\n" ++
  "  la t0, bv_exec_p; ld a3, 0(t0); la a4, c1_staging\n" ++
  "  jal ra, stage_system_call\n" ++
  "  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)\n" ++
  "  bnez a2, .Lpbs_fail\n" ++
  "  la t0, tx_account_writes_count; sd zero, 0(t0)\n" ++
  "  jal ra, write_sets_incorporate_tx\n" ++
  "  jal ra, read_sets_incorporate_tx\n" ++
  ".Lpbs_2935_skip:\n" ++
  -- fork.py:908 track_ancestor_access(1) — host-side unconditional after both
  -- system txs (not a 2935 bytecode side effect). Under-mark is FA-ward for
  -- BLOCKHASH witness coverage (#11378 FunctionTail).
  "  la t0, evm_oldest_ancestor_offset; ld t1, 0(t0); bnez t1, .Lpbs_ok\n" ++
  "  li t1, 1; sd t1, 0(t0)\n" ++
  ".Lpbs_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lpbs_ret\n" ++
  ".Lpbs_fail:\n" ++
  "  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lpbs_ret:\n" ++
  "  la t0, pbsst_saved_ra; ld ra, 0(t0)\n" ++
  "  ret"

/-! ## derive_withdrawal_requests (8uld3.2b, EIP-7002)

    Run the WITHDRAWAL_REQUEST_PREDEPLOY (0x00000961Ef480Eb55e80D19ad83579A64c007002)
    system call and surface its return_data as the withdrawal-request BODY. Per
    `process_general_purpose_requests` (fork.py):
      system_withdrawal_tx_output =
        process_checked_system_transaction(WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS, b'')
      if len(return_data) > 0: requests.append(WITHDRAWAL_REQUEST_TYPE + return_data)
    The 0x01 WITHDRAWAL_REQUEST_TYPE prefix is the request-list framing added by
    `assemble_execution_requests` (a2/a3 = withdrawal body) / RequestsHash at hash time,
    so the body produced here is the raw return_data (each request is 76 B = source 20 +
    pubkey 48 + amount 8; ≤ MAX_WITHDRAWAL_REQUESTS_PER_BLOCK=16). Empty return_data -> body
    len 0 (the caller appends nothing). Thin compose over `stage_system_call` (8uld3.2.1c):
      a0 = predeploy code ptr   a1 = code len   a2 = block exec payload ptr   a3 = output buffer
    Returns (tail-call to stage_system_call):
      a0 = withdrawal body ptr (= system_call_returndata)   a1 = body len   a2 = 0 ok / 1 unsupported -/
def deriveWithdrawalRequests_prog : Program :=
  [ .MV .x14 .x13,
    .MV .x13 .x12,
    .MV .x12 .x11,
    .MV .x11 .x10,
    .AUIPC .x10 (laHi GuestAddrs.withdrawal_request_predeploy_addr (GuestAddrs.derive_withdrawal_requests + 16)),
    .ADDI .x10 .x10 (laLo GuestAddrs.withdrawal_request_predeploy_addr (GuestAddrs.derive_withdrawal_requests + 16)),
    .JAL .x0 (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_withdrawal_requests + 24)) ]

/-- Reloc side-table for `deriveWithdrawalRequests_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def deriveWithdrawalRequests_relocs : RelocTable :=
  [ (4, .la .x10 "withdrawal_request_predeploy_addr"),
    (6, .jal .x0 "stage_system_call") ]

def deriveWithdrawalRequestsFunction : String :=
  "derive_withdrawal_requests:\n" ++ emitProgramR deriveWithdrawalRequests_prog deriveWithdrawalRequests_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `deriveWithdrawalRequests_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem deriveWithdrawalRequestsFunction_eq_prog :
    deriveWithdrawalRequestsFunction = "derive_withdrawal_requests:\n" ++ emitProgramR deriveWithdrawalRequests_prog deriveWithdrawalRequests_relocs := rfl

#guard deriveWithdrawalRequestsFunction.startsWith "derive_withdrawal_requests:\n"
#guard deriveWithdrawalRequests_prog.length = 7
/-- WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS (EIP-7002), 20 bytes big-endian. Referenced by
    `derive_withdrawal_requests`; emit alongside it in any unit that links the function. -/
def withdrawalRequestPredeployAddrData : String :=
  ".balign 8\n" ++
  "withdrawal_request_predeploy_addr:\n" ++
  "  .byte 0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5, 0x5e, 0x80, 0xd1, 0x9a, 0xd8, 0x35, 0x79, 0xa6, 0x4c, 0x00, 0x70, 0x02\n"

/-! ## derive_consolidation_requests (8uld3.3, EIP-7251)

    Run the CONSOLIDATION_REQUEST_PREDEPLOY (0x0000BBdDc7CE488642fb579F8B00f3a590007251)
    system call and surface its return_data as the consolidation-request BODY. Per
    `process_general_purpose_requests` (fork.py):
      system_consolidation_tx_output =
        process_checked_system_transaction(CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS, b'')
      if len(return_data) > 0: requests.append(CONSOLIDATION_REQUEST_TYPE + return_data)
    The 0x02 CONSOLIDATION_REQUEST_TYPE prefix is the request-list framing added by
    `assemble_execution_requests` (a4/a5 = consolidation body) / RequestsHash at hash time,
    so the body produced here is the raw return_data (each request is 116 B = source 20 +
    source_pubkey 48 + target_pubkey 48). Empty return_data -> body len 0 (caller appends
    nothing). Identical compose to `derive_withdrawal_requests`, only the predeploy differs:
      a0 = predeploy code ptr   a1 = code len   a2 = block exec payload ptr   a3 = output buffer
    Returns (tail-call to stage_system_call):
      a0 = consolidation body ptr (= system_call_returndata)   a1 = body len   a2 = 0 ok / 1 unsupported -/
def deriveConsolidationRequests_prog : Program :=
  [ .MV .x14 .x13,
    .MV .x13 .x12,
    .MV .x12 .x11,
    .MV .x11 .x10,
    .AUIPC .x10 (laHi GuestAddrs.consolidation_request_predeploy_addr (GuestAddrs.derive_consolidation_requests + 16)),
    .ADDI .x10 .x10 (laLo GuestAddrs.consolidation_request_predeploy_addr (GuestAddrs.derive_consolidation_requests + 16)),
    .JAL .x0 (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_consolidation_requests + 24)) ]

/-- Reloc side-table for `deriveConsolidationRequests_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def deriveConsolidationRequests_relocs : RelocTable :=
  [ (4, .la .x10 "consolidation_request_predeploy_addr"),
    (6, .jal .x0 "stage_system_call") ]

def deriveConsolidationRequestsFunction : String :=
  "derive_consolidation_requests:\n" ++ emitProgramR deriveConsolidationRequests_prog deriveConsolidationRequests_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `deriveConsolidationRequests_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem deriveConsolidationRequestsFunction_eq_prog :
    deriveConsolidationRequestsFunction = "derive_consolidation_requests:\n" ++ emitProgramR deriveConsolidationRequests_prog deriveConsolidationRequests_relocs := rfl

#guard deriveConsolidationRequestsFunction.startsWith "derive_consolidation_requests:\n"
#guard deriveConsolidationRequests_prog.length = 7
/-- CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS (EIP-7251), 20 bytes big-endian. Referenced by
    `derive_consolidation_requests`; emit alongside it in any unit that links the function. -/
def consolidationRequestPredeployAddrData : String :=
  ".balign 8\n" ++
  "consolidation_request_predeploy_addr:\n" ++
  "  .byte 0x00, 0x00, 0xbb, 0xdd, 0xc7, 0xce, 0x48, 0x86, 0x42, 0xfb, 0x57, 0x9f, 0x8b, 0x00, 0xf3, 0xa5, 0x90, 0x00, 0x72, 0x51\n"

/-- BUILDER_DEPOSIT_CONTRACT_ADDRESS + BUILDER_EXIT_CONTRACT_ADDRESS (EIP-8282,
    v0.6.0 fork.py:141-146), 20 bytes big-endian each. Referenced by the
    block-verdict builder checked-system-tx code prechecks. -/
def builderContractAddrData : String :=
  ".balign 8\n" ++
  "builder_deposit_contract_addr:\n" ++
  "  .byte 0x00, 0x00, 0xbf, 0xf4, 0x69, 0x84, 0xe3, 0x72, 0x56, 0x91, 0xfa, 0x54, 0x0a, 0x8c, 0x75, 0x89, 0x30, 0x0d, 0x82, 0x82\n" ++
  ".balign 8\n" ++
  "builder_exit_contract_addr:\n" ++
  "  .byte 0x00, 0x00, 0x64, 0xd6, 0x78, 0x50, 0x5a, 0xd4, 0x8f, 0x8c, 0xcb, 0x09, 0x3b, 0xc6, 0x56, 0x13, 0x80, 0x0e, 0x82, 0x82\n"

/-! ## EIP-8282 builder request derivation

The builder deposit and exit contracts use the same checked system-call path as
the EIP-7002/7251 request predeploys. These thin adapters keep the ABI explicit:
`a0=code`, `a1=code_len`, `a2=block_exec_payload`, `a3=staging_buffer`, and
return `(return_data_ptr, return_data_len, status)`.
-/

def deriveBuilderDepositRequestsFunction : String :=
  "derive_builder_deposit_requests:\n" ++
  "  mv a4, a3; mv a3, a2; mv a2, a1; mv a1, a0\n" ++
  "  la a0, builder_deposit_contract_addr\n" ++
  "  j stage_system_call\n"

def deriveBuilderExitRequestsFunction : String :=
  "derive_builder_exit_requests:\n" ++
  "  mv a4, a3; mv a3, a2; mv a2, a1; mv a1, a0\n" ++
  "  la a0, builder_exit_contract_addr\n" ++
  "  j stage_system_call\n"

/-! ## derive_block_system_requests (probe-only glue; #11156)

    Historical combined wrapper: run BOTH system-call request derivations — withdrawal
    (EIP-7002) then consolidation (EIP-7251) — and copy each return_data body to a STABLE
    buffer (`dbsr_*`). The live guest no longer jals this symbol: deferred system-request
    staging inlines the same sequence (and also deposits/exits). Kept for the
    `zisk_derive_block_system_requests` probe unit only. **KEEP** `deriveBlockSystemRequestsData`
    — `dbsr_wbody`/`dbsr_cbody`/… are still written by the inlined guest path and read by
    `requests_hash_verify`.
      a0 = withdrawal predeploy code ptr   a1 = wcode len
      a2 = consolidation predeploy code ptr a3 = ccode len
      a4 = block exec payload ptr           a5 = staging output buffer ptr (reused per call)
    Writes: dbsr_wbody + dbsr_wlen; dbsr_cbody + dbsr_clen.
    Returns a0 = 0 ok / 1 = a system call's staging was unsupported. -/
def deriveBlockSystemRequestsFunction : String :=
  "derive_block_system_requests:\n" ++
  "  la t0, dbsr_saved_ra; sd ra, 0(t0)\n" ++
  -- stash the consolidation args + exec + staging (the dispatcher clobbers everything)
  "  la t0, dbsr_ccode; sd a2, 0(t0)\n" ++
  "  la t0, dbsr_in_clen; sd a3, 0(t0)\n" ++
  "  la t0, dbsr_exec; sd a4, 0(t0)\n" ++
  "  la t0, dbsr_staging; sd a5, 0(t0)\n" ++
  -- derive withdrawal: derive_withdrawal_requests(a0=wcode, a1=wlen, a2=exec, a3=staging)
  "  mv a2, a4; mv a3, a5\n" ++
  "  jal ra, derive_withdrawal_requests\n" ++          -- a0=wbody, a1=wlen, a2=status
  "  bnez a2, .Ldbsr_fail\n" ++
  "  la t0, dbsr_wlen; sd a1, 0(t0)\n" ++
  "  mv t1, a0; la t2, dbsr_wbody; mv t3, a1\n" ++
  ".Ldbsr_wcopy:\n" ++
  "  beqz t3, .Ldbsr_wcopy_d; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Ldbsr_wcopy\n" ++
  ".Ldbsr_wcopy_d:\n" ++
  -- Each system predeploy is its own TransactionState.  Merge and clear this
  -- completed withdrawal call before beginning consolidation, exactly as
  -- incorporate_tx_into_block does for ordinary transactions.
  "  jal ra, read_sets_incorporate_tx\n" ++
  -- derive consolidation: derive_consolidation_requests(a0=ccode, a1=clen, a2=exec, a3=staging)
  "  la t0, dbsr_ccode; ld a0, 0(t0); la t0, dbsr_in_clen; ld a1, 0(t0)\n" ++
  "  la t0, dbsr_exec; ld a2, 0(t0); la t0, dbsr_staging; ld a3, 0(t0)\n" ++
  "  jal ra, derive_consolidation_requests\n" ++       -- a0=cbody, a1=clen, a2=status
  "  bnez a2, .Ldbsr_fail\n" ++
  "  la t0, dbsr_clen; sd a1, 0(t0)\n" ++
  "  mv t1, a0; la t2, dbsr_cbody; mv t3, a1\n" ++
  ".Ldbsr_ccopy:\n" ++
  "  beqz t3, .Ldbsr_ccopy_d; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Ldbsr_ccopy\n" ++
  ".Ldbsr_ccopy_d:\n" ++
  "  jal ra, read_sets_incorporate_tx\n" ++
  "  li a0, 0; j .Ldbsr_ret\n" ++
  ".Ldbsr_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ldbsr_ret:\n" ++
  "  la t0, dbsr_saved_ra; ld ra, 0(t0); ret\n"

/-- Globals for `derive_block_system_requests` (saved state across the dispatcher runs +
    the two stable body buffers). Bodies are bounded: withdrawals ≤ 16×76, consolidations
    ≤ a similar block cap; 2048 each is ample. -/
def deriveBlockSystemRequestsData : String :=
  ".balign 8\n" ++
  "dbsr_saved_ra:\n  .zero 8\n" ++
  "dbsr_ccode:\n  .zero 8\n" ++
  "dbsr_in_clen:\n  .zero 8\n" ++
  "dbsr_exec:\n  .zero 8\n" ++
  "dbsr_staging:\n  .zero 8\n" ++
  "dbsr_wlen:\n  .zero 8\n" ++
  "dbsr_clen:\n  .zero 8\n" ++
  "dbsr_bdlen:\n  .zero 8\n" ++
  "dbsr_belen:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "dbsr_wbody:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "dbsr_cbody:\n  .zero 2048\n"
  ++ ".balign 8\n" ++
  "dbsr_bdbody:\n  .zero 12288\n" ++
  ".balign 8\n" ++
  "dbsr_bebody:\n  .zero 2048\n" ++
  "aer_bd_ptr:\n  .zero 8\naer_bd_len:\n  .zero 8\n" ++
  "aer_be_ptr:\n  .zero 8\naer_be_len:\n  .zero 8\n"

/-- `zisk_stage_system_call_payload`: probe. Stages a synthetic predeploy + asserts the
    SYSTEM-specific fields: code length @+0, gas @env_base+448 == 30M, CALLER @env_base+64
    == SYSTEM_ADDRESS. (env_base read from srpc_env_base.)
    Output: +0 codelen, +8 gas, +16 caller_ok(1/0), +24 stage status. -/
def ziskStageSystemCallPayloadPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, scc_probe_target\n  la a1, scc_probe_code\n  li a2, 6\n  la a3, scc_probe_exec\n  la a4, scc_probe_out\n" ++
  "  jal ra, stage_system_call_payload\n" ++
  "  mv s0, a0\n" ++                                 -- stage status
  "  li t0, 0xa0010000\n" ++
  "  la t1, scc_probe_out\n  ld t2, 0(t1)\n  sd t2, 0(t0)\n" ++   -- codelen @ payload+0
  "  la t5, srpc_env_base; ld t1, 0(t5)\n" ++
  "  la t2, scc_probe_out; add t2, t2, t1\n" ++      -- &env_words
  "  ld t3, 448(t2)\n  sd t3, 8(t0)\n" ++            -- gas @ env_base+448
  -- CALLER @ env_base+64 == scc_system_addr (20B) ?
  "  addi t3, t2, 64; la t4, scc_system_addr; li t5, 20; li a0, 1\n" ++
  ".Lsccp_cmp:\n" ++
  "  beqz t5, .Lsccp_cmp_d\n" ++
  "  lbu a1, 0(t3); lbu a2, 0(t4); bne a1, a2, .Lsccp_ne\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lsccp_cmp\n" ++
  ".Lsccp_ne:\n  li a0, 0\n" ++
  ".Lsccp_cmp_d:\n" ++
  "  sd a0, 16(t0)\n" ++                             -- caller_ok
  "  sd s0, 24(t0)\n" ++                             -- stage status
  "  j .Lsccp_done\n" ++
  stageSystemCallPayloadFunction ++ "\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  stageRuntimePayloadWitnessContextFunction ++ "\n" ++
  ".Lsccp_done:"

def ziskStageSystemCallPayloadDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "scc_ctx:\n  .zero 192\n" ++
  ".balign 8\n" ++
  "scc_system_addr:\n" ++   -- SYSTEM_ADDRESS 0xfffffffffffffffffffffffffffffffffffffffe (20B BE)
  "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
  "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe\n" ++
  ".balign 8\n" ++
  "scc_probe_target:\n  .byte 0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5, 0x5e, 0x80, 0xd1, 0x9a, 0xd8, 0x35, 0x79, 0xa6, 0x4c, 0x00, 0x70, 0x02\n" ++  -- WITHDRAWAL_REQUEST_PREDEPLOY
  ".balign 8\n" ++
  "scc_probe_code:\n  .byte 0x60, 0x00, 0x60, 0x00, 0xf3, 0x00\n" ++   -- PUSH1 0; PUSH1 0; RETURN; (6 B)
  ".balign 8\n" ++
  "scc_probe_exec:\n  .zero 1024\n" ++   -- minimal block exec payload (env words zero; not asserted)
  ".balign 8\n" ++
  "scc_probe_out:\n  .zero 4096\n" ++
  -- data labels stage_runtime_payload_code references (M29 staging defaults to 0 -> inert)
  ".balign 8\n" ++
  "srpc_env_base:\n  .zero 8\n" ++
  "m29_stage_cur:\n  .zero 8\n" ++
  "m29_stage_count:\n  .zero 8\n" ++
  "m29_stage_table:\n  .zero 8192\n"

def ziskStageSystemCallPayloadProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageSystemCallPayloadPrologue
  dataAsm     := ziskStageSystemCallPayloadDataSection
}

end EvmAsm.Codegen
