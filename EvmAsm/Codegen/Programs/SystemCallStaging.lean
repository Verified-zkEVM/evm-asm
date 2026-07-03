/-
  EvmAsm.Codegen.Programs.SystemCallStaging

  `stage_system_call_payload` (bead evm-asm-8uld3.2.1.2, EIP-7002/7251) — stage the
  runtime payload for an Amsterdam system call (process_unchecked_system_transaction):
  caller = origin = SYSTEM_ADDRESS (0xff..fe), value 0, empty calldata, gas 30M, the
  target predeploy's code. Reuses the parameterized `stage_runtime_payload_code`
  (BlockVerdictContractStage.lean) with a synthesized SYSTEM context record, then
  overwrites the CALLER (env_base+64) + ORIGIN (env_base+128) env words with
  SYSTEM_ADDRESS (mirroring the 3vc2p.1 tx-sender staging).

  This is the staging half of the shared system-call harness (8uld3.2.1); the depth-0
  RETURN-data capture (8uld3.2.1a, #8681) + the compose step (8uld3.2.1c) close the loop.
  The predeploy storage preload (the EIP-7002/7251 queue) is a follow-up (count-0 storage
  works for a no-SLOAD predeploy / the probe). The caller looks up the predeploy code
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
    Stages caller=origin=SYSTEM_ADDRESS, value 0, empty calldata, gas 30M, code=predeploy. -/
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
  -- is_creation@48=0, calldata_len@64=0, recipient@72=target, value@96=0.
  "  la t0, scc_ctx\n" ++
  "  mv t1, t0; li t2, 24\n" ++
  ".Lscc_zero:\n" ++
  "  sd zero, 0(t1); addi t1, t1, 8; addi t2, t2, -1; bnez t2, .Lscc_zero\n" ++
  liAmsterdamSystemTransactionGas "t1" ++           -- t1 = 30000000
  "  sd t1, 40(t0)\n" ++                            -- gas@40
  "  addi t1, t0, 72; mv t2, s0; li t3, 20\n" ++    -- recipient@72 = target (20B)
  ".Lscc_recip:\n" ++
  "  beqz t3, .Lscc_recip_d\n" ++
  "  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, 1; addi t1, t1, 1; addi t3, t3, -1; j .Lscc_recip\n" ++
  ".Lscc_recip_d:\n" ++
  -- fhsxz.2.4.2.66.1: conservative payload-size guard (mirrors bmvmx.1.7.2 in
  -- dispatch_tx_runtime_code). stage_runtime_payload_code zeroes + writes
  -- round8(codelen) + storage_count*64 + m29_count*32 + 584 bytes into the output
  -- buffer with no bound of its own; every verdict call site passes c1_staging
  -- (c1StagingBytes, BlockVerdictParams.lean — shared constant, .66.1.2). Predeploy
  -- code is read from the witness and NOT EIP-170-bounded (the system_contract_errors
  -- EEST predeploys are 72946 B), so an unchecked copy clobbers the .data globals
  -- above c1_staging. Bail (a0=1, unsupported -> requests-hash fail) instead of
  -- corrupting .data. System-call calldata is always empty (ctx@64 stays 0).
  "  addi t1, s2, 7; andi t1, t1, -8\n" ++                                         -- round8(codelen)
  "  la t0, scc_preload_count; ld t2, 0(t0); slli t2, t2, 6; add t1, t1, t2\n" ++  -- + storage_count*64
  "  la t0, m29_stage_count; ld t2, 0(t0); slli t2, t2, 5; add t1, t1, t2\n" ++    -- + M29 hashes (count*32)
  "  addi t1, t1, 584; li t2, " ++ toString c1StagingBytes ++ "; bgtu t1, t2, .Lscc_toobig\n" ++              -- payload > buffer -> bail
  -- stage_runtime_payload_code(ctx, out, exec, code, codelen, null, 0)
  -- 8uld3.2.1.5: pass the predeploy STORAGE preload (a5/a6) so the predeploy's SLOAD of its
  -- request queue reads the staged witness values (not garbage). scc_preload_ptr/count default
  -- to 0 (empty-storage behavior, unchanged) unless the caller stages a preload first.
  "  la a0, scc_ctx\n  mv a1, s4\n  mv a2, s3\n  mv a3, s1\n  mv a4, s2\n" ++
  "  la t0, scc_preload_ptr; ld a5, 0(t0); la t0, scc_preload_count; ld a6, 0(t0)\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Lscc_ret\n" ++                        -- unsupported -> propagate
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
  "  mv s0, a4                    # out payload ptr (used only pre-dispatch)\n" ++
  -- 87gow: reset the captured return-data length to 0 BEFORE each system call. The capture
  -- (NoopHalt) writes system_call_returndata_len ONLY on a depth-0 RETURN <= 4096 bytes; a
  -- predeploy that ends in a clean STOP (empty return_data, spec fork.py:976-997) or an
  -- oversized return does NOT write it. Without this reset the consolidation system call would
  -- inherit the withdrawal call's stale length -> a spurious consolidation request body ->
  -- wrong header.requests_hash -> false-reject/accept. Spec: each return_data is a SEPARATE
  -- MessageCallOutput; empty == len 0.
  "  li t0, 0; la t1, system_call_returndata_len; sd t0, 0(t1)\n" ++
  "  li t0, 1; la t1, system_call_mode; sd t0, 0(t1)\n" ++       -- enable depth-0 RETURN capture
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

def deriveWithdrawalRequestsFunction : String :=
  "derive_withdrawal_requests:\n" ++ emitProgram deriveWithdrawalRequests_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `deriveWithdrawalRequests_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem deriveWithdrawalRequestsFunction_eq_prog :
    deriveWithdrawalRequestsFunction = "derive_withdrawal_requests:\n" ++ emitProgram deriveWithdrawalRequests_prog := rfl

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

def deriveConsolidationRequestsFunction : String :=
  "derive_consolidation_requests:\n" ++ emitProgram deriveConsolidationRequests_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `deriveConsolidationRequests_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem deriveConsolidationRequestsFunction_eq_prog :
    deriveConsolidationRequestsFunction = "derive_consolidation_requests:\n" ++ emitProgram deriveConsolidationRequests_prog := rfl

#guard deriveConsolidationRequestsFunction.startsWith "derive_consolidation_requests:\n"
#guard deriveConsolidationRequests_prog.length = 7
/-- CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS (EIP-7251), 20 bytes big-endian. Referenced by
    `derive_consolidation_requests`; emit alongside it in any unit that links the function. -/
def consolidationRequestPredeployAddrData : String :=
  ".balign 8\n" ++
  "consolidation_request_predeploy_addr:\n" ++
  "  .byte 0x00, 0x00, 0xbb, 0xdd, 0xc7, 0xce, 0x48, 0x86, 0x42, 0xfb, 0x57, 0x9f, 0x8b, 0x00, 0xf3, 0xa5, 0x90, 0x00, 0x72, 0x51\n"

/-! ## derive_block_system_requests (8uld3.2.3/8uld3.4 verdict glue)

    Run BOTH system-call request derivations for a block — withdrawal (EIP-7002) then
    consolidation (EIP-7251) — and copy each return_data body to a STABLE buffer. Necessary
    because `system_call_returndata` is a single shared buffer the dispatcher overwrites per
    call, so the verdict (which needs both bodies live at once to feed assemble/requests_hash)
    must copy the first body out before the second system call clobbers it.
      a0 = withdrawal predeploy code ptr   a1 = wcode len
      a2 = consolidation predeploy code ptr a3 = ccode len
      a4 = block exec payload ptr           a5 = staging output buffer ptr (reused per call)
    Writes: dbsr_wbody (withdrawal body) + dbsr_wlen; dbsr_cbody (consolidation body) + dbsr_clen.
    Returns a0 = 0 ok / 1 = a system call's staging was unsupported.
    Non-reentrant (saves ra + the consolidation args in globals across the dispatcher runs,
    which clobber sp/s-regs — same constraint as stage_system_call). The two calls are
    independent: the dispatcher re-initialises env per call. Deposits derive separately
    (parse_deposit_requests over receipts); the verdict composes all three. -/
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
  ".balign 8\n" ++
  "dbsr_wbody:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "dbsr_cbody:\n  .zero 2048\n"

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
  ".Lsccp_done:"

def ziskStageSystemCallPayloadDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "scc_ctx:\n  .zero 192\n" ++
  "scc_preload_ptr:\n  .zero 8\nscc_preload_count:\n  .zero 8\n" ++
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
