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
             a2 status (two failure classes — MUST stay distinguishable, #11810):
               0 = ok (dispatch ran; halt_kind ∈ {STOP=0, RETURN=1, SELFDESTRUCT=5})
               1 = staging failure (empty code / payload reject; no dispatch run)
               2 = execution failure (dispatch ran; MessageCallOutput.error —
                   REVERT or ExceptionalHalt; halt_kind ∉ success set)

    Callers MUST NOT collapse 1 and 2:
      - checked (7002/7251/8282): `bnez a2` rejects both — fork.py:773-777
        `if system_tx_output.error` plus empty-code InvalidBlock (:761-765).
      - unchecked (4788/2935): reject **only** a2=1; ignore a2=2 — fork.py:782
        process_unchecked "WITHOUT CHECKING … if the transaction fails".
        Staging failure is guest-internal undefined (arena/payload bound); we
        deliberately reject it (stricter than the spec) as the safe side.

    Stages the SYSTEM payload, runs the callable runtime dispatcher with
    system_call_mode=1 so the predeploy's depth-0 RETURN is captured (NoopHalt
    #8681) into system_call_returndata, then clears the flag.

    Spec pin `process_checked_system_transaction` (fork.py:761-765): empty
    system-contract code raises InvalidBlock. Callers of this seam are the
    checked request predeploys (7002/7251/8282); block-start unchecked
    (4788/2935) already skip before jal when code is empty. Rejecting empty
    code here restores the checked empty-code gate without changing those skip
    paths (#11806 / #11809).

    Exec-status discriminator is `rdg_halt_kind` (#11798 / #11815) — the same
    cell `dispatcher_tx_gas_settle` reads. Do NOT read OUTPUT+32: after #11815
    the verdict-callable path never stamps halt_kind there (claim-window fix). -/
def stageSystemCall_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.ssc_saved_ra (GuestAddrs.stage_system_call + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_saved_ra (GuestAddrs.stage_system_call + 0)),
    .SD .x5 .x1 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_saved_s0 (GuestAddrs.stage_system_call + 12)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_saved_s0 (GuestAddrs.stage_system_call + 12)),
    .SD .x5 .x8 (0 : BitVec 12),
    .MV .x6 .x10,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.stage_system_call + 28)),
    .MV .x10 .x6,
    .BEQ .x12 .x0 (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 36)),
    .MV .x8 .x14,
    .LI .x5 (0 : Word),
    .AUIPC .x6 (laHi GuestAddrs.system_call_returndata_len (GuestAddrs.stage_system_call + 48)),
    .ADDI .x6 .x6 (laLo GuestAddrs.system_call_returndata_len (GuestAddrs.stage_system_call + 48)),
    .SD .x6 .x5 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .AUIPC .x6 (laHi GuestAddrs.system_call_mode (GuestAddrs.stage_system_call + 64)),
    .ADDI .x6 .x6 (laLo GuestAddrs.system_call_mode (GuestAddrs.stage_system_call + 64)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.runtime_tx_auth_exec_fn (GuestAddrs.stage_system_call + 76)),
    .ADDI .x6 .x6 (laLo GuestAddrs.runtime_tx_auth_exec_fn (GuestAddrs.stage_system_call + 76)),
    .SD .x6 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rdg_halt_kind (GuestAddrs.stage_system_call + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rdg_halt_kind (GuestAddrs.stage_system_call + 88)),
    .SD .x5 .x0 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.stage_system_call_payload (GuestAddrs.stage_system_call + 100)),
    .BNE .x10 .x0 (brOff (GuestAddrs.stage_system_call + 224) (GuestAddrs.stage_system_call + 104)),
    .ADDI .x6 .x8 (8 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_dispatcher_input_ptr (GuestAddrs.stage_system_call + 112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_dispatcher_input_ptr (GuestAddrs.stage_system_call + 112)),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.runtime_dispatcher_call (GuestAddrs.stage_system_call + 124)),
    .AUIPC .x5 (laHi GuestAddrs.runtime_dispatcher_input_ptr (GuestAddrs.stage_system_call + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_dispatcher_input_ptr (GuestAddrs.stage_system_call + 128)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x5 (0 : Word),
    .AUIPC .x6 (laHi GuestAddrs.system_call_mode (GuestAddrs.stage_system_call + 144)),
    .ADDI .x6 .x6 (laLo GuestAddrs.system_call_mode (GuestAddrs.stage_system_call + 144)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.system_call_returndata (GuestAddrs.stage_system_call + 156)),
    .ADDI .x10 .x10 (laLo GuestAddrs.system_call_returndata (GuestAddrs.stage_system_call + 156)),
    .AUIPC .x5 (laHi GuestAddrs.system_call_returndata_len (GuestAddrs.stage_system_call + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.system_call_returndata_len (GuestAddrs.stage_system_call + 164)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rdg_halt_kind (GuestAddrs.stage_system_call + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rdg_halt_kind (GuestAddrs.stage_system_call + 176)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x6 .x5 (20 : BitVec 13),
    .LI .x5 (5 : Word),
    .BEQ .x6 .x5 (12 : BitVec 13),
    .LI .x12 (2 : Word),
    .JAL .x0 (44 : BitVec 21),
    .LI .x12 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .LI .x5 (0 : Word),
    .AUIPC .x6 (laHi GuestAddrs.system_call_mode (GuestAddrs.stage_system_call + 228)),
    .ADDI .x6 .x6 (laLo GuestAddrs.system_call_mode (GuestAddrs.stage_system_call + 228)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.system_call_returndata (GuestAddrs.stage_system_call + 240)),
    .ADDI .x10 .x10 (laLo GuestAddrs.system_call_returndata (GuestAddrs.stage_system_call + 240)),
    .LI .x11 (0 : Word),
    .LI .x12 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.ssc_saved_s0 (GuestAddrs.stage_system_call + 256)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_saved_s0 (GuestAddrs.stage_system_call + 256)),
    .LD .x8 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_saved_ra (GuestAddrs.stage_system_call + 268)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_saved_ra (GuestAddrs.stage_system_call + 268)),
    .LD .x1 .x5 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `stageSystemCall_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def stageSystemCall_relocs : RelocTable :=
  [ (0, .la .x5 "ssc_saved_ra"),
    (3, .la .x5 "ssc_saved_s0"),
    (7, .jal .x1 "account_read_record"),
    (12, .la .x6 "system_call_returndata_len"),
    (16, .la .x6 "system_call_mode"),
    (19, .la .x6 "runtime_tx_auth_exec_fn"),
    (22, .la .x5 "rdg_halt_kind"),
    (25, .jal .x1 "stage_system_call_payload"),
    (28, .la .x5 "runtime_dispatcher_input_ptr"),
    (31, .jal .x1 "runtime_dispatcher_call"),
    (32, .la .x5 "runtime_dispatcher_input_ptr"),
    (36, .la .x6 "system_call_mode"),
    (39, .la .x10 "system_call_returndata"),
    (41, .la .x5 "system_call_returndata_len"),
    (44, .la .x5 "rdg_halt_kind"),
    (57, .la .x6 "system_call_mode"),
    (60, .la .x10 "system_call_returndata"),
    (64, .la .x5 "ssc_saved_s0"),
    (67, .la .x5 "ssc_saved_ra") ]

def stageSystemCallFunction : String :=
  "stage_system_call:\n" ++ emitProgramR stageSystemCall_prog stageSystemCall_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `stageSystemCall_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem stageSystemCallFunction_eq_prog :
    stageSystemCallFunction = "stage_system_call:\n" ++ emitProgramR stageSystemCall_prog stageSystemCall_relocs := rfl

#guard stageSystemCallFunction.startsWith "stage_system_call:\n"
/-! ## process_block_start_system_transactions (GH #11431)

    Spec pin `amsterdam/forks/.../fork.py:897-910` `apply_body`:
      process_unchecked_system_transaction(BEACON_ROOTS, parent_beacon_block_root)
      process_unchecked_system_transaction(HISTORY_STORAGE, parent_hash)
      track_ancestor_access(1)
    before the user-tx loop. BAI = 0 for both (`block_access_index` starts at 0).

    Replaces the retired formula-descriptor path and its seed-only identity
    shortcut:
    each contract is looked up via `code_at_header_state_root`, executed through
    `stage_system_call` with the real 32-byte calldata, then
    `account_writes_emit_builder_tx` + `write_sets_incorporate_tx` (which emits
    BAL storage changes at `current_block_access_index` and merges into the
    block map for tier-2 SLOAD) + `read_sets_incorporate_tx`.

    Unchecked semantics (fork.py:782 process_unchecked): code_at miss / empty
    code → skip dispatch (no write), still mark OAO. Spec-level exec failure
    (a2=2 REVERT/ExceptionalHalt) is **ignored**. Staging failure (a2=1) still
    rejects — guest-internal undefined; stricter than the spec on purpose (#11810).

    Calldata layout (retired formula path / SSZ):
      parent_beacon_block_root @ SSZ_BASE+24 = bv_exec_p - 36
      parent_hash             @ SSZ_BASE+60 = bv_exec_p + 0
    a0 (out) = 0 ok / 1 fail. -/
def processBlockStartSystemTransactions_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.pbsst_saved_ra (GuestAddrs.process_block_start_system_transactions + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_saved_ra (GuestAddrs.process_block_start_system_transactions + 0)),
    .SD .x5 .x1 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.current_block_access_index (GuestAddrs.process_block_start_system_transactions + 12)),
    .ADDI .x5 .x5 (laLo GuestAddrs.current_block_access_index (GuestAddrs.process_block_start_system_transactions + 12)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 24)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 24)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 36)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 36)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness (GuestAddrs.process_block_start_system_transactions + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness (GuestAddrs.process_block_start_system_transactions + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.process_block_start_system_transactions + 60)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.process_block_start_system_transactions + 60)),
    .SD .x7 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness_len (GuestAddrs.process_block_start_system_transactions + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness_len (GuestAddrs.process_block_start_system_transactions + 72)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.process_block_start_system_transactions + 84)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.process_block_start_system_transactions + 84)),
    .SD .x7 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness (GuestAddrs.process_block_start_system_transactions + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness (GuestAddrs.process_block_start_system_transactions + 96)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness_len (GuestAddrs.process_block_start_system_transactions + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness_len (GuestAddrs.process_block_start_system_transactions + 108)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_parent_rlp (GuestAddrs.process_block_start_system_transactions + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_parent_rlp (GuestAddrs.process_block_start_system_transactions + 120)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_parent_rlp_len (GuestAddrs.process_block_start_system_transactions + 132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_parent_rlp_len (GuestAddrs.process_block_start_system_transactions + 132)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.bsr_addr_4788 (GuestAddrs.process_block_start_system_transactions + 144)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bsr_addr_4788 (GuestAddrs.process_block_start_system_transactions + 144)),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 152)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_len (GuestAddrs.process_block_start_system_transactions + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_len (GuestAddrs.process_block_start_system_transactions + 164)),
    .LD .x16 .x5 (0 : BitVec 12),
    .MV .x5 .x10,
    .MV .x6 .x11,
    .MV .x10 .x12,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.process_block_start_system_transactions + 188)),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.code_at_header_state_root (GuestAddrs.process_block_start_system_transactions + 200)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.process_block_start_system_transactions + 524) (GuestAddrs.process_block_start_system_transactions + 208)),
    .LI .x5 (5 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.process_block_start_system_transactions + 292) (GuestAddrs.process_block_start_system_transactions + 216)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_acct_struct (GuestAddrs.process_block_start_system_transactions + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_acct_struct (GuestAddrs.process_block_start_system_transactions + 220)),
    .ADDI .x5 .x5 (72 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.process_block_start_system_transactions + 232)),
    .ADDI .x6 .x6 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.process_block_start_system_transactions + 232)),
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (44 : BitVec 13),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (32 : BitVec 13),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (20 : BitVec 13),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.process_block_start_system_transactions + 524) (GuestAddrs.process_block_start_system_transactions + 288)),
    .BNE .x10 .x0 (brOff (GuestAddrs.process_block_start_system_transactions + 980) (GuestAddrs.process_block_start_system_transactions + 292)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 296)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 296)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.process_block_start_system_transactions + 524) (GuestAddrs.process_block_start_system_transactions + 308)),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 312)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.process_block_start_system_transactions + 324)),
    .ADDI .x7 .x7 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.process_block_start_system_transactions + 324)),
    .LD .x28 .x7 (0 : BitVec 12),
    .ADD .x29 .x6 .x28,
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 340)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 340)),
    .SD .x5 .x29 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 352)),
    .ADDI .x7 .x7 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 352)),
    .LD .x28 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 364)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 364)),
    .SD .x5 .x28 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 376)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 376)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (-36 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 392)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 392)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x6 (32 : Word),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 408)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 408)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bsr_addr_4788 (GuestAddrs.process_block_start_system_transactions + 420)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bsr_addr_4788 (GuestAddrs.process_block_start_system_transactions + 420)),
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 428)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 428)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 440)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 440)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 452)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 452)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.c1_staging (GuestAddrs.process_block_start_system_transactions + 464)),
    .ADDI .x14 .x14 (laLo GuestAddrs.c1_staging (GuestAddrs.process_block_start_system_transactions + 464)),
    .JAL .x1 (jalOff GuestAddrs.stage_system_call (GuestAddrs.process_block_start_system_transactions + 472)),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 476)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 476)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 488)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 488)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .BEQ .x12 .x5 (brOff (GuestAddrs.process_block_start_system_transactions + 980) (GuestAddrs.process_block_start_system_transactions + 504)),
    .JAL .x1 (jalOff GuestAddrs.account_writes_emit_builder_tx (GuestAddrs.process_block_start_system_transactions + 508)),
    .JAL .x1 (jalOff GuestAddrs.account_writes_incorporate_tx (GuestAddrs.process_block_start_system_transactions + 512)),
    .JAL .x1 (jalOff GuestAddrs.write_sets_incorporate_tx (GuestAddrs.process_block_start_system_transactions + 516)),
    .JAL .x1 (jalOff GuestAddrs.read_sets_incorporate_tx (GuestAddrs.process_block_start_system_transactions + 520)),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness (GuestAddrs.process_block_start_system_transactions + 524)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness (GuestAddrs.process_block_start_system_transactions + 524)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness_len (GuestAddrs.process_block_start_system_transactions + 536)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness_len (GuestAddrs.process_block_start_system_transactions + 536)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_parent_rlp (GuestAddrs.process_block_start_system_transactions + 548)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_parent_rlp (GuestAddrs.process_block_start_system_transactions + 548)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_parent_rlp_len (GuestAddrs.process_block_start_system_transactions + 560)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_parent_rlp_len (GuestAddrs.process_block_start_system_transactions + 560)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.bsr_addr_2935 (GuestAddrs.process_block_start_system_transactions + 572)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bsr_addr_2935 (GuestAddrs.process_block_start_system_transactions + 572)),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 580)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 580)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_len (GuestAddrs.process_block_start_system_transactions + 592)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_len (GuestAddrs.process_block_start_system_transactions + 592)),
    .LD .x16 .x5 (0 : BitVec 12),
    .MV .x5 .x10,
    .MV .x6 .x11,
    .MV .x10 .x12,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.process_block_start_system_transactions + 616)),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.code_at_header_state_root (GuestAddrs.process_block_start_system_transactions + 628)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.process_block_start_system_transactions + 948) (GuestAddrs.process_block_start_system_transactions + 636)),
    .LI .x5 (5 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.process_block_start_system_transactions + 720) (GuestAddrs.process_block_start_system_transactions + 644)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_acct_struct (GuestAddrs.process_block_start_system_transactions + 648)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_acct_struct (GuestAddrs.process_block_start_system_transactions + 648)),
    .ADDI .x5 .x5 (72 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.process_block_start_system_transactions + 660)),
    .ADDI .x6 .x6 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.process_block_start_system_transactions + 660)),
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (44 : BitVec 13),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (32 : BitVec 13),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (20 : BitVec 13),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.process_block_start_system_transactions + 948) (GuestAddrs.process_block_start_system_transactions + 716)),
    .BNE .x10 .x0 (brOff (GuestAddrs.process_block_start_system_transactions + 980) (GuestAddrs.process_block_start_system_transactions + 720)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 724)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 724)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.process_block_start_system_transactions + 948) (GuestAddrs.process_block_start_system_transactions + 736)),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 740)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.process_block_start_system_transactions + 740)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.process_block_start_system_transactions + 752)),
    .ADDI .x7 .x7 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.process_block_start_system_transactions + 752)),
    .LD .x28 .x7 (0 : BitVec 12),
    .ADD .x29 .x6 .x28,
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 768)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 768)),
    .SD .x5 .x29 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 780)),
    .ADDI .x7 .x7 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.process_block_start_system_transactions + 780)),
    .LD .x28 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 792)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 792)),
    .SD .x5 .x28 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 804)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 804)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 816)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 816)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x6 (32 : Word),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 832)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 832)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bsr_addr_2935 (GuestAddrs.process_block_start_system_transactions + 844)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bsr_addr_2935 (GuestAddrs.process_block_start_system_transactions + 844)),
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 852)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_ptr (GuestAddrs.process_block_start_system_transactions + 852)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 864)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_code_len (GuestAddrs.process_block_start_system_transactions + 864)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 876)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_exec_p (GuestAddrs.process_block_start_system_transactions + 876)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.c1_staging (GuestAddrs.process_block_start_system_transactions + 888)),
    .ADDI .x14 .x14 (laLo GuestAddrs.c1_staging (GuestAddrs.process_block_start_system_transactions + 888)),
    .JAL .x1 (jalOff GuestAddrs.stage_system_call (GuestAddrs.process_block_start_system_transactions + 896)),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 900)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 900)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 912)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 912)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .BEQ .x12 .x5 (52 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.account_writes_emit_builder_tx (GuestAddrs.process_block_start_system_transactions + 932)),
    .JAL .x1 (jalOff GuestAddrs.account_writes_incorporate_tx (GuestAddrs.process_block_start_system_transactions + 936)),
    .JAL .x1 (jalOff GuestAddrs.write_sets_incorporate_tx (GuestAddrs.process_block_start_system_transactions + 940)),
    .JAL .x1 (jalOff GuestAddrs.read_sets_incorporate_tx (GuestAddrs.process_block_start_system_transactions + 944)),
    .AUIPC .x5 (laHi GuestAddrs.evm_oldest_ancestor_offset (GuestAddrs.process_block_start_system_transactions + 948)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_oldest_ancestor_offset (GuestAddrs.process_block_start_system_transactions + 948)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (12 : BitVec 13),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (32 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 980)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_ptr (GuestAddrs.process_block_start_system_transactions + 980)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 992)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ssc_calldata_len (GuestAddrs.process_block_start_system_transactions + 992)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.pbsst_saved_ra (GuestAddrs.process_block_start_system_transactions + 1008)),
    .ADDI .x5 .x5 (laLo GuestAddrs.pbsst_saved_ra (GuestAddrs.process_block_start_system_transactions + 1008)),
    .LD .x1 .x5 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `processBlockStartSystemTransactions_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def processBlockStartSystemTransactions_relocs : RelocTable :=
  [ (0, .la .x5 "pbsst_saved_ra"),
    (3, .la .x5 "current_block_access_index"),
    (6, .la .x5 "ssc_calldata_ptr"),
    (9, .la .x5 "ssc_calldata_len"),
    (12, .la .x5 "svf_witness"),
    (15, .la .x7 "bv_witness_state_ptr"),
    (18, .la .x5 "svf_witness_len"),
    (21, .la .x7 "bv_witness_state_len"),
    (24, .la .x5 "svf_witness"),
    (27, .la .x5 "svf_witness_len"),
    (30, .la .x5 "svf_parent_rlp"),
    (33, .la .x5 "svf_parent_rlp_len"),
    (36, .la .x12 "bsr_addr_4788"),
    (38, .la .x5 "svf_codes_ptr"),
    (41, .la .x5 "svf_codes_len"),
    (47, .jal .x1 "account_read_record"),
    (50, .jal .x1 "code_at_header_state_root"),
    (55, .la .x5 "cahsr_acct_struct"),
    (58, .la .x6 "chahsr_empty_code_hash"),
    (74, .la .x5 "cahsr_code_length"),
    (78, .la .x5 "svf_codes_ptr"),
    (81, .la .x7 "cahsr_code_offset"),
    (85, .la .x5 "pbsst_code_ptr"),
    (88, .la .x7 "cahsr_code_length"),
    (91, .la .x5 "pbsst_code_len"),
    (94, .la .x5 "bv_exec_p"),
    (98, .la .x5 "ssc_calldata_ptr"),
    (102, .la .x5 "ssc_calldata_len"),
    (105, .la .x10 "bsr_addr_4788"),
    (107, .la .x5 "pbsst_code_ptr"),
    (110, .la .x5 "pbsst_code_len"),
    (113, .la .x5 "bv_exec_p"),
    (116, .la .x14 "c1_staging"),
    (118, .jal .x1 "stage_system_call"),
    (119, .la .x5 "ssc_calldata_ptr"),
    (122, .la .x5 "ssc_calldata_len"),
    (127, .jal .x1 "account_writes_emit_builder_tx"),
    (128, .jal .x1 "account_writes_incorporate_tx"),
    (129, .jal .x1 "write_sets_incorporate_tx"),
    (130, .jal .x1 "read_sets_incorporate_tx"),
    (131, .la .x5 "svf_witness"),
    (134, .la .x5 "svf_witness_len"),
    (137, .la .x5 "svf_parent_rlp"),
    (140, .la .x5 "svf_parent_rlp_len"),
    (143, .la .x12 "bsr_addr_2935"),
    (145, .la .x5 "svf_codes_ptr"),
    (148, .la .x5 "svf_codes_len"),
    (154, .jal .x1 "account_read_record"),
    (157, .jal .x1 "code_at_header_state_root"),
    (162, .la .x5 "cahsr_acct_struct"),
    (165, .la .x6 "chahsr_empty_code_hash"),
    (181, .la .x5 "cahsr_code_length"),
    (185, .la .x5 "svf_codes_ptr"),
    (188, .la .x7 "cahsr_code_offset"),
    (192, .la .x5 "pbsst_code_ptr"),
    (195, .la .x7 "cahsr_code_length"),
    (198, .la .x5 "pbsst_code_len"),
    (201, .la .x5 "bv_exec_p"),
    (204, .la .x5 "ssc_calldata_ptr"),
    (208, .la .x5 "ssc_calldata_len"),
    (211, .la .x10 "bsr_addr_2935"),
    (213, .la .x5 "pbsst_code_ptr"),
    (216, .la .x5 "pbsst_code_len"),
    (219, .la .x5 "bv_exec_p"),
    (222, .la .x14 "c1_staging"),
    (224, .jal .x1 "stage_system_call"),
    (225, .la .x5 "ssc_calldata_ptr"),
    (228, .la .x5 "ssc_calldata_len"),
    (233, .jal .x1 "account_writes_emit_builder_tx"),
    (234, .jal .x1 "account_writes_incorporate_tx"),
    (235, .jal .x1 "write_sets_incorporate_tx"),
    (236, .jal .x1 "read_sets_incorporate_tx"),
    (237, .la .x5 "evm_oldest_ancestor_offset"),
    (245, .la .x5 "ssc_calldata_ptr"),
    (248, .la .x5 "ssc_calldata_len"),
    (252, .la .x5 "pbsst_saved_ra") ]

def processBlockStartSystemTransactionsFunction : String :=
  "process_block_start_system_transactions:\n" ++ emitProgramR processBlockStartSystemTransactions_prog processBlockStartSystemTransactions_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `processBlockStartSystemTransactions_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem processBlockStartSystemTransactionsFunction_eq_prog :
    processBlockStartSystemTransactionsFunction = "process_block_start_system_transactions:\n" ++ emitProgramR processBlockStartSystemTransactions_prog processBlockStartSystemTransactions_relocs := rfl

#guard processBlockStartSystemTransactionsFunction.startsWith "process_block_start_system_transactions:\n"
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
      a0 = withdrawal body ptr (= system_call_returndata)   a1 = body len
      a2 = stage_system_call status (0 ok / 1 staging / 2 exec fail; checked callers bnez) -/
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
      a0 = consolidation body ptr (= system_call_returndata)   a1 = body len
      a2 = stage_system_call status (0 ok / 1 staging / 2 exec fail; checked callers bnez) -/
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

def deriveBuilderDepositRequests_prog : Program :=
  [ .MV .x14 .x13,
    .MV .x13 .x12,
    .MV .x12 .x11,
    .MV .x11 .x10,
    .AUIPC .x10 (laHi GuestAddrs.builder_deposit_contract_addr (GuestAddrs.derive_builder_deposit_requests + 16)),
    .ADDI .x10 .x10 (laLo GuestAddrs.builder_deposit_contract_addr (GuestAddrs.derive_builder_deposit_requests + 16)),
    .JAL .x0 (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_builder_deposit_requests + 24)) ]

/-- Reloc side-table for `deriveBuilderDepositRequests_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def deriveBuilderDepositRequests_relocs : RelocTable :=
  [ (4, .la .x10 "builder_deposit_contract_addr"),
    (6, .jal .x0 "stage_system_call") ]

def deriveBuilderDepositRequestsFunction : String :=
  "derive_builder_deposit_requests:\n" ++ emitProgramR deriveBuilderDepositRequests_prog deriveBuilderDepositRequests_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `deriveBuilderDepositRequests_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem deriveBuilderDepositRequestsFunction_eq_prog :
    deriveBuilderDepositRequestsFunction = "derive_builder_deposit_requests:\n" ++ emitProgramR deriveBuilderDepositRequests_prog deriveBuilderDepositRequests_relocs := rfl

#guard deriveBuilderDepositRequestsFunction.startsWith "derive_builder_deposit_requests:\n"
def deriveBuilderExitRequests_prog : Program :=
  [ .MV .x14 .x13,
    .MV .x13 .x12,
    .MV .x12 .x11,
    .MV .x11 .x10,
    .AUIPC .x10 (laHi GuestAddrs.builder_exit_contract_addr (GuestAddrs.derive_builder_exit_requests + 16)),
    .ADDI .x10 .x10 (laLo GuestAddrs.builder_exit_contract_addr (GuestAddrs.derive_builder_exit_requests + 16)),
    .JAL .x0 (jalOff GuestAddrs.stage_system_call (GuestAddrs.derive_builder_exit_requests + 24)) ]

/-- Reloc side-table for `deriveBuilderExitRequests_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def deriveBuilderExitRequests_relocs : RelocTable :=
  [ (4, .la .x10 "builder_exit_contract_addr"),
    (6, .jal .x0 "stage_system_call") ]

def deriveBuilderExitRequestsFunction : String :=
  "derive_builder_exit_requests:\n" ++ emitProgramR deriveBuilderExitRequests_prog deriveBuilderExitRequests_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `deriveBuilderExitRequests_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem deriveBuilderExitRequestsFunction_eq_prog :
    deriveBuilderExitRequestsFunction = "derive_builder_exit_requests:\n" ++ emitProgramR deriveBuilderExitRequests_prog deriveBuilderExitRequests_relocs := rfl

#guard deriveBuilderExitRequestsFunction.startsWith "derive_builder_exit_requests:\n"
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
    Returns a0 = 0 ok / 1 = a system call returned staging or exec failure. -/
/-! Probe-only local PC placeholder. -/
def deriveBlockSystemRequestsPc : Nat := 0x80000000

def deriveBlockSystemRequests_prog : Program :=
  [ .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 0)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 0)),
    .SD .x5 .x1 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 12)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 12)),
    .SD .x5 .x12 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 24)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 24)),
    .SD .x5 .x13 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 36)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 36)),
    .SD .x5 .x14 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 48)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 48)),
    .SD .x5 .x15 (0 : BitVec 12),
    .MV .x12 .x14,
    .MV .x13 .x15,
    .JAL .x1 (jalOff GuestAddrs.derive_withdrawal_requests (deriveBlockSystemRequestsPc + 68)),
    .BNE .x12 .x0 (brOff (deriveBlockSystemRequestsPc + 260) (deriveBlockSystemRequestsPc + 72)),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 76)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 76)),
    .SD .x5 .x11 (0 : BitVec 12),
    .MV .x6 .x10,
    .AUIPC .x7 (laHi 0 (deriveBlockSystemRequestsPc + 92)),
    .ADDI .x7 .x7 (laLo 0 (deriveBlockSystemRequestsPc + 92)),
    .MV .x28 .x11,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x6 (0 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JAL .x1 (jalOff GuestAddrs.read_sets_incorporate_tx (deriveBlockSystemRequestsPc + 132)),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 136)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 136)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 148)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 148)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 160)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 160)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 172)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 172)),
    .LD .x13 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.derive_consolidation_requests (deriveBlockSystemRequestsPc + 184)),
    .BNE .x12 .x0 (brOff (deriveBlockSystemRequestsPc + 260) (deriveBlockSystemRequestsPc + 188)),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 192)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 192)),
    .SD .x5 .x11 (0 : BitVec 12),
    .MV .x6 .x10,
    .AUIPC .x7 (laHi 0 (deriveBlockSystemRequestsPc + 208)),
    .ADDI .x7 .x7 (laLo 0 (deriveBlockSystemRequestsPc + 208)),
    .MV .x28 .x11,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x6 (0 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JAL .x1 (jalOff GuestAddrs.read_sets_incorporate_tx (deriveBlockSystemRequestsPc + 248)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .AUIPC .x5 (laHi 0 (deriveBlockSystemRequestsPc + 264)),
    .ADDI .x5 .x5 (laLo 0 (deriveBlockSystemRequestsPc + 264)),
    .LD .x1 .x5 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `deriveBlockSystemRequests_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def deriveBlockSystemRequests_relocs : RelocTable :=
  [ (0, .la .x5 "dbsr_saved_ra"),
    (3, .la .x5 "dbsr_ccode"),
    (6, .la .x5 "dbsr_in_clen"),
    (9, .la .x5 "dbsr_exec"),
    (12, .la .x5 "dbsr_staging"),
    (17, .jal .x1 "derive_withdrawal_requests"),
    (19, .la .x5 "dbsr_wlen"),
    (23, .la .x7 "dbsr_wbody"),
    (33, .jal .x1 "read_sets_incorporate_tx"),
    (34, .la .x5 "dbsr_ccode"),
    (37, .la .x5 "dbsr_in_clen"),
    (40, .la .x5 "dbsr_exec"),
    (43, .la .x5 "dbsr_staging"),
    (46, .jal .x1 "derive_consolidation_requests"),
    (48, .la .x5 "dbsr_clen"),
    (52, .la .x7 "dbsr_cbody"),
    (62, .jal .x1 "read_sets_incorporate_tx"),
    (66, .la .x5 "dbsr_saved_ra") ]

def deriveBlockSystemRequestsFunction : String :=
  "derive_block_system_requests:\n" ++ emitProgramR deriveBlockSystemRequests_prog deriveBlockSystemRequests_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `deriveBlockSystemRequests_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem deriveBlockSystemRequestsFunction_eq_prog :
    deriveBlockSystemRequestsFunction = "derive_block_system_requests:\n" ++ emitProgramR deriveBlockSystemRequests_prog deriveBlockSystemRequests_relocs := rfl

#guard deriveBlockSystemRequestsFunction.startsWith "derive_block_system_requests:\n"
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


end EvmAsm.Codegen
