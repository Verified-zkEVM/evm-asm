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
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.BlockVerdictContractStage

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
  -- stage_runtime_payload_code(ctx, out, exec, code, codelen, null, 0)
  "  la a0, scc_ctx\n  mv a1, s4\n  mv a2, s3\n  mv a3, s1\n  mv a4, s2\n  li a5, 0\n  li a6, 0\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Lscc_ret\n" ++                        -- unsupported -> propagate
  -- CALLER (env_base+64) + ORIGIN (env_base+128) = SYSTEM_ADDRESS (mirror 3vc2p.1).
  "  la t5, srpc_env_base; ld t1, 0(t5)\n" ++
  "  add t2, s4, t1\n" ++                            -- t2 = &env_words
  "  la t3, scc_system_addr; addi t4, t2, 64; li t5, 0\n" ++
  ".Lscc_caller:\n" ++
  "  li t6, 20; beq t5, t6, .Lscc_caller_d\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Lscc_caller\n" ++
  ".Lscc_caller_d:\n" ++
  "  addi t4, t2, 128; li t5, 0\n" ++
  ".Lscc_origin:\n" ++
  "  li t6, 20; beq t5, t6, .Lscc_origin_d\n" ++
  "  add a5, t3, t5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Lscc_origin\n" ++
  ".Lscc_origin_d:\n" ++
  "  li a0, 0\n" ++
  ".Lscc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

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
