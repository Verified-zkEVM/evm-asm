/-
  EvmAsm.Codegen.Programs.CreateRuntime

  CREATE/CREATE2 runtime child-frame staging helpers and probes.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Save dispatcher registers, stage the CREATE child frame, and restore. -/
def createStageInitcodeFrameCallAsm (kind : Nat) : String :=
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  sd x13, 16(sp)\n" ++
  "  mv a0, x13\n" ++
  "  mv a1, x12\n" ++
  "  li a2, " ++ toString kind ++ "\n" ++
  "  jal ra, create_stage_initcode_frame\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  ld x13, 16(sp)\n" ++
  "  addi sp, sp, 32\n"

/-- Save dispatcher registers, execute the staged CREATE child frame, and
    restore. The callee records status, returndata, and deployed-code
    candidates in the shared CREATE child arena. -/
def createExecuteInitcodeFrameCallAsm : String :=
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  sd x13, 16(sp)\n" ++
  "  jal ra, create_execute_initcode_frame\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  ld x13, 16(sp)\n" ++
  "  addi sp, sp, 32\n"

/-- Mirror the CREATE child returndata surface into the dispatcher returndata
    frame used by RETURNDATASIZE/RETURNDATACOPY. -/
def createCopyChildReturndataToFrameAsm : String :=
  "  la x18, evm_precompile_frame\n" ++
  "  sd x0, 0(x18)\n" ++
  "  la x19, create_child_return_len\n" ++
  "  ld x22, 0(x19)\n" ++
  "  sd x22, 8(x18)\n" ++
  "  la x19, create_child_returndata\n" ++
  "  addi x18, x18, 16\n" ++
  "  li x23, 256\n" ++
  "  bgeu x23, x22, 12f\n" ++
  "  mv x22, x23\n" ++
  "12:\n" ++
  "  beqz x22, 14f\n" ++
  "13:\n" ++
  "  lbu x24, 0(x19)\n" ++
  "  sb x24, 0(x18)\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  bnez x22, 13b\n" ++
  "14:\n"



/-- Probe for the CREATE child-frame staging helper.

Input payload after ziskemu's 8-byte length wrapper:
  bytes   0..  8 : kind, 0 = CREATE and 1 = CREATE2
  bytes   8.. 16 : initcode offset in `evm_memory`
  bytes  16.. 24 : initcode length
  bytes  24.. 32 : CREATE nonce
  bytes  32.. 52 : creator address, big-endian
  bytes  52.. 84 : CREATE2 salt, big-endian
  bytes  84..116 : value, big-endian
  bytes 116..    : initcode bytes

Output:
  bytes   0..  8 : staging status
  bytes   8.. 16 : kind
  bytes  16.. 24 : initcode length
  bytes  24.. 56 : target address slot, big-endian/padded
  bytes  56.. 88 : creator address slot, big-endian/padded
  bytes  88..120 : value, big-endian
  bytes 120..152 : first staged initcode bytes, zero-padded by initial data
-/
def runtimeCreateInitcodeFrameProbePrologue : String :=
  "  la sp, lp64_sp_top\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi t0, t0, 8\n" ++
  "  ld s0, 0(t0)\n" ++
  "  ld s1, 8(t0)\n" ++
  "  ld s2, 16(t0)\n" ++
  "  ld s3, 24(t0)\n" ++
  "  la t1, create_init_offset\n" ++
  "  sd s1, 0(t1)\n" ++
  "  la t1, create_init_size\n" ++
  "  sd s2, 0(t1)\n" ++
  "  la t1, create_nonce\n" ++
  "  sd s3, 0(t1)\n" ++
  "  addi t2, t0, 32\n" ++
  "  la t3, create_sender_be\n" ++
  "  li t4, 20\n" ++
  ".Lcreate_probe_sender_loop:\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  sb t5, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lcreate_probe_sender_loop\n" ++
  "  li t4, 12\n" ++
  ".Lcreate_probe_sender_pad_loop:\n" ++
  "  sb zero, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lcreate_probe_sender_pad_loop\n" ++
  "  addi t2, t0, 52\n" ++
  "  la t3, create_salt_be\n" ++
  "  li t4, 32\n" ++
  ".Lcreate_probe_salt_loop:\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  sb t5, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lcreate_probe_salt_loop\n" ++
  "  addi t2, t0, 84\n" ++
  "  addi t2, t2, 31\n" ++
  "  la t3, create_probe_value_word\n" ++
  "  li t4, 32\n" ++
  ".Lcreate_probe_value_loop:\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  sb t5, 0(t3)\n" ++
  "  addi t2, t2, -1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lcreate_probe_value_loop\n" ++
  "  la t2, evm_memory\n" ++
  "  add t2, t2, s1\n" ++
  "  addi t3, t0, 116\n" ++
  "  mv t4, s2\n" ++
  ".Lcreate_probe_init_loop:\n" ++
  "  beqz t4, .Lcreate_probe_address\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lcreate_probe_init_loop\n" ++
  ".Lcreate_probe_address:\n" ++
  "  bnez s0, .Lcreate_probe_create2\n" ++
  "  la a0, create_sender_be\n" ++
  "  mv a1, s3\n" ++
  "  la a2, create_address_be\n" ++
  "  jal ra, address_compute_create\n" ++
  "  j .Lcreate_probe_stage\n" ++
  ".Lcreate_probe_create2:\n" ++
  "  la a0, create_sender_be\n" ++
  "  la a1, create_salt_be\n" ++
  "  la a2, evm_memory\n" ++
  "  add a2, a2, s1\n" ++
  "  mv a3, s2\n" ++
  "  la a4, create_address_be\n" ++
  "  jal ra, address_compute_create2\n" ++
  ".Lcreate_probe_stage:\n" ++
  "  la a0, evm_memory\n" ++
  "  la a1, create_probe_value_word\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, create_stage_initcode_frame\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, create_child_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t1, create_child_kind\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  la t1, create_child_init_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  addi t0, t0, 24\n" ++
  "  la t1, create_child_target_be\n" ++
  "  li t2, 32\n" ++
  ".Lcreate_probe_output_target_loop:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcreate_probe_output_target_loop\n" ++
  "  la t1, create_child_creator_be\n" ++
  "  li t2, 32\n" ++
  ".Lcreate_probe_output_creator_loop:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcreate_probe_output_creator_loop\n" ++
  "  la t1, create_child_value_be\n" ++
  "  li t2, 32\n" ++
  ".Lcreate_probe_output_value_loop:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcreate_probe_output_value_loop\n" ++
  "  la t1, create_child_initcode\n" ++
  "  li t2, 32\n" ++
  ".Lcreate_probe_output_initcode_loop:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcreate_probe_output_initcode_loop\n" ++
  "  j .Lcreate_probe_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  createStageInitcodeFrameRuntimeFunction ++ "\n" ++
  ".Lcreate_probe_done:"

def runtimeCreateInitcodeFrameProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x10000\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "create_nonce:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "create_init_offset:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "create_init_size:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "create_sender_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_salt_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_address_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "create_probe_value_word:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_buffer:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_nonce_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ac_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_inner_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_outer_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_preimage:\n" ++
  "  .zero 88\n" ++
  emitCreateChildFrameData ++
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 262144\n" ++
  "lp64_sp_top:\n"

def runtimeCreateInitcodeFrameProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeCreateInitcodeFrameProbePrologue
  dataAsm     := runtimeCreateInitcodeFrameProbeDataSection
}


/-- Probe for the bounded CREATE initcode executor.

Input payload after ziskemu's 8-byte length wrapper:
  bytes   0..  8 : kind, preserved into the staged frame
  bytes   8.. 16 : initcode offset in `evm_memory`
  bytes  16.. 24 : initcode length
  bytes  24.. 56 : value, big-endian
  bytes  56..    : initcode bytes

Output:
  bytes   0..  8 : child status (2 deployed, 3 reverted, 4 failed, 5 OOG)
  bytes   8.. 16 : returndata length
  bytes  16.. 24 : deployed-code candidate length
  bytes  24.. 56 : first returndata bytes
  bytes  56.. 88 : first deployed-code candidate bytes
-/
def runtimeCreateInitcodeExecuteProbePrologue : String :=
  "  la sp, lp64_sp_top\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi t0, t0, 8\n" ++
  "  ld s0, 0(t0)\n" ++
  "  ld s1, 8(t0)\n" ++
  "  ld s2, 16(t0)\n" ++
  "  la t1, create_init_offset\n" ++
  "  sd s1, 0(t1)\n" ++
  "  la t1, create_init_size\n" ++
  "  sd s2, 0(t1)\n" ++
  "  addi t2, t0, 24\n" ++
  "  addi t2, t2, 31\n" ++
  "  la t3, create_probe_value_word\n" ++
  "  li t4, 32\n" ++
  ".Lcreate_exec_probe_value_loop:\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  sb t5, 0(t3)\n" ++
  "  addi t2, t2, -1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lcreate_exec_probe_value_loop\n" ++
  "  la t2, evm_memory\n" ++
  "  add t2, t2, s1\n" ++
  "  addi t3, t0, 56\n" ++
  "  mv t4, s2\n" ++
  ".Lcreate_exec_probe_init_loop:\n" ++
  "  beqz t4, .Lcreate_exec_probe_stage\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lcreate_exec_probe_init_loop\n" ++
  ".Lcreate_exec_probe_stage:\n" ++
  "  la a0, evm_memory\n" ++
  "  la a1, create_probe_value_word\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, create_stage_initcode_frame\n" ++
  "  jal ra, create_execute_initcode_frame\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, create_child_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t1, create_child_return_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  la t1, create_child_code_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  addi t0, t0, 24\n" ++
  "  la t1, create_child_returndata\n" ++
  "  li t2, 32\n" ++
  ".Lcreate_exec_probe_output_return_loop:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcreate_exec_probe_output_return_loop\n" ++
  "  la t1, create_child_code\n" ++
  "  li t2, 32\n" ++
  ".Lcreate_exec_probe_output_code_loop:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lcreate_exec_probe_output_code_loop\n" ++
  "  j .Lcreate_exec_probe_done\n" ++
  createStageInitcodeFrameRuntimeFunction ++ "\n" ++
  createExecuteInitcodeFrameRuntimeFunction ++ "\n" ++
  ".Lcreate_exec_probe_done:"

def runtimeCreateInitcodeExecuteProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeCreateInitcodeExecuteProbePrologue
  dataAsm     := runtimeCreateInitcodeFrameProbeDataSection
}


end EvmAsm.Codegen
