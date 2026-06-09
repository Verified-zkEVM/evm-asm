/-
  EvmAsm.Codegen.Programs.CreateDescend

  bmvmx/.61.8a: `create2_descend` — the CREATE2 (0xf5) handler logic over the
  existing inline init-code machinery (CreateRuntime.lean). CREATE2 needs no nonce
  (address = keccak(0xff‖sender‖salt‖keccak(initcode))[12:]), so it is the cleanest
  first slice of the CREATE family.

  Model (NOT a call_frame_descend): the handler stages the init code + runs the
  bounded mini-interpreter (`create_execute_initcode_frame`), then pushes the new
  address on success or 0 on failure. It reads the dispatcher registers directly
  (x12 = stack top, grows down; x13 = mem base; x20 = env base) and returns the new
  stack top in a0, so a 0xf5 handler can `jal create2_descend; mv x12, a0`.

  CREATE2 stack (x12, top first): value@0, offset@32, length@64, salt@96. Pops 4
  words, pushes 1 → new top = x12 + 96. Byte orders: the salt stack word is EVM-stack
  LE and is reversed to big-endian for the preimage; the 20-byte big-endian result
  address is reversed back to an LE stack word for the push.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.CreateRuntime
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## create2_descend
    Reads x12 (stack top) / x13 (mem base) / x20 (env base). Returns a0 = new stack
    top (x12 + 96). On `create_child_status == 2` (deployed) the new address is pushed;
    otherwise 0 is pushed. Reuses create_sender_be/create_salt_be/create_init_offset/
    create_init_size/create_address_be + address_compute_create2 + the staging/exec
    helpers. Preserves nothing the caller needs except the documented a0. -/
def create2DescendFunction : String :=
  "create2_descend:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, x12                   # stack top (value@0, offset@32, length@64, salt@96)\n" ++
  "  mv s1, x13                   # mem base\n" ++
  "  mv s2, x20                   # env base\n" ++
  -- init offset/size from the stack (low limb of each 32-byte word).
  "  ld t0, 32(s0); la t1, create_init_offset; sd t0, 0(t1)\n" ++
  "  ld t0, 64(s0); la t1, create_init_size;   sd t0, 0(t1)\n" ++
  -- creator = env.ADDRESS (env+0, 32B: address in the low 20 BE bytes).
  "  la t1, create_sender_be\n" ++
  "  ld t2, 0(s2); sd t2, 0(t1); ld t2, 8(s2); sd t2, 8(t1)\n" ++
  "  ld t2, 16(s2); sd t2, 16(t1); ld t2, 24(s2); sd t2, 24(t1)\n" ++
  -- salt: stack word (LE limbs) at s0+96 -> byte-reverse into create_salt_be (BE).
  "  addi t2, s0, 127; la t1, create_salt_be; li t0, 32\n" ++
  ".Lc2d_revsalt:\n" ++
  "  beqz t0, .Lc2d_revsalt_d\n  lbu t3, 0(t2); sb t3, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lc2d_revsalt\n" ++
  ".Lc2d_revsalt_d:\n" ++
  -- address_compute_create2(a0=sender, a1=salt_be, a2=mem+offset, a3=length, a4=out).
  "  la a0, create_sender_be; la a1, create_salt_be\n" ++
  "  la t0, create_init_offset; ld t0, 0(t0); add a2, s1, t0\n" ++
  "  la t0, create_init_size; ld a3, 0(t0)\n" ++
  "  la a4, create_address_be\n" ++
  "  jal ra, address_compute_create2\n" ++
  -- stage (a0=mem base, a1=stack top for the value word, a2=kind 1) + execute.
  "  mv a0, s1; mv a1, s0; li a2, 1\n" ++
  "  jal ra, create_stage_initcode_frame\n" ++
  "  jal ra, create_execute_initcode_frame\n" ++
  -- result slot = new top = s0 + 96 (popped 4 args, push 1). Zero it.
  "  addi t4, s0, 96\n" ++
  "  sd x0, 0(t4); sd x0, 8(t4); sd x0, 16(t4); sd x0, 24(t4)\n" ++
  "  la t0, create_child_status; ld t0, 0(t0); li t1, 2; bne t0, t1, .Lc2d_done\n" ++
  -- success: push the new address as an LE stack word (reverse the 20 BE bytes).
  "  la t2, create_address_be; addi t2, t2, 19; mv t1, t4; li t0, 20\n" ++
  ".Lc2d_revaddr:\n" ++
  "  beqz t0, .Lc2d_done\n  lbu t3, 0(t2); sb t3, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lc2d_revaddr\n" ++
  ".Lc2d_done:\n" ++
  "  addi a0, s0, 96              # new stack top\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 48\n" ++
  "  ret"

/-! ## create_descend
    The CREATE (0xf0) analog of create2_descend. CREATE stack (x12, top first):
    value@0, offset@32, length@64 (3 words, no salt) — pops 3, pushes 1 → new top
    = x12 + 64. Address = keccak(rlp([sender, nonce]))[12:] via address_compute_create;
    the nonce is read from `create_nonce` (the handler populates it with the creator's
    current nonce — a wiring concern, not this logic). Otherwise identical to
    create2_descend (stage + bounded mini-interpreter + push address/0). -/
def createDescendFunction : String :=
  "create_descend:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, x12                   # stack top (value@0, offset@32, length@64)\n" ++
  "  mv s1, x13                   # mem base\n" ++
  "  mv s2, x20                   # env base\n" ++
  "  ld t0, 32(s0); la t1, create_init_offset; sd t0, 0(t1)\n" ++
  "  ld t0, 64(s0); la t1, create_init_size;   sd t0, 0(t1)\n" ++
  "  la t1, create_sender_be\n" ++
  "  ld t2, 0(s2); sd t2, 0(t1); ld t2, 8(s2); sd t2, 8(t1)\n" ++
  "  ld t2, 16(s2); sd t2, 16(t1); ld t2, 24(s2); sd t2, 24(t1)\n" ++
  -- address = f(sender, nonce); no initcode input. nonce from create_nonce.
  "  la a0, create_sender_be; la t0, create_nonce; ld a1, 0(t0); la a2, create_address_be\n" ++
  "  jal ra, address_compute_create\n" ++
  "  mv a0, s1; mv a1, s0; li a2, 0\n" ++          -- stage: mem base, stack top (value), kind 0
  "  jal ra, create_stage_initcode_frame\n" ++
  "  jal ra, create_execute_initcode_frame\n" ++
  "  addi t4, s0, 64\n" ++                          -- result slot = new top (popped 3, push 1)
  "  sd x0, 0(t4); sd x0, 8(t4); sd x0, 16(t4); sd x0, 24(t4)\n" ++
  "  la t0, create_child_status; ld t0, 0(t0); li t1, 2; bne t0, t1, .Lcd_done\n" ++
  "  la t2, create_address_be; addi t2, t2, 19; mv t1, t4; li t0, 20\n" ++
  ".Lcd_revaddr:\n" ++
  "  beqz t0, .Lcd_done\n  lbu t3, 0(t2); sb t3, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lcd_revaddr\n" ++
  ".Lcd_done:\n" ++
  "  addi a0, s0, 64              # new stack top\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_create_descend`: CREATE (0xf0) known-answer probe (mirrors zisk_create2_descend
    without salt). Sets create_nonce, computes the expected address with a DIRECT
    address_compute_create, runs create_descend, asserts the pushed LE stack word equals
    the LE-reversed expected address and status==2.
    Output (0xa0010000): +0 status; +8 pushed low8; +16 expected-LE low8; +24 match. -/
def ziskCreateDescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, evm_env\n" ++
  "  li t1, 0; sd t1, 0(t0); sd t1, 8(t0); sd t1, 16(t0); sd t1, 24(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, evm_memory\n" ++
  "  li t1, 0x60; sb t1, 0(t0); li t1, 0x42; sb t1, 1(t0)\n" ++
  "  li t1, 0x60; sb t1, 2(t0); li t1, 0x00; sb t1, 3(t0)\n" ++
  "  li t1, 0x52; sb t1, 4(t0)\n" ++
  "  li t1, 0x60; sb t1, 5(t0); li t1, 0x01; sb t1, 6(t0)\n" ++
  "  li t1, 0x60; sb t1, 7(t0); li t1, 0x1f; sb t1, 8(t0)\n" ++
  "  li t1, 0xf3; sb t1, 9(t0)\n" ++
  "  la t0, create_nonce; li t1, 7; sd t1, 0(t0)\n" ++
  "  la t0, cd_stack\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  sd x0, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  li t1, 10; sd t1, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  la a0, evm_env; li a1, 7; la a2, cd_expected\n" ++
  "  jal ra, address_compute_create\n" ++
  "  la x12, cd_stack; la x13, evm_memory; la x20, evm_env\n" ++
  "  jal ra, create_descend\n" ++
  "  la t0, create_child_status; ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  la t0, cd_stack; addi t0, t0, 64; ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  la t2, cd_expected; addi t2, t2, 19; la t1, cd_exple; li t3, 20\n" ++
  "1:\n  beqz t3, 2f\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t3, t3, -1; j 1b\n" ++
  "2:\n" ++
  "  la t0, cd_exple; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  la t0, cd_stack; addi t0, t0, 64; la t1, cd_exple; li t3, 20; li t4, 1\n" ++
  "3:\n  beqz t3, 4f\n  lbu t5, 0(t0); lbu t6, 0(t1); bne t5, t6, 5f\n  addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; j 3b\n" ++
  "5:\n  li t4, 0\n" ++
  "4:\n  sd t4, 24(s0)\n" ++
  "  j .Lcdp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  createStageInitcodeFrameRuntimeFunction ++ "\n" ++
  createExecuteInitcodeFrameRuntimeFunction ++ "\n" ++
  createDescendFunction ++ "\n" ++
  ".Lcdp_done:"

def ziskCreateDescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_memory:\n  .zero 0x10000\n" ++
  ".balign 8\n" ++
  "evm_env:\n  .zero 656\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "create_nonce:\n  .zero 8\n" ++
  "create_init_offset:\n  .zero 8\n" ++
  "create_init_size:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "create_sender_be:\n  .zero 32\n" ++
  "create_salt_be:\n  .zero 32\n" ++
  "create_address_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_buffer:\n  .zero 32\n" ++
  "ac_nonce_be:\n  .zero 8\n" ++
  "ac_digest:\n  .zero 32\n" ++
  emitCreateChildFrameData ++
  ".balign 8\n" ++
  "cd_stack:\n  .zero 256\n" ++
  ".balign 32\n" ++
  "cd_expected:\n  .zero 32\n" ++
  "cd_exple:\n  .zero 32\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n  .zero 262144\n" ++
  "lp64_sp_top:\n"

def ziskCreateDescendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCreateDescendPrologue
  dataAsm     := ziskCreateDescendDataSection
}

/-- `zisk_create2_descend`: known-answer probe. Lays out a synthetic CREATE2 stack +
    init code + env, computes the expected address with a DIRECT address_compute_create2
    call, then runs create2_descend and asserts the pushed stack word equals the
    LE-reversed expected address and that status==2 (the mini-interp RETURNs code).
    Init code = PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 1; PUSH1 31; RETURN (deploys 0x42).
    Output (0xa0010000): +0 status (2); +8 pushed addr low8 vs +16 expected-LE low8;
    +24 match flag (1 if the full 20 bytes agree). -/
def ziskCreate2DescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- env at evm_env: ADDRESS@0 = sender 0x11..(low20 BE). Set a recognizable sender.
  "  la t0, evm_env\n" ++
  "  li t1, 0; sd t1, 0(t0); sd t1, 8(t0); sd t1, 16(t0); sd t1, 24(t0)\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++   -- sender BE: byte0=0xAA .. byte19=0xBB
  -- init code into evm_memory at offset 0: 60 42 60 00 52 60 01 60 1f f3 (10 bytes).
  "  la t0, evm_memory\n" ++
  "  li t1, 0x60; sb t1, 0(t0); li t1, 0x42; sb t1, 1(t0)\n" ++
  "  li t1, 0x60; sb t1, 2(t0); li t1, 0x00; sb t1, 3(t0)\n" ++
  "  li t1, 0x52; sb t1, 4(t0)\n" ++
  "  li t1, 0x60; sb t1, 5(t0); li t1, 0x01; sb t1, 6(t0)\n" ++
  "  li t1, 0x60; sb t1, 7(t0); li t1, 0x1f; sb t1, 8(t0)\n" ++
  "  li t1, 0xf3; sb t1, 9(t0)\n" ++
  -- synthetic stack at cd2_stack: value@0=0, offset@32=0, length@64=10, salt@96 (LE word).
  "  la t0, cd2_stack\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++          -- value = 0
  "  sd x0, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++        -- offset = 0
  "  li t1, 10; sd t1, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++ -- length = 10
  "  li t1, 0x99; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++ -- salt LE low byte 0x99
  -- Expected: direct address_compute_create2(sender, salt_be, mem, 10) -> cd2_expected.
  -- salt_be = reverse(salt LE word) -> byte31 = 0x99 (BE last byte).
  "  la t0, cd2_saltbe\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x99; sb t1, 31(t0)\n" ++                                        -- salt_be[31] = 0x99
  "  la a0, evm_env; la a1, cd2_saltbe; la a2, evm_memory; li a3, 10; la a4, cd2_expected\n" ++
  "  jal ra, address_compute_create2\n" ++
  -- Run create2_descend with x12=stack, x13=mem, x20=env.
  "  la x12, cd2_stack; la x13, evm_memory; la x20, evm_env\n" ++
  "  jal ra, create2_descend\n" ++
  "  mv s1, a0                    # new stack top\n" ++
  -- status
  "  la t0, create_child_status; ld t1, 0(t0); sd t1, 0(s0)\n" ++
  -- pushed addr (at new top = cd2_stack+96) low8, expected-LE low8, full-20 match
  "  la t0, cd2_stack; addi t0, t0, 96; ld t1, 0(t0); sd t1, 8(s0)\n" ++     -- pushed low8 (LE)
  -- build expected-LE = reverse(cd2_expected[0..20]) into cd2_exple, compare 20 bytes
  "  la t2, cd2_expected; addi t2, t2, 19; la t1, cd2_exple; li t3, 20\n" ++
  "1:\n  beqz t3, 2f\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t3, t3, -1; j 1b\n" ++
  "2:\n" ++
  "  la t0, cd2_exple; ld t1, 0(t0); sd t1, 16(s0)\n" ++                     -- expected-LE low8
  "  la t0, cd2_stack; addi t0, t0, 96; la t1, cd2_exple; li t3, 20; li t4, 1\n" ++
  "3:\n  beqz t3, 4f\n  lbu t5, 0(t0); lbu t6, 0(t1); bne t5, t6, 5f\n  addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; j 3b\n" ++
  "5:\n  li t4, 0\n" ++
  "4:\n  sd t4, 24(s0)\n" ++                                                 -- match flag
  "  j .Lcd2_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  createStageInitcodeFrameRuntimeFunction ++ "\n" ++
  createExecuteInitcodeFrameRuntimeFunction ++ "\n" ++
  create2DescendFunction ++ "\n" ++
  ".Lcd2_done:"

def ziskCreate2DescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_memory:\n  .zero 0x10000\n" ++
  ".balign 8\n" ++
  "evm_env:\n  .zero 656\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "create_init_offset:\n  .zero 8\n" ++
  "create_init_size:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "create_sender_be:\n  .zero 32\n" ++
  "create_salt_be:\n  .zero 32\n" ++
  "create_address_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_inner_digest:\n  .zero 32\n" ++
  "ac2_outer_digest:\n  .zero 32\n" ++
  "ac2_preimage:\n  .zero 88\n" ++
  emitCreateChildFrameData ++
  ".balign 8\n" ++
  "cd2_stack:\n  .zero 256\n" ++
  ".balign 32\n" ++
  "cd2_saltbe:\n  .zero 32\n" ++
  "cd2_expected:\n  .zero 32\n" ++
  "cd2_exple:\n  .zero 32\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n  .zero 262144\n" ++
  "lp64_sp_top:\n"

def ziskCreate2DescendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCreate2DescendPrologue
  dataAsm     := ziskCreate2DescendDataSection
}

end EvmAsm.Codegen
