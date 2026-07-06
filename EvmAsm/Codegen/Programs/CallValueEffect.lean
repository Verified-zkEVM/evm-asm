/-
  EvmAsm.Codegen.Programs.CallValueEffect

  `zisk_call_value_effect` — verifies the i3djw.1 CALL value-transfer NON-STORAGE
  effect producer runs through the LIVE callFrameGuestRegistry h_CALL gate WITHOUT
  corrupting the dispatcher invariants (x10/x12/x13 = PC/stack/mem-base).

  The producer (callDescendFallThrough, ChildFrameHandlers.lean) fires at `.Lcd_balok`
  on a value-bearing CALL whose caller balance covers the value: it looks up the
  callee (account_at_header_state_root), computes post = pre + value (u256_add_be),
  and appends a record (record_nonstorage_effect). All three helpers take args in
  a0/a2/a3 = x10/x12/x13, so the producer save/restores those around every call.

  Setup (witness supplied via `ziskemu -i`, account-mode fixture: ALICE, balance 1000):
    * env.ADDRESS = ALICE (the caller); the CALL `to` = ALICE (self), value = 50
      (< 1000, so the balance gate passes and the producer fires).
    * parent: CALL; PUSH1 0; SSTORE; PUSH1 0xAB; PUSH1 1; SSTORE; STOP.

  A correct (non-corrupting) producer: the gate reaches `.Lcd_balok`, the producer
  runs (lookup + add + record), and the dispatcher invariants survive so the parent
  resumes past the CALL and stores the 0xAB sentinel to slot 1, then STOPs cleanly.
  The check asserts halt 0 and slot 1 == 0xAB (the sentinel proves x10/x12/x13
  survived the producer). The CALL result (slot 0) is incidental here (no codes
  witness -> code resolution fails after the producer already fired). The effect-log
  CONTENTS are verified end-to-end when the comparator consumes them in i3djw.3.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.EvmBasic

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def callValueEffectPrologue : String :=
  "  la sp, lp64_sp_top\n" ++
  "  la x20, evm_env\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld t1, 8(t0)\n" ++              -- header_len
  "  ld t2, 16(t0)\n" ++             -- state_len
  "  addi t3, t0, 44\n" ++           -- header ptr
  "  add t4, t3, t1\n" ++            -- state ptr = header ptr + header_len
  "  sd t3, 576(x20)\n" ++           -- env witness header ptr
  "  sd t1, 584(x20)\n" ++           -- env witness header len (gate engages)
  "  sd t4, 592(x20)\n" ++           -- env witness state ptr
  "  sd t2, 600(x20)\n" ++           -- env witness state len
  "  sd x0, 608(x20)\n" ++           -- codes ptr = 0 (code resolution fails AFTER the producer)
  "  sd x0, 616(x20)\n" ++           -- codes len
  -- caller ADDRESS (env+0..19) = ALICE, stored REVERSED (gate reads env+19..env+0).
  "  addi t3, t0, 24\n" ++           -- src = canonical addr (input+24, MSB first)
  "  addi t4, x20, 19\n" ++
  "  li t5, 20\n" ++
  ".Lcve_addr:\n" ++
  "  lbu a6, 0(t3)\n  sb a6, 0(t4)\n" ++
  "  addi t3, t3, 1\n  addi t4, t4, -1\n  addi t5, t5, -1\n" ++
  "  bnez t5, .Lcve_addr\n" ++
  -- parent frame env
  "  li t0, 1000000\n  sd t0, 568(x20)\n" ++   -- gasRemaining
  "  li t0, 10\n  sd t0, 496(x20)\n" ++          -- codeSize (10-byte parent program)
  "  sd x0, 448(x20)\n" ++                       -- persistentLogLength = 0
  "  sd x0, 456(x20); sd x0, 464(x20)\n" ++
  "  sd x0, 472(x20); sd x0, 480(x20); sd x0, 488(x20)\n" ++
  "  la t0, evm_call_depth; sd x0, 0(t0)\n" ++
  -- CALL stack: 7 args at x12 = evm_stack_top - 224 (gas@0, to@32, value@64, ...).
  "  la x12, evm_stack_top\n" ++
  "  addi x12, x12, -224\n" ++
  "  mv t1, x12\n  li t2, 28\n" ++               -- zero 28 dwords (224 bytes)
  ".Lcve_zero:\n" ++
  "  sd x0, 0(t1)\n  addi t1, t1, 8\n  addi t2, t2, -1\n  bnez t2, .Lcve_zero\n" ++
  "  li t0, 50000\n  sd t0, 0(x12)\n" ++         -- gas
  -- to = ALICE (self): copy the canonical 20-byte addr (input+24) into the to-word x12+32.
  "  li t0, 0x40000000\n  addi t0, t0, 24\n  addi t1, x12, 32\n  li t2, 20\n" ++
  ".Lcve_to:\n" ++
  "  lbu a6, 0(t0)\n  sb a6, 0(t1)\n  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  bnez t2, .Lcve_to\n" ++
  "  li t0, 50\n  sd t0, 64(x12)\n" ++            -- value = 50 (< caller balance 1000 -> .Lcd_balok)
  -- dispatcher invariants (set last)
  "  la x13, evm_memory\n" ++
  "  la x10, cve_parent_code\n" ++
  "  la x21, cve_parent_code\n" ++
  "  j .dispatch_loop\n" ++
  emitRuntimeDispatcherLoop ++ "\n" ++
  frameBaseFunction ++ "\n" ++
  frameDepthPushFunction ++ "\n" ++
  frameDepthPopFunction ++ "\n" ++
  frameSaveRegsFunction ++ "\n" ++
  frameLoadRegsFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  callFrameSetCalldataFunction ++ "\n" ++
  callFrameForwardGasFunction ++ "\n" ++
  callFrameDescendFunction ++ "\n" ++
  frameReturnFunction ++ "\n" ++
  createFrameDescendFunction ++ "\n" ++
  codeAtHeaderStateRootFunction ++ "\n" ++
  accountAtHeaderStateRootFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  recordNonstorageEffectFunction ++ "\n" ++
  nonstorageEffectLatestBalanceFunction

def callValueEffectData : String :=
  emitRuntimeDispatcherDataSection callFrameGuestRegistry ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "frame_call_ctx:\n  .zero 32800\n" ++
  ".balign 16\n" ++
  "frame_parent_bases:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "rb_running_block_bloom:\n  .zero 256\n" ++
  "rb_running_receipt_bloom:\n  .zero 256\n" ++
  "rb_bloom_checkpoints:\n  .zero 262144\n" ++
  ".balign 8\n" ++
  "cd_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "cd_zero_word:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "cd_caller_be:\n  .zero 32\n" ++
  "cd_callee_be:\n  .zero 32\n" ++
  "cd_value_be:\n  .zero 32\n" ++
  "cd_balance_be:\n  .zero 32\n" ++
  "cd_caller_newbal:\n  .zero 32\n" ++
  "cd_xfer_gas_precharged:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "cahsr_state_root:\n  .zero 32\n" ++
  "cahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 8\n" ++
  "cahsr_code_offset:\n  .zero 8\n" ++
  "cahsr_code_length:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  -- parent: CALL; PUSH1 0; SSTORE; PUSH1 0xAB; PUSH1 1; SSTORE; STOP.
  "cve_parent_code:\n  .byte 0xf1, 0x60, 0x00, 0x55, 0x60, 0xab, 0x60, 0x01, 0x55, 0x00\n" ++
  ".balign 8\n" ++
  "cve_tail_pad:\n  .byte 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef\n"

def callValueEffectUnit : BuildUnit := {
  body        := []
  prologueAsm := callValueEffectPrologue
  epilogueAsm := emitDispatcherEpilogue callFrameGuestRegistry evmAddEpilogue
  dataAsm     := callValueEffectData
}

end EvmAsm.Codegen
