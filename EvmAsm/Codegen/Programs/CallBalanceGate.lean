/-
  EvmAsm.Codegen.Programs.CallBalanceGate

  `zisk_call_balance_gate` — positive verification of the value-bearing CALL
  balance gate (bead fhsxz.2.4.2.61.6.4.1 / PR #8540) through the REAL dispatch
  loop with a genuine account-witness context.

  The gate (`callDescendFallThrough`, ChildFrameHandlers.lean) rejects a
  value-bearing CALL/CALLCODE — pushing 0 and NOT descending — when the caller's
  **live** balance is below the transfer value. The handlers read env+32
  (`.selfBalance`), not `balance_live_else_header_state_root` (drj99.1; #11019).
  This probe drives the live `callFrameGuestRegistry` h_CALL handler (with the
  gate wired in, unlike the push-0 `callFrameProbeRegistry`) so the rejection
  is exercised end-to-end.

  Setup (witness supplied at runtime via `ziskemu -i`, built by
  codegen-zisk-call-balance-gate-check.sh, reusing the balance-at-header-state-root
  fixture in `account` mode):
    * the caller account (env.ADDRESS) exists in the state trie with balance 100;
    * the parent runs:  CALL; PUSH1 0; SSTORE; PUSH1 0xAB; PUSH1 1; SSTORE; STOP
      with a CALL whose value word = 200 (> 100) to a non-precompile callee.

  A correct gate: value 200 > balance 100 → push 0, advance PC past the CALL,
  WITHOUT descending (evm_call_depth stays 0). The parent then SSTOREs the CALL
  result (0) to slot 0 and a sentinel 0xAB to slot 1, proving (a) the call was
  rejected (slot 0 == 0) and (b) the parent resumed and ran to completion (slot 1
  == 0xAB). The check script asserts halt 0, two emitted slots, slot 0 == 0,
  slot 1 == 0xAB.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.EvmBasic

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def callBalanceGatePrologue : String :=
  "  la sp, lp64_sp_top\n" ++
  "  la x20, evm_env\n" ++
  -- Read the account-witness from the ziskemu input region (8-byte length prefix
  -- at INPUT_ADDR+0, then the record: header_len(8) state_len(8) addr(20) header state).
  "  li t0, 0x40000000\n" ++
  "  ld t1, 8(t0)\n" ++              -- header_len
  "  ld t2, 16(t0)\n" ++             -- state_len
  "  addi t3, t0, 44\n" ++           -- header ptr
  "  add t4, t3, t1\n" ++            -- state ptr = header ptr + header_len
  "  sd t3, 576(x20)\n" ++           -- env witness header ptr
  "  sd t1, 584(x20)\n" ++           -- env witness header len (nonzero -> gate engages)
  "  sd t4, 592(x20)\n" ++           -- env witness state ptr
  "  sd t2, 600(x20)\n" ++           -- env witness state len
  "  sd x0, 608(x20)\n" ++           -- codes ptr (unused: gate fails before code resolution)
  "  sd x0, 616(x20)\n" ++           -- codes len
  -- caller ADDRESS (env+0..19): store the canonical 20-byte addr REVERSED so the
  -- gate's env+19..env+0 read reconstructs the canonical big-endian address.
  "  addi t3, t0, 24\n" ++           -- src = canonical addr (MSB first)
  "  addi t4, x20, 19\n" ++          -- dst = env+19 (descending)
  "  li t5, 20\n" ++
  ".Lcbg_addr:\n" ++
  "  lbu a6, 0(t3)\n  sb a6, 0(t4)\n" ++
  "  addi t3, t3, 1\n  addi t4, t4, -1\n  addi t5, t5, -1\n" ++
  "  bnez t5, .Lcbg_addr\n" ++
  -- parent frame env
  "  li t0, 1000000\n  sd t0, 568(x20)\n" ++   -- gasRemaining
  "  li t0, 10\n  sd t0, 496(x20)\n" ++          -- codeSize (10-byte parent program)
  "  sd x0, 448(x20)\n" ++                       -- persistentLogLength = 0
  "  sd x0, 464(x20)\n" ++
  "  sd x0, 472(x20); sd x0, 488(x20)\n" ++
  "  la t0, evm_call_depth; sd x0, 0(t0)\n" ++
  -- CALL stack: 7 args at x12 = evm_stack_top - 224 (gas@0, to@32, value@64, ...).
  "  la x12, evm_stack_top\n" ++
  "  addi x12, x12, -224\n" ++
  "  mv t1, x12\n  li t2, 28\n" ++               -- zero 28 dwords (224 bytes)
  ".Lcbg_zero:\n" ++
  "  sd x0, 0(t1)\n  addi t1, t1, 8\n  addi t2, t2, -1\n  bnez t2, .Lcbg_zero\n" ++
  "  li t0, 50000\n  sd t0, 0(x12)\n" ++         -- gas (unused on the fail path)
  "  li t0, 0x42\n  sd t0, 32(x12)\n" ++          -- to = 0x42 (non-precompile -> gate)
  "  li t0, 200\n  sd t0, 64(x12)\n" ++           -- value = 200 (> caller balance 100)
  -- dispatcher invariants (set last)
  "  la x13, evm_memory\n" ++
  "  la x10, cbg_parent_code\n" ++
  "  la x21, cbg_parent_code\n" ++
  "  j .dispatch_loop\n" ++
  emitRuntimeDispatcherLoop ++ "\n" ++
  -- Frame helpers (the opcode witness helpers come from the epilogue; the gate's
  -- descend arm references call_frame_descend/frame_return even though the
  -- insufficient-balance path never reaches them).
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
  sparseWindowReadFunction ++ "\n" ++   -- referenced by the guest registry's depth-aware RETURN/REVERT tails
  sparseWindowWriteFunction ++ "\n" ++
  -- The CREATE handler's descend arm and the CALL gate's code-resolution arm are
  -- assembled (though the insufficient-balance path never runs them), so their
  -- symbols must resolve.
  createFrameDescendFunction ++ "\n" ++
  codeAtHeaderStateRootFunction ++ "\n" ++
  -- i3djw.1: the value-bearing balance gate now also runs the non-storage effect producer
  -- (account_at_header_state_root + u256_add_be + record_nonstorage_effect). The reject path
  -- in this probe never runs them, but the symbols must resolve.
  accountAtHeaderStateRootFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  recordNonstorageEffectFunction

def callBalanceGateData : String :=
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
  -- CALL balance-gate scratch (callDescendFallThrough): call descriptor, zero
  -- value word, and the caller addr / value / looked-up balance compare buffers.
  ".balign 8\n" ++
  "cd_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "cd_zero_word:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "cd_caller_be:\n  .zero 32\n" ++
  "cd_value_be:\n  .zero 32\n" ++
  "cd_balance_be:\n  .zero 32\n" ++
  "cd_caller_newbal:\n  .zero 32\n" ++
  -- code_at_header_state_root scratch (referenced by the gate's code-resolution
  -- arm, assembled but not run on the insufficient-balance path).
  ".balign 32\n" ++
  "cahsr_state_root:\n  .zero 32\n" ++
  "cahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 8\n" ++
  "cahsr_code_offset:\n  .zero 8\n" ++
  "cahsr_code_length:\n  .zero 8\n" ++
  -- account_at_header_state_root scratch (i3djw.1 producer's callee balance/nonce lookup).
  ".balign 32\n" ++
  "aahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  -- parent: CALL; PUSH1 0; SSTORE; PUSH1 0xAB; PUSH1 1; SSTORE; STOP.
  "cbg_parent_code:\n  .byte 0xf1, 0x60, 0x00, 0x55, 0x60, 0xab, 0x60, 0x01, 0x55, 0x00\n" ++
  ".balign 8\n" ++
  -- Non-zero tail pad: ziskemu zeroes the final .data bytes; keep STOP intact.
  "cbg_tail_pad:\n  .byte 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef\n"


end EvmAsm.Codegen
