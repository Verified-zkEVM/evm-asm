/-
  EvmAsm.Codegen.Programs.CallFrameRoundtrip

  `zisk_call_roundtrip` — end-to-end verification of the nested-call cycle through
  the REAL dispatch loop (bead .61.6.6): descend into a child frame, run the child,
  and have its STOP RESUME the parent instead of halting the guest.

  It is a self-contained dispatcher (the `callFrameProbeRegistry`: depth-aware STOP
  + push-0 CALL, so it does not pull in the code-resolution tree) with the embedded
  frame helpers linked. The `_start` sets up a depth-0 parent frame and descends
  MANUALLY via `call_frame_descend` (with a fixed child-code blob, so no witness /
  `code_at_header_state_root` is needed), then `j .dispatch_loop`:

    child code = [PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 0x5a; PUSH2 299; MSTORE8;
                  PUSH2 300; PUSH1 0; RETURN]
      → MSTORE is a GUARDED opcode running in the child frame — it exercises the
        frame-relative stack-underflow guard (the child's x12 lives in the call
        arena, above the global stack); a broken/global guard would underflow →
        guest halt_kind 7. It writes mem[0..32), plants marker mem[299] = 0x5a,
        then RETURN(0, 300) returns 300 B — past the retired 256-byte cap.
      → depth-aware RETURN sees depth>0 → `frame_return` → stages the FULL
        300-byte returndata into `evm_precompile_frame` and restores the parent
        at pc+1.
    parent code = [<descend placeholder>, RETURNDATASIZE, PUSH1 0, SSTORE,
                   PUSH1 1, PUSH2 299, PUSH1 31, RETURNDATACOPY,
                   PUSH1 0, MLOAD, PUSH1 1, SSTORE, STOP]
      → RETURNDATASIZE reads the staged size (300) → slot 0; RETURNDATACOPY
        copies returndata[299] (start+size = 300 ≤ retlen, spec-legal; the old
        256-cap guard would have .exit_invalid'd — evm-asm-pwqhw) into mem[31];
        MLOAD(0) → slot 1 = 0x5a; `STOP` halts at depth 0.

  So a correct round trip writes slot 0 = 300 (true staged size) and slot 1 =
  0x5a (a byte copied from past the old cap) — exercising the frame-relative
  guard (#8539), full-length returndata staging (#8541 + evm-asm-pwqhw), and the
  cap-free h_RETURNDATACOPY end-to-end. The check script asserts both pairs and
  halt_kind 0.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.EvmBasic

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def callFrameRoundtripPrologue : String :=
  -- Parent frame (depth 0) setup.
  "  la sp, lp64_sp_top\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++
  -- Simulate the 7 CALL args on the parent stack (x12 = evm_stack_top - 7*32):
  -- frame_return pops netPopBytes (192 = 6 words) and pushes the result, landing
  -- x12 at evm_stack_top - 32 (one result word), as a real CALL would.
  "  la x12, evm_stack_top\n" ++
  "  addi x12, x12, -224\n" ++
  "  la x10, rt_parent_code\n" ++
  "  la x21, rt_parent_code\n" ++
  "  li t0, 1000000\n  sd t0, 568(x20)\n" ++       -- parent gasRemaining
  "  li t0, 20\n  sd t0, 496(x20)\n" ++             -- parent codeSize
  "  sd x0, 448(x20); sd x0, 456(x20); sd x0, 464(x20)\n" ++
  "  sd x0, 472(x20); sd x0, 480(x20)\n" ++
  "  la t0, evm_call_depth; sd x0, 0(t0)\n" ++
  -- Build the call descriptor for the manual descend (child = rt_child_code).
  "  la t2, rt_cd_desc\n" ++
  "  la t3, rt_to_word; sd t3, 0(t2)\n" ++          -- to_ptr (dummy)
  "  la t3, rt_cd_zero; sd t3, 8(t2)\n" ++          -- value_ptr = zero word
  "  sd x0, 16(t2)\n" ++                            -- is_static = 0
  "  sd x0, 24(t2); sd x0, 32(t2)\n" ++             -- argsOff / argsLen = 0
  "  sd x0, 40(t2); sd x0, 48(t2)\n" ++             -- outOff / outSize = 0
  "  li t3, 192; sd t3, 56(t2)\n" ++                -- netPopBytes
  "  la t3, rt_child_code; sd t3, 64(t2)\n" ++      -- code_ptr = child code
  "  li t3, 17; sd t3, 72(t2)\n" ++                 -- code_len (MSTORE word; MSTORE8 marker@299; RETURN(0,300))
  "  li t3, 100000; sd t3, 80(t2)\n" ++             -- requested_gas
  "  sd x0, 88(t2)\n" ++                            -- value_nonzero = 0
  "  la a1, rt_cd_desc\n" ++
  "  jal ra, call_frame_descend\n" ++
  "  j .dispatch_loop\n" ++
  emitRuntimeDispatcherLoop ++ "\n" ++
  -- Only the FRAME helpers (the opcode witness helpers are already emitted by the
  -- epilogue, so including the full embedded-helper block would double-define them).
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
  createFrameDescendFunction ++ "\n" ++   -- .61.8.3.5: CREATE tail (shared registry) descends via create_frame_descend
  frameReturnFunction ++ "\n" ++
  recordNonstorageEffectFunction ++ "\n" ++   -- i3djw.2: CREATE-RETURN deposit records the created account's non-storage effect
  -- Probe-local LINK stubs for helper functions the emitted CALL/CREATE/witness
  -- handler tails `jal` into. This probe's bytecode never executes a CALL /
  -- CREATE / BALANCE / EXTCODE* opcode (the descend is manual), so none of
  -- these are reachable; they exist only so the standalone probe links after
  -- the shared registry grew these dependencies.
  "account_at_header_state_root: ret\n" ++
  "account_extract_nonce: ret\n" ++
  "bal_same_block_delegation_code_resolve: ret\n" ++
  "code_at_header_state_root: ret\n" ++
  "evm_storage_access_seed_key: ret\n" ++
  "account_state_latest_balance: ret\n" ++
  "rlp_list_count_items: ret\n" ++
  "u256_add_be: ret\n" ++
  "u256_sub_be: ret\n" ++
  "witness_codes_lookup_by_hash: ret"

def callFrameRoundtripData : String :=
  emitRuntimeDispatcherDataSection callFrameProbeRegistry ++ "\n" ++
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
  -- Probe-local DATA stubs (`la`-referenced by the emitted handler tails; not
  -- reached by this probe's bytecode — see the text-stub comment above).
  ".balign 32\n" ++
  "evm_halt_flag:\n  .zero 8\n" ++
  "bsr_addr_4788:\n  .zero 32\n" ++
  "bv_eip4788_current_fast_seen:\n  .zero 8\n" ++
  "cahsr_code_length:\n  .zero 8\n" ++
  "cahsr_code_offset:\n  .zero 8\n" ++
  "callee_balance_count:\n  .zero 8\n" ++
  "callee_balance_table:\n  .zero 512\n" ++
  "cd_balance_be:\n  .zero 32\n" ++
  "cd_callee_be:\n  .zero 32\n" ++
  "cd_new_account_charged_current:\n  .zero 8\n" ++
  "cd_value_be:\n  .zero 32\n" ++
  "cd_xfer_gas_precharged:\n  .zero 8\n" ++
  "swd_4788_root_slot:\n  .zero 32\n" ++
  "swd_4788_root_val:\n  .zero 40\n" ++
  "swd_4788_root_vlen:\n  .zero 8\n" ++
  "swd_4788_slot:\n  .zero 32\n" ++
  "swd_ts_be8:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "rt_cd_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "rt_cd_zero:\n  .zero 32\n" ++
  "rt_to_word:\n  .zero 32\n" ++
  ".balign 8\n" ++
  -- parent: [descend-placeholder, RETURNDATASIZE, PUSH1 0x00, SSTORE,
  --          PUSH1 0x01, PUSH2 0x012b, PUSH1 0x1f, RETURNDATACOPY,
  --          PUSH1 0x00, MLOAD, PUSH1 0x01, SSTORE, STOP].
  -- On the child's return the parent resumes at pc+1 (RETURNDATASIZE), which reads
  -- the child's 300-byte returndata size from evm_precompile_frame (staged by
  -- frame_return) and SSTOREs it to slot 0 (== 300 proves true-length staging).
  -- Then RETURNDATACOPY(dest=31, offset=299, size=1) reads PAST the retired
  -- 256-byte cap (start+size = 300 ≤ retlen matches execution-specs; the old
  -- guard (3) would .exit_invalid here — evm-asm-pwqhw) into mem[31], and
  -- MLOAD(0) → SSTORE slot 1 records the copied marker (== 0x5a).
  "rt_parent_code:\n  .byte 0x00, 0x3d, 0x60, 0x00, 0x55\n" ++
  "  .byte 0x60, 0x01, 0x61, 0x01, 0x2b, 0x60, 0x1f, 0x3e\n" ++
  "  .byte 0x60, 0x00, 0x51, 0x60, 0x01, 0x55, 0x00\n" ++
  -- child: PUSH1 0x42; PUSH1 0; MSTORE;             (mem[0..32) word, byte31=0x42)
  --        PUSH1 0x5a; PUSH2 0x012b; MSTORE8;       (marker mem[299] = 0x5a)
  --        PUSH2 0x012c; PUSH1 0; RETURN.           (RETURN(0, 300) — > 256)
  -- The MSTORE is a GUARDED opcode running in the child frame — it exercises the
  -- frame-relative underflow guard (a child-frame x12 in the call arena). The
  -- 300-byte return exceeds the retired 256-byte staging cap so the roundtrip
  -- witnesses full-length staging end-to-end.
  "rt_child_code:\n  .byte 0x60, 0x42, 0x60, 0x00, 0x52\n" ++
  "  .byte 0x60, 0x5a, 0x61, 0x01, 0x2b, 0x53\n" ++
  "  .byte 0x61, 0x01, 0x2c, 0x60, 0x00, 0xf3\n" ++
  ".balign 8\n" ++
  -- Non-zero tail pad. ziskemu reads the final bytes of `.data` as 0 (the
  -- data-tail-zeroing artifact, memory: ziskemu-zeroes-data-tail-pad-probe-
  -- fixtures). Without a pad after `rt_child_code` its last byte (0xf3 RETURN)
  -- would be silently zeroed to 0x00 (STOP), so the child would run a guard-free
  -- STOP and never exercise the depth-aware RETURN this probe is meant to verify.
  "rt_tail_pad:\n  .byte 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef\n"

def callFrameRoundtripUnit : BuildUnit := {
  body        := []
  prologueAsm := callFrameRoundtripPrologue
  epilogueAsm := emitDispatcherEpilogue callFrameProbeRegistry evmAddEpilogue
  dataAsm     := callFrameRoundtripData
}

end EvmAsm.Codegen
