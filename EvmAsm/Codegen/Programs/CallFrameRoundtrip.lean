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

    child code = [PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 0x20; PUSH1 0; RETURN]
      → MSTORE is a GUARDED opcode running in the child frame — it exercises the
        frame-relative stack-underflow guard (the child's x12 lives in the call
        arena, above the global stack); a broken/global guard would underflow →
        guest halt_kind 7. It writes mem[0]=0x42, then RETURN(0,32) returns 32 B.
      → depth-aware RETURN sees depth>0 → `frame_return` → stages the 32-byte
        returndata into `evm_precompile_frame` and restores the parent at pc+1.
    parent code = [<descend placeholder>, RETURNDATASIZE, PUSH1 0, SSTORE, STOP]
      → RETURNDATASIZE reads the staged size (32) and `PUSH1 0; SSTORE` writes it
        to slot 0; `STOP` halts at depth 0.

  So a correct round trip writes storage slot 0 = 32 (the child returndata size) —
  exercising the frame-relative guard (#8539) AND the returndata staging (#8541)
  end-to-end. The check script asserts the dedup'd storage pair is (slot 0, 32)
  and halt_kind 0.
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
  "  li t0, 6\n  sd t0, 496(x20)\n" ++              -- parent codeSize
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
  "  li t3, 10; sd t3, 72(t2)\n" ++                 -- code_len (PUSH1 0x42;PUSH1 0;MSTORE;PUSH1 0x20;PUSH1 0;RETURN)
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
  recordNonstorageEffectFunction   -- i3djw.2: CREATE-RETURN deposit records the created account's non-storage effect

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
  ".balign 8\n" ++
  "rt_cd_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "rt_cd_zero:\n  .zero 32\n" ++
  "rt_to_word:\n  .zero 32\n" ++
  ".balign 8\n" ++
  -- parent: [descend-placeholder, RETURNDATASIZE, PUSH1 0x00, SSTORE, STOP].
  -- On the child's return the parent resumes at pc+1 (RETURNDATASIZE), which reads
  -- the child's 32-byte returndata size from evm_precompile_frame (staged by
  -- frame_return), then SSTOREs it to slot 0 (so slot 0 == 32 proves the staging).
  "rt_parent_code:\n  .byte 0x00, 0x3d, 0x60, 0x00, 0x55, 0x00\n" ++
  -- child: PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 0x20; PUSH1 0; RETURN. The MSTORE
  -- is a GUARDED opcode running in the child frame — it exercises the
  -- frame-relative underflow guard (a child-frame x12 in the call arena). It
  -- writes mem[0]=0x42 then RETURN(0,32) returns a 32-byte buffer.
  "rt_child_code:\n  .byte 0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3\n" ++
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
