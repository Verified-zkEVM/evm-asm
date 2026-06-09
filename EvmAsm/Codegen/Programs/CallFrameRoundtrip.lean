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

    child code = [STOP]                      → runs at the child frame (depth 1)
      → depth-aware STOP sees depth>0 → `frame_return` → restores the parent
      → parent resumes at parent_pc+1
    parent code = [<descend placeholder>, PUSH1 0, SSTORE, STOP]
      → the success word `frame_return` pushed is on the parent stack
      → `PUSH1 0; SSTORE` stores it to slot 0; `STOP` halts at depth 0

  So a correct round trip writes storage slot 0 = 1 (the propagated success word).
  The check script asserts OUTPUT's dedup'd storage pair is (slot 0, value 1) and
  halt_kind 0 — i.e. the child returned to the parent and success propagated.
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
  "  li t0, 5\n  sd t0, 496(x20)\n" ++              -- parent codeSize
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
  "  li t3, 1; sd t3, 72(t2)\n" ++                  -- code_len
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
  frameReturnFunction

def callFrameRoundtripData : String :=
  emitRuntimeDispatcherDataSection callFrameProbeRegistry ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "frame_call_ctx:\n  .zero 32800\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x29000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "rt_cd_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "rt_cd_zero:\n  .zero 32\n" ++
  "rt_to_word:\n  .zero 32\n" ++
  ".balign 8\n" ++
  -- parent: [descend-placeholder, PUSH1 0x00, SSTORE, STOP]; child: [STOP]
  "rt_parent_code:\n  .byte 0x00, 0x60, 0x00, 0x55, 0x00\n" ++
  "rt_child_code:\n  .byte 0x00\n"

def callFrameRoundtripUnit : BuildUnit := {
  body        := []
  prologueAsm := callFrameRoundtripPrologue
  epilogueAsm := emitDispatcherEpilogue callFrameProbeRegistry evmAddEpilogue
  dataAsm     := callFrameRoundtripData
}

end EvmAsm.Codegen
