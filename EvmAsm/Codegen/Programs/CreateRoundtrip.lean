/-
  EvmAsm.Codegen.Programs.CreateRoundtrip

  `zisk_create_roundtrip` — end-to-end verification of the INLINE CREATE descent
  (bead fhsxz.2.4.2.61.8) through the REAL dispatch loop.

  Earlier work established that the CREATE/CREATE2 descent is wired INLINE in
  `childFrameHandlers`' createUnsupportedTail (stage init code + the bounded
  mini-interpreter + push the deployed address); the standalone create_descend
  (#8579/#8581) is an unused dup. But only create_descend was probe-tested — the
  inline TAIL (the path the guest/verdict actually run) was never exercised through
  the dispatch loop. This probe closes that gap and is the verification harness for
  the deposit (.8b-2), nonce bookkeeping (.8b-3), and self-contained-gate activation
  (.8c).

  Setup: a depth-0 frame whose memory is pre-loaded with init code and whose
  bytecode does a CREATE then SSTOREs the result:

    init code @ mem[0] (10 B): PUSH1 0xAA; PUSH1 0; MSTORE8; PUSH1 1; PUSH1 0; RETURN
      → MSTORE8 mem[0]=0xAA, RETURN(0,1) returns the 1-byte deployed code {0xAA}.
    parent code (11 B): PUSH1 10; PUSH1 0; PUSH1 0; CREATE; PUSH1 0; SSTORE; STOP
      → CREATE(value=0, offset=0, size=10) stages mem[0..10], runs the mini-interp
        (create_child_status=2, deployed {0xAA}), pushes the derived address; then
        PUSH1 0; SSTORE writes the address to storage slot 0; STOP halts at depth 0.

  No account-witness context is attached (env+584 = 0), so the tail takes the clean
  path (skip balance/collision gates, create_nonce defaults to 0) and the address is
  keccak(rlp([env.ADDRESS, 0]))[12:] — non-zero. A correct round trip therefore
  writes storage slot 0 = the (non-zero) deployed address. The check script asserts
  halt_kind 0, one emitted slot, slot key 0, and a NON-ZERO slot value (CREATE
  deployed + pushed an address through the inline tail).
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.EvmBasic

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def createRoundtripPrologue : String :=
  -- Depth-0 frame setup (empty stack; parent runs the CREATE bytecode directly).
  "  la sp, lp64_sp_top\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++
  "  la x12, evm_stack_top\n" ++                    -- empty stack (grows down)
  "  la x10, cr_parent_code\n" ++
  "  la x21, cr_parent_code\n" ++
  "  li t0, 1000000\n  sd t0, 568(x20)\n" ++        -- gasRemaining
  "  li t0, 11\n  sd t0, 496(x20)\n" ++             -- codeSize (parent code len)
  "  sd x0, 448(x20); sd x0, 456(x20); sd x0, 464(x20)\n" ++   -- storage log length etc.
  "  sd x0, 472(x20); sd x0, 480(x20)\n" ++
  "  sd x0, 584(x20)\n" ++                          -- no account-witness ctx -> clean CREATE path
  "  la t0, evm_call_depth; sd x0, 0(t0)\n" ++
  -- Pre-load the 10-byte init code into evm_memory[0..10].
  "  la t1, cr_init_code; la t2, evm_memory; li t3, 10\n" ++
  ".Lcr_preload:\n" ++
  "  beqz t3, .Lcr_preload_done\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lcr_preload\n" ++
  ".Lcr_preload_done:\n" ++
  "  j .dispatch_loop\n" ++
  emitRuntimeDispatcherLoop ++ "\n" ++
  -- Frame helpers (mirror call_roundtrip: the opcode witness helpers come from the
  -- epilogue; including the full embedded-helper block would double-define them).
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

def createRoundtripData : String :=
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
  -- parent: PUSH1 10; PUSH1 0; PUSH1 0; CREATE; PUSH1 0; SSTORE; STOP.
  "cr_parent_code:\n  .byte 0x60, 0x0a, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x60, 0x00, 0x55, 0x00\n" ++
  -- init code: PUSH1 0xAA; PUSH1 0; MSTORE8; PUSH1 1; PUSH1 0; RETURN -> deploys {0xAA}.
  "cr_init_code:\n  .byte 0x60, 0xaa, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xf3\n" ++
  ".balign 8\n" ++
  -- Non-zero tail pad: ziskemu zeroes the final .data bytes, which would corrupt the
  -- last code byte (memory: ziskemu-zeroes-data-tail-pad-probe-fixtures).
  "cr_tail_pad:\n  .byte 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef\n"

def createRoundtripUnit : BuildUnit := {
  body        := []
  prologueAsm := createRoundtripPrologue
  epilogueAsm := emitDispatcherEpilogue callFrameProbeRegistry evmAddEpilogue
  dataAsm     := createRoundtripData
}

end EvmAsm.Codegen
