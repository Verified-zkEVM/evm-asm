/-
  EvmAsm.Codegen.Programs.CallDepthLimit

  `zisk_call_depth_limit` -- focused probe for the CALL-family handler depth
  cap. It mirrors the depth-gate prefix and fail tail in `callDescendFallThrough`:
  when `evm_call_depth >= 1024`, the handler pops the CALL args, pushes 0,
  advances the parent PC, and resumes without entering `call_frame_descend`.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.ChildFrameHandlerTailHelpers

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Probe the depth-limit branch with the same live register convention as the
    CALL handler. Output u64s at `OUTPUT_ADDR`:
      +0  evm_call_depth after (expect 1024)
      +8  pushed CALL result   (expect 0)
      +16 stack delta          (expect 192)
      +24 parent PC after      (expect 0x501) -/
def callDepthLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, evm_call_depth; li t1, 1024; sd t1, 0(t0)\n" ++
  "  la x12, cdl_stack\n" ++
  "  mv s1, x12\n" ++
  "  mv t1, x12\n  li t2, 28\n" ++
  ".Lcdl_zero:\n" ++
  "  sd x0, 0(t1)\n  addi t1, t1, 8\n  addi t2, t2, -1\n  bnez t2, .Lcdl_zero\n" ++
  "  li t0, 50000\n  sd t0, 0(x12)\n" ++
  "  li t0, 0x42\n  sd t0, 32(x12)\n" ++
  "  li x10, 0x500\n" ++
  "  la x13, cdl_mem\n" ++
  "  la x20, cdl_env\n" ++
  "  li x21, 0x600\n" ++
  -- Mirrors `callDescendFallThrough`: depth gate before balance/code lookup.
  "  la t0, evm_call_depth\n" ++
  "  ld t0, 0(t0)\n" ++
  "  li t1, 1024\n" ++
  "  bgeu t0, t1, .Lcdl_fail\n" ++
  "  li t2, 0xee\n  sd t2, 8(s0)\n  j .Lcdl_done\n" ++
  -- Mirrors the CALL fail tail: pop 192 bytes, push zero word, advance PC.
  ".Lcdl_fail:\n" ++
  "  addi x12, x12, 192\n" ++
  "  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  ld t1, 0(x12); sd t1, 8(s0)\n" ++
  "  sub t1, x12, s1; sd t1, 16(s0)\n" ++
  "  sd x10, 24(s0)\n" ++
  ".Lcdl_done:"

def callDepthLimitData : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "cdl_stack:\n  .zero 256\n" ++
  "cdl_mem:\n  .zero 64\n" ++
  "cdl_env:\n  .zero 640\n"

def callDepthLimitUnit : BuildUnit := {
  body        := NOP
  prologueAsm := callDepthLimitPrologue
  dataAsm     := callDepthLimitData
}

/-- Exercise the exact shared precompile depth-failure tail.  Unlike
    `callDepthLimitPrologue`, which preserves the historical generic-tail
    mirror, this probe invokes `precompileDepthGateAsm` itself and returns to
    the dispatcher-resume label that the production tail targets. -/
def precompileDepthLimitPrologue (labelStem : String) (target : Nat) : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, evm_call_depth; li t1, 1024; sd t1, 0(t0)\n" ++
  "  la x12, cdl_stack\n" ++
  "  mv s1, x12\n" ++
  "  mv t1, x12\n  li t2, 28\n" ++
  ".Lcdl_pre_zero_" ++ labelStem ++ ":\n" ++
  "  sd x0, 0(t1)\n  addi t1, t1, 8\n  addi t2, t2, -1\n  bnez t2, .Lcdl_pre_zero_" ++ labelStem ++ "\n" ++
  "  li t0, 50000\n  sd t0, 0(x12)\n" ++
  "  li t0, " ++ toString target ++ "\n  sd t0, 32(x12)\n" ++
  "  li x10, 0x500\n" ++
  "  la x13, cdl_mem\n" ++
  "  la x20, cdl_env\n" ++
  -- At depth 1024 this takes the shared gate; its `dispatchContinueRet`
  -- returns here, exactly as it returns to the production dispatcher resume.
  precompileDepthGateAsm labelStem 192 ++
  "  li t0, 0xee\n  sd t0, 8(s0)\n" ++
  ".Ldispatch_resume:\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  ld t1, 0(x12); sd t1, 8(s0)\n" ++
  "  sub t1, x12, s1; sd t1, 16(s0)\n" ++
  "  sd x10, 24(s0)\n"

/-- Ordinary supported-precompile placement: target 0x01 (ECRECOVER). -/
def callDepthPrecompileLimitUnit : BuildUnit := {
  body        := NOP
  prologueAsm := precompileDepthLimitPrologue "cdl_precompile" 1
  dataAsm     := callDepthLimitData ++ ".balign 8\nevm_precompile_frame:\n  .zero 16\n"
}

/-- EIP-4788 placement: target is the beacon-roots system contract's low word.
    The shared gate runs before its current/stale split. -/
def callDepthEip4788LimitUnit : BuildUnit := {
  body        := NOP
  prologueAsm := precompileDepthLimitPrologue "cdl_eip4788" 0x0000000000004788
  dataAsm     := callDepthLimitData ++ ".balign 8\nevm_precompile_frame:\n  .zero 16\n"
}

end EvmAsm.Codegen
