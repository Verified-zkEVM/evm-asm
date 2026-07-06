/-
  EvmAsm.EL.PrecompileCallOutputBridge

  Pure bridge from precompile CALL results to caller-memory output-copy bytes.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.CallOutputArgsMemory
import EvmAsm.EL.PrecompileCallBridge

namespace EvmAsm.EL

namespace PrecompileCallOutputBridge

abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult
abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev Byte := EvmAsm.EL.Byte

/-- Byte written to caller memory by a precompile result's CALL output copy. -/
def precompileOutputByteAt
    (state : WorldState) (result : PrecompileResult) (range : MemoryRange)
    (addr : Nat) : Byte :=
  CallOutputMemory.callOutputByteAt
    (PrecompileCallBridge.callResultFromPrecompile state result) range addr

/-- CALL-argument specialization for precompile output copy. -/
def precompileCallOutputByteFromArgs
    (state : WorldState) (result : PrecompileResult) (args : CallArgs)
    (addr : Nat) : Byte :=
  precompileOutputByteAt state result args.output addr

/-- STATICCALL-argument specialization for precompile output copy. -/
def precompileStaticCallOutputByteFromArgs
    (state : WorldState) (result : PrecompileResult) (args : StaticCallArgs)
    (addr : Nat) : Byte :=
  precompileOutputByteAt state result args.output addr

/-- Output byte for an attempted known-cost precompile dispatch. `none` means the
    caller should continue down the non-precompile/payload-specific path. -/
def attemptedKnownCostPrecompileOutputByte
    (input : MessageCallExecution.CallExecutionInput) (out : List Byte)
    (range : MemoryRange) (addr : Nat) : Option Byte :=
  (PrecompileCallBridge.attemptKnownCostPrecompileCall input out).map
    (fun result => CallOutputMemory.callOutputByteAt result range addr)

theorem precompileOutputByteAt_eq
    (state : WorldState) (result : PrecompileResult) (range : MemoryRange)
    (addr : Nat) :
    precompileOutputByteAt state result range addr =
      CallOutputMemory.callOutputByteAt
        (PrecompileCallBridge.callResultFromPrecompile state result) range addr := rfl

theorem precompileOutputByteAt_success
    (state : WorldState) (out : List Byte) (gasRemaining : Nat)
    (range : MemoryRange) (addr : Nat) :
    precompileOutputByteAt state
        (EvmAsm.Evm64.PrecompileResult.ok out gasRemaining) range addr =
      CallOutputMemory.callOutputByteAt
        { status := .success
          state := state
          output := out
          gasRemaining := gasRemaining }
        range addr := rfl

theorem precompileOutputByteAt_failure
    (state : WorldState) (gasRemaining : Nat) (range : MemoryRange) (addr : Nat) :
    precompileOutputByteAt state
        (EvmAsm.Evm64.PrecompileResult.fail gasRemaining) range addr = 0 := by
  exact CallOutputMemory.callOutputByteAt_failure state [] gasRemaining range addr

@[simp] theorem precompileOutputByteAt_zero_size
    (state : WorldState) (result : PrecompileResult) (offset : EvmAsm.Evm64.EvmWord)
    (addr : Nat) :
    precompileOutputByteAt state result { offset := offset, size := 0 } addr = 0 := by
  simpa [precompileOutputByteAt] using
    CallOutputMemory.callOutputByteAt_zero_size
      (PrecompileCallBridge.callResultFromPrecompile state result) offset addr

theorem precompileOutputByteAt_success_at_output_add
    {state : WorldState} {out : List Byte} {gasRemaining : Nat}
    {range : MemoryRange} {i : Nat}
    (h : i < (CallOutputBridge.copiedOutputForRange
      { status := .success
        state := state
        output := out
        gasRemaining := gasRemaining }
      range).length) :
    precompileOutputByteAt state
        (EvmAsm.Evm64.PrecompileResult.ok out gasRemaining) range
        (CallOutputMemory.outputStart range + i) =
      (CallOutputBridge.copiedOutputForRange
        { status := .success
          state := state
          output := out
          gasRemaining := gasRemaining }
        range)[i]'h := by
  exact CallOutputMemory.callOutputByteAt_at_output_add h

theorem precompileCallOutputByteFromArgs_eq
    (state : WorldState) (result : PrecompileResult) (args : CallArgs)
    (addr : Nat) :
    precompileCallOutputByteFromArgs state result args addr =
      precompileOutputByteAt state result (CallArgsBridge.callOutputRange args) addr := rfl

theorem precompileStaticCallOutputByteFromArgs_eq
    (state : WorldState) (result : PrecompileResult) (args : StaticCallArgs)
    (addr : Nat) :
    precompileStaticCallOutputByteFromArgs state result args addr =
      precompileOutputByteAt state result (CallArgsBridge.staticCallOutputRange args) addr := rfl

theorem precompileCallOutputByteFromArgs_failure
    (state : WorldState) (gasRemaining : Nat) (args : CallArgs) (addr : Nat) :
    precompileCallOutputByteFromArgs state
        (EvmAsm.Evm64.PrecompileResult.fail gasRemaining) args addr = 0 :=
  precompileOutputByteAt_failure state gasRemaining args.output addr

theorem precompileStaticCallOutputByteFromArgs_failure
    (state : WorldState) (gasRemaining : Nat) (args : StaticCallArgs) (addr : Nat) :
    precompileStaticCallOutputByteFromArgs state
        (EvmAsm.Evm64.PrecompileResult.fail gasRemaining) args addr = 0 :=
  precompileOutputByteAt_failure state gasRemaining args.output addr

theorem attemptedKnownCostPrecompileOutputByte_none_of_call_none
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    {range : MemoryRange} {addr : Nat}
    (h_attempt : PrecompileCallBridge.attemptKnownCostPrecompileCall input out = none) :
    attemptedKnownCostPrecompileOutputByte input out range addr = none := by
  simp [attemptedKnownCostPrecompileOutputByte, h_attempt]

theorem attemptedKnownCostPrecompileOutputByte_some_of_call_some
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    {range : MemoryRange} {addr : Nat} {result : CallResult}
    (h_attempt : PrecompileCallBridge.attemptKnownCostPrecompileCall input out = some result) :
    attemptedKnownCostPrecompileOutputByte input out range addr =
      some (CallOutputMemory.callOutputByteAt result range addr) := by
  simp [attemptedKnownCostPrecompileOutputByte, h_attempt]

theorem attemptedKnownCostPrecompileOutputByte_none_non_precompile
    {input : MessageCallExecution.CallExecutionInput} {out : List Byte}
    {range : MemoryRange} {addr : Nat}
    (h_decode : EvmAsm.Evm64.PrecompileDispatch.decode? input.frame.callee = none) :
    attemptedKnownCostPrecompileOutputByte input out range addr = none := by
  apply attemptedKnownCostPrecompileOutputByte_none_of_call_none
  exact PrecompileCallBridge.attemptKnownCostPrecompileCall_none_non_precompile h_decode

end PrecompileCallOutputBridge

end EvmAsm.EL
