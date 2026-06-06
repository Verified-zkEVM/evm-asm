/-
  EvmAsm.Codegen.Programs.EvmStackHandlers

  Dispatcher handler families for PUSH, DUP, and SWAP opcodes.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Swap.Program

namespace EvmAsm.Codegen

/-! ## stack opcode handler families -/

/-- PUSH0..PUSH32. Opcode byte = `0x5f + n`; the handler advances
    `x10` by `1 + n` (one opcode byte + `n` immediate bytes). -/
def pushHandlers : List OpcodeHandlerSpec :=
  (List.range 33).map (fun n =>
    { label   := s!"h_PUSH{n}"
      opcodes := [0x5f + n]
      preBody := stackOverflowGuardAsm
      body    := EvmAsm.Evm64.evm_push n
      tail    := .advanceAndRet (1 + n) })

/-- DUP1..DUP16. Opcode byte = `0x7f + n` (so DUP1 = `0x80`);
    width 1. `evm_dup n` duplicates the n-th stack item (1-indexed
    from top) onto the top. -/
def dupHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_DUP{n}"
      opcodes := [0x7f + n]
      preBody := stackUnderflowGuardAsm n
      body    := EvmAsm.Evm64.evm_dup n
      tail    := .advanceAndRet 1 })

/-- SWAP1..SWAP16. Opcode byte = `0x8f + n` (so SWAP1 = `0x90`);
    width 1. `evm_swap n` swaps the top with the (n+1)-th stack
    item. -/
def swapHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_SWAP{n}"
      opcodes := [0x8f + n]
      preBody := stackUnderflowGuardAsm (n + 1)
      body    := EvmAsm.Evm64.evm_swap n
      tail    := .advanceAndRet 1 })

end EvmAsm.Codegen
