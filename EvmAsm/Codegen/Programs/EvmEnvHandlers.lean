/-
  EvmAsm.Codegen.Programs.EvmEnvHandlers

  Dispatcher handlers for simple environment opcodes.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.Env.Program

namespace EvmAsm.Codegen

/-- M12 simple environment opcodes (13 of them, one record each).

    All 13 share the verified body
    `EvmAsm.Evm64.Env.evm_env_load envBaseReg tmpReg field`
    (9 instructions = 36 bytes per handler) parameterized over a
    `SimpleEnvField`. The dispatcher prologue sets `x20 = &evm_env`
    (a 416-byte = 13×32 region in `.data` initialised to zero), and
    each handler passes `.x20` as `envBaseReg` plus `.x15` as
    `tmpReg`. None of these bodies touch `x10`, so `preBody := ""`.

    `x20` was chosen over `x14` (the M8/M9/M10 save register) because
    DIV/MOD/SDIV/SMOD/ADDMOD all use `preBody := "mv x14, x10"`:
    `x14` is explicitly "outside the dispatcher's preserved set" per
    M8's docstring. `x20` is a callee-saved LP64 register with zero
    references in any `EvmAsm/Evm64/*/Program.lean` and zero uses by
    any existing handler's `preBody`/`tail`, making it the cleanest
    long-term home for the env base.

    The env region is zero-initialised; non-zero env values come
    from a future host-preload PR. The wiring correctness (each
    opcode byte routes to the right field offset, x12 advances, the
    32 bytes land on the stack) is what M12 validates. -/
def envHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_ADDRESS"    , opcodes := [0x30], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .address    , tail := .advanceAndRet 1 }
  , { label := "h_ORIGIN"     , opcodes := [0x32], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .origin     , tail := .advanceAndRet 1 }
  , { label := "h_CALLER"     , opcodes := [0x33], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .caller     , tail := .advanceAndRet 1 }
  , { label := "h_CALLVALUE"  , opcodes := [0x34], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .callValue  , tail := .advanceAndRet 1 }
  , { label := "h_GASPRICE"   , opcodes := [0x3a], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .gasPrice   , tail := .advanceAndRet 1 }
  , { label := "h_COINBASE"   , opcodes := [0x41], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .coinbase   , tail := .advanceAndRet 1 }
  , { label := "h_TIMESTAMP"  , opcodes := [0x42], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .timestamp  , tail := .advanceAndRet 1 }
  , { label := "h_NUMBER"     , opcodes := [0x43], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .number     , tail := .advanceAndRet 1 }
  , { label := "h_PREVRANDAO" , opcodes := [0x44], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .prevrandao , tail := .advanceAndRet 1 }
  , { label := "h_GASLIMIT"   , opcodes := [0x45], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .gasLimit   , tail := .advanceAndRet 1 }
  , { label := "h_CHAINID"    , opcodes := [0x46], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .chainId    , tail := .advanceAndRet 1 }
  , { label := "h_SELFBALANCE", opcodes := [0x47], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .selfBalance, tail := .advanceAndRet 1 }
  , { label := "h_BASEFEE"    , opcodes := [0x48], body := EvmAsm.Evm64.Env.evm_env_load .x20 .x15 .baseFee    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
