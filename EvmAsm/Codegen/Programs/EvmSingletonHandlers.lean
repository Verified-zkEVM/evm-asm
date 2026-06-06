/-
  EvmAsm.Codegen.Programs.EvmSingletonHandlers

  Fixed-shape singleton dispatcher handlers for arithmetic, bitwise,
  comparison, shift, CLZ, and POP opcodes.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.Eq.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Programs.Clz

namespace EvmAsm.Codegen

private def stackUnderflowGuardSaveX10Asm (wordCount : Nat) : String :=
  stackUnderflowGuardAsm wordCount ++ "\n  mv x9, x10"

/-- Tail used by handlers whose verified body clobbers `x10` (the
    EVM code pointer in our dispatcher convention). Restores `x10`
    from `x9` (saved via `preBody`), then advances by 1 and returns. -/
private def x10RestoreAdvance1 : HandlerTail :=
  .custom "  mv x10, x9\n  addi x10, x10, 1\n  ret"

/-- Fixed-shape singleton opcodes: parameter-free verified `Program`s
    that fit the standard `<body>` + `addi x10, x10, 1` + `ret` ABI.

    Four bodies (`evm_mul`, `evm_signextend`, `evm_byte`, `evm_shr`)
    use `x10` as an internal scratch / accumulator register, which
    clobbers our dispatcher's preserved EVM code pointer. They carry
    `preBody := "  mv x9, x10"` to stash x10 in x9 (a register no
    verified opcode body touches) and use `x10RestoreAdvance1` as
    the tail to restore before advancing. -/
def singletonHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_ADD"        , opcodes := [0x01], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_add       , tail := .advanceAndRet 1 }
  , { label := "h_MUL"        , opcodes := [0x02], preBody := stackUnderflowGuardSaveX10Asm 2, body := EvmAsm.Evm64.evm_mul       , tail := x10RestoreAdvance1 }
  , { label := "h_SUB"        , opcodes := [0x03], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_sub       , tail := .advanceAndRet 1 }
  , { label := "h_SIGNEXTEND" , opcodes := [0x0b], preBody := stackUnderflowGuardSaveX10Asm 2, body := EvmAsm.Evm64.evm_signextend, tail := x10RestoreAdvance1 }
  , { label := "h_LT"         , opcodes := [0x10], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_lt        , tail := .advanceAndRet 1 }
  , { label := "h_GT"         , opcodes := [0x11], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_gt        , tail := .advanceAndRet 1 }
  , { label := "h_SLT"        , opcodes := [0x12], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_slt       , tail := .advanceAndRet 1 }
  , { label := "h_SGT"        , opcodes := [0x13], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_sgt       , tail := .advanceAndRet 1 }
  , { label := "h_EQ"         , opcodes := [0x14], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_eq        , tail := .advanceAndRet 1 }
  , { label := "h_ISZERO"     , opcodes := [0x15], preBody := stackUnderflowGuardAsm 1, body := EvmAsm.Evm64.evm_iszero    , tail := .advanceAndRet 1 }
  , { label := "h_AND"        , opcodes := [0x16], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_and       , tail := .advanceAndRet 1 }
  , { label := "h_OR"         , opcodes := [0x17], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_or        , tail := .advanceAndRet 1 }
  , { label := "h_XOR"        , opcodes := [0x18], preBody := stackUnderflowGuardAsm 2, body := EvmAsm.Evm64.evm_xor       , tail := .advanceAndRet 1 }
  , { label := "h_NOT"        , opcodes := [0x19], preBody := stackUnderflowGuardAsm 1, body := EvmAsm.Evm64.evm_not       , tail := .advanceAndRet 1 }
  , { label := "h_BYTE"       , opcodes := [0x1a], preBody := stackUnderflowGuardSaveX10Asm 2, body := EvmAsm.Evm64.evm_byte      , tail := x10RestoreAdvance1 }
  , { label := "h_SHL"        , opcodes := [0x1b], preBody := stackUnderflowGuardSaveX10Asm 2, body := EvmAsm.Evm64.evm_shl       , tail := x10RestoreAdvance1 }
  , { label := "h_SHR"        , opcodes := [0x1c], preBody := stackUnderflowGuardSaveX10Asm 2, body := EvmAsm.Evm64.evm_shr       , tail := x10RestoreAdvance1 }
  , { label := "h_SAR"        , opcodes := [0x1d], preBody := stackUnderflowGuardSaveX10Asm 2, body := EvmAsm.Evm64.evm_sar       , tail := x10RestoreAdvance1 }
  , { label := "h_CLZ"        , opcodes := [0x1e], preBody := stackUnderflowGuardAsm 1, body := []                         , tail := clzTail }
  , { label := "h_POP"        , opcodes := [0x50], preBody := stackUnderflowGuardAsm 1, body := EvmAsm.Evm64.evm_pop       , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
