/-
  EvmAsm.EL.CreateStackExecutionBridge

  Pure stack-to-execution bridge for CREATE and CREATE2 (GH #115).
-/

import EvmAsm.Evm64.CreateArgsStackDecode
import EvmAsm.EL.CreateInitcodeBridge
import EvmAsm.EL.CreateResultBridge

namespace EvmAsm.EL

namespace CreateStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev CreateKind := EvmAsm.Evm64.CreateArgs.Kind
abbrev Decoded := EvmAsm.Evm64.CreateArgsStackDecode.Decoded
abbrev MemoryReader := CreateInitcodeBridge.MemoryReader

/-- Runtime state visible to the pure CREATE stack bridge. -/
structure CreateStackState where
  stack : List EvmWord

def stackRestAfterCreate? (kind : CreateKind) : List EvmWord -> Option (List EvmWord)
  | _value :: _offset :: _size :: rest =>
      match kind with
      | .create => some rest
      | .create2 =>
          match rest with
          | _salt :: rest => some rest
          | _ => none
  | _ => none

def requestFromDecoded
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord) :
    Decoded -> CreateRequest
  | .create args =>
      CreateInitcodeBridge.createRequestFromMemory creator readByte gas args
  | .create2 args =>
      CreateInitcodeBridge.create2RequestFromMemory creator readByte gas args

def requestFromStack? (kind : CreateKind) (creator : Address)
    (readByte : MemoryReader) (gas : EvmWord) (stack : List EvmWord) :
    Option CreateRequest :=
  (EvmAsm.Evm64.CreateArgsStackDecode.decodeCreateStack? kind stack).map
    (requestFromDecoded creator readByte gas)

theorem stackRestAfterCreate?_create
    (value offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterCreate? .create (value :: offset :: size :: rest) =
      some rest := rfl

theorem stackRestAfterCreate?_create2
    (value offset size salt : EvmWord) (rest : List EvmWord) :
    stackRestAfterCreate? .create2 (value :: offset :: size :: salt :: rest) =
      some rest := rfl

@[simp] theorem stackRestAfterCreate?_nil (kind : CreateKind) :
    stackRestAfterCreate? kind [] = none := rfl

@[simp] theorem stackRestAfterCreate?_singleton
    (kind : CreateKind) (value : EvmWord) :
    stackRestAfterCreate? kind [value] = none := rfl

theorem stackRestAfterCreate?_create_none_of_empty :
    stackRestAfterCreate? .create [] = none := rfl

theorem stackRestAfterCreate?_create_none_of_one
    (value : EvmWord) :
    stackRestAfterCreate? .create [value] = none := rfl

theorem stackRestAfterCreate?_create_none_of_two
    (value offset : EvmWord) :
    stackRestAfterCreate? .create [value, offset] = none := rfl

theorem stackRestAfterCreate?_create2_none_of_empty :
    stackRestAfterCreate? .create2 [] = none := rfl

theorem stackRestAfterCreate?_create2_none_of_one
    (value : EvmWord) :
    stackRestAfterCreate? .create2 [value] = none := rfl

theorem stackRestAfterCreate?_create2_none_of_two
    (value offset : EvmWord) :
    stackRestAfterCreate? .create2 [value, offset] = none := rfl

theorem stackRestAfterCreate?_create2_none_of_three
    (value offset size : EvmWord) :
    stackRestAfterCreate? .create2 [value, offset, size] = none := rfl

theorem requestFromStack?_create
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord)
    (value offset size : EvmWord) (rest : List EvmWord) :
    requestFromStack? .create creator readByte gas
        (value :: offset :: size :: rest) =
      some
        (CreateInitcodeBridge.createRequestFromMemory creator readByte gas
          (EvmAsm.Evm64.CreateArgsStackDecode.mkCreate value offset size)) := rfl

end CreateStackExecutionBridge

end EvmAsm.EL
