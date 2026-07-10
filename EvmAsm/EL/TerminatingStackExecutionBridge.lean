/-
  EvmAsm.EL.TerminatingStackExecutionBridge

  Pure stack-to-result bridge for terminating opcodes (GH #113).
-/

import EvmAsm.Evm64.TerminatingArgsStackDecode
import EvmAsm.EL.TerminatingDataMemory

namespace EvmAsm.EL

namespace TerminatingStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind
abbrev TerminatingArgs := EvmAsm.Evm64.TerminatingArgs.Args
abbrev MemoryReader := TerminatingDataMemory.MemoryReader

/-- Runtime state visible to the pure terminating-opcode stack bridge. -/
structure TerminatingStackState where
  stack : List EvmWord

def stackRestAfterTerminating? :
    TerminatingKind -> List EvmWord -> Option (List EvmWord)
  | .stop, stack => some stack
  | .return_, _offset :: _size :: rest => some rest
  | .revert, _offset :: _size :: rest => some rest
  | .invalid, stack => some stack
  | .selfdestruct, _beneficiary :: rest => some rest
  | _, _ => none

def argsFromStack? : TerminatingKind -> List EvmWord -> Option TerminatingArgs
  | .stop, _ => some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
  | .return_, stack =>
      EvmAsm.Evm64.TerminatingArgsStackDecode.decodeReturnStack? stack
  | .revert, stack =>
      EvmAsm.Evm64.TerminatingArgsStackDecode.decodeRevertStack? stack
  | .invalid, _ => some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
  | .selfdestruct, stack =>
      (EvmAsm.Evm64.TerminatingArgsStackDecode.decodeSelfdestructStack? stack).map
        (fun _beneficiary => EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)

theorem stackRestAfterTerminating?_stop (stack : List EvmWord) :
    stackRestAfterTerminating? .stop stack = some stack := rfl

theorem stackRestAfterTerminating?_return
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .return_ (offset :: size :: rest) =
      some rest := rfl

theorem stackRestAfterTerminating?_revert
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .revert (offset :: size :: rest) =
      some rest := rfl

theorem stackRestAfterTerminating?_invalid (stack : List EvmWord) :
    stackRestAfterTerminating? .invalid stack = some stack := rfl

theorem stackRestAfterTerminating?_selfdestruct
    (beneficiary : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .selfdestruct (beneficiary :: rest) =
      some rest := rfl

theorem stackRestAfterTerminating?_return_none_of_empty :
    stackRestAfterTerminating? .return_ [] = none := rfl

theorem stackRestAfterTerminating?_return_none_of_one
    (offset : EvmWord) :
    stackRestAfterTerminating? .return_ [offset] = none := rfl

theorem stackRestAfterTerminating?_revert_none_of_empty :
    stackRestAfterTerminating? .revert [] = none := rfl

theorem stackRestAfterTerminating?_revert_none_of_one
    (offset : EvmWord) :
    stackRestAfterTerminating? .revert [offset] = none := rfl

theorem stackRestAfterTerminating?_selfdestruct_none_of_empty :
    stackRestAfterTerminating? .selfdestruct [] = none := rfl

theorem argsFromStack?_return
    (offset size : EvmWord) (rest : List EvmWord) :
    argsFromStack? .return_ (offset :: size :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.returnArgs offset size) := rfl

theorem argsFromStack?_revert
    (offset size : EvmWord) (rest : List EvmWord) :
    argsFromStack? .revert (offset :: size :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.revertArgs offset size) := rfl

theorem argsFromStack?_selfdestruct
    (beneficiary : EvmWord) (rest : List EvmWord) :
    argsFromStack? .selfdestruct (beneficiary :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0) := rfl

theorem argsFromStack?_return_none_of_empty :
    argsFromStack? .return_ [] = none := rfl

theorem argsFromStack?_return_none_of_one
    (offset : EvmWord) :
    argsFromStack? .return_ [offset] = none := rfl

theorem argsFromStack?_revert_none_of_empty :
    argsFromStack? .revert [] = none := rfl

theorem argsFromStack?_revert_none_of_one
    (offset : EvmWord) :
    argsFromStack? .revert [offset] = none := rfl

theorem argsFromStack?_selfdestruct_none_of_empty :
    argsFromStack? .selfdestruct [] = none := rfl

def resultStatusForKind : TerminatingKind -> CallStatus
  | .stop => .success
  | .return_ => .success
  | .revert => .revert
  | .invalid => .failure
  | .selfdestruct => .success

def resultOutputForKind
    (kind : TerminatingKind) (readByte : MemoryReader) (args : TerminatingArgs) :
    List Byte :=
  match kind with
  | .stop => []
  | .return_ => TerminatingDataMemory.terminatingDataFromMemory readByte args
  | .revert => TerminatingDataMemory.terminatingDataFromMemory readByte args
  | .invalid => []
  | .selfdestruct => []

end TerminatingStackExecutionBridge

end EvmAsm.EL
