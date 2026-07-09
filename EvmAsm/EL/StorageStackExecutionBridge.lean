/-
  EvmAsm.EL.StorageStackExecutionBridge

  Pure stack-to-ECALL execution bridge for SLOAD/SSTORE (GH #110).
-/

import EvmAsm.EL.StorageArgsEcallBridge

namespace EvmAsm.EL

namespace StorageStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev StorageKind := EvmAsm.Evm64.StorageArgs.Kind
abbrev StorageAccessList := StorageArgsEcallBridge.StorageAccessList

/-- Runtime state visible to the pure storage stack bridge. -/
structure StorageStackState where
  stack : List EvmWord

def stackRestAfterStorage? (kind : StorageKind) :
    List EvmWord -> Option (List EvmWord)
  | _slot :: rest =>
      match kind with
      | .sload => some rest
      | .sstore =>
          match rest with
          | _value :: rest => some rest
          | _ => none
  | _ => none

theorem stackRestAfterStorage?_sload
    (slot : EvmWord) (rest : List EvmWord) :
    stackRestAfterStorage? .sload (slot :: rest) = some rest := rfl

theorem stackRestAfterStorage?_sstore
    (slot value : EvmWord) (rest : List EvmWord) :
    stackRestAfterStorage? .sstore (slot :: value :: rest) = some rest := rfl

@[simp] theorem stackRestAfterStorage?_nil (kind : StorageKind) :
    stackRestAfterStorage? kind [] = none := rfl

theorem stackRestAfterStorage?_sload_none_of_empty :
    stackRestAfterStorage? .sload [] = none := rfl

theorem stackRestAfterStorage?_sstore_none_of_empty :
    stackRestAfterStorage? .sstore [] = none := rfl

theorem stackRestAfterStorage?_sstore_none_of_one
    (slot : EvmWord) :
    stackRestAfterStorage? .sstore [slot] = none := rfl

end StorageStackExecutionBridge

end EvmAsm.EL
