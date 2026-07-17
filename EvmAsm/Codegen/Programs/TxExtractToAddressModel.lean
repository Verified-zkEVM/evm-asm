/-
  Pure model for `tx_extract_to_address` success domain.

  Status codes match the guest routine:
    0 : success (to is 0 or 20 bytes)
    1 : tx_type_dispatch failed
    2 : `to` field extraction failed
-/

import EvmAsm.EL.RLP.Decode
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressModel

open EvmAsm.EL.RLP
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Rv64

/-- Field index of `to` by EIP-2718 type. -/
def toFieldIndex (ty : Nat) : Nat :=
  if ty = 0 then 3 else if ty = 1 then 4 else 5

/-- Decode outer/inner list payload items (canonical EL decode). -/
def decodeListItems (bs : List (BitVec 8)) : Option (List RLPItem) :=
  match decode bs with
  | some (.list items, rest) =>
    if rest.isEmpty then some items else none
  | _ => none

/-- Pure extract-to-address: (status, toBytes20-or-empty, isCreation).
    On non-success, toBytes is [] and isCreation is 0. -/
def teerExtractToAddress (txBytes : List (BitVec 8)) :
    Word × List (BitVec 8) × Word :=
  let st := (teerTxTypeDispatch txBytes).1
  let ty := (teerTxTypeDispatch txBytes).2.1
  let innerOff := (teerTxTypeDispatch txBytes).2.2
  if st ≠ (0 : Word) then
    ((1 : Word), [], (0 : Word))
  else
    let inner := txBytes.drop innerOff.toNat
    match decodeListItems inner with
    | none => ((2 : Word), [], (0 : Word))
    | some items =>
      match items[toFieldIndex ty.toNat]? with
      | some (.bytes content) =>
        if content.length = 0 then
          ((0 : Word), [], (1 : Word))
        else if content.length = 20 then
          ((0 : Word), content, (0 : Word))
        else
          ((2 : Word), [], (0 : Word))
      | _ => ((2 : Word), [], (0 : Word))

/-- Success-domain guard for ExtractAssumed packaging. -/
def extractSuccess (txBytes : List (BitVec 8)) : Prop :=
  (teerExtractToAddress txBytes).1 = (0 : Word)

theorem extractSuccess_status
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    (teerExtractToAddress txBytes).1 = (0 : Word) := h

end EvmAsm.Codegen.TxExtractToAddressModel
