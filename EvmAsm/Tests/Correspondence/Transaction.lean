/-
  EvmAsm.Tests.Correspondence.Transaction

  The transaction-decode instance of the spec-correspondence harness:
  `decode_transaction` against the vendored reference
  `ethereum.forks.amsterdam.transactions.decode_transaction` (the exact
  counterpart function, pinned by the `execution-specs` gitlink recorded in
  the corpus header stamp).

  Method: docs/agents/spec-correspondence.md.

  This module imports only `SpecRef/Transactions.lean` (decoder and
  re-encoder used for the aux axis) plus the harness — no Mathlib. Keep it
  that way: it is what lets the check run as a per-PR gate
  (scripts/check-correspondence-deps.sh enforces the closure).
-/

import EvmAsm.Stateless.SpecRef.Transactions
import EvmAsm.Tests.Correspondence.Harness

namespace EvmAsm.Tests.Correspondence.Transaction

open EvmAsm.Stateless.SpecRef
open EvmAsm.Tests.Correspondence

/-- Render one bytes field the way the oracle does (`"<hex>"`). -/
private def q (bs : Bytes) : String :=
  "\"" ++ hexOfBytes bs ++ "\""

/-- Render one numeric field the way the oracle does (decimal). -/
private def n (x : Nat) : String :=
  toString x

/-- `to` is `Option Address` in the model but `Bytes0 | Address` in the
    reference: a contract creation decodes to `Bytes0(b"")`, which the oracle
    renders as `""` (the empty hex string). -/
private def renderTo : Option Address → String
  | none => "\"\""
  | some a => q a

private def renderAccess (a : Access) : String :=
  "(" ++ q a.account ++ " (" ++ String.intercalate " " (a.slots.map q) ++ "))"

private def renderAccessList (xs : List Access) : String :=
  "(" ++ String.intercalate " " (xs.map renderAccess) ++ ")"

private def renderAuthorization (a : Authorization) : String :=
  "(" ++ n a.chainId ++ " " ++ q a.address ++ " " ++ n a.nonce ++ " " ++
    n a.yParity ++ " " ++ n a.r ++ " " ++ n a.s ++ ")"

private def renderAuthorizations (xs : List Authorization) : String :=
  "(" ++ String.intercalate " " (xs.map renderAuthorization) ++ ")"

private def renderHashes (xs : List VersionedHash) : String :=
  "(" ++ String.intercalate " " (xs.map q) ++ ")"

/-- Render a decoded transaction exactly as the oracle does:
    `(tx <variant> <fields...>)` with bytes quoted-hex and numerics decimal. -/
private def renderTx : _root_.EvmAsm.Stateless.SpecRef.Transaction → String
  | .legacy t =>
      "(tx legacy " ++ String.intercalate " "
        [n t.nonce, n t.gasPrice, n t.gas, renderTo t.to, n t.value, q t.data,
         n t.v, n t.r, n t.s] ++ ")"
  | .accessList t =>
      "(tx access-list " ++ String.intercalate " "
        [n t.chainId, n t.nonce, n t.gasPrice, n t.gas, renderTo t.to,
         n t.value, q t.data, renderAccessList t.accessList, n t.yParity,
         n t.r, n t.s] ++ ")"
  | .feeMarket t =>
      "(tx fee-market " ++ String.intercalate " "
        [n t.chainId, n t.nonce, n t.maxPriorityFeePerGas, n t.maxFeePerGas,
         n t.gas, renderTo t.to, n t.value, q t.data,
         renderAccessList t.accessList, n t.yParity, n t.r, n t.s] ++ ")"
  | .blob t =>
      "(tx blob " ++ String.intercalate " "
        [n t.chainId, n t.nonce, n t.maxPriorityFeePerGas, n t.maxFeePerGas,
         n t.gas, q t.to, n t.value, q t.data, renderAccessList t.accessList,
         n t.maxFeePerBlobGas, renderHashes t.blobVersionedHashes,
         n t.yParity, n t.r, n t.s] ++ ")"
  | .setCode t =>
      "(tx set-code " ++ String.intercalate " "
        [n t.chainId, n t.nonce, n t.maxPriorityFeePerGas, n t.maxFeePerGas,
         n t.gas, q t.to, n t.value, q t.data, renderAccessList t.accessList,
         renderAuthorizations t.authorizations, n t.yParity, n t.r,
         n t.s] ++ ")"

/-- Our decode: hex input → `SpecRef.decode_transaction` → rendered value.
    Any decode failure (including malformed hex) is a rejection. -/
private def runDecode (hex : String) : Option String :=
  match parseHexBytes hex with
  | none => none
  | some bs =>
    match decode_transaction bs with
    | .ok tx => some (renderTx tx)
    | .error _ => none

/-- Our aux: re-encode the decoded transaction with `encode_transaction` and
    check it reproduces the input bytes. -/
private def runReencode (hex : String) : Option Bool :=
  match parseHexBytes hex with
  | none => none
  | some bs =>
    match decode_transaction bs with
    | .ok tx => some (encode_transaction tx == bs)
    | .error _ => none

/-- The transaction-decode subject. -/
def subject : Subject := {
  family := "transaction"
  run := runDecode
  aux := runReencode
  auxLabel := "encode"
  ourName := "SpecRef.decode_transaction/encode_transaction"
  docPage := "docs/agents/spec-correspondence.md"
}

/-- First valid record of the committed corpus (a legacy transfer) — used by
    the planted records below. -/
private def plantedValidInput : String :=
  "df010782520894000000000000000000000000000000000000000105801b0203"

private def plantedValidDetail : String :=
  "(tx legacy 1 7 21000 \"0000000000000000000000000000000000000001\" 5 \"\" 27 2 3)"

/-- Self-test fixtures: one planted finding per comparison class, so the
    self-test run fails loudly if the comparison logic silently stops seeing
    a divergence class (docs/agents/spec-correspondence.md). -/
def plantedRecords : List Record := [
  -- AGREE baseline: a record the oracle itself emitted.
  { input := plantedValidInput, accepted := true,
    detail := plantedValidDetail, auxSame := some true },
  -- STRICTER: we reject what the oracle claims to accept (c0 = empty list,
  -- not a legacy transaction).
  { input := "c0", accepted := true, detail := "(tx legacy 0 0 0 \"\" 0 \"\" 0 0 0)" },
  -- LOOSER: we accept what the oracle claims to reject.
  { input := plantedValidInput, accepted := false,
    detail := plantedValidDetail },
  -- VALUE MISMATCH: both accept, different rendered value.
  { input := plantedValidInput, accepted := true, detail := "\"ffff\"" },
  -- AUX MISMATCH: both accept with the same value, but aux differs.
  { input := plantedValidInput, accepted := true,
    detail := plantedValidDetail, auxSame := some false }
]

end EvmAsm.Tests.Correspondence.Transaction
