/-
  EvmAsm.Tests.Correspondence.Header

  The header-decode instance of the spec-correspondence harness:
  `_decode_header` against the vendored reference
  `ethereum.forks.amsterdam.stateless._decode_header` (the exact counterpart
  function, pinned by the `execution-specs` gitlink recorded in the corpus
  header stamp).

  Method: docs/agents/spec-correspondence.md.

  This module imports only `SpecRef/Stateless.lean` (the decoder) and
  `SpecRef/BlocksRlp.lean` (the re-encoder used for the aux axis) plus the
  harness — no Mathlib. Keep it that way: it is what lets the check run as a
  per-PR gate (scripts/check-correspondence-deps.sh enforces the closure).
-/

import EvmAsm.Stateless.SpecRef.Stateless
import EvmAsm.Stateless.SpecRef.BlocksRlp
import EvmAsm.Tests.Correspondence.Harness

namespace EvmAsm.Tests.Correspondence.Header

open EvmAsm.EL.RLP
open EvmAsm.Stateless.SpecRef
open EvmAsm.Tests.Correspondence

/-- Render a decoded `Header` exactly as the Python oracle renders the
reference dataclass: `(header current|previous <fields...>)` with byte fields
as `"<hex>"` and numeric fields in decimal, in the reference's field
declaration order. The previous-fork arm has no `block_access_list_hash` /
`slot_number`. -/
private def renderHeader (h : Header) : String :=
  let q (bs : Bytes) := "\"" ++ hexOfBytes bs ++ "\""
  let n (x : Nat) := toString x
  let common :=
    [ q h.parentHash, q h.ommersHash, q h.coinbase, q h.stateRoot,
      q h.transactionsRoot, q h.receiptRoot, q h.bloom,
      n h.difficulty, n h.number, n h.gasLimit, n h.gasUsed, n h.timestamp,
      q h.extraData, q h.prevRandao, q h.nonce, n h.baseFeePerGas,
      q h.withdrawalsRoot, n h.blobGasUsed, n h.excessBlobGas,
      q h.parentBeaconBlockRoot, q h.requestsHash ]
  let (tag, fields) :=
    if h.isCurrentFork then
      ("current", common ++ [q h.blockAccessListHash, n h.slotNumber])
    else
      ("previous", common)
  "(header " ++ tag ++ " " ++ String.intercalate " " fields ++ ")"

/-- Decode side: `_decode_header` against the vendored
`stateless._decode_header` — both reject trailing bytes, nested fields,
non-canonical scalars and wrong `FixedBytes` widths. -/
def runDecode (inputHex : String) : Option String := do
  let bs ← parseHexBytes inputHex
  match _decode_header bs with
  | .ok h => some (renderHeader h)
  | .error _ => none

/-- Encode side, as the auxiliary axis: does re-encoding the decoded header
via `headerToRlpItem` reproduce the input byte-for-byte? The aux is
unconditional on the accepting path (BlocksRlp.lean:19-25), and the corpus's
`differs` axis tests it without a second corpus. -/
def runReencode (inputHex : String) : Option Bool := do
  let bs ← parseHexBytes inputHex
  match _decode_header bs with
  | .ok h => some (encode (headerToRlpItem h) == bs)
  | .error _ => none

def subject : Subject :=
  { family := "header"
    run := runDecode
    aux := runReencode
    auxLabel := "encode"
    ourName := "_decode_header/headerToRlpItem"
    docPage := "docs/agents/spec-correspondence.md" }

/-- The all-zero-fields valid current-fork header (corpus record 0), used by
the planted records below. -/
private def plantedValidInput : String :=
  "f90279a00000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000940000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000b901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080018401c9c380800180a0000000000000000000000000000000000000000000000000000000000000000088000000000000000007a000000000000000000000000000000000000000000000000000000000000000008080a00000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000001"

/-- The oracle's render of `plantedValidInput`. -/
private def plantedValidDetail : String :=
  "(header current \"0000000000000000000000000000000000000000000000000000000000000000\" \"0000000000000000000000000000000000000000000000000000000000000000\" \"0000000000000000000000000000000000000000\" \"0000000000000000000000000000000000000000000000000000000000000000\" \"0000000000000000000000000000000000000000000000000000000000000000\" \"0000000000000000000000000000000000000000000000000000000000000000\" \"00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\" 0 1 30000000 0 1 \"\" \"0000000000000000000000000000000000000000000000000000000000000000\" \"0000000000000000\" 7 \"0000000000000000000000000000000000000000000000000000000000000000\" 0 0 \"0000000000000000000000000000000000000000000000000000000000000000\" \"0000000000000000000000000000000000000000000000000000000000000000\" \"0000000000000000000000000000000000000000000000000000000000000000\" 1)"

/-- Planted records for the self-test: one finding per class, including the
aux axis. `c0` (the empty RLP list) is rejected by both sides. -/
def plantedRecords : List Record :=
  [ { input := plantedValidInput, accepted := true, detail := plantedValidDetail }  -- agrees
  , { input := "c0", accepted := true, detail := "(header current)" }                -- we are stricter
  , { input := plantedValidInput, accepted := false, detail := "Planted" }           -- we are looser
  , { input := plantedValidInput, accepted := true, detail := "\"ffff\"" }           -- value mismatch
    -- valid, correct value, but claims re-encoding does NOT reproduce it
  , { input := plantedValidInput, accepted := true, detail := plantedValidDetail, auxSame := some false }
  ]

end EvmAsm.Tests.Correspondence.Header
