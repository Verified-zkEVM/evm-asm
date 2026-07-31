/-
  EvmAsm.Tests.Correspondence.Rlp

  The RLP instance of the spec-correspondence harness: `EvmAsm.EL.RLP` against
  `ethereum_rlp`, the reference RLP implementation used by execution-specs.

  Method: docs/agents/spec-correspondence.md.
  Findings and the routine table: docs/rlp-spec-correspondence.md.

  RLP is an **external-reference** family — `ethereum_rlp` is a PyPI package,
  not vendored under `execution-specs/src/` — so it needs the pin-stamp and
  staleness machinery the harness provides. A family whose reference is vendored
  does not; see the method page's reference taxonomy.

  This module imports only `EvmAsm.EL.RLP.FullDecode`, whose transitive closure
  is `Decode` and `Basic` — no Mathlib. Keep it that way: it is what lets the
  check run as a per-PR gate.
-/

import EvmAsm.EL.RLP.FullDecode
import EvmAsm.Tests.Correspondence.Harness

namespace EvmAsm.Tests.Correspondence.Rlp

open EvmAsm.EL.RLP
open EvmAsm.Tests.Correspondence

/-- Render an `RLPItem` in the same S-expression form the Python oracle emits:
bytes as `"<hex>"`, lists as `(<item> ...)`. Keeping both renderers textually
identical means the comparison needs no parser on either side. -/
partial def render : RLPItem → String
  | .bytes data => "\"" ++ hexOfBytes data ++ "\""
  | .list items => "(" ++ String.intercalate " " (items.map render) ++ ")"

/-- Decode side: `decodeFully` rejects a prefix decode that leaves trailing
input, matching `rlp.decode` at the pinned version. -/
def runDecode (inputHex : String) : Option String := do
  let bs ← parseHexBytes inputHex
  let item ← decodeFully bs
  some (render item)

/-- Encode side, as the auxiliary axis: does re-encoding the decoded value
reproduce the input byte-for-byte? Comparing that boolean against the
reference's own answer tests `EL.RLP.encode` without needing a second corpus. -/
def runReencode (inputHex : String) : Option Bool := do
  let bs ← parseHexBytes inputHex
  let item ← decodeFully bs
  some (encode item == bs)

def subject : Subject :=
  { family := "rlp"
    run := runDecode
    aux := runReencode
    auxLabel := "encode"
    ourName := "EL.RLP.decodeFully/encode"
    docPage := "docs/rlp-spec-correspondence.md" }

/-- Planted records for the self-test. `820102` is a valid 2-byte string;
`8100` is a non-canonical wrapping of `0x00` and is rejected by both sides. -/
def plantedRecords : List Record :=
  [ { input := "820102", accepted := true,  detail := "\"0102\"" }   -- agrees
  , { input := "8100",   accepted := true,  detail := "\"00\"" }     -- we are stricter
  , { input := "820102", accepted := false, detail := "Planted" }    -- we are looser
  , { input := "820102", accepted := true,  detail := "\"ffff\"" }   -- value mismatch
    -- valid, correct value, but claims re-encoding does NOT reproduce it
  , { input := "820102", accepted := true,  detail := "\"0102\"", auxSame := some false }
  ]

end EvmAsm.Tests.Correspondence.Rlp
