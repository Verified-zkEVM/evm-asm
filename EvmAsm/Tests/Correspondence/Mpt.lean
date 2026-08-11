/-
  EvmAsm.Tests.Correspondence.Mpt

  The MPT decode instance of the spec-correspondence harness.  The wire
  boundary is decode-only: a root RLP preimage and optional child preimages
  are converted with `build_node_db`, then `decode_witness_to_mpt` is anchored
  at the root hash.  This mirrors the reference's authenticated witness
  construction without pretending that the write side or full WitnessState is
  an input/output routine.

  The same family carries the two pure helpers feeding that boundary:
  `compact_to_nibbles` and `decode_account_from_leaf`.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/incremental_mpt.py`
  (`compact_to_nibbles`, `_decode_witness_node`, `decode_witness_to_mpt`) and
  `witness_state.py:102` (`_decode_account_from_leaf`), pinned by the
  `execution-specs` gitlink.

  Method: docs/agents/spec-correspondence.md.
-/

import EvmAsm.Stateless.SpecRef.IncrementalMpt
import EvmAsm.Tests.Correspondence.Harness

namespace EvmAsm.Tests.Correspondence.Mpt

open EvmAsm.EL.RLP
open EvmAsm.Stateless.SpecRef
open EvmAsm.Tests.Correspondence

private def q (bs : Bytes) : String :=
  "\"" ++ hexOfBytes bs ++ "\""

private partial def renderNode : Option MutableNode → String
  | none => "(node empty)"
  | some (.hashed h) => "(node hashed " ++ q h ++ ")"
  | some (.leaf rest value) => "(node leaf " ++ q rest ++ " " ++ q value ++ ")"
  | some (.extension segment child) =>
      "(node extension " ++ q segment ++ " " ++ renderNode (some child) ++ ")"
  | some (.branch children value) =>
      "(node branch (" ++ String.intercalate " " (children.map (fun child =>
        match child with
        | none => "none"
        | some node => renderNode (some node))) ++ ") " ++ q value ++ ")"

private def parseNodes? (fields : List String) : Option (List Bytes) :=
  fields.mapM parseHexBytes

private def runCompact (s : String) : Option String := do
  let bs ← parseHexBytes s
  match compact_to_nibbles bs with
  | .ok (nibbles, isLeaf) =>
      some <| "(compact " ++ q nibbles ++ " " ++ toString isLeaf ++ ")"
  | .error _ => none

private def runNodes (rootAndChildren : List String) (omitRoot : Bool) : Option String := do
  let fields ← parseNodes? rootAndChildren
  let root ← fields.head?
  let dbFields := if omitRoot then fields.drop 1 else fields
  let nodeDb := build_node_db dbFields
  match decode_witness_to_mpt nodeDb (keccak256 root) with
  | .ok decoded => some (renderNode decoded)
  | .error _ => none

private def runAccount (s : String) : Option String := do
  let bs ← parseHexBytes s
  match decode_account_from_leaf bs with
  | .ok (account, storageRoot) =>
      some <| "(account " ++ toString account.nonce ++ " " ++
        toString account.balance ++ " " ++ q storageRoot ++ " " ++
        q account.codeHash ++ ")"
  | .error _ => none

def runDecode (line : String) : Option String :=
  match line.splitOn "|" with
  | ["compact", s] => runCompact s
  | "node" :: root :: children => runNodes (root :: children) false
  | "missing" :: root :: children => runNodes (root :: children) true
  | ["account", s] => runAccount s
  | _ => none

private def runCanonicalRlp (line : String) : Option Bool := do
  match line.splitOn "|" with
  | ["compact", _] => some true
  | "node" :: root :: _ =>
      let bs ← parseHexBytes root
      let item ← decodeFully bs
      some (encode item == bs)
  | "missing" :: root :: _ =>
      let bs ← parseHexBytes root
      let item ← decodeFully bs
      some (encode item == bs)
  | ["account", s] =>
      let bs ← parseHexBytes s
      let item ← decodeFully bs
      some (encode item == bs)
  | _ => none

def subject : Subject :=
  { family := "mpt"
    run := runDecode
    aux := runCanonicalRlp
    auxLabel := "canonical-rlp"
    -- At the pinned main (05c9c08f6), SpecRef's `Root`/`Hash32` aliases do
    -- not enforce the FixedBytes widths enforced by the Python reference.
    -- Keep the resulting account-only port defect visible (tracked in #12008)
    -- and ratchet its population: a count change or a non-account divergence
    -- is a failure.
    expectedLooser := fun line => line.startsWith "account|"
    expectedLooserCount := 138
    ourName := "SpecRef.compact_to_nibbles/decode_witness_to_mpt/decode_account_from_leaf"
    docPage := "docs/agents/spec-correspondence.md" }

def plantedRecords : List Record :=
  [ { input := "compact|20ab", accepted := true,
      detail := "(compact \"0a0b\" true)", auxSame := some true }
  , { input := "compact|", accepted := true, detail := "(compact \"\" false)" }
  , { input := "compact|20ab", accepted := false,
      detail := "Planted" }
  , { input := "compact|20ab", accepted := true,
      detail := "(compact \"ffff\" true)" }
  , { input := "compact|20ab", accepted := true,
      detail := "(compact \"0a0b\" true)", auxSame := some false }
  ]

end EvmAsm.Tests.Correspondence.Mpt
