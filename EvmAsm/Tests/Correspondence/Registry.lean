/-
  EvmAsm.Tests.Correspondence.Registry

  The list of families the correspondence harness can check, and the CLI that
  dispatches on it. Adding a family is: write a `Subject` module, add one row
  here, generate its corpus with `scripts/spec-oracle.py`. See
  docs/agents/spec-correspondence.md §"How to add a family".

  Registering here is what forces a family to gain a self-test — the driver has
  no path that runs a comparison without one.

  Keep this module Mathlib-free (see `Harness.lean`): it is the import root of
  the `correspondence-check` executable.
-/

import EvmAsm.Tests.Correspondence.Harness
import EvmAsm.Tests.Correspondence.Bal
import EvmAsm.Tests.Correspondence.Header
import EvmAsm.Tests.Correspondence.Rlp

namespace EvmAsm.Tests.Correspondence.Registry

open EvmAsm.Tests.Correspondence

/-- A registered family: its subject plus the records its self-test plants. -/
structure Family where
  subject : Subject
  planted : List Record

def families : List Family :=
  [ { subject := Rlp.subject, planted := Rlp.plantedRecords }
  , { subject := Bal.subject, planted := Bal.plantedRecords }
  , { subject := Header.subject, planted := Header.plantedRecords }
    -- SSZ has no entry: its guest tower was built independently of
    -- SpecRef/SszCodec.lean and its reference codec (`remerkleable`) is a
    -- separate external package, so there is no shared model to differential
    -- against. Its correspondence page is prose-only and says so.
    -- See docs/ssz-spec-correspondence.md.
  ]

def find? (name : String) : Option Family :=
  families.find? (·.subject.family == name)

def names : String := String.intercalate ", " (families.map (·.subject.family))

def usage : String :=
  s!"usage: correspondence-check <family> [corpus-path] [--self-test]\n\
     families: {names}\n\
     \n\
     Replays a committed oracle corpus against the Lean model for <family> and\n\
     classifies every disagreement. Exit: 0 agree / 1 divergence or stale pin /\n\
     2 the corpus could not be read.\n\
     \n\
     Method: docs/agents/spec-correspondence.md"

def main (args : List String) : IO UInt32 := do
  let positional := args.filter (!·.startsWith "--")
  let selfTestOnly := args.contains "--self-test"
  match positional with
  | [] =>
      if selfTestOnly then
        -- No family named: self-test every registered family. This is what CI
        -- runs, so a newly registered family cannot skip the obligation.
        let mut worst : UInt32 := 0
        for f in families do
          let rc ← selfTest f.subject f.planted
          if rc != 0 then worst := rc
        return worst
      else
        IO.eprintln usage
        return 2
  | name :: rest =>
      let some f := find? name
        | IO.eprintln s!"error: unknown family `{name}`; known: {names}"
          IO.eprintln usage
          return 2
      if selfTestOnly then
        return (← selfTest f.subject f.planted)
      let path : System.FilePath :=
        match rest with
        | p :: _ => System.FilePath.mk p
        | [] => corpusPath f.subject.family
      run f.subject path

end EvmAsm.Tests.Correspondence.Registry
