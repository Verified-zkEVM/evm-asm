/-
  EvmAsm.Tests.Correspondence.Bal

  The BAL (block access list) **canonical ordering** instance of the
  spec-correspondence harness: `SpecRef._build_from_builder` against
  `execution-specs`' `_build_from_builder`.

  Method: docs/agents/spec-correspondence.md.
  Findings and the routine table: docs/bal-spec-correspondence.md.

  ## Why this family is audited at the model boundary

  BAL sorting is stateful at the surface — a mutable builder threaded through
  block execution — so it has no data-in/data-out interface at *routine*
  granularity (method §5). The functional boundary chosen here is
  `builder → canonical BlockAccessList`, which is pure on both sides.

  That choice is what makes this instance possible at all.
  `EvmAsm/Codegen/Programs/BalCanonicalSort.lean` defines only `String`s — zero
  `: Program` — so `cpsTripleWithin` cannot state sortedness, and issue #10817
  is blocked on a ~230-instruction conversion. **A model-boundary differential
  needs no `Program`, no triple and no conversion**, so it can answer "is our
  canonical ordering the reference's ordering?" today, leaving "does the asm
  implement it?" as the named remaining obligation.

  It also answers that module's standing objection — that sortedness plus
  permutation is insufficient because a sort on the wrong key is still sorted
  and still a permutation. A differential against the reference's *declared*
  ordering is exactly the independent key that objection asks for.

  ## Reference kind

  **Vendored** (`execution-specs/src/ethereum/forks/amsterdam/block_access_lists.py`),
  so per method §6 this family needs none of the external-package version
  machinery RLP requires — the gitlink pins it.

  ## Wire format

  One builder per corpus line; the canonical output uses the *same* grammar, so
  parser and renderer are inverses and a diff is readable.

      builder   := account ("#" account)*        -- empty line = no accounts
      account   := addrHex "|" sChanges "|" reads "|" bals "|" nonces "|" codes
      sChanges  := slotGroup ("/" slotGroup)*
      slotGroup := slot ":" change (";" change)*
      change    := index "," value
      reads     := slot (";" slot)*
      bals      := index "," value (";" ...)*    -- nonces likewise
      codes     := index "," codeHex (";" ...)*

  Numbers are decimal (`U256`/`U64`/index are all `Nat` in SpecRef); addresses
  and code are hex. Separators are all distinct, so no escaping is needed.
-/

import EvmAsm.Stateless.SpecRef.BlockAccessLists
import EvmAsm.Tests.Correspondence.Harness

namespace EvmAsm.Tests.Correspondence.Bal

open EvmAsm.Stateless.SpecRef
open EvmAsm.Tests.Correspondence

/-! ## Parsing -/

/-- `splitOn` returns `[""]` on the empty string; a corpus field that is absent
should yield no items, not one empty item. -/
private def parts (sep s : String) : List String :=
  if s.isEmpty then [] else s.splitOn sep

private def natOf? (s : String) : Option Nat := s.trimAscii.toString.toNat?

/-- `index "," value` -/
private def pairOf? (s : String) : Option (Nat × Nat) :=
  match s.splitOn "," with
  | [a, b] => do let x ← natOf? a; let y ← natOf? b; some (x, y)
  | _ => none

private def storageChangesOf? (s : String) : Option (List (U256 × List StorageChange)) :=
  (parts "/" s).mapM fun group =>
    match group.splitOn ":" with
    | [slotS, changesS] => do
        let slot ← natOf? slotS
        let cs ← (parts ";" changesS).mapM fun c => do
          let (i, v) ← pairOf? c
          some (StorageChange.mk i v)
        some (slot, cs)
    | _ => none

private def codesOf? (s : String) : Option (List CodeChange) :=
  (parts ";" s).mapM fun item =>
    match item.splitOn "," with
    | [iS, codeS] => do
        let i ← natOf? iS
        let code ← parseHexBytes codeS
        some (CodeChange.mk i code)
    | _ => none

/-- Parse one corpus line into a builder. `none` on any malformed field — the
harness reads that as "we reject this input". -/
def parseBuilder? (line : String) : Option BlockAccessListBuilder := do
  let accounts ← (parts "#" line).mapM fun acct =>
    match acct.splitOn "|" with
    | [addrS, scS, readsS, balsS, noncesS, codesS] => do
        let addr ← parseHexBytes addrS
        let sc ← storageChangesOf? scS
        let reads ← (parts ";" readsS).mapM natOf?
        let bals ← (parts ";" balsS).mapM fun i => do
          let (a, b) ← pairOf? i; some (BalanceChange.mk a b)
        let nonces ← (parts ";" noncesS).mapM fun i => do
          let (a, b) ← pairOf? i; some (NonceChange.mk a b)
        let codes ← codesOf? codesS
        some (addr, ({ storageChanges := sc, storageReads := reads,
                       balanceChanges := bals, nonceChanges := nonces,
                       codeChanges := codes } : AccountData))
    | _ => none
  some { blockAccessIndex := 0, accounts := accounts }

/-! ## Rendering -/

private def renderSlotGroup (sc : SlotChanges) : String :=
  toString sc.slot ++ ":" ++
    String.intercalate ";" (sc.changes.map fun c =>
      toString c.blockAccessIndex ++ "," ++ toString c.newValue)

private def renderAccount (a : AccountChanges) : String :=
  String.intercalate "|"
    [ hexOfBytes a.address
    , String.intercalate "/" (a.storageChanges.map renderSlotGroup)
    , String.intercalate ";" (a.storageReads.map toString)
    , String.intercalate ";" (a.balanceChanges.map fun b =>
        toString b.blockAccessIndex ++ "," ++ toString b.postBalance)
    , String.intercalate ";" (a.nonceChanges.map fun n =>
        toString n.blockAccessIndex ++ "," ++ toString n.newNonce)
    , String.intercalate ";" (a.codeChanges.map fun c =>
        toString c.blockAccessIndex ++ "," ++ hexOfBytes c.newCode) ]

def render (bal : BlockAccessList) : String :=
  String.intercalate "#" (bal.map renderAccount)

/-! ## The two axes -/

/-- Primary: builder → canonical BAL, rendered. This is the ordering question. -/
def runCanonicalize (line : String) : Option String := do
  let b ← parseBuilder? line
  some (render (_build_from_builder b))

/-- Auxiliary axis: were the **accounts** already in canonical address order?

    Scoped deliberately to the top-level account list, because that is the only
    part of "was the input already canonical" the reference can answer. Python
    stores `storage_reads` in a `Set`, which destroys input order before
    `_build_from_builder` ever sees it — CPython even iterates `{223, 75}` as
    `[75, 223]`, so a reads-based version of this axis reports "already
    canonical" for *every* input and measures nothing. Accounts live in a
    `Dict`, which preserves insertion order, so the question is well posed on
    both sides.

    A first version of this axis included reads and produced 32 spurious
    mismatches — an artifact of the reference's representation, not a finding.
    Narrowing it is the honest fix; manufacturing a comparison the reference
    cannot express is exactly what the method warns against. -/
def runAccountsAlreadyOrdered (line : String) : Option Bool := do
  let b ← parseBuilder? line
  let inputAddrs := b.accounts.map (·.1)
  let canonicalAddrs := (_build_from_builder b).map (·.address)
  some (inputAddrs == canonicalAddrs)

def subject : Subject :=
  { family := "bal"
    run := runCanonicalize
    aux := runAccountsAlreadyOrdered
    auxLabel := "accounts-ordered"
    ourName := "SpecRef._build_from_builder"
    docPage := "docs/bal-spec-correspondence.md" }

/-- Planted records for the self-test: exactly one of each finding class plus one
agreement. `aa…` sorts before `bb…`, so the two-account input is reordered. -/
def plantedRecords : List Record :=
  let twoAccts := "bb00000000000000000000000000000000000000|||||" ++
                  "#aa00000000000000000000000000000000000000|||||"
  let sorted := "aa00000000000000000000000000000000000000|||||" ++
                "#bb00000000000000000000000000000000000000|||||"
  [ -- agrees: reordered input, correct canonical output, and correctly reported
    -- as NOT already canonical
    { input := twoAccts, accepted := true, detail := sorted, auxSame := some false }
    -- stricter: malformed (an account with too few fields); we reject, oracle says accept
  , { input := "zz|bogus", accepted := true, detail := "anything" }
    -- looser: well-formed input the oracle claims to reject
  , { input := sorted, accepted := false, detail := "Planted" }
    -- value mismatch: valid input, wrong expected ordering
  , { input := twoAccts, accepted := true, detail := twoAccts }
    -- aux mismatch: correct ordering, wrong already-canonical bit
  , { input := sorted, accepted := true, detail := sorted, auxSame := some false }
  ]

end EvmAsm.Tests.Correspondence.Bal
