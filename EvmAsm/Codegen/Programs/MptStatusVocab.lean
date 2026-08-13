/-
  EvmAsm.Codegen.Programs.MptStatusVocab

  Single source of truth for the three MPT-lookup status vocabularies
  (walk / account_at_address / cahsr family) and the explicit
  cross-layer remaps. GH #12234.

  Other modules MUST NOT restate the full status tables — point here
  with "see MptStatusVocab". Asm remap sites carry `STATUS_VOCAB:` tags
  audited by `scripts/check-mpt-status-vocab.sh` against the committed
  snapshot `scripts/mpt-status-vocab-expected.txt`.
-/

namespace EvmAsm.Codegen.MptStatusVocab

/-! ## Walk / `mpt_lookup_by_key` (mirrors `mpt_walk`) -/

namespace Walk
/-- Found a value at the path. -/
abbrev found : Nat := 0
/-- Clean path-absent (empty slot / path exhausted / trie not-found). -/
abbrev absent : Nat := 1
/-- True parse error: hash-authenticated bytes fail RLP / node-kind. -/
abbrev parse : Nat := 2
/-- Unresolved HashedNode: referenced child hash absent from witness. -/
abbrev unresolved : Nat := 3
end Walk

/-! ## `account_at_address` -/

namespace Account
abbrev found : Nat := 0
abbrev absent : Nat := 1
abbrev parse : Nat := 2
/-- `account_decode` failure on a present leaf. -/
abbrev decodeFail : Nat := 3
/-- Remapped from `Walk.unresolved`. -/
abbrev unresolved : Nat := 4
end Account

/-! ## `code_at_header_state_root` / cahsr family -/

namespace Cahsr
abbrev found : Nat := 0
abbrev absent : Nat := 1
abbrev parse : Nat := 2
abbrev decodeFail : Nat := 3
/-- Header parse / state_root size fail. -/
abbrev headerFail : Nat := 4
/-- Code hash not found in `witness.codes`. -/
abbrev codeMiss : Nat := 5
/-- Remapped from `Account.unresolved`. -/
abbrev unresolved : Nat := 6
end Cahsr

/-! ## Explicit remaps — never identity-pass walk unresolved into cahsr space -/

/-- Walk status → account status. Unresolved is the only non-identity map. -/
def accountOfWalk (s : Nat) : Nat :=
  if s == Walk.unresolved then Account.unresolved else s

/-- Account status → cahsr status. Unresolved is the only non-identity map
    among account outcomes (headerFail / codeMiss are cahsr-local). -/
def cahsrOfAccount (s : Nat) : Nat :=
  if s == Account.unresolved then Cahsr.unresolved else s

def cahsrOfWalk (s : Nat) : Nat := cahsrOfAccount (accountOfWalk s)

-- Propagation rule (typed).
#guard accountOfWalk Walk.unresolved == Account.unresolved
#guard cahsrOfAccount Account.unresolved == Cahsr.unresolved
#guard cahsrOfWalk Walk.unresolved == Cahsr.unresolved
-- Identity is forbidden for the unresolved chain (would collide with
-- Account.decodeFail=3 and Cahsr.headerFail=4).
#guard accountOfWalk Walk.unresolved != Walk.unresolved
#guard cahsrOfAccount Account.unresolved != Account.unresolved
#guard cahsrOfWalk Walk.unresolved != Walk.unresolved
#guard cahsrOfWalk Walk.unresolved != Cahsr.headerFail
#guard cahsrOfWalk Walk.unresolved != Cahsr.codeMiss
#guard cahsrOfWalk Walk.unresolved != Cahsr.decodeFail
-- Stable identity for the shared 0/1/2 codes.
#guard accountOfWalk Walk.found == Account.found
#guard accountOfWalk Walk.absent == Account.absent
#guard accountOfWalk Walk.parse == Account.parse
#guard cahsrOfAccount Account.found == Cahsr.found
#guard cahsrOfAccount Account.absent == Cahsr.absent
#guard cahsrOfAccount Account.parse == Cahsr.parse
#guard cahsrOfAccount Account.decodeFail == Cahsr.decodeFail

/-- Lossy probe adapter: unresolved HashedNode → clean absent.
    Only `mpt_walk_probe` (and sites tagged `STATUS_VOCAB: probe-remap`)
    may perform this collapse. -/
def probeRemap (s : Nat) : Nat :=
  if s == Walk.unresolved then Walk.absent else s

#guard probeRemap Walk.unresolved == Walk.absent
#guard probeRemap Walk.parse == Walk.parse
#guard probeRemap Walk.absent == Walk.absent

end EvmAsm.Codegen.MptStatusVocab
