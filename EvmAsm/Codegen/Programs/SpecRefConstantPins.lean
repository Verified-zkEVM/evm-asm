/-
  EvmAsm.Codegen.Programs.SpecRefConstantPins

  **#11517, applied to constants: SpecRef's definition versus the asm side's copy of it.**

  #12032 pinned the *byte-list* copies of `EMPTY_CODE_HASH` / `EMPTY_TRIE_ROOT`
  (`AccountDecodeCorrespondence.lean` — read that module first; it is the template,
  and it explains why a direct tie to SpecRef's `keccak256`-computed definitions is
  handled separately). This module completes that sweep by auditing **every** place
  in the tree carrying one of the three hash sentinels and pinning the copies #12032 did
  not reach, then extends it to the SpecRef constants whose asm-side copy is a *flattened*
  form of a *derived* definition. Named for the general shape rather than for hashes,
  because the second half is gas and size constants and the first divergence found is the
  reason the module exists at all.

  ## ⭐ The audit, honestly counted

  A raw grep for the leading bytes of the three sentinels hits 140 sites. Almost all of
  them are the *same* emitted `.data` text repeated across program modules, or prose, not
  independent definitions. Classified (SpecRef's own computed definitions excluded — they
  are the reference side, not a duplicate):

  | constant | sites | (A) independent asm-side `def` | (B) emitted `.data` byte run | (C) doc / fixture / expected value | (D) reference to another copy |
  |---|---|---|---|---|---|
  | `EMPTY_CODE_HASH` (`0xc5d2…a470`) | 78 | 3 | 46 | 29 | 0 |
  | `EMPTY_TRIE_ROOT` (`0x56e8…b421`) | 44 | 2 | 25 | 17 | 0 |
  | `EMPTY_OMMER_HASH` (`0x1dcc…9347`) | 18 | 1 | 12 | 5 | 0 |

  So the grep overcounts the drift surface by more than twenty to one: **six category-(A)
  definitions exist across the whole tree.** Three of them are the byte lists #12032
  already pinned. The other three are the hex-`String` constants in
  `EvmAsm/Stateless/Constants.lean` — and one of those is **wrong**.

  ## ✅ DIVERGENCE REPAIRED (#12081): `emptyOmmerHashHex` now holds the empty-ommers hash

  `EvmAsm/Stateless/Constants.lean:63` previously read

      def emptyOmmerHashHex : String := emptyTrieRootHex

  which made it `56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421` —
  the empty-*trie* root. `EMPTY_OMMER_HASH = keccak256(rlp([]))` hashes the RLP of the
  empty **list** (`0xc0`), whereas `EMPTY_TRIE_ROOT = keccak256(rlp(b""))` hashes the
  RLP of the empty **byte string** (`0x80`); the two differ. The slip's mechanism: the
  old docstring glossed `keccak256(rlp_encode([]))` as `keccak256(0x80)`, conflating
  the empty list with the empty string, and the alias inherited the conflation.

  #12082 recorded the divergence here as the kernel-checked theorems
  `divergence_emptyOmmerHashHex` / `divergence_emptyOmmerHashHex_eq_trieRoot` and
  deliberately deferred the repair to #12081 so defect and fix were reviewed on their
  own terms. #12081 landed the repair: the constant now holds the correct literal, the
  docs were corrected, and the two divergence theorems were **retired** — their content
  *was* the bug, so inverting them would have stated the fix twice under a misleading
  name. The record survives here and in the `fix_emptyOmmerHashHex` theorems below.

  Verified at the repair: `keccak256(0xc0) =
  1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347` and
  `keccak256(0x80) = 56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421`
  (both computed, not transcribed). The SpecRef witness
  (`EvmAsm.Stateless.SpecRef.EMPTY_OMMER_HASH`, `SeamShell.lean:111`, which computes
  `keccak256 (encS (.list []))`) and all twelve emitted `.data` copies
  (`0x1d, 0xcc, 0x4d, 0xe8`) already carried the correct value; the pinned `String`
  constant now agrees with them.

  ## What this module pins

  `hexNat?` parses the 64-hex-digit `String` form so the `String` constants can be
  compared against the numerals SpecRef's `#guard`s use (`WitnessState.lean:41-46`) and
  against the byte-list constants #12032 pinned. Every pin is `decide` over concrete
  data — no `keccak256` evaluation is involved anywhere in this file, so none of the
  proofs need a raised recursion limit.

  ## Why the other categories are not pinned here

  **(B) Bytes inside emitted asm `String`s** — 83 sites, e.g. `Dispatch.lean:850`,
  `BlockValidate.lean:364`, `MptInsertWalk.lean:351`. These are the guest's actual
  `.data` bytes and *can* drift from the Lean side, but a theorem about a `def … : String`
  is the wrong instrument: what is needed is an emission-level tie, and the emitted text
  is not addressable as structured data from a proof. They were instead **checked
  exhaustively out-of-band**: all 46 emitted `EMPTY_CODE_HASH` copies, all 25 emitted
  `EMPTY_TRIE_ROOT` copies and all 12 emitted `EMPTY_OMMER_HASH` copies are byte-identical
  to each other and to the correct value — 83 sites, three distinct values, zero
  disagreements. A `scripts/`-level scan is the right home for keeping that true; see
  the note in the closing section.

  **(C) Doc comments, test fixtures and expected values** — 51 sites. Most are prose
  quoting the constant inside a `/-- … -/` block (`Account.lean:58`,
  `AccountFields.lean:51`, `ChainAggregator.lean:506`, `HeaderFields.lean:735`, …), which
  cannot be false in the kernel's sense. The rest are data that already has a checker:
  `Codegen/Tests/Cases.lean:660,687` (`expectedOutHex`, checked by the differential
  harness) and the SpecRef witness-node preimages `IncrementalMptWrite.lean:630-631`
  (`wnode1` / `wnode2` embed both sentinels inside an RLP account leaf, and the enclosing
  `#guard`s on the resulting roots would fail on any edit to them). Neither needs a pin
  here.

  **(D) References to an already-pinned `def`** — none found. Every site is either its own
  literal or emitted text; no module reads a constant defined in another module. That is
  itself a finding: centralisation never happened, which is how a wrong `Constants.lean`
  went unnoticed for as long as it did. The single cross-`def` reference anywhere in the
  sweep is `Constants.lean:63`'s alias — and it is the defect.
-/
import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Codegen.Programs.AccountIsEip161EmptySpec
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.CreateDeployedCodeValid
import EvmAsm.Codegen.Programs.CreateInitcodeSizeValid
import EvmAsm.Stateless.Constants
import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Stateless.SpecRef.Transactions
import EvmAsm.Stateless.SpecRef.WitnessState

namespace EvmAsm.Codegen

namespace SpecRefConstantPins

open EvmAsm.Codegen.AccountDecodeSpec (adEmptyTrieRootBytes adEmptyCodeHashBytes)
open EvmAsm.Codegen.AccountIsEip161EmptySpec (aieEmptyCodeHashBytes)
open EvmAsm.Stateless.SpecRef (bytesBEtoNat)
open EvmAsm.Stateless.Constants (keccak256EmptyHashHex emptyTrieRootHex emptyOmmerHashHex)

/-! ## Reading the `String` form

    `EvmAsm/Stateless/Constants.lean` stores its three sentinels as 64-character hex
    `String`s, so pinning them needs a parser. `hexNat?` is deliberately partial in the
    `Option` sense: a non-hex character yields `none` rather than a silently-wrong digit,
    so a pin cannot be satisfied by a malformed string that happens to fold to the right
    number. It is a reader, not a fourth copy of any constant. -/

/-- Value of a single lower- or upper-case hex digit; `none` on any other character. -/
private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Big-endian hex fold with an accumulator, structural on the character list. -/
private def hexNatAux : Nat → List Char → Option Nat
  | acc, [] => some acc
  | acc, c :: cs =>
    match hexDigit? c with
    | none => none
    | some d => hexNatAux (acc * 16 + d) cs

/-- Parse a hex `String` big-endian; `none` if any character is not a hex digit. -/
def hexNat? (s : String) : Option Nat := hexNatAux 0 s.toList

/-! ## The `EMPTY_CODE_HASH` copies

    Four copies now exist in Lean: SpecRef's computed `keccak256 []`, two baked byte
    lists (both pinned by #12032), and the hex `String` here. -/

/-- `keccak256EmptyHashHex` (`Constants.lean:49`) folds to the numeral SpecRef's
    `#guard` uses for `EMPTY_CODE_HASH` (`WitnessState.lean:42-43`). -/
theorem keccak256EmptyHashHex_value :
    hexNat? keccak256EmptyHashHex
      = some 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  decide

/-- ⭐ The `String` copy and the account-decoder byte copy are the same 256-bit value.

    A genuine kernel equality between two independent asm-side definitions written in
    two different representations — no keccak evaluation, no numeral standing in the
    middle. This is the tie that would have caught a typo in either one. -/
theorem keccak256EmptyHashHex_eq_adBytes :
    hexNat? keccak256EmptyHashHex = some (bytesBEtoNat adEmptyCodeHashBytes) := by
  decide

/-- …and the same for the `account_is_eip161_empty` copy, whose verdict is *defined* by
    comparing a decoded field against it. -/
theorem keccak256EmptyHashHex_eq_aieBytes :
    hexNat? keccak256EmptyHashHex = some (bytesBEtoNat aieEmptyCodeHashBytes) := by
  decide

/-- The hex form is exactly 64 characters, i.e. a full 32-byte hash and not a truncation
    that happens to fold to the same number after leading-zero loss. -/
theorem keccak256EmptyHashHex_length : keccak256EmptyHashHex.length = 64 := by decide

/-! ## The `EMPTY_TRIE_ROOT` copies -/

/-- `emptyTrieRootHex` (`Constants.lean:57`) folds to the numeral SpecRef's `#guard` uses
    for `EMPTY_TRIE_ROOT` (`WitnessState.lean:45-46`). -/
theorem emptyTrieRootHex_value :
    hexNat? emptyTrieRootHex
      = some 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421 := by
  decide

/-- ⭐ The `String` copy and the account-decoder byte copy agree outright. -/
theorem emptyTrieRootHex_eq_adBytes :
    hexNat? emptyTrieRootHex = some (bytesBEtoNat adEmptyTrieRootBytes) := by
  decide

/-- Full 32-byte width, as above. -/
theorem emptyTrieRootHex_length : emptyTrieRootHex.length = 64 := by decide

/-- The two sentinels are distinct values — worth stating because `Constants.lean` aliases
    one constant to another (see the divergence below), so "these two names denote the same
    string" is a shape that actually occurs in this file and must not go unremarked. -/
theorem trieRoot_ne_codeHash : hexNat? emptyTrieRootHex ≠ hexNat? keccak256EmptyHashHex := by
  decide

/-! ## ⛔ `EMPTY_OMMER_HASH`: the divergence (#11517 outcome 3)

    Stated, not repaired. See the module docstring for the provenance of the slip and for
    the two witnesses that carry the correct value. -/

/-- ✅ **`emptyOmmerHashHex` holds the empty-ommers hash** (the #12081 fix pin,
    replacing the retired `divergence_emptyOmmerHashHex`).

    The first conjunct is the value it now holds, `keccak256(0xc0)`. The second is the
    trie-root value it *used* to alias — kept in the statement so the record of the
    divergence is itself kernel-checked rather than only narrated above. The third
    records, in the caller-facing form the retired
    `divergence_emptyOmmerHashHex_eq_trieRoot` used, that reaching for the named
    ommers constant no longer yields the storage-root sentinel. -/
theorem fix_emptyOmmerHashHex :
    hexNat? emptyOmmerHashHex
        = some 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
      ∧ hexNat? emptyTrieRootHex
        = some 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421
      ∧ hexNat? emptyOmmerHashHex ≠ hexNat? emptyTrieRootHex := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Beyond the sentinels: the *derived* SpecRef constants

    A wider sweep for SpecRef ↔ asm constant duplication turned up a large surface —
    roughly a hundred numbers, clustered in the gas schedule (`Evm64/Gas.lean`,
    `Evm64/{Memory,Log,Storage}Gas.lean`, `Codegen/GasConstants.lean`,
    `Codegen/Programs/{AmsterdamSystemTx,BlockVerdictParams}.lean`) and the precompile
    tables (`Stateless/VM/Precompiles.lean`, including two 128-entry BLS MSM discount
    tables). **Every pair checked is numerically equal today**, so there is no second
    divergence to report; the risk there is future drift, and pinning it wholesale is a
    separate, much larger piece of work than #11517's template asks for.

    Three of those duplicates are singled out here because they are the *sharpest* form of
    the risk and the cheapest to close: the SpecRef side is a **derived expression** and
    the asm side is a **flattened literal**. Repricing any input to the SpecRef formula
    changes it silently and leaves the asm number stale, with nothing failing — the
    #11516 shape exactly. The literal-vs-literal duplicates elsewhere are lower risk
    (an edit to either side is a deliberate act) and are left for the follow-up.

    Each pin below is `decide` over concrete `Nat`s: it forces SpecRef's formula to be
    evaluated and compared against the asm literal at elaboration time. -/

/-- ⭐ EIP-7702 per-authorization regular gas. SpecRef derives it as
    `AUTH_TUPLE_BYTES * TX_DATA_TOKEN_FLOOR + PRECOMPILE_ECRECOVER + COLD_ACCOUNT_ACCESS
    + 2 * WARM_ACCESS` over five separately-defined constants
    (`SpecRef/Gas.lean`, `REGULAR_PER_AUTH_BASE_COST`); `bvEip7702AuthRegularGas`
    (`BlockVerdictParams.lean`) is the flattened `7816`. Repricing any of those five
    inputs now breaks this build instead of silently staling the block-verdict capacity
    bound that is computed from it. -/
theorem bvEip7702AuthRegularGas_eq_spec :
    bvEip7702AuthRegularGas = EvmAsm.Stateless.SpecRef.GasCosts.REGULAR_PER_AUTH_BASE_COST := by
  decide

/-- ⭐ EIP-3860 initcode cap. SpecRef derives it as `2 * MAX_CODE_SIZE`
    (`SpecRef/Transactions.lean`, `MAX_INIT_CODE_SIZE`); `maxInitcodeSize`
    (`CreateInitcodeSizeValid.lean`) is the flattened `131072`. This file's own docstring
    records that a stale cutoff here once wrongly rejected valid init code, which is why
    the derived side is worth forcing. -/
theorem maxInitcodeSize_eq_spec :
    maxInitcodeSize = EvmAsm.Stateless.SpecRef.MAX_INIT_CODE_SIZE := by decide

/-- EIP-7907 deployed-code cap, the constant the one above is derived from
    (`SpecRef/Transactions.lean`, `MAX_CODE_SIZE` vs `CreateDeployedCodeValid.lean`,
    `maxDeployedCodeSize`). Pinned alongside so the pair cannot drift apart from each
    other either. -/
theorem maxDeployedCodeSize_eq_spec :
    maxDeployedCodeSize = EvmAsm.Stateless.SpecRef.MAX_CODE_SIZE := by decide

/-- The asm side's own derivation relationship, stated so that a future edit which fixes
    one cap and forgets the other is caught even without the SpecRef pins above. -/
theorem maxInitcodeSize_eq_two_maxDeployedCodeSize :
    maxInitcodeSize = 2 * maxDeployedCodeSize := by decide

/-! ## Closing notes

    **What is now tied to what.** For each of `EMPTY_CODE_HASH` and `EMPTY_TRIE_ROOT` the
    Lean-side copies are a connected component: `Constants.lean`'s `String` ↔
    `AccountDecodeSpec`'s bytes ↔ (`EMPTY_CODE_HASH` only) `AccountIsEip161EmptySpec`'s
    bytes, plus the numeral pins to SpecRef's `#guard`s. Editing any one of them without
    editing the others now fails the build. `EMPTY_OMMER_HASH` has no Lean-side byte
    constant to tie to — only the divergent `String` and the emitted text — which is
    precisely why its defect survived.

    **Category (B) has no proof-level home.** The 83 emitted `.byte` sites were verified
    identical out-of-band, but nothing in the kernel keeps them that way. A source-scan
    gate under `scripts/` that re-derives the three 32-byte runs from every `.data` section
    and rejects any that is not one of the three known-good values is the natural follow-up;
    it is not attempted here because this module is additive and touches no gate.

    **What the wider sweep left open.** The gas-schedule and precompile duplications
    described in the previous section are unpinned by design here: all equal today, none
    tripwired, and far too many to fold into a module about hash sentinels. Two structural
    observations from that sweep are worth carrying to #11517 rather than losing:
    `Codegen/GasConstants.lean`'s header states that referencing SpecRef was *deliberately*
    declined (to keep `SpecRef.Gas` out of every importer's reachable set) and that, since
    the spec mirror "holds the same numbers independently", it "already functions as the
    cross-check a shared definition would have given". It does not: the module's `#guard`s
    restate each asm `def` against the numeral it is defined as, which catches an edit to
    the asm side but is silent if SpecRef is the side that moves — and a repricing moves
    SpecRef first. The reachable-set argument is sound; the claim that a docstring citation
    substitutes for a check is not. And
    `Codegen/MemoryBudgetGuard.lean` already references SpecRef for two constants yet
    defines a third copy of the `1024` call-depth limit next to them. One further stale
    citation, category (C): `Evm64/WitnessAssertions.lean` justifies its index capacity by
    citing `MAX_WITNESS_NODES = 2^20`, while `SpecRef/Ssz.lean` defines it as `2^22`. The
    bound stays fail-closed either way (the builder returns failure rather than
    truncating), so it is a wrong citation rather than a wrong bound. -/

end SpecRefConstantPins

end EvmAsm.Codegen
