# Soundness assumptions for the guest

This document separates two kinds of soundness assumptions. Section 1 records **assumptions the
guest is entitled to make about its inputs**. They are not implementation details: a caller that
violates one is outside the specified interface, and the guest's behaviour on such an input carries
no soundness guarantee. Section 2 records the cryptographic assumptions underlying commitment
checks; those are not caller-violable input preconditions.

Each entry states the assumption, why the guest needs it, and what happens if it is broken.

---

## 1. No account in the supplied pre-state may have a nonce of 2^64 or more

**Assumption.** Every account in the supplied pre-state has a nonce strictly below 2^64 — one
whose significant representation fits in 8 bytes.

**Why the guest needs it.** The guest's account representation is 8 bytes wide, and the decoder
enforces it: `account_decode` scans past the nonce field's leading zero bytes and then gates the
**significant** length at 8, branching to decode failure above it (`State.lean:97-98` at
`b543802a4`, `.LI .x7 (8 : Word)` then `.BLTU .x7 .x6`). The pinned spec has no such bound:
`Account.nonce` is `Uint`, arbitrary-size (`state.py:57-59`), and the witness decoder constructs
it from the field bytes with no length or value check (`witness_state.py:114`). So a pre-state
leaf carrying a 9-significant-byte nonce decodes fine on the reference and fails on the guest.

**Why it is safe to assume.** Execution cannot produce such a nonce. Enumerating every nonce
write in the pinned fork: ordinary transactions reject `tx.nonce ≥ U64.MAX_VALUE` and increment
once (`transactions.py:553-584`, `fork.py:555-558`, `fork.py:906`); CREATE/CREATE2 reject a
sender nonce of 2^64 − 1 before incrementing and start created accounts at 0
(`system.py:89-105`, `interpreter.py:180-196`); EIP-7702 delegation applies the same cap and a
single increment (`eoa_delegation.py:171, 187-189, 228-230`); system transactions add no new
writer (`fork.py:696-735`). The maximum reachable by ordinary transitions is therefore
2^64 − 1 — exactly at the guest's boundary. Only two supply paths can present a wider nonce:
**genesis**, whose allocation is unbounded (`genesis.py:209-221`), and a **directly-supplied
pre-state**, whose leaf bytes the caller chooses.

**Consequence if broken.** The guest false-**rejects**: it declines a state the reference would
accept. That is the safe direction — the guest never accepts a block or root it should not; it
simply refuses to rule on an input outside the interface.

**This is a claim about state provenance, and nothing in the guest enforces it.** The guest
verifies supplied witness bytes against a supplied root; it does not derive nonces from
transactions, so it cannot distinguish a post-genesis state produced by ordinary capped
transitions from a hand-minted one. The assumption is discharged by whoever produces the
pre-state, not by any check the decoder performs.

**Obligations this places on callers.**

- **Producers of pre-states** must guarantee every account nonce is below 2^64. Any state
  reached from a compliant genesis by ordinary, EIP-2681-capped transitions satisfies this
  automatically.
- **Test and fixture harnesses** constructing synthetic pre-states or genesis allocations must
  not mint accounts with nonces at or above 2^64. A fixture that does is not measuring a
  divergence: it is operating outside the specified interface, and the guest's reject there is
  the specified behaviour.

**Do not "fix" this by widening the guest's bounds.** Matching the reference would mean
representing the nonce as an unbounded `Uint` — a representation change, not a bound tweak — and
the 8-byte account field is pervasive through the decoder, the state assertions and every
account-write path. Loosening a single gate would leave the representation assumption in place
everywhere else while removing the one place it was visible; and since the failure direction is
a false reject, the narrow gate denies the caller nothing it was ever entitled to.

---

## 2. Cryptographic assumptions (not input preconditions)

Section 1 records assumptions about caller-supplied inputs. The assumption below is different:
it is a computational assumption about the cryptographic functions used by the commitment checks.
It is not a caller-violable input precondition, and no guest gate can discharge it by rejecting a
particular input.

### Collision resistance of commitment hashes

**Assumption.** Keccak-256 is collision resistant for the Keccak commitments used by the BAL,
post-state-root, and block-hash checks, and SHA-256 is collision resistant for the EIP-7685
execution-requests commitment. In practical terms, it must be infeasible to construct distinct
byte strings with the same relevant digest.

**Where it is load-bearing.**

- **BAL digest (Keccak).** `bal_serializer_verify` rebuilds the BAL, hashes the rebuilt and
  supplied sections, and accepts when their four 64-bit digest words are equal
  (`EvmAsm/Codegen/Programs/BalSerializer.lean:1159-1167`). This check does not compare the raw
  BAL bytes. The step from equal digest to equal bytes relies on collision resistance.
- **Post-state root (Keccak/MPT).** The verdict computes `sv_recomputed` with `block_state_root`
  and compares it with the supplied 32-byte header root
  (`EvmAsm/Codegen/Programs/BlockVerdictMtxRuntime.lean:739-748`); the state-root routine's final
  MPT root is produced by `mpt_bounded_state_root`
  (`EvmAsm/Codegen/Programs/BlockVerdictStateRoot.lean:445-449`). A collision could let a wrong
  post-state trie share the claimed root. The same Keccak assumption also supports witness/MPT
  preimage authentication, where the node database is keyed by Keccak digests
  (`EvmAsm/Stateless/SpecRef/IncrementalMpt.lean:23-34`).
- **Block hash (Keccak).** The verdict hashes the reconstructed header RLP with
  `block_hash_from_header` and compares the result with the supplied block hash
  (`EvmAsm/Codegen/Programs/BlockVerdictFunction.lean:65-72`); that helper is defined as the
  Keccak hash of the header RLP (`EvmAsm/Codegen/Programs/Header.lean:1128-1178`). A collision
  could make a different reconstructed header pass this commitment check.
- **Execution-requests hash (SHA-256).** The receipts tail calls `requests_hash_verify` and
  rejects a nonzero status (`EvmAsm/Codegen/Programs/BlockVerdictReceiptsTail.lean:126-135`).
  The verifier assembles and compares the 32-byte commitment
  (`EvmAsm/Codegen/Programs/AssembleExecutionRequests.lean:159-215`), and the requests-hash
  implementation is the EIP-7685 nested SHA-256 construction, not Keccak
  (`EvmAsm/Codegen/Programs/RequestsHash.lean:1-6,112-136`). A collision could make different
  derived request bytes pass the header commitment.

**Consequence if broken.** The guest could accept a supplied commitment whose digest matches the
recomputed digest even though the underlying bytes or structure differ: a BAL serializer/builder
mismatch, an incorrect post-state trie, an incorrect header, or incorrect execution requests could
evade its corresponding check. This is separate from an implementation bug that computes the
wrong digest.

**What this is not.** `zkvm_keccak256_spec_within`
(`EvmAsm/Codegen/Proofs/HashBridgeKeccakTop.lean:280-292`) proves machine-level correctness of
the emitted Keccak computation for its input window. It does not prove collision resistance of the
mathematical Keccak function. Likewise, a machine-level SHA-256 correctness proof would not imply
SHA-256 collision resistance. The latter belongs in this cryptographic-assumption section, not
among the input preconditions above.

---

*Written by **Claude Code** (k3 agent) at the maintainer's direction. Placed in `docs/` to match
the existing convention (`docs/agents/…`, `docs/4ch8f-…`) rather than creating a second top-level
documentation directory.*
