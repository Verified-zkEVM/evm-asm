/-
  EvmAsm.Stateless.Witness.NodeDb.Lookup

  Lookup a node by its keccak hash. Mirrors Python's
  `node_db[hash]` dict access.

  ## Calling convention

      Input:
        a0 = ptr to 32-byte hash
      Output:
        a0 = ptr to node bytes (0 on miss)
        a1 = node length in bytes (0 on miss)
        a2 = ZKVM_EOK (0) on hit, WITNESS_MISSING_NODE (TBD) on miss

  ## Algorithm (RISC-V plan)

      Build a deterministic index over `(keccak256(node), ptr, len)` records,
      then lookup by comparing the full 32-byte hash. The first draft used
      `bucket = hash[0..4] mod NUM_BUCKETS` with linked chains, but GH #7929
      notes that attacker-shaped buckets can become a DoS frontier. Prefer a
      bounded-worst-case layout such as a sorted flat table with binary search,
      a trie over hash bytes, or a balanced tree.

  On miss, the caller routes to
  `EvmAsm.Stateless.unimplemented_exit` with reason
  `REASON_WITNESS_MISSING_NODE`. A missing node means the witness
  was incomplete -- the prover did not include a required MPT
  node -- which is a stateless-verification failure.


  ## Existing implementations surveyed

  - execution-specs builds a Python `Dict[keccak256(entry)] = entry` once in
    `forks/amsterdam/witness_state.py`, and `incremental_mpt.py` resolves child
    hashes by dictionary lookup during trie decoding. This confirms the desired
    semantic model is pre-indexed lookup, not repeated witness-section scans.
  - geth exposes trie-node reads through keyed database helpers such as
    `ReadTrieNode` / `ReadLegacyTrieNode` / `ReadStorageTrieNode`; the hot path
    is a database/cache lookup by node identity, not a linear proof scan.
  - reth's trie implementation is cursor-oriented (`TrieCursor`,
    `HashedCursor`) over hashed state/trie data, again avoiding repeated
    re-hashing of every candidate node per traversal step.
  - Erigon documents flat key-value state/trie storage and trie `Get` APIs;
    it also avoids scanning all witness nodes for each child reference.

  For this zkVM guest, a randomized or adversarially-collidable hash table is a
  poor fit: the prover controls witness bytes. Use a deterministic bounded
  structure with full-hash equality checks.

  ## PR-K19 status

  Asm implementation lands in
  `EvmAsm.Codegen.Programs.witnessLookupByHashFunction`. PR-K19
  ships the linear-scan version (O(N) per lookup): walk every
  entry in the SSZ list, compute `keccak256(entry_bytes)`, and
  compare against the target hash. The bucket-chain layout
  described above remains the eventual target -- a follow-up
  PR replaces the linear scan with a pre-built bucket table.

  ## Calling convention (linear scan, PR-K19)

      Input:
        a0 (input)  : SSZ list section ptr (e.g. witness.state
                      or witness.codes section bytes)
        a1 (input)  : section_len
        a2 (input)  : 32-byte target hash ptr
        a3 (input)  : u64 output ptr (receives byte offset
                      within section where the matched entry
                      starts; meaningful only on hit)
        a4 (input)  : u64 output ptr (receives byte length of
                      the matched entry; meaningful only on hit)
        ra (input)  : return

      Output:
        a0 = 0  on hit (entry found)
        a0 = 1  on miss (no entry has the target hash, or
                section was empty)

  Caller computes the matched entry's byte pointer as
  `section_ptr + *out_start_offset`.

  ## Implementation shape

  Uses one 32-byte `.data` scratch (`wlh_scratch_hash`) for the
  per-iteration keccak output. The linear scan is not size-capped: sections
  without a registered index (notably `witness.codes`, which can exceed
  64 KiB via large predeploy bytecode) must still resolve, since a capped
  miss turns into a false witness-integrity rejection. Repeated lookups on
  a large section should go through the sorted index built by
  `witness_index_build` (the stateless verdict registers `witness.state`).
-/

namespace EvmAsm.Stateless.Witness.NodeDb.Lookup

-- TODO(stateless-witness): expose a `cpsTripleWithin` spec
-- over `witness_lookup_by_hash` once the abstract DB semantics
-- are formalised.

end EvmAsm.Stateless.Witness.NodeDb.Lookup
