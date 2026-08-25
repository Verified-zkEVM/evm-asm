/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.MerkleizeFull

  Arbitrary-length SSZ merkleization with `Z_d` zero-padding.
  Lifts PR-S6's power-of-two reduction to the general SSZ case:
  any chunk count `n` paired with a capacity `2^limit_log2 ≥ n`.

  ## Algorithm

  Two phases:

    1. Pad chunks up to `M = next_pow2(n)` with `Z_0 = 0x00 * 32`.
       Reduce in place with `ssz_merkleize_pow2` (PR-S6).
       After this step, the partial root corresponds to a tree
       of depth `log2(M) =: d_M`.

    2. For `d` from `d_M` to `limit_log2 - 1`:
           partial_root = sha256_pair(partial_root, Z_d)
       That is, the current root is the left subtree at depth
       `d`; the right subtree is an all-zero tree at the same
       depth, whose root is `Z_d`. Pair-hashing them together
       lifts the root one level. After `limit_log2 - d_M`
       iterations, the root has been lifted to depth
       `limit_log2`, matching the SSZ Container capacity.

  Edge case: `n = 0`. Skip step 1 (no chunks to pad); the SSZ
  root is `Z_{limit_log2}` directly, fetched from the PR-S5
  table.

  ## Why this matches the SSZ spec

  SSZ `merkleize(chunks, limit)` is defined as the root of a
  perfect binary tree of depth `ceil(log2(limit))`, whose first
  `len(chunks)` leaves are the input chunks and whose remaining
  leaves are zero. Phase 1 hashes the populated part of the tree
  up to depth `d_M`. Phase 2 lifts that root up the spine: at
  each depth `d`, the *right* sibling is `Z_d` because the right
  subtree at depth `d` (above the populated region) is entirely
  zero leaves, and `Z_d` is by definition the hash of an all-zero
  subtree at that depth.

  ## Contract

  Caller convention:

      a0 (input)  : pointer to `n * 32` chunk bytes (read-only)
      a1 (input)  : n       (0 ≤ n ≤ 32)
      a2 (input)  : limit_log2 L (0 ≤ L ≤ 31; capacity = 2^L)
                    Precondition: `n ≤ 2^L`. Caller-checked.
      a3 (input)  : 32-byte output ptr
      ra (input)  : return address

      a0 (output) : ZKVM_EOK (0) on success
      32 bytes at *a3 : SSZ Merkle root

  Cap on `n` (=32) keeps the padded scratch fixed (1024 B); cap
  on `L` (=31) matches the PR-S5 zero-hashes table. Both extend
  as larger SSZ types appear without breaking the function
  signature.

  ## Implementation shape

  `sszMerkleizeFunction` (in `EvmAsm/Codegen/Programs.lean`)
  emits the labelled function `ssz_merkleize:`. Internally calls:
    * `ssz_merkleize_pow2` (PR-S6) for phase 1
    * `zkvm_sha256`        (PR-S2) once per Z_d mix-in

  BuildUnits that use it must inline `zkvmSha256Function`,
  `sszMerkleizePow2Function`, `sszMerkleizeFunction`, and the
  `ssz_zero_hashes` `.rodata` table once each, behind a skip-jump
  so `_start` fall-through misses them.

  ## PR-S7 status

  Defines the contract for arbitrary-length SSZ merkleization.
  Executable lives where its caller wants it inlined (PR-S7's
  `zisk_ssz_merkleize` probe BuildUnit). PR-S8 wires this into
  `compute_new_payload_request_root` to stamp the real SSZ root
  into `OUTPUT[0..32]` (replacing the keccak stub PR-K7 put
  there).
-/

module

@[expose] public section
namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Maximum input chunk count supported by `ssz_merkleize`.
    Matches `sszMerkleizePow2MaxChunks`; the padded scratch is
    `sszMerkleizeMaxChunks * 32 = 1024` bytes. -/
def sszMerkleizeMaxChunks : Nat := 32

/-- Maximum `limit_log2` supported. Matches `sszZeroHashesDepth`
    minus 1 -- the function can mix in Z_0..Z_{30} during the
    zero-padding phase, lifting up to depth 31. -/
def sszMerkleizeMaxLimitLog2 : Nat := 31

end EvmAsm.Stateless.SSZ.HashTreeRoot
