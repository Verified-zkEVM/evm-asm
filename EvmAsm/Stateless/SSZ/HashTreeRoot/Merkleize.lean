/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.Merkleize

  SSZ pairwise merkleization for a power-of-two chunk count.

  ## Algorithm

  Given `n` (a power of two) and a contiguous buffer of `n`
  32-byte chunks, compute the Merkle root by repeatedly
  pair-hashing adjacent chunks:

      while n > 1:
          for i in 0..n/2:
              chunks[i] = sha256_pair(chunks[2i], chunks[2i+1])
          n = n / 2
      root = chunks[0]

  This is the *fixed* (power-of-two) case. The general SSZ
  merkleize() also pads short lists out to the next power of two
  using `Z_d` from the zero-hashes table (PR-S5). That extension
  lands in a follow-up PR; the fixed case already covers any SSZ
  Container whose field count is a power of two (and is the
  inner kernel used by the padded version too).

  ## Contract

  Caller convention:

      a0 (input)  : pointer to `n * 32` contiguous bytes
                    (the chunks, treated as read-only -- the
                    function copies them into a scratch buffer
                    before reducing in-place)
      a1 (input)  : `n` (power of two; 1 ≤ n ≤ 32)
      a2 (input)  : pointer to a 32-byte output buffer
      ra (input)  : return address

      a0 (output) : ZKVM_EOK (0) on success
      32 bytes at *a2  : SSZ Merkle root over the input chunks

  The function uses a 1024-byte scratch buffer
  (`ssz_merkleize_scratch`) to do the reduction without
  mutating the caller's input. Cap on `n` (=32) keeps the
  scratch fixed-size; larger lists land in follow-up PRs.

  ## Implementation shape

  `sszMerkleizePow2Function` (in `EvmAsm/Codegen/Programs.lean`)
  emits the labelled function `ssz_merkleize_pow2:`. Internally
  it calls `zkvm_sha256` (PR-S2) once per pair-hash with `a1 = 64`
  (mirroring `sszPairHashCallAsm`). BuildUnits that consume it
  must inline both `zkvmSha256Function` and
  `sszMerkleizePow2Function` once, behind a skip-jump so
  `_start` fall-through misses them.

  ## Why a separate file from `ZeroHashes`

  `ZeroHashes` describes pure data (constants emitted to
  `.rodata`); `Merkleize` describes a verified callable. Keeping
  them in sibling files mirrors the
  `Headers/{Decode,Validate,BlockHash}` layout (data shape vs.
  verified Program) and gives each its own slot for a future
  `Spec.lean` CPS triple.

  ## PR-S6 status

  Defines the contract; the executable lives where it's inlined
  (PR-S6's `zisk_ssz_merkleize_pow2` probe BuildUnit). PR-S7+
  reuse the same function symbol from larger merkleizers without
  re-emitting it.
-/

module

@[expose] public section
namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Maximum input chunk count supported by `ssz_merkleize_pow2`.
    Determines the size of the scratch buffer (1024 bytes for
    `sszMerkleizePow2MaxChunks = 32`). -/
def sszMerkleizePow2MaxChunks : Nat := 32

end EvmAsm.Stateless.SSZ.HashTreeRoot
