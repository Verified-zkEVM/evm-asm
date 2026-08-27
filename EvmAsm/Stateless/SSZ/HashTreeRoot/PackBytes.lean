/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.PackBytes

  Pack an arbitrary byte string into 32-byte chunks for SSZ
  merkleization.

  ## Why

  SSZ's `hash_tree_root` for `Bytes` (variable-length byte
  string) and `Bytes[N]` (fixed-length byte vector) is computed
  by:

    1. Pack: split the bytes into 32-byte chunks. The final
       chunk is right-zero-padded if the byte count is not a
       multiple of 32.
    2. Merkleize: feed the chunks to `ssz_merkleize` with a
       capacity matching the SSZ declaration (limit = ceil(L /
       32) chunks for `Bytes`, or `ceil(N / 32)` for `Bytes[N]`).
    3. (Variable-length only:) mix in the byte length.

  This module supplies step 1: the chunk packer. Steps 2 and 3
  live above it (PR-S7 already has step 2; mix-in-length is a
  later PR-S+ once a concrete consumer surfaces).

  ## Contract

  Caller convention:

      a0 (input)  : pointer to source bytes
      a1 (input)  : byte length L (0 ≤ L ≤ 1024;
                    cap matches `sszMerkleizeMaxChunks * 32`)
      a2 (input)  : pointer to a (32 * ceil(L/32))-byte
                    output chunk buffer
      ra (input)  : return address

      a0 (output) : chunk count, `ceil(L / 32)`
      32 * a0 bytes at *a2 :
          source bytes in order, with the final chunk zero-
          padded if `L % 32 != 0`. When `L == 0`, no bytes are
          written and `a0` returns `0`.

  ## Implementation shape

  `sszPackBytesFunction` emits the labelled function
  `ssz_pack_bytes:`. Roughly:

      copy L bytes from src to dst (byte-by-byte, the input may
        be unaligned; this is the worst case 1024 byte copies,
        ~3K instructions in the slow path -- acceptable for
        bring-up; a future PR can specialise to 8-byte units
        when the source is known aligned)
      if L % 32 != 0:
        zero-pad bytes [L .. ceil(L/32) * 32) of dst
      return ceil(L / 32) in a0

  ## Why a separate file

  Pack-bytes is the only SSZ machinery that *writes* chunks
  rather than *consumes* them. Splitting it from
  `Merkleize{Full}` keeps each module's proof obligation
  focused: pack proves a memory-layout postcondition (chunks
  are byte-identical to source plus zero-padding), merkleize
  proves a hashing postcondition (root matches the recursive
  SHA-256 spec). Composing them lets the eventual proof of
  `hash_tree_root(Bytes)` follow as a one-line composition.

  ## PR-S8 status

  Defines the contract; executable lives where it's inlined
  (PR-S8's `zisk_ssz_pack_bytes` probe BuildUnit). PR-S9
  composes pack + merkleize into a single `hash_tree_root_bytes`
  entry point.
-/

module

public section
namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Maximum byte length supported by `ssz_pack_bytes`.
    `sszPackBytesMaxLen = sszMerkleizeMaxChunks * 32 = 1024`
    so the output stays within the merkleize chunk cap. -/
def sszPackBytesMaxLen : Nat := 1024

end EvmAsm.Stateless.SSZ.HashTreeRoot
