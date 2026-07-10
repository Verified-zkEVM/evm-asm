/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.ZeroHashes

  Pre-computed SSZ zero-hashes table Z_0..Z_31 in `.rodata`.

  ## Definition

  The SSZ merkleization "zero hashes" are the per-depth hashes of
  all-zero subtrees:

      Z_0 = 0x00..00      (32 bytes, the zero leaf)
      Z_i = sha256(Z_{i-1} ‖ Z_{i-1})

  These show up everywhere SSZ merkleizes a variable-length list
  with capacity > population: missing leaves are treated as Z_0,
  and any subtree of all-zero leaves at depth `d` hashes to Z_d.
  Pre-computing the table once at codegen time means the
  merkleize loop (PR-S6) can skip recursing into all-zero
  subtrees -- a substantial constant-factor win for the typical
  case where most SSZ "List"-shaped fields are short relative to
  their declared `Limit`.

  See the SSZ spec at
  https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md#merkleization
  The pinned execution-specs tree does not expose a fork-local helper for this
  table; the construction above is the SSZ merkleization rule.  See the
  consensus-specs reference linked above.

  ## Layout

  Emitted as a single 1024-byte `.rodata` block under the label
  `ssz_zero_hashes`. Entry `i` lives at byte offset `i * 32`:

      ssz_zero_hashes + 0   : Z_0  (32 zero bytes)
      ssz_zero_hashes + 32  : Z_1  (sha256(0x00 * 64))
      ssz_zero_hashes + 64  : Z_2  (sha256(Z_1 ‖ Z_1))
      ...
      ssz_zero_hashes + 992 : Z_31 (depth-31 zero subtree)

  Depth 32 covers SSZ "Limit" values up to 2^32 = 4 billion -- in
  practice the largest SSZ types Amsterdam touches (e.g.
  `List[Bytes, 2**32]`) cap out well before that, so 32 entries
  suffice. The full Beacon Chain SSZ uses depth 41 (per
  consensus-specs), which the same emission scheme trivially
  extends to if a Beacon-Chain consumer shows up.

  ## Values

  Computed once with Python:

      import hashlib
      z = [b"\\x00" * 32]
      for _ in range(31):
          z.append(hashlib.sha256(z[-1] + z[-1]).digest())

  Output `z[1]` matches PR-S4's `Z_1` test fixture:
  `f5a5fd42..fb4b`. Pinning the full table here serves as both
  a precomputed constant and a regression check on the SHA-256
  intrinsic / wrapper (any future SHA-256 layout regression
  surfaces by mismatching Z_i for some i).

  ## Contract

  Caller convention (lookup-only):

      a0 (input)  : depth index i in 0..32 (u64; only low byte
                    consulted by `ssz_zero_hashes_lookup` -- the
                    asm shim PR-S6 lands -- but the spec is
                    i < 32 and behaviour on i >= 32 is undefined)
      a1 (input)  : pointer to 32-byte output buffer

      32 bytes at *a1  : Z_i

  Asm shim landing in PR-S6 alongside the merkleize loop.

  ## PR-S5 status

  Documents the layout. The table itself is emitted by
  `EvmAsm.Codegen.Programs.sszZeroHashesDataSection` and exercised
  by the `zisk_ssz_zero_hashes` probe BuildUnit (which reads
  depth `i` from host input and writes Z_i to OUTPUT). PR-S6
  reuses the same `ssz_zero_hashes` symbol from the merkleize
  routine without re-emitting it.
-/

namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Number of pre-computed SSZ zero hashes. Covers SSZ List/
    Vector capacities up to `2^32`. -/
def sszZeroHashesDepth : Nat := 32

end EvmAsm.Stateless.SSZ.HashTreeRoot
