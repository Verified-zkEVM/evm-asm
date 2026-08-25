/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.HashBytes

  Full SSZ `hash_tree_root(Bytes)` for variable-length byte
  strings. Composes the three building blocks landed in the
  earlier PRs:

  PR-S8 `ssz_pack_bytes`     : bytes → 32-byte chunks
  PR-S7 `ssz_merkleize`      : chunks → partial root (Z_d-padded)
  PR-S2 `zkvm_sha256`        : final mix_in_length(partial, len)

  ## SSZ spec

  For a value `v : Bytes` declared with capacity `B_max` bytes:

      chunks  = pack(v)                       # 32-byte chunks
      partial = merkleize(chunks, ceil(log2(B_max / 32)))
      length_chunk = u256(len(v))             # 32-byte LE u256
      root    = sha256(partial ‖ length_chunk)

  The `length_chunk` step is the SSZ "mix_in_length" operation,
  required for variable-length types (`Bytes`, `List[T, N]`).
  Fixed-length types (`Bytes[N]`, `Vector[T, N]`) skip the
  mix-in.

  ## Contract

  Caller convention:

      a0 (input)  : src bytes ptr
      a1 (input)  : L = byte length (0 ≤ L ≤ 1024)
      a2 (input)  : limit_log2_chunks
                    (chunks-capacity = 2^limit_log2_chunks;
                    `B_max = 32 * 2^limit_log2_chunks`;
                    0 ≤ limit_log2_chunks ≤ 31)
                    Precondition: ceil(L/32) ≤ 2^limit_log2_chunks
      a3 (input)  : 32-byte output ptr
      ra (input)  : return

      a0 (output) : ZKVM_EOK (0) on success
      32 bytes at *a3 : SSZ root = sha256(partial ‖ u256(L))

  ## Implementation shape

  `sszHashTreeRootBytesFunction` emits `ssz_hash_tree_root_bytes:`
  -- a thin wrapper that:
    1. Calls `ssz_pack_bytes` to write chunks into a 1024-byte
       work buffer (`ssz_hb_chunks`).
    2. Calls `ssz_merkleize` with the chunk count and capacity
       to write the partial root into a 32-byte slot
       (`ssz_hb_partial`).
    3. Writes the length as a 32-byte little-endian u256 into
       a second 32-byte slot (`ssz_hb_length`).
    4. Calls `zkvm_sha256` over the 64-byte concatenation
       (`partial ‖ length`) to produce the final root at the
       caller's output ptr.

  Two new `.data` scratches: `ssz_hb_chunks` (1024 B) and
  `ssz_hb_mix` (64 B = partial ‖ length). The merkleize and
  pack-bytes functions use their own scratch buffers internally,
  so no aliasing.

  ## PR-S9 status

  Wraps the existing primitives; no new cryptographic
  operations introduced. PR-S10+ wires this into the stateless
  guest's `compute_new_payload_request_root` (replacing the
  PR-K7 keccak stub in OUTPUT[0..32]).
-/

module

@[expose] public section
namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Maximum byte length the `ssz_hash_tree_root_bytes` function
    can accept. Matches `sszPackBytesMaxLen = 1024`. -/
def sszHashBytesMaxLen : Nat := 1024

end EvmAsm.Stateless.SSZ.HashTreeRoot
