/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.ExecutionWitness

  SSZ `hash_tree_root` for the amsterdam `ExecutionWitness`
  Container (the SSZ shape that ships inside `SszStatelessInput.
  witness`):

      class SszExecutionWitness(Container):
        state:   List[ByteList[2^10], 2^22]
        codes:   List[ByteList[2^16], 2^18]
        headers: List[ByteList[2^10], 2^8]

  ## SSZ algorithm for a Container

  For a Container with N fields:

    1. field_root[i] = hash_tree_root(field_i)   for i in 0..N
    2. root = merkleize(field_root[0..N], ceil(log2(N)))

  No `mix_in_length` step (Containers have a fixed shape; only
  variable-length List/Bytes types mix in length).

  For `ExecutionWitness` (N = 3 fields):
    root = merkleize([state_root, codes_root, headers_root],
                     ceil(log2(3)) = 2)

  Capacity = 4 slots; the 4th slot is `Z_0` (the zero-leaf root).
  PR-S6 `ssz_merkleize_pow2` handles the pad-to-next-pow2 step;
  PR-S7 `ssz_merkleize` is what we actually call (its log2=2
  matches log2(M=4) so no Z_d mix-in beyond the chunk-padding).

  ## SSZ encoding of a variable-size Container

  A Container with `K` variable-size fields begins with `K`
  u32 LE offsets (one per field). Each offset is the byte
  position from the section's start where that field's body
  begins. The first body byte comes immediately after the
  offset table. Field `i`'s body extends from `offset[i]` to
  `offset[i+1]`, with the last field's body extending to
  `section_end`.

  For `ExecutionWitness` (3 var-size fields, 12-byte offset
  table):

      bytes  0.. 4 : off_state    (= 12 if state is first body byte)
      bytes  4.. 8 : off_codes
      bytes  8..12 : off_headers
      bytes 12..   : concatenated field bodies

  ## Contract

  Caller convention:

      a0 (input)  : witness section ptr (read-only)
      a1 (input)  : section_len in bytes
      a2 (input)  : 32-byte output ptr
      ra (input)  : return

      a0 (output) : ZKVM_EOK (0) on success
      32 bytes at *a2 : SSZ root

  Per-field caps (inherited from `ssz_hash_tree_root_list_bytelist`):

      state.N   ≤ 32   (schema allows up to 2^22)
      codes.N   ≤ 32   (schema allows up to 2^18)
      headers.N ≤ 32   (schema allows up to 256)

  Production-sized witnesses with thousands of state nodes
  exceed these caps; a follow-up PR grows the merkleize
  scratch buffer.

  ## Implementation shape

  `sszHashTreeRootExecutionWitnessFunction` emits
  `ssz_hash_tree_root_execution_witness:`. Reads the three
  u32 offsets, derives per-field section bounds, calls
  `ssz_hash_tree_root_list_bytelist` three times with the
  spec's capacity log2s (state: 5/22, codes: 11/18,
  headers: 5/8), then calls `ssz_merkleize` over the 3 child
  roots with limit_log2 = 2 to produce the Container root.

  One new `.data` scratch:
    ssz_ew_field_roots : 96 B (3 × 32-byte field roots)
-/

namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Field count for the amsterdam `ExecutionWitness` Container.
    Used as the SSZ "capacity" for merkleizing the field roots
    (with limit_log2 = ceil(log2 sszExecutionWitnessFieldCount)). -/
def sszExecutionWitnessFieldCount : Nat := 3

end EvmAsm.Stateless.SSZ.HashTreeRoot
