/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.ListByteList

  SSZ `hash_tree_root(List[ByteList[B], M])` for variable-length
  lists of variable-length byte strings.

  The amsterdam witness type `witness.headers` is exactly this
  shape: `List[ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS]`
  with `MAX_BYTES_PER_HEADER = 1024`, `MAX_WITNESS_HEADERS = 256`.

  ## SSZ algorithm

  For a list value `v : List[ByteList[B], M]`:

    1. For each element `e` in `v`:
         child_root[i] = hash_tree_root(ByteList[B](e))
       That is, recursively SSZ-hash each element as a ByteList.
    2. partial = merkleize(child_root[0..N], ceil(log2(M)))
       where `N = len(v)` and capacity is M slots.
    3. length_chunk = u256_le(N)
    4. root = sha256(partial ‖ length_chunk)

  The recursion (step 1) uses `ssz_hash_tree_root_bytes`
  (PR-S9). The mix-in (steps 2–4) is identical to the byte-list
  case (PR-S9), differing only in what gets mixed in as the
  length (element count, not byte count).

  ## Input encoding

  The function reads the SSZ-encoded `List[ByteList[B], M]`
  *section* directly. SSZ encoding of a list of variable-size
  elements is:

      bytes  0 .. 4N        : N u32 LE inner offsets (one per element)
      bytes  4N .. section_end : element bytes, concatenated

  The k-th inner offset is the byte position (from the section's
  start) where element k begins. The 0-th offset always equals
  `4 * N`, so the element count can be derived as
  `N = offset_0 / 4` when the section is non-empty.

  An empty section (`section_len = 0`) represents `N = 0`.

  ## Contract

  Caller convention:

      a0 (input)  : pointer to the SSZ list section (read-only)
      a1 (input)  : section_len in bytes (0 = empty list)
      a2 (input)  : per-element ByteList byte_limit_log2_chunks
                    (0 ≤ ≤ 31; byte capacity = 32 * 2^a2)
      a3 (input)  : list capacity count_limit_log2
                    (0 ≤ ≤ 31; element capacity = 2^a3)
      a4 (input)  : 32-byte output ptr
      ra (input)  : return

      a0 (output) : ZKVM_EOK (0) on success
      32 bytes at *a4 : SSZ root

  ## Caps for PR-S11

  Element count `N` ≤ 32 (matches `sszMerkleizeMaxChunks`). The
  amsterdam `witness.headers` schema allows up to 256, but
  every test fixture this repo has stays well below 32; a
  follow-up PR can lift the cap by growing the merkleize
  scratch buffer.

  ## Implementation shape

  `sszHashTreeRootListByteListFunction` emits the labelled
  function `ssz_hash_tree_root_list_bytelist:`. Internally:
    1. If section empty: take the N = 0 short-circuit
       (root = sha256(Z_{count_log2} ‖ 0_chunk)).
    2. Else: read offset_0, derive N. For each element i in 0..N,
       compute offset bounds and call
       `ssz_hash_tree_root_bytes(el_i_bytes, el_i_len,
        byte_log2, &child_roots[i])`.
    3. Call `ssz_merkleize(child_roots, N, count_log2,
        partial)`.
    4. Build (partial ‖ u256_le(N)) and call `zkvm_sha256`
       to produce the final root.

  Two new scratch buffers in `.data`:
    ssz_ltb_child_roots : 1024 B (32 × 32-byte child roots)
    ssz_ltb_partial     : 32 B   (merkleize output)
    ssz_ltb_mix         : 64 B   (partial ‖ length buffer)

  ## PR-S11 status

  Defines the contract. The executable lives where it's
  inlined (PR-S11's `stateless_guest` epilogue is the first
  consumer; the dedicated probe `zisk_ssz_hash_tree_root_list_bytelist`
  is the standalone smoke test).
-/

module

public section
namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Maximum element count supported by
    `ssz_hash_tree_root_list_bytelist`. PR-S11 ships at 32;
    matches the inner `sszMerkleizeMaxChunks` cap. -/
def sszListByteListMaxElems : Nat := 32

end EvmAsm.Stateless.SSZ.HashTreeRoot
