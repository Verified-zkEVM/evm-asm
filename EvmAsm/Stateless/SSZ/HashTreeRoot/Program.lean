/-
  EvmAsm.Stateless.SSZ.HashTreeRoot.Program

  SSZ merkleization primitive: `sha256_pair(L, R) = sha256(L ‖ R)`.

  This is the only hash the SSZ `hash_tree_root` machinery needs --
  every higher-level operation (leaf, mix_in_length, list/vector
  packing, Container hashing) reduces to a tree of pair-hashes
  over 32-byte chunks. See
  `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  / `_serialize.py` and the SSZ spec at
  https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md
  for the full reduction.

  ## Why this lives behind a thin shim

  `zkvm_sha256(data, len, output)` already accepts arbitrary
  length, so the underlying call for `sha256_pair` is exactly:

      zkvm_sha256(buf, 64, out)

  where `buf` holds `L ‖ R` (32 bytes followed by 32 bytes). The
  shim's job is to document the convention in one place so:

    * the proof for `compute_new_payload_request_root` can attach
      a CPS triple to a single named entry point (mirrors the role
      of `Stateless.Headers.BlockHash.blockHashCallAsm` for the
      keccak side -- PR-K13 / #5276),
    * higher-level merkleization code (PR-S5+) can call
      `ssz_pair_hash` by symbol instead of inlining the 64-byte
      buffer dance every time.

  ## Contract

  Caller convention (mirrors zkvm-standards plus a fixed 64-byte
  buffer pointer):

      a0 (input)  : pointer to a contiguous 64-byte buffer
                    holding `L ‖ R` (L = bytes 0..32, R = 32..64)
      a1 (input)  : 64 (the constant length)
      a2 (input)  : pointer to a 32-byte output buffer
      ra (input)  : return address (caller sets)

      a0 (output) : ZKVM_EOK (0) on success
      32 bytes at *a2  : sha256(L ‖ R)

  Side effects identical to `zkvm_sha256`: clobbers `t0..t6`,
  `a0..a2`, `ra`; uses callee-saved registers via the called
  function's own stack frame; requires `sp` to point at usable
  RAM.

  ## Implementation shape

  `sszPairHashCallAsm` is a 2-instruction asm snippet -- set
  `a1 = 64`, then `jal ra, zkvm_sha256` -- delegating to the
  Merkle-Damgaard wrapper landed in PR-S2 (#5290 -- the
  `zkvm_sha256` symbol emitted by
  `EvmAsm.Codegen.Programs.zkvmSha256Function`).

  Embedding the function definition is the caller's
  responsibility: a BuildUnit that uses `ssz_pair_hash` must
  inline `zkvmSha256Function` once in its prologue or epilogue,
  guarded by a skip-jump so `_start` fall-through misses it. Same
  pattern as `statelessGuestUnit` for keccak.

  ## Future SSZ work that hangs off this shim

  Once landed:
    * PR-S5 adds `ssz_zero_hashes` -- precomputed Z_0..Z_31
      table in `.rodata` (Z_i = sha256_pair(Z_{i-1}, Z_{i-1})),
      so list/vector padding doesn't recompute zero subtrees.
    * PR-S6 adds the merkleize() routine: pairwise-hash a length-N
      list of 32-byte chunks down to a single root.
    * PR-S7 adds mix_in_length / mix_in_selector for variable-size
      SSZ types.
    * PR-S8 wires the real `compute_new_payload_request_root` and
      stamps it into `OUTPUT_ADDR[0..32]`, replacing the keccak
      stub that PR-K5/K7 wired in.

  ## PR-S4 status

  Defines the asm shim only. The actual `ssz_pair_hash`
  *executable* lives where its caller wants it inlined -- in
  PR-S4 that's the `zisk_ssz_pair_hash` probe BuildUnit (which
  inlines `zkvmSha256Function`).
-/

module

@[expose] public section
namespace EvmAsm.Stateless.SSZ.HashTreeRoot

/-- Asm shim for SSZ `sha256_pair(L, R)` -- sets `a1 = 64`, then
    delegates to the parameterised `zkvm_sha256` function defined
    in `EvmAsm/Codegen/Programs.lean` (PR-S2). The caller's
    BuildUnit must inline `zkvmSha256Function` once for the
    symbol to resolve at link time.

    Calling convention:
    * `a0` (input)  : pointer to 64-byte buffer (L ‖ R)
    * `a2` (input)  : pointer to 32-byte output buffer
    * `ra` (input)  : return address (caller sets)
    * `a0` (output) : `ZKVM_EOK` (0) on success
    * 32 bytes at the output pointer hold `sha256(L ‖ R)`.

    The shim writes `64` into `a1` so callers don't have to (and
    cannot accidentally pass a non-64 length: the SSZ merkleize
    invariant pins it). -/
def sszPairHashCallAsm : String :=
  "  # Stateless.SSZ.HashTreeRoot.sszPairHashCallAsm\n" ++
  "  # Calls zkvm_sha256(a0=64-byte buf, a1=64, a2=output).\n" ++
  "  # On return: a0 = ZKVM_EOK (0); 32 bytes at *a2 hold\n" ++
  "  #            sha256(bytes[a0..a0+64)).\n" ++
  "  li a1, 64\n" ++
  "  jal ra, zkvm_sha256"

end EvmAsm.Stateless.SSZ.HashTreeRoot
