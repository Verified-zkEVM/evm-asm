/-
  EvmAsm.Stateless.Constants

  Well-known Ethereum hash constants the stateless guest references
  in multiple places. Centralising them keeps each value at a
  single source of truth and gives specs a stable name to refer
  to (instead of inline 64-hex-char literals).

  ## Constants exported

  - `keccak256EmptyHashHex` -- `keccak256(b"") =
       c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.
       Used as `EMPTY_CODE_HASH` (accounts with no contract code)
       and as a trivial baseline in `Stateless/Headers/BlockHash`
       tests.
  - `emptyTrieRootHex`      -- `keccak256(rlp_encode_empty_list) =
       56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421`.
       The MPT root of an empty trie. Used as `storage_root` for
       accounts with no storage, and as the initial state root
       in pre-genesis testing.
  - `emptyOmmerHashHex`     -- `keccak256(rlp_encode_empty_list)`
       (same as `emptyTrieRootHex`). Post-merge headers store this
       as the `ommers_hash` constant.

  Each constant is a 64-hex-character `String` because the
  consumers (asm test fixtures, Python harnesses, debug output)
  all consume hex. A `ByteVector 32` form can be added later if
  Lean-side proofs need byte-level reasoning.
-/

namespace EvmAsm.Stateless.Constants

/-! ## Resource-envelope constants

    The stateless guest's finite arenas are derived for this declared
    block-gas envelope.  It is a precondition of the top-level soundness
    statement, not a consensus rule and not a runtime rejection gate. -/

/-- The declared block-gas limit covered by the finite-resource theorem.
    Inputs declaring a larger limit remain outside that theorem's promise. -/
def resourceBlockGasLimit : Nat := 200000000

#guard resourceBlockGasLimit = 200000000

/-- Hex string of `keccak256(b"")`. Same value also doubles as
    `EMPTY_CODE_HASH` (accounts without contract code reference
    this hash; per EIP-161 these accounts get deleted from the
    state trie). -/
def keccak256EmptyHashHex : String :=
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

/-- Hex string of `keccak256(rlp_encode("")) = keccak256(0x80)`
    — keccak of the RLP empty BYTE STRING. The MPT root of an empty trie;
    accounts with no storage have `storage_root = emptyTrieRootHex`. This is
    NOT the post-merge `ommers_hash` constant (that is `emptyOmmerHashHex`
    below, keccak of the RLP empty LIST `0xc0`). -/
def emptyTrieRootHex : String :=
  "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

/-- `EMPTY_OMMER_HASH = keccak256(rlp([]))` — keccak of the RLP empty LIST
    (`0xc0`). Post-merge headers carry this fixed `ommers_hash` value because
    there are no ommer blocks in proof-of-stake. Distinct from
    `emptyTrieRootHex` (keccak of `0x80`); the two were aliased until
    GH #12081. -/
def emptyOmmerHashHex : String :=
  "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

end EvmAsm.Stateless.Constants
