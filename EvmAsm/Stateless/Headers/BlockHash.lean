/-
  EvmAsm.Stateless.Headers.BlockHash

  Compute the canonical Ethereum block hash:

      block_hash(header) = keccak256(rlp_encoded_header_bytes)

  ## Contract

  Caller convention (same as the zkvm-standards `zkvm_keccak256`
  C signature):

      a0 : pointer to RLP-encoded header bytes (the data)
      a1 : length in bytes
      a2 : pointer to 32-byte output buffer (the block hash)
      ra : return address
      a0 : on return, ZKVM_EOK (0) on success

  ## Implementation shape

  `blockHashCallAsm` is a 1-instruction asm snippet -- `jal ra,
  zkvm_keccak256` -- that delegates to the parameterised keccak
  wrapper landed in PR-K3 (#5227, merged on main as
  `zkvm_keccak256` symbol emitted by
  `EvmAsm.Codegen.Programs.zkvmKeccak256Function`).

  Embedding the function definition is the caller's
  responsibility: a BuildUnit that calls `block_hash` must
  inline `zkvmKeccak256Function` once in its prologue or
  epilogue, guarded by a skip-jump so `_start` fall-through
  misses it. The pattern is the one already used by
  `statelessGuestUnit` (PR-K5 / #5239) and the keccak probes:

      prologueAsm := setupAsm                                ++
                     Stateless.Headers.BlockHash.blockHashCallAsm ++
                     "\n  j .Ldone\n"                        ++
                     zkvmKeccak256Function                   ++
                     "\n.Ldone:"

  where `setupAsm` lands the data ptr in `a0`, len in `a1`,
  output ptr in `a2`, and sets `sp` to a usable stack frame.

  ## Why this lives in `Stateless/Headers/`

  Block hashing is the first verified step of header validation
  (`Stateless.Headers.Validate.validate_headers`), and the same
  keccak shape appears in tx hashing
  (`Stateless.Transaction.RecoverSender`) and MPT node hashing
  (`Stateless.Witness.NodeDb.Program`). Putting the callable
  here -- rather than duplicating per consumer -- gives the
  Lean proof structure a single point to attach a CPS triple
  ("32 bytes at `a2` are keccak256 of bytes at `a0..a0+a1`")
  that all callers reuse.

  ## PR-K13 status

  Defines the asm shim only. Future PRs:

  - PR-K14: refactor `statelessGuestUnit`'s epilogue to use
            `blockHashCallAsm` instead of inlining `jal ra,
            zkvm_keccak256` directly. Pure refactor; behaviour
            unchanged.
  - Headers.Validate uses `blockHashCallAsm` once per header
    element in the parent_hash chain check.
  - The verified-side `cpsTripleWithin` over `block_hash` lands
    in `Spec.lean` once we compose the existing `KeccakEcallBridge`
    proof with the new asm shim's executable semantics.
-/

module

public section
namespace EvmAsm.Stateless.Headers.BlockHash

/-- Asm shim for `block_hash` -- delegates to the parameterised
    `zkvm_keccak256` function defined in
    `EvmAsm/Codegen/Programs.lean` (PR-K3). The caller's
    BuildUnit must inline `zkvmKeccak256Function` once for the
    symbol to resolve at link time.

    Calling convention:
    * `a0` (input)  : pointer to data
    * `a1` (input)  : length in bytes
    * `a2` (input)  : pointer to 32-byte output buffer
    * `ra` (input)  : return address (caller sets)
    * `a0` (output) : `ZKVM_EOK` (0) on success
    * 32 bytes at the output pointer hold `keccak256(data)`.

    Side effects (besides writing the 32 output bytes):
    * Clobbers `t0..t6`, `a0..a2`, `ra` (per the
      `zkvm_keccak256` function's documented clobber set).
    * Saves and restores `s0..s4` via the called function's
      stack frame; requires `sp` to point at usable RAM. -/
def blockHashCallAsm : String :=
  "  # Stateless.Headers.BlockHash.blockHashCallAsm\n" ++
  "  # Calls zkvm_keccak256(a0=data, a1=len, a2=output).\n" ++
  "  # On return: a0 = ZKVM_EOK (0); 32 bytes at *a2 hold\n" ++
  "  #            keccak256(bytes[a0..a0+a1)).\n" ++
  "  jal ra, zkvm_keccak256"

end EvmAsm.Stateless.Headers.BlockHash
