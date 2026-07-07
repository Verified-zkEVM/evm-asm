/-
  EvmAsm.Codegen.Programs.EvmBlobContextHandlers

  Dispatcher handlers for blob context opcodes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.BlobBaseFee.Program
import EvmAsm.Evm64.BlobHash.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## M28 blob-context opcodes

  `BLOBBASEFEE` (0x4a) is an Amsterdam/Cancun context opcode. The
  executable spec computes it as `calculate_blob_gas_price(block_env.excess_blob_gas)`;
  this runtime dispatcher receives that already-computed 256-bit word in the
  `pack-bytecode.py --blob-base-fee` input trailer and copies it to `evm_env+512`.

  `BLOBHASH` (0x49) reads `tx_env.blob_versioned_hashes[index]` from the
  bounded `evm_blob_hashes` table. The runtime prologue copies up to 16
  entries from `pack-bytecode.py --blob-hashes` and stores the copied count at
  `evm_env+544`; indexes outside that count, or indexes with nonzero high
  limbs, push zero per execution-specs. -/
def blobContextHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_BLOBBASEFEE"
    , opcodes := [0x4a]
    , preBody := stackOverflowGuardAsm
      -- The verified BLOBBASEFEE program (`BlobBaseFee/Spec.lean`), the same
      -- instruction list as the former inline `blobBaseFeeBody`.
    , body := EvmAsm.Evm64.BlobBaseFee.evm_blobbasefee .x20 .x15
    , tail := .advanceAndRet 1 } ]
  ++
  [ { label := "h_BLOBHASH"
    , opcodes := [0x49]
      -- The `la` (link-time symbol resolution) stays in preBody glue and
      -- seeds `tableBaseReg = x15` for the verified body — the CALLDATALOAD
      -- staging precedent. The body is the verified `evm_blobhash` program
      -- (`BlobHash/Spec.lean`): three high-limb guards + a bounds guard vs
      -- the count cell (env+544) route to a zero push; a valid index copies
      -- `evm_blob_hashes[idx]` (32-byte stride) onto the stack top in place.
    , preBody := stackUnderflowGuardAsm 1 ++ "\n" ++
                 "  la x15, evm_blob_hashes"
    , body := EvmAsm.Evm64.BlobHash.evm_blobhash .x20 .x15 .x14 .x16 .x17
    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
