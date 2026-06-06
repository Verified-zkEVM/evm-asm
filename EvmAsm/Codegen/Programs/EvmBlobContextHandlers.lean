/-
  EvmAsm.Codegen.Programs.EvmBlobContextHandlers

  Dispatcher handlers for blob context opcodes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Dispatch

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
  let blobBaseFeeBody : Program :=
    ADDI .x12 .x12 (-32) ;;
    LD .x15 .x20 (BitVec.ofNat 12 512) ;;
    SD .x12 .x15 0 ;;
    LD .x15 .x20 (BitVec.ofNat 12 520) ;;
    SD .x12 .x15 8 ;;
    LD .x15 .x20 (BitVec.ofNat 12 528) ;;
    SD .x12 .x15 16 ;;
    LD .x15 .x20 (BitVec.ofNat 12 536) ;;
    SD .x12 .x15 24
  [ { label := "h_BLOBBASEFEE"
    , opcodes := [0x4a]
    , body := blobBaseFeeBody
    , tail := .advanceAndRet 1 } ]
  ++
  [ { label := "h_BLOBHASH"
    , opcodes := [0x49]
    , preBody := stackUnderflowGuardAsm 1
    , body := []
    , tail := .custom <|
        "  ld x14, 8(x12)\n" ++          -- high limbs must be zero
        "  bnez x14, .Lblobhash_zero\n" ++
        "  ld x14, 16(x12)\n" ++
        "  bnez x14, .Lblobhash_zero\n" ++
        "  ld x14, 24(x12)\n" ++
        "  bnez x14, .Lblobhash_zero\n" ++
        "  ld x14, 0(x12)\n" ++          -- x14 = low u64 index
        "  ld x15, 544(x20)\n" ++        -- x15 = copied blob_hash_count
        "  bgeu x14, x15, .Lblobhash_zero\n" ++
        "  slli x14, x14, 5\n" ++        -- 32 bytes per versioned hash
        "  la x15, evm_blob_hashes\n" ++
        "  add x15, x15, x14\n" ++
        "  ld x16, 0(x15)\n" ++
        "  sd x16, 0(x12)\n" ++
        "  ld x16, 8(x15)\n" ++
        "  sd x16, 8(x12)\n" ++
        "  ld x16, 16(x15)\n" ++
        "  sd x16, 16(x12)\n" ++
        "  ld x16, 24(x15)\n" ++
        "  sd x16, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret\n" ++
        ".Lblobhash_zero:\n" ++
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

end EvmAsm.Codegen
