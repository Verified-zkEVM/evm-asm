/-
  EvmAsm.Codegen.Programs.EvmBlockHashHandlers

  Dispatcher handler for BLOCKHASH.
-/

import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

/-- M29 BLOCKHASH handler backed by the runtime block-history trailer.

    Runtime input supplies:
      - `env + 552`: current block number (`cur`, u64)
      - `env + 560`: number of loaded recent hashes (`count`, clamped to 256)
      - `evm_block_hashes`: `count` 32-byte hashes in increasing block-number
        order, matching execution-specs' `block_env.block_hashes`.

    The handler implements Amsterdam `block_hash` behavior for u64 targets:
      - nonzero high limbs in the target word -> zero
      - target >= cur -> zero
      - cur - target > count -> zero
      - otherwise copy `block_hashes[count - (cur - target)]` into the
        popped stack slot.

    Note: env+512..+543 is occupied by BLOBBASEFEE (M28). -/
def blockHashHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_BLOCKHASH"
    , opcodes := [0x40]
    , preBody := stackUnderflowGuardAsm 1
    , body := []
    , tail := .custom <|
        "  ld x14, 8(x12)\n" ++
        "  bnez x14, .Lblockhash_zero\n" ++
        "  ld x14, 16(x12)\n" ++
        "  bnez x14, .Lblockhash_zero\n" ++
        "  ld x14, 24(x12)\n" ++
        "  bnez x14, .Lblockhash_zero\n" ++
        "  ld x14, 0(x12)\n" ++       -- x14 = target block number
        "  ld x15, 552(x20)\n" ++     -- x15 = current block number (env+552)
        "  bgeu x14, x15, .Lblockhash_zero\n" ++
        "  sub x16, x15, x14\n" ++    -- x16 = cur - target, strictly positive
        "  ld x17, 560(x20)\n" ++     -- x17 = loaded hash count (env+560)
        "  bgtu x16, x17, .Lblockhash_zero\n" ++
        "  sub x17, x17, x16\n" ++    -- index = count - age
        "  slli x17, x17, 5\n" ++     -- index * 32
        "  la x18, evm_block_hashes\n" ++
        "  add x18, x18, x17\n" ++
        "  ld x19, 0(x18)\n" ++
        "  sd x19, 0(x12)\n" ++
        "  ld x19, 8(x18)\n" ++
        "  sd x19, 8(x12)\n" ++
        "  ld x19, 16(x18)\n" ++
        "  sd x19, 16(x12)\n" ++
        "  ld x19, 24(x18)\n" ++
        "  sd x19, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret\n" ++
        ".Lblockhash_zero:\n" ++
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

end EvmAsm.Codegen
