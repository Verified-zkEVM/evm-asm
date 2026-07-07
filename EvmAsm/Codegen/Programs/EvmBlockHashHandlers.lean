/-
  EvmAsm.Codegen.Programs.EvmBlockHashHandlers

  Dispatcher handler for BLOCKHASH.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.BlockHash.Program

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
      -- The link-time `la` stays in preBody glue and seeds `tableBaseReg =
      -- x18` for the verified body (the BLOBHASH/CALLDATALOAD precedent).
      -- The body is the verified `evm_blockhash` program
      -- (`BlockHash/Spec.lean`): three high-limb guards, target ≥ cur and
      -- age > count guards route to a zero push; a valid target copies
      -- `evm_block_hashes[count - (cur - target)]` onto the stack top.
    , preBody := stackUnderflowGuardAsm 1 ++ "\n" ++
                 "  la x18, evm_block_hashes"
    , body := EvmAsm.Evm64.BlockHash.evm_blockhash .x20 .x18 .x14 .x16 .x19
    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
