/-
  EvmAsm.Codegen.Programs.EvmAccountWitness

  Runtime dispatcher account-witness handlers for EXTCODESIZE and EXTCODEHASH.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.RuntimeSameBlockCode

namespace EvmAsm.Codegen

/-! ## Runtime account-witness opcodes

    EXTCODEHASH (0x3f) now reads the account trie through the optional
    runtime account-witness context populated by `pack-bytecode.py` and
    `emitRuntimeDispatcherSetup`. If no witness context is present, it keeps
    the old deterministic zero behavior. -/

/-- Copy an EVM stack address word into natural 20-byte address order.

    Stack bytes 0..19 hold the low 160-bit address little-endian; trie lookup
    helpers expect the big-endian byte string whose keccak selects the account
    path. `x12` is the EVM stack pointer and `t1` points at
    `eahsr_address_scratch`. -/
private def extcodehashWitnessAddressCopy : String :=
  String.intercalate "" <|
    (List.range 20).map fun i =>
      s!"  lbu t2, {19 - i}(x12)\n  sb t2, {i}(t1)\n"

/-- Raw dispatcher handler for EXTCODEHASH backed by
    `extcodehash_at_header_state_root`.

    The EVM stack word stores the low 160-bit address little-endian; the
    helper expects the natural 20-byte address order used for
    `keccak(address)`, so the handler first reverses bytes 0..19 into
    `eahsr_address_scratch`. Net stack delta is zero: the address word is
    overwritten with the 32-byte EIP-1052 result. -/
private def extcodehashWitnessTail : HandlerTail :=
  .custom <|
    "  la t1, eahsr_address_scratch\n" ++
    extcodehashWitnessAddressCopy ++
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp)\n" ++
    "  sd x12, 8(sp)\n" ++
    "  sd x21, 16(sp)\n" ++
    "  sd x13, 24(sp)\n" ++
    "  la a0, eahsr_address_scratch\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_charge\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp)\n" ++
    "  sd x12, 8(sp)\n" ++
    "  sd x21, 16(sp)\n" ++
    "  sd x13, 24(sp)\n" ++
    "  la a0, eahsr_address_scratch\n" ++
    "  jal ra, runtime_same_block_delegation_code\n" ++
    "  bnez a0, .Lextcodehash_after_same_block\n" ++
    "  la t0, rsbd_code_ptr; ld a0, 0(t0)\n" ++
    "  la t0, rsbd_code_len; ld a1, 0(t0)\n" ++
    "  la a2, rsbd_hash\n" ++
    "  jal ra, zkvm_keccak256\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  la t0, rsbd_hash; addi t0, t0, 31; mv t1, x12; li t2, 32\n" ++
    ".Lextcodehash_same_block_rev:\n" ++
    "  beqz t2, .Lextcodehash_same_block_rev_done\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lextcodehash_same_block_rev\n" ++
    ".Lextcodehash_same_block_rev_done:\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    ".Lextcodehash_after_same_block:\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  ld t0, 584(x20)\n" ++          -- header length; zero means no witness context
    "  beqz t0, .Lextcodehash_no_context\n" ++
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp)\n" ++
    "  sd x12, 8(sp)\n" ++
    "  sd x21, 16(sp)\n" ++
    "  sd x13, 24(sp)\n" ++
    "  ld a0, 576(x20)\n" ++         -- header ptr
    "  ld a1, 584(x20)\n" ++         -- header len
    "  la a2, eahsr_address_scratch\n" ++
    "  ld a3, 592(x20)\n" ++         -- witness.state ptr
    "  ld a4, 600(x20)\n" ++         -- witness.state len
    "  ld a5, 8(sp)\n" ++            -- saved EVM stack ptr; a2 aliases x12
    "  jal ra, extcodehash_at_header_state_root\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    ".Lextcodehash_no_context:\n" ++
    "  sd zero, 0(x12)\n" ++
    "  sd zero, 8(x12)\n" ++
    "  sd zero, 16(x12)\n" ++
    "  sd zero, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop"

/-- Raw dispatcher handler for EXTCODESIZE backed by
    `extcodesize_at_header_state_root`.

    Net stack delta is zero: the input address word is overwritten with the
    u64 code length, zero-extended across the 256-bit EVM stack word. -/
private def extcodesizeWitnessTail : HandlerTail :=
  .custom <|
    "  la t1, eahsr_address_scratch\n" ++
    extcodehashWitnessAddressCopy ++
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp)\n" ++
    "  sd x12, 8(sp)\n" ++
    "  sd x21, 16(sp)\n" ++
    "  sd x13, 24(sp)\n" ++
    "  la a0, eahsr_address_scratch\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_charge\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp)\n" ++
    "  sd x12, 8(sp)\n" ++
    "  sd x21, 16(sp)\n" ++
    "  sd x13, 24(sp)\n" ++
    "  la a0, eahsr_address_scratch\n" ++
    "  jal ra, runtime_same_block_delegation_code\n" ++
    "  bnez a0, .Lextcodesize_after_same_block\n" ++
    "  la t0, rsbd_code_len; ld t1, 0(t0)\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  sd t1, 0(x12)\n" ++
    "  sd zero, 8(x12)\n" ++
    "  sd zero, 16(x12)\n" ++
    "  sd zero, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    ".Lextcodesize_after_same_block:\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  ld t0, 584(x20)\n" ++
    "  beqz t0, .Lextcodesize_no_context\n" ++
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp)\n" ++
    "  sd x12, 8(sp)\n" ++
    "  sd x21, 16(sp)\n" ++
    "  sd x13, 24(sp)\n" ++
    "  ld a0, 576(x20)\n" ++         -- header ptr
    "  ld a1, 584(x20)\n" ++         -- header len
    "  la a2, eahsr_address_scratch\n" ++
    "  ld a3, 592(x20)\n" ++         -- witness.state ptr
    "  ld a4, 600(x20)\n" ++         -- witness.state len
    "  ld a5, 608(x20)\n" ++         -- witness.codes ptr
    "  ld a6, 616(x20)\n" ++         -- witness.codes len
    "  jal ra, extcodesize_at_header_state_root\n" ++
    "  la t0, ecsahsr_code_len\n" ++
    "  ld t1, 0(t0)\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  sd t1, 0(x12)\n" ++
    "  sd zero, 8(x12)\n" ++
    "  sd zero, 16(x12)\n" ++
    "  sd zero, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    ".Lextcodesize_no_context:\n" ++
    "  sd zero, 0(x12)\n" ++
    "  sd zero, 8(x12)\n" ++
    "  sd zero, 16(x12)\n" ++
    "  sd zero, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop"

def accountWitnessHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_EXTCODESIZE"
    , opcodes := [0x3b]
    , preBody := stackUnderflowGuardAsm 1
    , body := []
    , tail := extcodesizeWitnessTail }
  , { label := "h_EXTCODEHASH"
    , opcodes := [0x3f]
    , preBody := stackUnderflowGuardAsm 1
    , body := []
    , tail := extcodehashWitnessTail } ]

end EvmAsm.Codegen
