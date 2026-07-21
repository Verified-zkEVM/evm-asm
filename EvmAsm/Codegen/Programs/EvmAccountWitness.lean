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
    "  beqz a0, .Lextcodehash_same_block_code\n" ++
    -- A successful NULL delegation against a previously nonexistent authority
    -- materializes an empty account but need not produce a BAL code_changes
    -- tuple (empty -> empty). execution-specs therefore returns EMPTY_CODE_HASH,
    -- whereas a pre-state-only lookup reports nonexistent and would return 0.
    "  la t0, teer_success_count; ld t1, 0(t0); li t2, 0\n" ++
    ".Lextcodehash_cleared_find_loop:\n" ++
    "  beq t2, t1, .Lextcodehash_after_same_block\n" ++
    "  slli t3, t2, 5; la t4, teer_success_table; add t3, t3, t4\n" ++
    "  la t4, eahsr_address_scratch; mv t5, t3; li t6, 20\n" ++
    ".Lextcodehash_cleared_addr_cmp:\n" ++
    "  beqz t6, .Lextcodehash_cleared_addr_match\n" ++
    "  lbu a0, 0(t4); lbu a1, 0(t5); bne a0, a1, .Lextcodehash_cleared_next\n" ++
    "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lextcodehash_cleared_addr_cmp\n" ++
    ".Lextcodehash_cleared_addr_match:\n" ++
    "  lw t4, 20(t3); bnez t4, .Lextcodehash_cleared_empty\n" ++
    ".Lextcodehash_cleared_next:\n" ++
    "  addi t2, t2, 1; j .Lextcodehash_cleared_find_loop\n" ++
    ".Lextcodehash_cleared_empty:\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x21, 16(sp); ld x13, 24(sp)\n" ++
    "  la t0, eahsr_empty_code_hash; addi t0, t0, 31; mv t1, x12; li t2, 32\n" ++
    ".Lextcodehash_cleared_rev:\n" ++
    "  beqz t2, .Lextcodehash_cleared_done\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lextcodehash_cleared_rev\n" ++
    ".Lextcodehash_cleared_done:\n" ++
    "  addi sp, sp, 32; addi x10, x10, 1\n" ++
    dispatchContinueRet ++ "\n" ++
    ".Lextcodehash_same_block_code:\n" ++
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
    dispatchContinueRet ++ "\n" ++
    ".Lextcodehash_after_same_block:\n" ++
    -- During initcode, ADDRESS denotes the account being created. It exists
    -- for EIP-1052 but has no deployed code yet, so EXTCODEHASH(ADDRESS)
    -- returns EMPTY_CODE_HASH rather than the pre-state witness result.
    "  la t0, evm_call_depth\n  ld t0, 0(t0)\n" ++
    "  la t1, create_frame_flag\n  slli t2, t0, 3\n  add t1, t1, t2\n  ld t1, 0(t1)\n" ++
    "  beqz t1, .Lextcodehash_not_create_self\n" ++
    "  la t0, eahsr_address_scratch\n  addi t1, x20, 19\n  li t2, 20\n" ++
    ".Lextcodehash_create_self_cmp:\n" ++
    "  beqz t2, .Lextcodehash_create_self_empty\n" ++
    "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lextcodehash_not_create_self\n" ++
    "  addi t0, t0, 1; addi t1, t1, -1; addi t2, t2, -1; j .Lextcodehash_create_self_cmp\n" ++
    ".Lextcodehash_create_self_empty:\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  la t0, eahsr_empty_code_hash; addi t0, t0, 31; mv t1, x12; li t2, 32\n" ++
    ".Lextcodehash_create_self_rev:\n" ++
    "  beqz t2, .Lextcodehash_create_self_done\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lextcodehash_create_self_rev\n" ++
    ".Lextcodehash_create_self_done:\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet ++ "\n" ++
    ".Lextcodehash_not_create_self:\n" ++
    -- Check exec_code_effect_log for CREATE'd contract code (extcodehash
    -- after CREATE: the deployed code is in the log but not in the BAL
    -- code_changes or the pre-state witness).
    "  la a0, exec_code_effect_log\n" ++
    "  la t0, exec_code_effect_count; ld a1, 0(t0)\n" ++
    "  la a2, eahsr_address_scratch\n" ++
    "  jal ra, find_code_effect_by_address\n" ++
    "  beqz a0, .Lextcodehash_witness_check\n" ++
    -- Found CREATE'd code: keccak(code) → hash
    "  mv t3, a0\n" ++
    "  ld a1, 40(t3)\n" ++
    "  addi a0, t3, 48\n" ++
    "  la a2, rsbd_hash\n" ++
    "  jal ra, zkvm_keccak256\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    "  la t0, rsbd_hash; addi t0, t0, 31; mv t1, x12; li t2, 32\n" ++
    ".Lextcodehash_create_rev:\n" ++
    "  beqz t2, .Lextcodehash_create_rev_done\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lextcodehash_create_rev\n" ++
    ".Lextcodehash_create_rev_done:\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet ++ "\n" ++
    ".Lextcodehash_witness_check:\n" ++
    "  la t0, eahsr_same_tx_empty_flag; sd zero, 0(t0)\n" ++
    "  la t0, exec_nonstorage_effect_count; ld t2, 0(t0)\n" ++
    "  beqz t2, .Lextcodehash_witness_state\n" ++
    "  la t1, exec_nonstorage_effect_log; li t3, 112; mul t3, t2, t3; add t1, t1, t3\n" ++
    ".Lextcodehash_nse_scan:\n" ++
    "  addi t1, t1, -112\n" ++
    "  la t4, eahsr_address_scratch; li t5, 0\n" ++
    ".Lextcodehash_nse_addr_cmp:\n" ++
    "  li t6, 20; beq t5, t6, .Lextcodehash_nse_match\n" ++
    "  add a0, t1, t5; lbu a0, 0(a0)\n" ++
    "  add a1, t4, t5; lbu a1, 0(a1)\n" ++
    "  bne a0, a1, .Lextcodehash_nse_next\n" ++
    "  addi t5, t5, 1; j .Lextcodehash_nse_addr_cmp\n" ++
    ".Lextcodehash_nse_next:\n" ++
    "  addi t2, t2, -1; bnez t2, .Lextcodehash_nse_scan\n" ++
    "  j .Lextcodehash_witness_state\n" ++
    ".Lextcodehash_nse_match:\n" ++
    "  ld t4, 64(t1); ld t5, 72(t1); or t4, t4, t5\n" ++
    "  ld t5, 80(t1); or t4, t4, t5\n" ++
    "  ld t5, 88(t1); or t4, t4, t5\n" ++
    "  ld t5, 104(t1); or t4, t4, t5\n" ++
    "  beqz t4, .Lextcodehash_witness_state\n" ++
    "  li t4, 1; la t5, eahsr_same_tx_empty_flag; sd t4, 0(t5)\n" ++
    -- A same-transaction-created account that SELFDESTRUCTs during its
    -- constructor remains an EIP-1052 empty-code account until transaction
    -- finalization.  Its deletion record deliberately has zero post-balance
    -- and nonce, so the non-storage-effect scan above cannot distinguish it
    -- from a pre-state absence.  The per-transaction destroyed-address table
    -- carries the exact BE address and is rollback-scoped by frame_return.
    -- On overflow, retain the conservative pre-state result.
    ".Lextcodehash_witness_state:\n" ++
    "  la t0, evm_selfdestruct_destroyed_overflow; ld t0, 0(t0); bnez t0, .Lextcodehash_sd_empty_done\n" ++
    "  la t0, evm_selfdestruct_destroyed_count; ld t1, 0(t0); beqz t1, .Lextcodehash_sd_empty_done\n" ++
    "  la t2, evm_selfdestruct_destroyed_table\n" ++
    ".Lextcodehash_sd_empty_scan:\n" ++
    "  mv t3, t2; la t4, eahsr_address_scratch; li t5, 20\n" ++
    ".Lextcodehash_sd_empty_cmp:\n" ++
    "  beqz t5, .Lextcodehash_sd_empty_found\n" ++
    "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lextcodehash_sd_empty_next\n" ++
    "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lextcodehash_sd_empty_cmp\n" ++
    ".Lextcodehash_sd_empty_next:\n" ++
    "  addi t2, t2, 32; addi t1, t1, -1; bnez t1, .Lextcodehash_sd_empty_scan\n" ++
    "  j .Lextcodehash_sd_empty_done\n" ++
    ".Lextcodehash_sd_empty_found:\n" ++
    "  li t0, 1; la t1, eahsr_same_tx_empty_flag; sd t0, 0(t1)\n" ++
    ".Lextcodehash_sd_empty_done:\n" ++
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
    "  la a5, rsbd_hash\n" ++        -- helper writes canonical hash bytes; stack needs word order below
    "  jal ra, extcodehash_at_header_state_root\n" ++
    "  ld x10, 0(sp)\n" ++
    "  ld x12, 8(sp)\n" ++
    "  ld x21, 16(sp)\n" ++
    "  ld x13, 24(sp)\n" ++
    -- If the pre-state witness says the account is absent (EXTCODEHASH = 0),
    -- a precomputed same-transaction balance/nonce effect means the account
    -- now exists with empty code, so EIP-1052 returns EMPTY_CODE_HASH.
    "  la t0, rsbd_hash; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2\n" ++
    "  ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
    "  bnez t1, .Lextcodehash_witness_copy\n" ++
    "  la t0, eahsr_same_tx_empty_flag; ld t0, 0(t0); beqz t0, .Lextcodehash_witness_copy\n" ++
    "  la t0, eahsr_empty_code_hash; la t1, rsbd_hash; li t2, 32\n" ++
    ".Lextcodehash_same_tx_empty_hash:\n" ++
    "  beqz t2, .Lextcodehash_witness_copy\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lextcodehash_same_tx_empty_hash\n" ++
    ".Lextcodehash_witness_copy:\n" ++
    "  la t0, rsbd_hash; addi t0, t0, 31; mv t1, x12; li t2, 32\n" ++
    ".Lextcodehash_witness_rev:\n" ++
    "  beqz t2, .Lextcodehash_witness_rev_done\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lextcodehash_witness_rev\n" ++
    ".Lextcodehash_witness_rev_done:\n" ++
    "  addi sp, sp, 32\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet ++ "\n" ++
    ".Lextcodehash_no_context:\n" ++
    "  sd zero, 0(x12)\n" ++
    "  sd zero, 8(x12)\n" ++
    "  sd zero, 16(x12)\n" ++
    "  sd zero, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet

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
    "  ld t0, 568(x20)\n" ++
    "  li t1, 100\n" ++
    "  bltu t0, t1, .exit_outofgas\n" ++
    "  sub t0, t0, t1\n" ++
    "  sd t0, 568(x20)\n" ++
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
    dispatchContinueRet ++ "\n" ++
    ".Lextcodesize_after_same_block:\n" ++
    -- Check exec_code_effect_log for CREATE'd contract code
    "  la a0, exec_code_effect_log\n" ++
    "  la t0, exec_code_effect_count; ld a1, 0(t0)\n" ++
    "  la a2, eahsr_address_scratch\n" ++
    "  jal ra, find_code_effect_by_address\n" ++
    "  beqz a0, .Lextcodesize_witness_check\n" ++
    -- Found: return code_len
    "  ld t1, 40(a0)\n" ++
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
    dispatchContinueRet ++ "\n" ++
    ".Lextcodesize_witness_check:\n" ++
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
    dispatchContinueRet ++ "\n" ++
    ".Lextcodesize_no_context:\n" ++
    "  sd zero, 0(x12)\n" ++
    "  sd zero, 8(x12)\n" ++
    "  sd zero, 16(x12)\n" ++
    "  sd zero, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet

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
