/-
  EvmAsm.Codegen.Programs.EvmExtcodecopy

  Runtime dispatcher EXTCODECOPY handler backed by account-witness code bytes.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.RuntimeSameBlockCode

namespace EvmAsm.Codegen

/-! ## Runtime EXTCODECOPY witness opcode

    EXTCODECOPY (0x3c) reads account code bytes through the optional runtime
    account-witness context and writes directly into `evm_memory`. -/

/-- Copy an EVM stack address word into natural 20-byte address order.

    Stack bytes 0..19 hold the low 160-bit address little-endian; trie lookup
    helpers expect the big-endian byte string whose keccak selects the account
    path. `x12` is the EVM stack pointer and `t1` points at
    `ecc_address_scratch`. -/
private def extcodecopyWitnessAddressCopy : String :=
  String.intercalate "" <|
    (List.range 20).map fun i =>
      s!"  lbu t2, {19 - i}(x12)
  sb t2, {i}(t1)
"

/-- Raw dispatcher handler for EXTCODECOPY backed by
    `extcodecopy_at_header_state_root`.

    Stack contract from execution-specs Amsterdam `extcodecopy`:
      top word     : address
      second word  : memory_start_index
      third word   : code_start_index
      fourth word  : size

    The prelude charges the copy word gas plus destination memory expansion
    before mutation, matching execution-specs `extcodecopy`. The helper writes
    `size` bytes into `evm_memory + memory_start_index`, zero-padding
    missing/empty/past-end cases. This handler ignores helper status after the
    call because the helper pre-zeroes the requested output window before
    trie/code lookup. -/
private def extcodecopyWitnessTail : HandlerTail :=
  .custom <|
    "  ld x14, 32(x12)
" ++         -- memory_start_index
    "  ld x15, 96(x12)
" ++         -- size
    -- eccob.1: both EXTCODECOPY copy paths consume only the low 64-bit code offset.
    -- If any high limb is nonzero, or the low limb is at/above the deployed-code cap,
    -- normalize to 32768 so the existing zero-padded copy loops cannot wrap the source index.
    "  ld x16, 64(x12)
" ++
    "  ld x17, 72(x12)
  ld x18, 80(x12)
  or x17, x17, x18
" ++
    "  ld x18, 88(x12)
  or x17, x17, x18
" ++
    "  bnez x17, .Lrt_ecc_oob_offset
" ++
    "  li x18, 32768
  bltu x16, x18, .Lrt_ecc_offset_ok
" ++
    ".Lrt_ecc_oob_offset:
" ++
    "  li x18, 32768
  sd x18, 64(x12)
" ++
    ".Lrt_ecc_offset_ok:
" ++
    memDynamicArenaOogGuardAsm "extcodecopy" "x14" "x15" "x16" "x17" ++
    "  ld x5, " ++ toString activeMemorySizeOff ++ "(x20)
" ++
    "  la x6, ecc_old_active; sd x5, 0(x6)
" ++
    "  addi sp, sp, -8
" ++
    "  sd x5, 0(sp)
" ++
    copyWordGasAsm "extcodecopy" "x15" "x16" "x17" "x18" ++
    updateActiveMemorySizeAsm "extcodecopy" "x14" "x15" "x16" "x17" "x18" "x6" true ++
    "  ld x5, 0(sp)
" ++
    "  addi sp, sp, 8
" ++
    "  ld x6, " ++ toString activeMemorySizeOff ++ "(x20)
" ++
    "  add x7, x13, x5
" ++
    "  add x8, x13, x6
" ++
    ".Lrt_ecc_zero_new_mem:
" ++
    "  bgeu x7, x8, .Lrt_ecc_zero_new_done
" ++
    "  sb zero, 0(x7)
" ++
    "  addi x7, x7, 1
" ++
    "  j .Lrt_ecc_zero_new_mem
" ++
    ".Lrt_ecc_zero_new_done:
" ++
    "  add x19, x13, x14
" ++       -- output ptr = evm_memory + memory_start
    "  la t1, ecc_address_scratch
" ++
    extcodecopyWitnessAddressCopy ++
    "  addi sp, sp, -32
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x13, 16(sp)
" ++
    "  sd x21, 24(sp)
" ++
    "  la a0, ecc_address_scratch
" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "
" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "
" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "
" ++
    "  jal ra, runtime_access_account_charge
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  ld x21, 24(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  ld t0, 568(x20)
" ++
    "  li t1, 100
" ++
    "  bltu t0, t1, .exit_outofgas
" ++
    "  sub t0, t0, t1
" ++
    "  sd t0, 568(x20)
" ++
    "  ld x14, 32(x12)
" ++
    "  ld t0, 568(x20)
" ++
    "  li t1, 100
" ++
    "  bltu t0, t1, .exit_outofgas
" ++
    "  sub t0, t0, t1
" ++
    "  sd t0, 568(x20)
" ++

    "  ld x15, 96(x12)
" ++
    "  add x19, x13, x14
" ++
    "  addi sp, sp, -64
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x13, 16(sp)
" ++
    "  sd x14, 24(sp)
" ++
    "  sd x15, 32(sp)
" ++
    "  sd x19, 40(sp)
" ++
    "  sd x21, 48(sp)
" ++
    "  la a0, ecc_address_scratch
" ++
    "  jal ra, runtime_same_block_delegation_code
" ++
    "  bnez a0, .Lrt_ecc_after_same_block
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  ld x14, 24(sp)
" ++
    "  ld x15, 32(sp)
" ++
    "  ld x19, 40(sp)
" ++
    "  ld x21, 48(sp)
" ++
    "  addi sp, sp, 64
" ++
    "  la t0, rsbd_code_ptr; ld t1, 0(t0)
" ++
    "  la t0, rsbd_code_len; ld t2, 0(t0)
" ++
    "  ld t3, 64(x12)
" ++
    "  li t4, 0
" ++
    ".Lrt_ecc_same_loop:
" ++
    "  beq t4, x15, .Lrt_ecc_same_done
" ++
    "  add t5, t3, t4
" ++
    "  bgeu t5, t2, .Lrt_ecc_same_zero
" ++
    "  add t6, t1, t5; lbu t6, 0(t6)
" ++
    "  j .Lrt_ecc_same_store
" ++
    ".Lrt_ecc_same_zero:
" ++
    "  li t6, 0
" ++
    ".Lrt_ecc_same_store:
" ++
    "  add t0, x19, t4; sb t6, 0(t0)
" ++
    "  addi t4, t4, 1; j .Lrt_ecc_same_loop
" ++
    ".Lrt_ecc_same_done:
" ++
    "  la t0, ecc_same_block_hit; li t1, 1; sd t1, 0(t0)
" ++
    "  add t0, x14, x15
" ++
    "  la t1, ecc_old_active; ld t1, 0(t1)
" ++
    "  bgeu t0, t1, .Lrt_ecc_tail_start_ok
" ++
    "  mv t0, t1
" ++
    ".Lrt_ecc_tail_start_ok:
" ++
    "  ld t2, " ++ toString activeMemorySizeOff ++ "(x20)
" ++
    ".Lrt_ecc_tail_zero_loop:
" ++
    "  bgeu t0, t2, .Lrt_ecc_tail_zero_done
" ++
    "  add t3, x13, t0; sb zero, 0(t3)
" ++
    "  addi t0, t0, 1
" ++
    "  j .Lrt_ecc_tail_zero_loop
" ++
    ".Lrt_ecc_tail_zero_done:
" ++
    "  addi x12, x12, 128
" ++
    "  addi x10, x10, 1
" ++
    dispatchContinueRet ++ "\n" ++
    ".Lrt_ecc_after_same_block:
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  ld x14, 24(sp)
" ++
    "  ld x15, 32(sp)
" ++
    "  ld x19, 40(sp)
" ++
    "  ld x21, 48(sp)
" ++
    "  addi sp, sp, 64
" ++
    -- A same-transaction CREATE deposit is not visible in the header-state code
    -- witness. The CREATE return path records deployed bytes in
    -- exec_code_effect_log, so EXTCODECOPY must consult that current-code overlay
    -- before falling back to the pre-block trie helper.
    "  addi sp, sp, -64
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x13, 16(sp)
" ++
    "  sd x14, 24(sp)
" ++
    "  sd x15, 32(sp)
" ++
    "  sd x19, 40(sp)
" ++
    "  sd x21, 48(sp)
" ++
    "  la a0, exec_code_effect_log
" ++
    "  la t0, exec_code_effect_count; ld a1, 0(t0)
" ++
    "  la a2, ecc_address_scratch
" ++
    "  jal ra, find_code_effect_by_address
" ++
    "  mv t0, a0
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  ld x14, 24(sp)
" ++
    "  ld x15, 32(sp)
" ++
    "  ld x19, 40(sp)
" ++
    "  ld x21, 48(sp)
" ++
    "  addi sp, sp, 64
" ++
    "  beqz t0, .Lrt_ecc_no_create_effect
" ++
    "  addi t1, t0, 48
" ++
    "  ld t2, 40(t0)
" ++
    "  ld t3, 64(x12)
" ++
    "  li t4, 0
" ++
    "  j .Lrt_ecc_same_loop
" ++
    ".Lrt_ecc_no_create_effect:
" ++
    "  ld t0, 608(x20)
" ++         -- witness.codes ptr
    "  la t1, eccp_codes_ptr
" ++
    "  sd t0, 0(t1)
" ++
    "  ld t0, 616(x20)
" ++         -- witness.codes len
    "  la t1, eccp_codes_len
" ++
    "  sd t0, 0(t1)
" ++
    "  addi sp, sp, -32
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x13, 16(sp)
" ++
    "  sd x21, 24(sp)
" ++
    "  ld a0, 576(x20)
" ++         -- header ptr
    "  ld a1, 584(x20)
" ++         -- header len; zero means no witness context
    "  beqz a1, .Lrt_ecc_no_context
" ++
    "  ld a3, 64(x12)
" ++          -- code_start_index
    "  la a2, ecc_address_scratch
" ++
    "  mv a4, x15
" ++              -- size
    "  mv a5, x19
" ++              -- output buffer
    "  ld a6, 592(x20)
" ++         -- witness.state ptr
    "  ld a7, 600(x20)
" ++         -- witness.state len
    "  jal ra, extcodecopy_at_header_state_root
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  ld x21, 24(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  addi x12, x12, 128
" ++
    "  addi x10, x10, 1
" ++
    dispatchContinueRet ++ "\n" ++
    ".Lrt_ecc_no_context:
" ++
    "  mv t0, x19
" ++
    "  mv t1, x15
" ++
    ".Lrt_ecc_zero_loop:
" ++
    "  beqz t1, .Lrt_ecc_zero_done
" ++
    "  sb zero, 0(t0)
" ++
    "  addi t0, t0, 1
" ++
    "  addi t1, t1, -1
" ++
    "  j .Lrt_ecc_zero_loop
" ++
    ".Lrt_ecc_zero_done:
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x13, 16(sp)
" ++
    "  ld x21, 24(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  addi x12, x12, 128
" ++
    "  addi x10, x10, 1
" ++
    dispatchContinueRet

def extcodecopyWitnessHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_EXTCODECOPY"
    , opcodes := [0x3c]
    , preBody := stackUnderflowGuardAsm 4
    , body := []
    , tail := extcodecopyWitnessTail } ]

end EvmAsm.Codegen
