/-
  EvmAsm.Codegen.Programs.EvmAccessGas

  Shared runtime account-access gas helper for EIP-2929 warm/cold account
  costs. Consumers pass a bounded 32-byte-stride table of 20-byte canonical
  big-endian addresses. The dispatcher static gas table already charges the
  100-gas warm floor for account opcodes, so this helper charges only the
  2500-gas cold delta and records newly cold addresses.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def runtimeAccessAccountCapacity : Nat := 64
def runtimeAccessAccountRecordSize : Nat := 32
def runtimeAccessColdDeltaGas : Nat := 2500
def runtimeAccessAccountOutcomeCapacity : Nat := 64
def runtimeAccessAccountOutcomeRecordSize : Nat := 64

def runtimeAccessAccountCountLabel : String := "evm_access_account_count"
def runtimeAccessAccountTableLabel : String := "evm_access_account_table"
def runtimeAccessSeedScratchLabel : String := "evm_access_seed_addr"
def runtimeAccessAccountOutcomeCountLabel : String := "evm_access_account_outcome_count"
def runtimeAccessAccountOutcomeTableLabel : String := "evm_access_account_outcomes"

def runtimeAccessAccountOutcomeData : String :=
  ".balign 8\n" ++
  runtimeAccessAccountOutcomeCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountOutcomeTableLabel ++ ":\n" ++
  "  .zero " ++
    toString (runtimeAccessAccountOutcomeCapacity * runtimeAccessAccountOutcomeRecordSize) ++ "\n"

/-! ## runtime_access_account_charge

    Calling convention:
      a0 (input)  : address ptr (20 bytes, canonical BE)
      a1 (input)  : table ptr (capacity * 32 bytes)
      a2 (input)  : count ptr (u64)
      a3 (input)  : capacity (records)
      x20 (input) : runtime env base; gasRemaining is env+568
      a0 (output) : 0 if warm/precompile, 1 if cold and inserted

    Exceptional paths jump to `.exit_outofgas`:
      - cold access when `gasRemaining < 2500`
      - table is full and the target is not already warm

    Active precompiles are always warm and are not inserted. The active set
    mirrors the runtime precompile dispatcher surface: 0x01..0x11 and 0x100. -/
def runtimeAccessAccountChargeFunction : String :=
  "runtime_access_account_charge:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # address ptr\n" ++
  "  mv s1, a1                   # table ptr\n" ++
  "  mv s2, a2                   # count ptr\n" ++
  "  mv s3, a3                   # capacity\n" ++
  "  # Active precompiles are warm: canonical BE address with first 18 bytes zero\n" ++
  "  li t0, 0\n" ++
  ".Lraag_pc_prefix_loop:\n" ++
  "  li t1, 18\n" ++
  "  beq t0, t1, .Lraag_pc_low16\n" ++
  "  add t2, s0, t0\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  bnez t3, .Lraag_scan_table\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lraag_pc_prefix_loop\n" ++
  ".Lraag_pc_low16:\n" ++
  "  lbu t2, 18(s0)\n" ++
  "  lbu t3, 19(s0)\n" ++
  "  slli t2, t2, 8\n" ++
  "  or t2, t2, t3\n" ++
  "  li t3, 1\n" ++
  "  bltu t2, t3, .Lraag_scan_table\n" ++
  "  li t3, 17\n" ++
  "  bgeu t3, t2, .Lraag_precompile\n" ++
  "  li t3, 256\n" ++
  "  beq t2, t3, .Lraag_precompile\n" ++
  ".Lraag_scan_table:\n" ++
  "  ld t6, 0(s2)                # count\n" ++
  "  li t0, 0                    # i\n" ++
  ".Lraag_scan_loop:\n" ++
  "  beq t0, t6, .Lraag_cold\n" ++
  "  slli t1, t0, 5              # i * 32\n" ++
  "  add t1, s1, t1              # record ptr\n" ++
  "  li t2, 0                    # byte index\n" ++
  ".Lraag_cmp_loop:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lraag_warm\n" ++
  "  add t4, s0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lraag_next_record\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lraag_cmp_loop\n" ++
  ".Lraag_next_record:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lraag_scan_loop\n" ++
  ".Lraag_cold:\n" ++
  "  bgeu t6, s3, .exit_outofgas\n" ++
  "  ld t0, 568(x20)\n" ++
  "  li t1, " ++ toString runtimeAccessColdDeltaGas ++ "\n" ++
  "  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(x20)\n" ++
  "  slli t0, t6, 5\n" ++
  "  add t1, s1, t0\n" ++
  "  li t2, 0\n" ++
  ".Lraag_copy_loop:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lraag_insert_done\n" ++
  "  add t4, s0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  sb t4, 0(t5)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lraag_copy_loop\n" ++
  ".Lraag_insert_done:\n" ++
  "  sw zero, 20(t1); sw zero, 24(t1); sw zero, 28(t1)\n" ++
  "  addi t6, t6, 1\n" ++
  "  sd t6, 0(s2)\n" ++
  "  li a0, 1\n" ++
  "  li a4, 1\n" ++
  "  li a5, " ++ toString runtimeAccessColdDeltaGas ++ "\n" ++
  "  j .Lraag_ret\n" ++
  ".Lraag_precompile:\n" ++
  "  li a0, 0\n" ++
  "  li a4, 2\n" ++
  "  li a5, 0\n" ++
  "  j .Lraag_ret\n" ++
  ".Lraag_warm:\n" ++
  "  li a0, 0\n" ++
  "  li a4, 0\n" ++
  "  li a5, 0\n" ++
  ".Lraag_ret:\n" ++
  "  la t0, " ++ runtimeAccessAccountOutcomeCountLabel ++ "\n" ++
  "  ld t1, 0(t0)\n" ++
  "  li t2, " ++ toString runtimeAccessAccountOutcomeCapacity ++ "\n" ++
  "  bgeu t1, t2, .Lraag_record_done\n" ++
  "  addi t2, t1, 1\n" ++
  "  sd t2, 0(t0)\n" ++
  "  slli t3, t1, 6\n" ++
  "  la t4, " ++ runtimeAccessAccountOutcomeTableLabel ++ "\n" ++
  "  add t3, t4, t3\n" ++
  "  li t0, 0\n" ++
  ".Lraag_record_copy_loop:\n" ++
  "  li t1, 20\n" ++
  "  beq t0, t1, .Lraag_record_zero_pad\n" ++
  "  add t2, s0, t0\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  add t5, t3, t0\n" ++
  "  sb t4, 0(t5)\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lraag_record_copy_loop\n" ++
  ".Lraag_record_zero_pad:\n" ++
  "  li t1, 32\n" ++
  "  beq t0, t1, .Lraag_record_fields\n" ++
  "  add t5, t3, t0\n" ++
  "  sb zero, 0(t5)\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lraag_record_zero_pad\n" ++
  ".Lraag_record_fields:\n" ++
  "  sd a4, 32(t3)              # 0 warm, 1 cold, 2 active precompile\n" ++
  "  sd a5, 40(t3)              # gas delta charged\n" ++
  "  sd zero, 48(t3)\n" ++
  "  sd zero, 56(t3)\n" ++
  ".Lraag_record_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-! ## runtime_access_account_seed

    Insert an initially warm account address without charging gas. This is
    used only during transaction/frame setup; opcode consumers should use
    `runtime_access_account_charge`.

    Calling convention matches the table portion of
    `runtime_access_account_charge`:
      a0 = canonical 20-byte BE address ptr
      a1 = table ptr
      a2 = count ptr
      a3 = capacity

    Duplicate addresses are ignored. Table-full insertion jumps to
    `.exit_outofgas`, which should be unreachable for the small initial seed
    set and 64-entry table. -/
def runtimeAccessAccountSeedFunction : String :=
  "runtime_access_account_seed:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv s3, a3\n" ++
  "  ld t6, 0(s2)\n" ++
  "  li t0, 0\n" ++
  ".Lraas_scan_loop:\n" ++
  "  beq t0, t6, .Lraas_insert\n" ++
  "  slli t1, t0, 5\n" ++
  "  add t1, s1, t1\n" ++
  "  li t2, 0\n" ++
  ".Lraas_cmp_loop:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lraas_ret_zero\n" ++
  "  add t4, s0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lraas_next_record\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lraas_cmp_loop\n" ++
  ".Lraas_next_record:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lraas_scan_loop\n" ++
  ".Lraas_insert:\n" ++
  "  bgeu t6, s3, .exit_outofgas\n" ++
  "  slli t0, t6, 5\n" ++
  "  add t1, s1, t0\n" ++
  "  li t2, 0\n" ++
  ".Lraas_copy_loop:\n" ++
  "  li t3, 20\n" ++
  "  beq t2, t3, .Lraas_insert_done\n" ++
  "  add t4, s0, t2\n" ++
  "  add t5, t1, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  sb t4, 0(t5)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lraas_copy_loop\n" ++
  ".Lraas_insert_done:\n" ++
  "  sw zero, 20(t1); sw zero, 24(t1); sw zero, 28(t1)\n" ++
  "  addi t6, t6, 1\n" ++
  "  sd t6, 0(s2)\n" ++
  "  li a0, 1\n" ++
  "  j .Lraas_ret\n" ++
  ".Lraas_ret_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lraas_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

def runtimeAccessWordToBe20Asm (tag srcReg dstReg idxReg tmpReg : String) : String :=
  "  addi " ++ srcReg ++ ", " ++ srcReg ++ ", 19\n" ++
  "  li " ++ idxReg ++ ", 20\n" ++
  ".Lraaw2be_" ++ tag ++ "_loop:\n" ++
  "  lbu " ++ tmpReg ++ ", 0(" ++ srcReg ++ ")\n" ++
  "  sb " ++ tmpReg ++ ", 0(" ++ dstReg ++ ")\n" ++
  "  addi " ++ srcReg ++ ", " ++ srcReg ++ ", -1\n" ++
  "  addi " ++ dstReg ++ ", " ++ dstReg ++ ", 1\n" ++
  "  addi " ++ idxReg ++ ", " ++ idxReg ++ ", -1\n" ++
  "  bnez " ++ idxReg ++ ", .Lraaw2be_" ++ tag ++ "_loop\n"

/-! ## runtime_access_seed_initial_accounts

    Seed the single-frame runtime's initial warm account table from the env
    words known before opcode execution:
      - ADDRESS/current executing account at env+0
      - CALLER at env+64
      - ORIGIN/sender at env+256

    The standalone runtime does not currently carry a distinct tx.to/create
    address outside ADDRESS, so follow-up frame work can extend this surface
    when that context exists. Active precompile addresses remain warm through
    `runtime_access_account_charge`'s precompile fast path. -/
def runtimeAccessSeedInitialAccountsFunction : String :=
  "runtime_access_seed_initial_accounts:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  la s0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  "  la t0, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  sd zero, 0(t0)\n" ++
  "  mv t1, x20\n" ++
  "  mv t2, s0\n" ++
  runtimeAccessWordToBe20Asm "address" "t1" "t2" "t3" "t4" ++
  "  mv a0, s0\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_seed\n" ++
  "  addi t1, x20, 64\n" ++
  "  mv t2, s0\n" ++
  runtimeAccessWordToBe20Asm "caller" "t1" "t2" "t3" "t4" ++
  "  mv a0, s0\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_seed\n" ++
  "  addi t1, x20, 256\n" ++
  "  mv t2, s0\n" ++
  runtimeAccessWordToBe20Asm "origin" "t1" "t2" "t3" "t4" ++
  "  mv a0, s0\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_seed\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-! ## runtime_access_seed_account_list

    Seed initially warm account addresses from a decoded transaction/access-list
    account list. The list uses the same 32-byte stride as the runtime warmth
    table: the canonical 20-byte big-endian address is stored at bytes 0..20,
    and bytes 20..32 are ignored padding.

    Calling convention:
      a0 = address-list ptr
      a1 = address count

    The helper seeds the global runtime account table used by opcode gas
    helpers. Duplicate addresses are ignored by `runtime_access_account_seed`.
    Transaction decoding code can call this once it has materialized the
    tx.to/access-list account tuples. -/
def runtimeAccessSeedAccountListFunction : String :=
  "runtime_access_seed_account_list:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  la s2, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la s3, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li s4, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  ".Lraasl_loop:\n" ++
  "  beqz s1, .Lraasl_done\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s3\n" ++
  "  mv a3, s4\n" ++
  "  jal ra, runtime_access_account_seed\n" ++
  "  addi s0, s0, 32\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lraasl_loop\n" ++
  ".Lraasl_done:\n" ++
  "  ld a0, 0(s3)\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_runtime_access_account_gas`: probe BuildUnit.

    Input selector at byte 0:
      0 = success sequence: cold A, warm A, active precompile 0x04.
      1 = under-gas cold access; expects `.exit_outofgas`.

    Success output:
      +0 first status, +8 gas, +16 count, +24 second status, +32 gas,
      +40 count, +48 precompile status, +56 gas, +64 count. -/
def ziskRuntimeAccessAccountGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, rta_env\n" ++
  "  li t0, 0x40000008\n" ++
  "  ld t0, 0(t0)\n" ++
  "  beqz t0, .Lraag_probe_success\n" ++
  "  li t1, 2499\n" ++
  "  sd t1, 568(x20)\n" ++
  "  la a0, rta_addr_b\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  j .Lraag_probe_done\n" ++
  ".Lraag_probe_success:\n" ++
  "  li t1, 3000\n" ++
  "  sd t1, 568(x20)\n" ++
  "  la t0, rta_count\n" ++
  "  sd zero, 0(t0)\n" ++
  "  la a0, rta_addr_a\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  ld t1, 568(x20); sd t1, 8(t0)\n" ++
  "  la t2, rta_count; ld t1, 0(t2); sd t1, 16(t0)\n" ++
  "  la a0, rta_addr_a\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 24(t0)\n" ++
  "  ld t1, 568(x20); sd t1, 32(t0)\n" ++
  "  la t2, rta_count; ld t1, 0(t2); sd t1, 40(t0)\n" ++
  "  la a0, rta_addr_precompile\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 48(t0)\n" ++
  "  ld t1, 568(x20); sd t1, 56(t0)\n" ++
  "  la t2, rta_count; ld t1, 0(t2); sd t1, 64(t0)\n" ++
  "  j .Lraag_probe_done\n" ++
  runtimeAccessAccountChargeFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li t1, 6\n" ++
  "  sd t1, 32(t0)\n" ++
  ".Lraag_probe_done:"

def ziskRuntimeAccessAccountGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rta_env:\n" ++
  "  .zero 656\n" ++
  ".balign 8\n" ++
  "rta_count:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "rta_table:\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  "rta_addr_a:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0xaa,0xbb,0xcc,0xdd\n" ++
  "rta_addr_b:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x11,0x22,0x33,0x44\n" ++
  "rta_addr_precompile:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4\n" ++
  runtimeAccessAccountOutcomeData

def ziskRuntimeAccessAccountGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRuntimeAccessAccountGasPrologue
  dataAsm     := ziskRuntimeAccessAccountGasDataSection
}

/-- `zisk_runtime_access_account_outcome_records`: probe BuildUnit.

    Runs the same cold/warm/precompile sequence as the gas probe and exposes
    the appended account access outcomes:
      +0 outcome count
      +8 warmth table count
      +16 final gas
      +24 first record status
      +32 first record gas delta
      +40 second record status
      +48 second record gas delta
      +56 third record status
      +64 third record gas delta. -/
def ziskRuntimeAccessAccountOutcomeRecordsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, rta_env\n" ++
  "  li t1, 3000\n" ++
  "  sd t1, 568(x20)\n" ++
  "  la t0, rta_count\n" ++
  "  sd zero, 0(t0)\n" ++
  "  la t0, " ++ runtimeAccessAccountOutcomeCountLabel ++ "\n" ++
  "  sd zero, 0(t0)\n" ++
  "  la a0, rta_addr_a\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  la a0, rta_addr_a\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  la a0, rta_addr_precompile\n" ++
  "  la a1, rta_table\n" ++
  "  la a2, rta_count\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, " ++ runtimeAccessAccountOutcomeCountLabel ++ "\n" ++
  "  ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  la t0, rta_count\n" ++
  "  ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  ld t1, 568(x20); sd t1, 16(s0)\n" ++
  "  la t0, " ++ runtimeAccessAccountOutcomeTableLabel ++ "\n" ++
  "  ld t1, 32(t0); sd t1, 24(s0)\n" ++
  "  ld t1, 40(t0); sd t1, 32(s0)\n" ++
  "  addi t0, t0, 64\n" ++
  "  ld t1, 32(t0); sd t1, 40(s0)\n" ++
  "  ld t1, 40(t0); sd t1, 48(s0)\n" ++
  "  addi t0, t0, 64\n" ++
  "  ld t1, 32(t0); sd t1, 56(s0)\n" ++
  "  ld t1, 40(t0); sd t1, 64(s0)\n" ++
  "  j .Lraag_outcome_probe_done\n" ++
  runtimeAccessAccountChargeFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  li t0, 0xa0010000; li t1, 6; sd t1, 0(t0)\n" ++
  ".Lraag_outcome_probe_done:"

def ziskRuntimeAccessAccountOutcomeRecordsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRuntimeAccessAccountOutcomeRecordsPrologue
  dataAsm     := ziskRuntimeAccessAccountGasDataSection
}

/-- `zisk_runtime_access_seed_initial`: probe BuildUnit. Seeds ADDRESS,
    CALLER, and ORIGIN from a fake runtime env, then charges those addresses,
    an unrelated address, and an active precompile. Output is five
    `(status, gasRemaining, count)` triples. -/
def ziskRuntimeAccessSeedInitialPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, rta_seed_env\n" ++
  "  la t0, rta_seed_address_word\n" ++
  "  ld t1, 0(t0); sd t1, 0(x20)\n" ++
  "  ld t1, 8(t0); sd t1, 8(x20)\n" ++
  "  ld t1, 16(t0); sd t1, 16(x20)\n" ++
  "  ld t1, 24(t0); sd t1, 24(x20)\n" ++
  "  la t0, rta_seed_caller_word\n" ++
  "  ld t1, 0(t0); sd t1, 64(x20)\n" ++
  "  ld t1, 8(t0); sd t1, 72(x20)\n" ++
  "  ld t1, 16(t0); sd t1, 80(x20)\n" ++
  "  ld t1, 24(t0); sd t1, 88(x20)\n" ++
  "  la t0, rta_seed_origin_word\n" ++
  "  ld t1, 0(t0); sd t1, 256(x20)\n" ++
  "  ld t1, 8(t0); sd t1, 264(x20)\n" ++
  "  ld t1, 16(t0); sd t1, 272(x20)\n" ++
  "  ld t1, 24(t0); sd t1, 280(x20)\n" ++
  "  jal ra, runtime_access_seed_initial_accounts\n" ++
  "  li t1, 10000\n" ++
  "  sd t1, 568(x20)\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la a0, rta_seed_address_be\n" ++
  "  jal ra, rta_seed_charge_one\n" ++
  "  la a0, rta_seed_caller_be\n" ++
  "  jal ra, rta_seed_charge_one\n" ++
  "  la a0, rta_seed_origin_be\n" ++
  "  jal ra, rta_seed_charge_one\n" ++
  "  la a0, rta_seed_other_be\n" ++
  "  jal ra, rta_seed_charge_one\n" ++
  "  la a0, rta_addr_precompile\n" ++
  "  jal ra, rta_seed_charge_one\n" ++
  "  j .Lraasi_done\n" ++
  "rta_seed_charge_one:\n" ++
  "  addi sp, sp, -8\n" ++
  "  sd ra, 0(sp)\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  sd a0, 0(s0)\n" ++
  "  ld t0, 568(x20); sd t0, 8(s0)\n" ++
  "  la t1, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  ld t0, 0(t1); sd t0, 16(s0)\n" ++
  "  addi s0, s0, 24\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 8\n" ++
  "  ret\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
  runtimeAccessAccountChargeFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li t1, 6\n" ++
  "  sd t1, 32(t0)\n" ++
  ".Lraasi_done:"

def ziskRuntimeAccessSeedInitialDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rta_seed_env:\n" ++
  "  .zero 656\n" ++
  ".balign 8\n" ++
  runtimeAccessAccountCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountTableLabel ++ ":\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  runtimeAccessSeedScratchLabel ++ ":\n" ++
  "  .zero 32\n" ++
  "rta_seed_address_word:\n" ++
  "  .byte 0xdd,0xcc,0xbb,0xaa,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0\n" ++
  "rta_seed_caller_word:\n" ++
  "  .byte 0x44,0x33,0x22,0x11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0\n" ++
  "rta_seed_origin_word:\n" ++
  "  .byte 0x88,0x77,0x66,0x55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0\n" ++
  "rta_seed_address_be:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0xaa,0xbb,0xcc,0xdd\n" ++
  "rta_seed_caller_be:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x11,0x22,0x33,0x44\n" ++
  "rta_seed_origin_be:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x55,0x66,0x77,0x88\n" ++
  "rta_seed_other_be:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x99,0xaa,0xbb,0xcc\n" ++
  "rta_addr_precompile:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4\n" ++
  runtimeAccessAccountOutcomeData

def ziskRuntimeAccessSeedInitialProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRuntimeAccessSeedInitialPrologue
  dataAsm     := ziskRuntimeAccessSeedInitialDataSection
}

/-! `zisk_runtime_access_seed_account_list`: probe BuildUnit.

    Input memory layout (`ziskemu -i` payload starts at base + 8):
      +0  u64 count
      +8  first 32-byte address-list record
      +40 second 32-byte address-list record

    The check script supplies the same account twice. Output:
      +0  count after list seed
      +8  gas after list seed
      +16 status for charging seeded account A
      +24 gas after charging A
      +32 count after charging A
      +40 status for charging unlisted account B
      +48 gas after charging B
      +56 count after charging B. -/
def ziskRuntimeAccessSeedAccountListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, rta_list_seed_env\n" ++
  "  li t1, 5000\n" ++
  "  sd t1, 568(x20)\n" ++
  "  la t0, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  sd zero, 0(t0)\n" ++
  "  la t0, " ++ runtimeAccessAccountOutcomeCountLabel ++ "\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li t0, 0x40000008\n" ++
  "  ld a1, 0(t0)\n" ++
  "  addi a0, t0, 8\n" ++
  "  jal ra, runtime_access_seed_account_list\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  ld t1, 568(x20); sd t1, 8(s0)\n" ++
  "  li t0, 0x40000010\n" ++
  "  mv a0, t0\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  sd a0, 16(s0)\n" ++
  "  ld t1, 568(x20); sd t1, 24(s0)\n" ++
  "  la t0, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  ld t1, 0(t0); sd t1, 32(s0)\n" ++
  "  la a0, rta_list_seed_addr_b\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  sd a0, 40(s0)\n" ++
  "  ld t1, 568(x20); sd t1, 48(s0)\n" ++
  "  la t0, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  ld t1, 0(t0); sd t1, 56(s0)\n" ++
  "  j .Lraasl_probe_done\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedAccountListFunction ++ "\n" ++
  runtimeAccessAccountChargeFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  li t0, 0xa0010000; li t1, 6; sd t1, 0(t0)\n" ++
  ".Lraasl_probe_done:"

def ziskRuntimeAccessSeedAccountListDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rta_list_seed_env:\n" ++
  "  .zero 656\n" ++
  ".balign 8\n" ++
  runtimeAccessAccountCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountTableLabel ++ ":\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  "rta_list_seed_addr_b:\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x11,0x22,0x33,0x44\n" ++
  runtimeAccessAccountOutcomeData

def ziskRuntimeAccessSeedAccountListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRuntimeAccessSeedAccountListPrologue
  dataAsm     := ziskRuntimeAccessSeedAccountListDataSection
}

end EvmAsm.Codegen
