/-
  EvmAsm.Codegen.Programs.EvmStorageAccessGas

  Runtime storage-key warmth table for EIP-2929 SLOAD/SSTORE gas.
  The dispatcher already charges the 100-gas warm/static floor for
  SLOAD and SSTORE; this helper charges the missing 2000-gas cold
  storage-key delta on first touch and records the key as warm.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Maximum `(address, slot)` storage access keys tracked by the runtime
    opcode harness. Each entry is 64 bytes: 32-byte address token followed
    by the 32-byte storage slot in EVM stack order. -/
def storageAccessGasMaxKeys : Nat := 64
def storageAccessOutcomeMaxRecords : Nat := 64
def storageAccessOutcomeRecordSize : Nat := 96
def storageAccessColdDeltaGas : Nat := 2000

/-- Data labels consumed by `evm_storage_access_charge_key`. -/
def storageAccessGasData : String :=
  ".balign 8\n" ++
  "evm_storage_access_count:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_storage_access_zero_address:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "evm_storage_access_keys:\n" ++
  s!"  .zero {storageAccessGasMaxKeys * 64}\n" ++
  ".balign 8\n" ++
  "evm_storage_access_outcome_count:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_storage_access_outcomes:\n" ++
  s!"  .zero {storageAccessOutcomeMaxRecords * storageAccessOutcomeRecordSize}\n"


def storageAccessKeyScanAsm (tag warmLabel coldLabel nextLabel : String) : String :=
  "  la t0, evm_storage_access_keys\n" ++
  "  la t1, evm_storage_access_count\n" ++
  "  ld t2, 0(t1)\n" ++
  "  mv t3, t0\n" ++
  s!".L{tag}_scan:\n" ++
  s!"  beqz t2, .L{coldLabel}\n" ++
  "  ld t4, 0(t3)\n" ++
  "  ld t5, 0(t6)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  "  ld t4, 8(t3)\n" ++
  "  ld t5, 8(t6)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  "  ld t4, 16(t3)\n" ++
  "  ld t5, 16(t6)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  "  ld t4, 24(t3)\n" ++
  "  ld t5, 24(t6)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  "  ld t4, 32(t3)\n" ++
  "  ld t5, 0(a1)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  "  ld t4, 40(t3)\n" ++
  "  ld t5, 8(a1)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  "  ld t4, 48(t3)\n" ++
  "  ld t5, 16(a1)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  "  ld t4, 56(t3)\n" ++
  "  ld t5, 24(a1)\n" ++
  s!"  bne t4, t5, .L{nextLabel}\n" ++
  s!"  j .L{warmLabel}\n" ++
  s!".L{nextLabel}:\n" ++
  "  addi t3, t3, 64\n" ++
  "  addi t2, t2, -1\n" ++
  s!"  j .L{tag}_scan\n"

def storageAccessKeyInsertAsm (doneLabel : String) : String :=
  "  slli t3, t2, 6\n" ++
  "  add t3, t0, t3\n" ++
  "  ld t4, 0(t6)\n" ++
  "  sd t4, 0(t3)\n" ++
  "  ld t4, 8(t6)\n" ++
  "  sd t4, 8(t3)\n" ++
  "  ld t4, 16(t6)\n" ++
  "  sd t4, 16(t3)\n" ++
  "  ld t4, 24(t6)\n" ++
  "  sd t4, 24(t3)\n" ++
  "  ld t4, 0(a1)\n" ++
  "  sd t4, 32(t3)\n" ++
  "  ld t4, 8(a1)\n" ++
  "  sd t4, 40(t3)\n" ++
  "  ld t4, 16(a1)\n" ++
  "  sd t4, 48(t3)\n" ++
  "  ld t4, 24(a1)\n" ++
  "  sd t4, 56(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  sd t2, 0(t1)\n" ++
  s!"  j .L{doneLabel}\n"

/-! ## evm_storage_access_charge_key

    Calling convention:
      a0 input  : address-token ptr (32 bytes), or 0 for the current
                  single-contract zero token.
      a1 input  : storage-slot ptr (32 bytes, EVM stack byte order).
      a2 input  : gasRemaining cell ptr.
      a0 output : status:
                    0 = already warm, no gas charged;
                    1 = cold, charged 2000 and inserted;
                    2 = out of gas, table unchanged;
                    3 = table full, table/gas unchanged.

    The dispatcher's opcode table charges SLOAD/SSTORE 100 before the
    handler runs, so this helper only charges the EIP-2929 cold delta
    (`COLD_SLOAD_COST - WARM_STORAGE_READ_COST = 2100 - 100 = 2000`).
-/
def storageAccessGasFunction : String :=
  "evm_storage_access_charge_key:\n" ++
  "  mv t6, a0\n" ++
  "  bnez t6, .Lsag_addr_ready\n" ++
  "  la t6, evm_storage_access_zero_address\n" ++
  ".Lsag_addr_ready:\n" ++
  "  la t0, evm_storage_access_keys\n" ++
  "  la t1, evm_storage_access_count\n" ++
  "  ld t2, 0(t1)\n" ++
  "  mv t3, t0\n" ++
  ".Lsag_scan:\n" ++
  "  beqz t2, .Lsag_cold\n" ++
  "  ld t4, 0(t3)\n" ++
  "  ld t5, 0(t6)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  ld t4, 8(t3)\n" ++
  "  ld t5, 8(t6)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  ld t4, 16(t3)\n" ++
  "  ld t5, 16(t6)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  ld t4, 24(t3)\n" ++
  "  ld t5, 24(t6)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  ld t4, 32(t3)\n" ++
  "  ld t5, 0(a1)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  ld t4, 40(t3)\n" ++
  "  ld t5, 8(a1)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  ld t4, 48(t3)\n" ++
  "  ld t5, 16(a1)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  ld t4, 56(t3)\n" ++
  "  ld t5, 24(a1)\n" ++
  "  bne t4, t5, .Lsag_next\n" ++
  "  li a0, 0\n" ++
  "  li a3, 0\n" ++
  "  j .Lsag_record_and_ret\n" ++
  ".Lsag_next:\n" ++
  "  addi t3, t3, 64\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lsag_scan\n" ++
  ".Lsag_cold:\n" ++
  "  ld t2, 0(t1)\n" ++
  s!"  li t4, {storageAccessGasMaxKeys}\n" ++
  "  bgeu t2, t4, .Lsag_full\n" ++
  "  ld t5, 0(a2)\n" ++
  s!"  li t4, {storageAccessColdDeltaGas}\n" ++
  "  bltu t5, t4, .Lsag_oog\n" ++
  "  sub t5, t5, t4\n" ++
  "  sd t5, 0(a2)\n" ++
  "  slli t3, t2, 6\n" ++
  "  add t3, t0, t3\n" ++
  "  ld t4, 0(t6)\n" ++
  "  sd t4, 0(t3)\n" ++
  "  ld t4, 8(t6)\n" ++
  "  sd t4, 8(t3)\n" ++
  "  ld t4, 16(t6)\n" ++
  "  sd t4, 16(t3)\n" ++
  "  ld t4, 24(t6)\n" ++
  "  sd t4, 24(t3)\n" ++
  "  ld t4, 0(a1)\n" ++
  "  sd t4, 32(t3)\n" ++
  "  ld t4, 8(a1)\n" ++
  "  sd t4, 40(t3)\n" ++
  "  ld t4, 16(a1)\n" ++
  "  sd t4, 48(t3)\n" ++
  "  ld t4, 24(a1)\n" ++
  "  sd t4, 56(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  sd t2, 0(t1)\n" ++
  "  li a0, 1\n" ++
  s!"  li a3, {storageAccessColdDeltaGas}\n" ++
  "  j .Lsag_record_and_ret\n" ++
  ".Lsag_oog:\n" ++
  "  li a0, 2\n" ++
  "  li a3, 0\n" ++
  "  j .Lsag_record_and_ret\n" ++
  ".Lsag_full:\n" ++
  "  li a0, 3\n" ++
  "  li a3, 0\n" ++
  "  j .Lsag_record_and_ret\n" ++
  ".Lsag_record_and_ret:\n" ++
  "  la t0, evm_storage_access_outcome_count\n" ++
  "  ld t1, 0(t0)\n" ++
  s!"  li t2, {storageAccessOutcomeMaxRecords}\n" ++
  "  bgeu t1, t2, .Lsag_record_skip\n" ++
  "  addi t2, t1, 1\n" ++
  "  sd t2, 0(t0)\n" ++
  "  slli t3, t1, 6              # i * 64\n" ++
  "  slli t4, t1, 5              # i * 32\n" ++
  "  add t3, t3, t4              # i * 96\n" ++
  "  la t4, evm_storage_access_outcomes\n" ++
  "  add t3, t4, t3\n" ++
  "  ld t4, 0(t6);  sd t4, 0(t3)\n" ++
  "  ld t4, 8(t6);  sd t4, 8(t3)\n" ++
  "  ld t4, 16(t6); sd t4, 16(t3)\n" ++
  "  ld t4, 24(t6); sd t4, 24(t3)\n" ++
  "  ld t4, 0(a1);  sd t4, 32(t3)\n" ++
  "  ld t4, 8(a1);  sd t4, 40(t3)\n" ++
  "  ld t4, 16(a1); sd t4, 48(t3)\n" ++
  "  ld t4, 24(a1); sd t4, 56(t3)\n" ++
  "  sd a0, 64(t3)               # status/outcome\n" ++
  "  sd a3, 72(t3)               # gas delta charged\n" ++
  "  sd zero, 80(t3)\n" ++
  "  sd zero, 88(t3)\n" ++
  ".Lsag_record_skip:\n" ++
  "  ret"

/-- Probe for `evm_storage_access_charge_key`.

    Input memory layout (`ziskemu -i` payload starts at base + 8):
      bytes 8..16   initial gas
      bytes 16..48  slot A
      bytes 48..80  slot B

    Output layout records `(status, gas, count)` after A, then after A
    again, then after B, at 24-byte strides from OUTPUT. -/
def ziskStorageAccessGasProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld t1, 8(t0)\n" ++
  "  la a2, sag_probe_gas\n" ++
  "  sd t1, 0(a2)\n" ++
  "  addi a1, t0, 16\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li t2, 0xa0010000\n" ++
  "  sd a0, 0(t2)\n" ++
  "  ld t3, 0(a2)\n" ++
  "  sd t3, 8(t2)\n" ++
  "  la t4, evm_storage_access_count\n" ++
  "  ld t5, 0(t4)\n" ++
  "  sd t5, 16(t2)\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 16\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li t2, 0xa0010000\n" ++
  "  sd a0, 24(t2)\n" ++
  "  ld t3, 0(a2)\n" ++
  "  sd t3, 32(t2)\n" ++
  "  la t4, evm_storage_access_count\n" ++
  "  ld t5, 0(t4)\n" ++
  "  sd t5, 40(t2)\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 48\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li t2, 0xa0010000\n" ++
  "  sd a0, 48(t2)\n" ++
  "  ld t3, 0(a2)\n" ++
  "  sd t3, 56(t2)\n" ++
  "  la t4, evm_storage_access_count\n" ++
  "  ld t5, 0(t4)\n" ++
  "  sd t5, 64(t2)\n" ++
  "  j .Lsag_probe_done\n" ++
  storageAccessGasFunction ++ "\n" ++
  ".Lsag_probe_done:"
/-! ## evm_storage_access_seed_key

    Calling convention:
      a0 input  : address-token ptr (32 bytes), or 0 for the current
                  single-contract zero token.
      a1 input  : storage-slot ptr (32 bytes, EVM stack byte order).
      a0 output : status:
                    0 = already warm, no table mutation;
                    1 = inserted as warm, no gas charged;
                    3 = table full, table unchanged.

    This is the storage-key analogue of `runtime_access_account_seed`.
    Transaction setup can use it for EIP-2930 access-list storage keys;
    opcode consumers should keep using `evm_storage_access_charge_key`. -/
def storageAccessSeedFunction : String :=
  "evm_storage_access_seed_key:\n" ++
  "  mv t6, a0\n" ++
  "  bnez t6, .Lssg_addr_ready\n" ++
  "  la t6, evm_storage_access_zero_address\n" ++
  ".Lssg_addr_ready:\n" ++
  storageAccessKeyScanAsm "ssg" "ssg_warm" "ssg_insert" "ssg_next" ++
  ".Lssg_warm:\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lssg_insert:\n" ++
  "  ld t2, 0(t1)\n" ++
  s!"  li t4, {storageAccessGasMaxKeys}\n" ++
  "  bgeu t2, t4, .Lssg_full\n" ++
  storageAccessKeyInsertAsm "ssg_inserted" ++
  ".Lssg_inserted:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lssg_full:\n" ++
  "  li a0, 3\n" ++
  "  ret"

/-- Probe for `evm_storage_access_charge_key`.

    Input memory layout (`ziskemu -i` payload starts at base + 8):
      bytes 8..16   initial gas
      bytes 16..48  slot A
      bytes 48..80  slot B

    Output layout records `(status, gas, count)` after A, then after A
    again, then after B, at 24-byte strides from OUTPUT. -/

def ziskStorageAccessGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sag_probe_gas:\n" ++
  "  .zero 8\n" ++
  storageAccessGasData

def ziskStorageAccessGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStorageAccessGasProbePrologue
  dataAsm     := ziskStorageAccessGasDataSection
}
def ziskStorageAccessSeedProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld t1, 8(t0)\n" ++
  "  la a2, sas_probe_gas\n" ++
  "  sd t1, 0(a2)\n" ++
  "  addi a1, t0, 16\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_seed_key\n" ++
  "  li t2, 0xa0010000\n" ++
  "  sd a0, 0(t2)\n" ++
  "  ld t3, 0(a2)\n" ++
  "  sd t3, 8(t2)\n" ++
  "  la t4, evm_storage_access_count\n" ++
  "  ld t5, 0(t4)\n" ++
  "  sd t5, 16(t2)\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 16\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_seed_key\n" ++
  "  li t2, 0xa0010000\n" ++
  "  sd a0, 24(t2)\n" ++
  "  ld t3, 0(a2)\n" ++
  "  sd t3, 32(t2)\n" ++
  "  la t4, evm_storage_access_count\n" ++
  "  ld t5, 0(t4)\n" ++
  "  sd t5, 40(t2)\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 16\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li t2, 0xa0010000\n" ++
  "  sd a0, 48(t2)\n" ++
  "  ld t3, 0(a2)\n" ++
  "  sd t3, 56(t2)\n" ++
  "  la t4, evm_storage_access_count\n" ++
  "  ld t5, 0(t4)\n" ++
  "  sd t5, 64(t2)\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 48\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li t2, 0xa0010000\n" ++
  "  sd a0, 72(t2)\n" ++
  "  ld t3, 0(a2)\n" ++
  "  sd t3, 80(t2)\n" ++
  "  la t4, evm_storage_access_count\n" ++
  "  ld t5, 0(t4)\n" ++
  "  sd t5, 88(t2)\n" ++
  "  j .Lsas_probe_done\n" ++
  storageAccessSeedFunction ++ "\n" ++
  storageAccessGasFunction ++ "\n" ++
  ".Lsas_probe_done:"

def ziskStorageAccessSeedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sas_probe_gas:\n" ++
  "  .zero 8\n" ++
  storageAccessGasData

def ziskStorageAccessSeedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStorageAccessSeedProbePrologue
  dataAsm     := ziskStorageAccessSeedDataSection
}



/-- Probe for storage-access outcome records.

    Output layout:
      +0  outcome count
      +8  warmth table count
      +16 final gas
      +24 first record status
      +32 first record gas delta
      +40 second record status
      +48 second record gas delta
      +56 third record status
      +64 third record gas delta -/
def ziskStorageAccessOutcomeRecordsProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld t1, 8(t0)\n" ++
  "  la a2, sag_probe_gas\n" ++
  "  sd t1, 0(a2)\n" ++
  "  addi a1, t0, 16\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 16\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 48\n" ++
  "  li a0, 0\n" ++
  "  jal ra, evm_storage_access_charge_key\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, evm_storage_access_outcome_count\n" ++
  "  ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  la t0, evm_storage_access_count\n" ++
  "  ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  la t0, sag_probe_gas\n" ++
  "  ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  la t0, evm_storage_access_outcomes\n" ++
  "  ld t1, 64(t0); sd t1, 24(s0)\n" ++
  "  ld t1, 72(t0); sd t1, 32(s0)\n" ++
  "  addi t0, t0, 96\n" ++
  "  ld t1, 64(t0); sd t1, 40(s0)\n" ++
  "  ld t1, 72(t0); sd t1, 48(s0)\n" ++
  "  addi t0, t0, 96\n" ++
  "  ld t1, 64(t0); sd t1, 56(s0)\n" ++
  "  ld t1, 72(t0); sd t1, 64(s0)\n" ++
  "  j .Lsag_outcome_probe_done\n" ++
  storageAccessGasFunction ++ "\n" ++
  ".Lsag_outcome_probe_done:"

def ziskStorageAccessOutcomeRecordsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStorageAccessOutcomeRecordsProbePrologue
  dataAsm     := ziskStorageAccessGasDataSection
}

end EvmAsm.Codegen
