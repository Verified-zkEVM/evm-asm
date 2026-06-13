/-
  EvmAsm.Codegen.Programs.SeedTxAccessList

  nxio8.5.1: seed an EIP-2930/1559 transaction `access_list` into the runtime
  EIP-2929 storage-warmth set at transaction start.

  execution-specs warms every `(address, storage_key)` pair in the tx access
  list BEFORE execution, so the first SLOAD/SSTORE on a listed slot is charged
  WARM (the cold 2000-gas delta is skipped). The guest's runtime warm set
  (`evm_storage_access_keys` / `evm_storage_access_count`, EvmStorageAccessGas)
  starts empty per tx; without seeding, a listed-slot SLOAD/SSTORE is charged
  COLD, over-counting the tx's regular gas vs the spec.

  This slice provides the iterator helper + a probe ONLY; wiring it into the
  dispatcher tx-setup (and confirming the regular-gas reachability into a
  consensus check) is the follow-up nxio8.5.2.

  Warm-set key layout consumed by `evm_storage_access_charge_key` (and produced
  here): 32-byte address token (env.ADDRESS format = the 20-byte address
  big-endian, LEFT-aligned, high 12 bytes zero) followed by the 32-byte storage
  slot. The access-list RLP gives the address as a 20-byte string (field 0 of
  each entry) and each slot as a 32-byte string (the field-1 sub-list items);
  this mirrors the iteration in `access_list_count` (TxExtract.lean).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.EvmStorageAccessGas

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## seed_tx_access_list

    Calling convention:
      a0 (input)  : access_list bytes ptr (whole encoded outer list)
      a1 (input)  : access_list byte length
      ra (input)  : return
      a0 (output) : 0 success (all (address, slot) pairs seeded); 1 malformed
                    RLP (parse failure). Empty list (`0xc0`) -> 0, nothing seeded.

    For each access-list entry `[address, [slot...]]`: build the 32-byte address
    token (20 bytes big-endian, left-aligned), then seed every slot key via
    `evm_storage_access_seed_key(token, slot)` into the global EIP-2929 warm set.
    Re-warming an already-present key is idempotent (seed status 0); a full table
    (status 3) is treated as success here (warmth is a gas optimisation, not a
    correctness gate — a missed seed only over-charges, never under-charges). -/
def seedTxAccessListFunction : String :=
  "seed_tx_access_list:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                   # outer list ptr\n" ++
  "  mv s1, a1                   # outer list len\n" ++
  "  # outer entry count -> s2.\n" ++
  "  mv a0, s0; mv a1, s1; la a2, stal_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lstal_fail\n" ++
  "  la t0, stal_scratch; ld s2, 0(t0)\n" ++
  "  beqz s2, .Lstal_ok\n" ++
  "  li s3, 0                    # entry index\n" ++
  ".Lstal_entry_loop:\n" ++
  "  beq s3, s2, .Lstal_ok\n" ++
  "  # entry s3 bounds (list item -> item-start offset).\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s3\n" ++
  "  la a3, stal_eoff; la a4, stal_elen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstal_fail\n" ++
  "  la t0, stal_eoff; ld t1, 0(t0); add s4, s0, t1   # entry ptr\n" ++
  "  la t0, stal_elen; ld s5, 0(t0)                    # entry len\n" ++
  "  # entry field 0 = address (20-byte string -> content offset).\n" ++
  "  mv a0, s4; mv a1, s5; li a2, 0\n" ++
  "  la a3, stal_aoff; la a4, stal_alen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstal_fail\n" ++
  "  # build the 32-byte token: zero it, then copy the address bytes left-aligned.\n" ++
  "  la t0, stal_token; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, stal_aoff; ld t1, 0(t0); add t1, s4, t1   # address content ptr\n" ++
  "  la t0, stal_alen; ld t2, 0(t0)                    # address byte length\n" ++
  "  la t3, stal_token; li t4, 0\n" ++
  ".Lstal_addr_cp:\n" ++
  "  beq t4, t2, .Lstal_addr_done\n" ++
  "  add t5, t1, t4; lbu t6, 0(t5)\n" ++
  "  add t5, t3, t4; sb t6, 0(t5)\n" ++
  "  addi t4, t4, 1; j .Lstal_addr_cp\n" ++
  ".Lstal_addr_done:\n" ++
  "  # entry field 1 = slots sub-list (list item -> item-start offset).\n" ++
  "  mv a0, s4; mv a1, s5; li a2, 1\n" ++
  "  la a3, stal_soff; la a4, stal_slen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstal_fail\n" ++
  "  la t0, stal_soff; ld t1, 0(t0); add s6, s4, t1   # slots sub-list ptr\n" ++
  "  la t0, stal_slen; ld s7, 0(t0)                    # slots sub-list len\n" ++
  "  # slot count -> s8.\n" ++
  "  mv a0, s6; mv a1, s7; la a2, stal_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lstal_fail\n" ++
  "  la t0, stal_scratch; ld s8, 0(t0)\n" ++
  "  li s9, 0                    # slot index\n" ++
  ".Lstal_slot_loop:\n" ++
  "  beq s9, s8, .Lstal_entry_next\n" ++
  "  mv a0, s6; mv a1, s7; mv a2, s9\n" ++
  "  la a3, stal_koff; la a4, stal_klen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstal_fail\n" ++
  "  la t0, stal_koff; ld t1, 0(t0); add t1, s6, t1   # slot content ptr (a1)\n" ++
  "  la a0, stal_token; mv a1, t1\n" ++
  "  jal ra, evm_storage_access_seed_key\n" ++
  "  addi s9, s9, 1; j .Lstal_slot_loop\n" ++
  ".Lstal_entry_next:\n" ++
  "  addi s3, s3, 1; j .Lstal_entry_loop\n" ++
  ".Lstal_ok:\n" ++
  "  li a0, 0; j .Lstal_ret\n" ++
  ".Lstal_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lstal_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- Scratch labels for `seed_tx_access_list` (offsets/lengths from the RLP
    walk + the 32-byte address token). Distinct `stal_` prefix; emit once in any
    unit that links `seedTxAccessListFunction`. -/
def seedTxAccessListDataSection : String :=
  ".balign 8\n" ++
  "stal_scratch:\n  .zero 8\n" ++
  "stal_eoff:\n  .zero 8\n" ++
  "stal_elen:\n  .zero 8\n" ++
  "stal_aoff:\n  .zero 8\n" ++
  "stal_alen:\n  .zero 8\n" ++
  "stal_soff:\n  .zero 8\n" ++
  "stal_slen:\n  .zero 8\n" ++
  "stal_koff:\n  .zero 8\n" ++
  "stal_klen:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "stal_token:\n  .zero 32\n"

/-- `zisk_seed_tx_access_list`: focused probe.

    Input layout (ziskemu writes an 8-byte length header at +0, so user byte k
    is at INPUT+8+k):
      user +0   : access_list byte length (u64)
      user +8   : access_list RLP bytes

    Output layout at 0xa0010000:
      +0  status (0 ok / 1 malformed)
      +8  evm_storage_access_count after seeding (total slots seeded)
      +16 first warm-set key: address-token byte 0 (expect address[0])
      +24 first warm-set key: slot byte 0 (at key+32)
      +32 first warm-set key: address-token bytes 18,19 packed (expect address tail) -/
def ziskSeedTxAccessListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000           # input base (8-byte length header at +0)\n" ++
  "  ld a1, 8(t6)                # access_list len (user +0)\n" ++
  "  addi a0, t6, 16             # access_list ptr (user +8)\n" ++
  "  jal ra, seed_tx_access_list\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  la t1, evm_storage_access_count; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  # first warm-set key (64 bytes): token@+0, slot@+32.\n" ++
  "  la t1, evm_storage_access_keys\n" ++
  "  lbu t2, 0(t1); sd t2, 16(t0)         # token byte 0\n" ++
  "  lbu t2, 32(t1); sd t2, 24(t0)        # slot byte 0\n" ++
  "  lbu t2, 19(t1); sd t2, 32(t0)        # token byte 19 (address tail)\n" ++
  "  j .Lstal_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  storageAccessSeedFunction ++ "\n" ++
  seedTxAccessListFunction ++ "\n" ++
  ".Lstal_pdone:"

def ziskSeedTxAccessListDataSection : String :=
  ".section .data\n" ++
  seedTxAccessListDataSection ++ "\n" ++
  storageAccessGasData

def ziskSeedTxAccessListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSeedTxAccessListPrologue
  dataAsm     := ziskSeedTxAccessListDataSection
}

end EvmAsm.Codegen
