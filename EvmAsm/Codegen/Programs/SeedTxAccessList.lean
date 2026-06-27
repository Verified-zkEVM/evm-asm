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
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmStorageAccessGas
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxDecode2930
import EvmAsm.Codegen.Programs.TxDecode1559
import EvmAsm.Codegen.Programs.TxDecode4844
import EvmAsm.Codegen.Programs.TxDecode7702

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
  -- bal_2930: build the env.ADDRESS-format token (address reversed into bytes 0..L-1
  -- of a zeroed 32-byte word = the address as a little-endian 256-bit integer) used
  -- by the storage-key warm set. stal_token holds the address big-endian in bytes
  -- 0..L-1 (L = stal_alen, normally 20); reverse it: token_le[L-1-i] = token[i].
  "  la t0, stal_token_le; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t3, stal_token; la t4, stal_token_le; la t0, stal_alen; ld t2, 0(t0); li t1, 0\n" ++
  ".Lstal_addr_rev:\n" ++
  "  beq t1, t2, .Lstal_addr_rev_done\n" ++
  "  add t5, t3, t1; lbu t6, 0(t5)\n" ++          -- token[i] (big-endian byte i)
  "  sub t5, t2, t1; addi t5, t5, -1\n" ++         -- L-1-i
  "  add t5, t4, t5; sb t6, 0(t5)\n" ++            -- token_le[L-1-i] = token[i]
  "  addi t1, t1, 1; j .Lstal_addr_rev\n" ++
  ".Lstal_addr_rev_done:\n" ++
  -- w35wj: also seed the access-list ACCOUNT address into the EIP-2929 runtime
  -- account warm table. execution-specs warms access_list_addresses before
  -- execution (fork.py:1085-1091), so the first account-touching opcode
  -- (BALANCE/EXTCODE*/CALL/EIP-7702 delegation access/...) on a listed account is
  -- charged WARM (100), not COLD (2600). Without this the guest over-charges the
  -- regular gas by the 2500 cold delta vs the spec on any tx with an access list.
  -- stal_token holds the 20-byte BE address in bytes 0..19, matching
  -- runtime_access_account_seed's expectation; the seed preserves s4..s9 (saves
  -- only s0..s3), so the slot loop below is intact. Idempotent / table-full safe.
  "  la a0, stal_token; la a1, evm_access_account_table\n" ++
  "  la a2, evm_access_account_count; li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_seed\n" ++
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
  "  la t0, stal_koff; ld t1, 0(t0); add t1, s6, t1   # slot content ptr (big-endian, <=32B)\n" ++
  -- bal_2930: build the 32-byte LITTLE-ENDIAN slot key the SLOAD/SSTORE handler uses
  -- (the EVM stack stores the slot value low-byte-first). The RLP slot is big-endian
  -- with leading zeros stripped (length stal_klen): slot_le[klen-1-i] = slot_be[i].
  -- Guard klen > 32 (malformed/adversarial RLP): skip this key (a missed warm seed only
  -- over-charges, never under-charges) rather than overflow the 32-byte slot buffer.
  "  la t0, stal_klen; ld t2, 0(t0); li t5, 32; bgtu t2, t5, .Lstal_slot_skip\n" ++
  "  la t0, stal_slot_le; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t3, stal_slot_le; li t4, 0\n" ++
  ".Lstal_slot_rev:\n" ++
  "  beq t4, t2, .Lstal_slot_rev_done\n" ++
  "  add t5, t1, t4; lbu t6, 0(t5)\n" ++          -- slot_be[i]
  "  sub t5, t2, t4; addi t5, t5, -1\n" ++         -- klen-1-i
  "  add t5, t3, t5; sb t6, 0(t5)\n" ++            -- slot_le[klen-1-i] = slot_be[i]
  "  addi t4, t4, 1; j .Lstal_slot_rev\n" ++
  ".Lstal_slot_rev_done:\n" ++
  "  la a0, stal_token_le; la a1, stal_slot_le\n" ++
  "  jal ra, evm_storage_access_seed_key\n" ++
  ".Lstal_slot_skip:\n" ++
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
  "stal_token:\n  .zero 32\n" ++
  -- bal_2930 (bv_fail=41): storage-key warm set keys on env.ADDRESS (the 20-byte
  -- address as a little-endian 256-bit word: low 20 bytes = address reversed) and
  -- the slot in EVM stack order (little-endian). The RLP access list gives both
  -- big-endian, so the storage-key seed needs an LE address token + a 32-byte LE
  -- slot that MATCH the SLOAD/SSTORE lookup key (the account-warm seed above keeps
  -- the canonical-BE stal_token, which is the format runtime_access_account_charge
  -- expects).
  ".balign 8\n" ++
  "stal_token_le:\n  .zero 32\n" ++
  "stal_slot_le:\n  .zero 32\n"


/-! ## tx_access_list_span

    Calling convention:
      a0 (input)  : encoded transaction ptr
      a1 (input)  : encoded transaction byte length
      a2 (input)  : out ptr for access_list ptr (u64)
      a3 (input)  : out ptr for access_list length (u64)
      ra (input)  : return
      a0 (output) : 0 typed tx with access_list span; 1 legacy/no access_list;
                    2 malformed or unsupported typed transaction

    The returned span is the whole encoded access_list item, including its RLP
    list prefix, so callers can pass it directly to `seed_tx_access_list`. -/
def txAccessListSpanFunction : String :=
  "tx_access_list_span:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # span ptr out\n" ++
  "  mv s3, a3                   # span len out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, txal_type; la a3, txal_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltxal_fail\n" ++
  "  la t0, txal_type; ld s4, 0(t0)\n" ++
  "  la t0, txal_inner_off; ld t1, 0(t0)\n" ++
  "  beqz s4, .Ltxal_none\n" ++
  "  add s5, s0, t1              # inner ptr\n" ++
  "  sub s6, s1, t1              # inner len\n" ++
  "  li t0, 1\n" ++
  "  beq s4, t0, .Ltxal_type1\n" ++
  "  li t0, 2\n" ++
  "  beq s4, t0, .Ltxal_type2\n" ++
  "  li t0, 3\n" ++
  "  beq s4, t0, .Ltxal_type3\n" ++
  "  li t0, 4\n" ++
  "  beq s4, t0, .Ltxal_type4\n" ++
  "  j .Ltxal_fail\n" ++
  ".Ltxal_type1:\n" ++
  "  mv a0, s5; mv a1, s6; la a2, txal_decode\n" ++
  "  jal ra, tx_eip2930_decode\n" ++
  "  bnez a0, .Ltxal_fail\n" ++
  "  la t0, txal_decode; ld t1, 128(t0); ld t2, 136(t0)\n" ++
  "  j .Ltxal_have_span\n" ++
  ".Ltxal_type2:\n" ++
  "  mv a0, s5; mv a1, s6; la a2, txal_decode\n" ++
  "  jal ra, tx_eip1559_decode\n" ++
  "  bnez a0, .Ltxal_fail\n" ++
  "  la t0, txal_decode; ld t1, 160(t0); ld t2, 168(t0)\n" ++
  "  j .Ltxal_have_span\n" ++
  ".Ltxal_type3:\n" ++
  "  mv a0, s5; mv a1, s6; la a2, txal_decode\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltxal_fail\n" ++
  "  la t0, txal_decode; lwu t1, 152(t0); lwu t2, 156(t0)\n" ++
  "  j .Ltxal_have_span\n" ++
  ".Ltxal_type4:\n" ++
  "  mv a0, s5; mv a1, s6; la a2, txal_decode\n" ++
  "  jal ra, tx_eip7702_decode\n" ++
  "  bnez a0, .Ltxal_fail\n" ++
  "  la t0, txal_decode; lwu t1, 152(t0); lwu t2, 156(t0)\n" ++
  ".Ltxal_have_span:\n" ++
  "  add t3, s5, t1\n" ++
  "  sd t3, 0(s2); sd t2, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Ltxal_ret\n" ++
  ".Ltxal_none:\n" ++
  "  li a0, 1\n" ++
  "  j .Ltxal_ret\n" ++
  ".Ltxal_fail:\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  li a0, 2\n" ++
  ".Ltxal_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

def txAccessListSpanDataSection : String :=
  ".balign 8\n" ++
  "txal_type:\n  .zero 8\n" ++
  "txal_inner_off:\n  .zero 8\n" ++
  "txal_span_ptr:\n  .zero 8\n" ++
  "txal_span_len:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "t29_offset:\n  .zero 8\n" ++
  "t29_length:\n  .zero 8\n" ++
  "t1d_offset:\n  .zero 8\n" ++
  "t1d_length:\n  .zero 8\n" ++
  "t48_offset:\n  .zero 8\n" ++
  "t48_length:\n  .zero 8\n" ++
  "t77_offset:\n  .zero 8\n" ++
  "t77_length:\n  .zero 8\n" ++
  "tcbg_blob_fee_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "txal_decode:\n  .zero 248\n"

/-- `zisk_tx_access_list_span`: focused probe.

    Input layout:
      user +0   : encoded transaction byte length (u64)
      user +8   : encoded transaction bytes

    Output layout at 0xa0010000:
      +0  status (0 span / 1 legacy-no-list / 2 malformed)
      +8  access_list offset from encoded transaction base, or 0
      +16 access_list byte length, or 0
      +24 first byte of the access_list span, or 0 -/
def ziskTxAccessListSpanPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000           # input base (8-byte length header at +0)\n" ++
  "  ld a1, 8(s0)                # tx len (user +0)\n" ++
  "  addi a0, s0, 16             # tx ptr (user +8)\n" ++
  "  mv s1, a0                   # save tx ptr\n" ++
  "  la a2, txal_span_ptr; la a3, txal_span_len\n" ++
  "  jal ra, tx_access_list_span\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  la t1, txal_span_ptr; ld t2, 0(t1)\n" ++
  "  la t1, txal_span_len; ld t3, 0(t1)\n" ++
  "  bnez a0, .Ltxal_probe_zero\n" ++
  "  sub t4, t2, s1\n" ++
  "  sd t4, 8(t0)\n" ++
  "  sd t3, 16(t0)\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  sd t5, 24(t0)\n" ++
  "  j .Ltxal_pdone\n" ++
  ".Ltxal_probe_zero:\n" ++
  "  sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  j .Ltxal_pdone\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  -- Cursor-walk RLP primitives required by the tx decoders below
  -- (the decoders now use the single-pass walker; mirror it here so the
  -- standalone probe links, as the guest closure is not bundled).
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  rlpContentToU64Function ++ "\n" ++
  rlpContentToU256BeFunction ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  txEip1559DecodeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  txEip7702DecodeFunction ++ "\n" ++
  txAccessListSpanFunction ++ "\n" ++
  ".Ltxal_pdone:"

def ziskTxAccessListSpanDataSection : String :=
  ".section .data\n" ++
  txAccessListSpanDataSection

def ziskTxAccessListSpanProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxAccessListSpanPrologue
  dataAsm     := ziskTxAccessListSpanDataSection
}

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
