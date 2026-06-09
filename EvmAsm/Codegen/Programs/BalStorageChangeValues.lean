/-
  EvmAsm.Codegen.Programs.BalStorageChangeValues

  `bal_storage_change_values` (bead bmvmx.1.6.1) — parse a BAL AccountChanges'
  `storage_changes` into PARALLEL (slot key, final post-value) arrays. This is the
  value-bearing companion to `bal_recipient_storage_keys` (which yields only the
  keys); the post-values are needed by the execution-vs-BAL storage consistency
  check (bmvmx.1.6.2): the verdict will compare these against the exec storage
  log's final per-slot values to reject a BAL that execution would not produce.

  AccountChanges = RLP `[address, storage_changes, storage_reads, balance_changes,
  nonce_changes, code_changes]`. Each `storage_changes` entry is
  `[slot_key, [ [tx_index, new_value] ... ]]`; the slot's POST value is the
  `new_value` of the LAST (highest tx_index) tuple — the others are intermediate
  writes superseded within the block.

  Both keys and values are emitted as 32-byte big-endian, left-padded.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_change_values

    Calling convention:
      a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
      a2 = out keys ptr   (count × 32-byte big-endian slot keys)
      a3 = out values ptr (count × 32-byte big-endian post values)
    Returns:
      a0 = count of (key, value) pairs written (0 on parse failure — conservative).

    For each `storage_changes` entry: key = item 0; value = item 1 of the LAST
    tuple of item 1. Pointers are recomputed after each `rlp_list_nth_item` /
    `rlp_list_count_items` call (those clobber the a/t registers). `s3` (the
    storage_changes list ptr) and the scratch offsets survive across the calls. -/
def balStorageChangeValuesFunction : String :=
  "bal_storage_change_values:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                    # account ptr\n" ++
  "  mv s1, a1                    # account len\n" ++
  "  mv s2, a2                    # out keys ptr\n" ++
  "  la t0, bscv_vptr; sd a3, 0(t0)   # out values ptr (data label, s-regs are full)\n" ++
  -- storage_changes = account item 1.
  "  mv a0, s0; mv a1, s1; li a2, 1; la a3, bscv_scoff; la a4, bscv_sclen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  "  la t0, bscv_scoff; ld t0, 0(t0); add s3, s0, t0   # sc_ptr\n" ++
  "  la t0, bscv_sclen; ld s4, 0(t0)                   # sc_len\n" ++
  "  mv a0, s3; mv a1, s4; la a2, bscv_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  "  la t0, bscv_cnt; ld s5, 0(t0)                     # entry count\n" ++
  "  mv s6, zero                  # i\n" ++
  ".Lbscv_loop:\n" ++
  "  beq s6, s5, .Lbscv_done\n" ++
  -- entry = nth(storage_changes, i).
  "  mv a0, s3; mv a1, s4; mv a2, s6; la a3, bscv_eoff; la a4, bscv_elen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  "  la t0, bscv_eoff; ld t0, 0(t0); add t1, s3, t0    # entry ptr\n" ++
  "  la t0, bscv_elen; ld t2, 0(t0)                    # entry len\n" ++
  -- key = nth(entry, 0).
  "  mv a0, t1; mv a1, t2; li a2, 0; la a3, bscv_koff; la a4, bscv_klen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  "  la t0, bscv_eoff; ld t0, 0(t0); add t1, s3, t0    # recompute entry ptr\n" ++
  "  la t0, bscv_koff; ld t3, 0(t0); add t1, t1, t3    # key bytes ptr\n" ++
  "  la t0, bscv_klen; ld t4, 0(t0)                    # key byte len\n" ++
  "  li t5, 32; bgtu t4, t5, .Lbscv_fail\n" ++
  -- write key into keys[i] (= s2 + i*32), left-padded.
  "  slli t0, s6, 5; add t6, s2, t0                    # key dst base\n" ++
  "  mv t0, t6; li t5, 32\n" ++
  ".Lbscv_kzero:\n" ++
  "  beqz t5, .Lbscv_kzdone\n  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbscv_kzero\n" ++
  ".Lbscv_kzdone:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, t6, t5         # dst = base + (32 - klen)\n" ++
  ".Lbscv_kcopy:\n" ++
  "  beqz t4, .Lbscv_kcdone\n  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbscv_kcopy\n" ++
  ".Lbscv_kcdone:\n" ++
  -- value_list = nth(entry, 1).
  "  la t0, bscv_eoff; ld t0, 0(t0); add t1, s3, t0    # entry ptr\n" ++
  "  la t0, bscv_elen; ld t2, 0(t0)                    # entry len\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 1; la a3, bscv_voff; la a4, bscv_vlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  -- tuple_count = count_items(value_list).
  "  la t0, bscv_eoff; ld t0, 0(t0); add t1, s3, t0\n" ++
  "  la t0, bscv_voff; ld t3, 0(t0); add t1, t1, t3    # value_list ptr\n" ++
  "  la t0, bscv_vlen; ld t2, 0(t0)\n" ++
  "  mv a0, t1; mv a1, t2; la a2, bscv_vcnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  "  la t0, bscv_vcnt; ld t3, 0(t0)\n" ++
  "  beqz t3, .Lbscv_fail                              # no tuples -> malformed\n" ++
  "  addi t3, t3, -1                                   # last tuple index\n" ++
  "  la t0, bscv_lastidx; sd t3, 0(t0)\n" ++
  -- last_tuple = nth(value_list, last).
  "  la t0, bscv_eoff; ld t0, 0(t0); add t1, s3, t0\n" ++
  "  la t0, bscv_voff; ld t3, 0(t0); add t1, t1, t3    # value_list ptr\n" ++
  "  la t0, bscv_vlen; ld t2, 0(t0)\n" ++
  "  la t0, bscv_lastidx; ld a2, 0(t0)\n" ++
  "  mv a0, t1; mv a1, t2; la a3, bscv_toff; la a4, bscv_tlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  -- new_value = nth(last_tuple, 1).
  "  la t0, bscv_eoff; ld t0, 0(t0); add t1, s3, t0\n" ++
  "  la t0, bscv_voff; ld t3, 0(t0); add t1, t1, t3    # value_list ptr\n" ++
  "  la t0, bscv_toff; ld t3, 0(t0); add t1, t1, t3    # tuple ptr\n" ++
  "  la t0, bscv_tlen; ld t2, 0(t0)\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 1; la a3, bscv_noff; la a4, bscv_nlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbscv_fail\n" ++
  "  la t0, bscv_eoff; ld t0, 0(t0); add t1, s3, t0\n" ++
  "  la t0, bscv_voff; ld t3, 0(t0); add t1, t1, t3    # value_list ptr\n" ++
  "  la t0, bscv_toff; ld t3, 0(t0); add t1, t1, t3    # tuple ptr\n" ++
  "  la t0, bscv_noff; ld t3, 0(t0); add t1, t1, t3    # new_value bytes ptr\n" ++
  "  la t0, bscv_nlen; ld t4, 0(t0)                    # new_value byte len\n" ++
  "  li t5, 32; bgtu t4, t5, .Lbscv_fail\n" ++
  -- write value into values[i] (= bscv_vptr + i*32), left-padded.
  "  la t0, bscv_vptr; ld t6, 0(t0); slli t0, s6, 5; add t6, t6, t0   # value dst base\n" ++
  "  mv t0, t6; li t5, 32\n" ++
  ".Lbscv_vzero:\n" ++
  "  beqz t5, .Lbscv_vzdone\n  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbscv_vzero\n" ++
  ".Lbscv_vzdone:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, t6, t5\n" ++
  ".Lbscv_vcopy:\n" ++
  "  beqz t4, .Lbscv_vcdone\n  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbscv_vcopy\n" ++
  ".Lbscv_vcdone:\n" ++
  "  addi s6, s6, 1; j .Lbscv_loop\n" ++
  ".Lbscv_done:\n" ++
  "  mv a0, s5\n" ++
  "  j .Lbscv_ret\n" ++
  ".Lbscv_fail:\n" ++
  "  li a0, 0\n" ++
  ".Lbscv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- Scratch data for `bal_storage_change_values`. -/
def balStorageChangeValuesData : String :=
  ".balign 8\n" ++
  "bscv_vptr:\n  .zero 8\n" ++
  "bscv_scoff:\n  .zero 8\n" ++ "bscv_sclen:\n  .zero 8\n" ++
  "bscv_cnt:\n  .zero 8\n" ++
  "bscv_eoff:\n  .zero 8\n" ++ "bscv_elen:\n  .zero 8\n" ++
  "bscv_koff:\n  .zero 8\n" ++ "bscv_klen:\n  .zero 8\n" ++
  "bscv_voff:\n  .zero 8\n" ++ "bscv_vlen:\n  .zero 8\n" ++
  "bscv_vcnt:\n  .zero 8\n" ++ "bscv_lastidx:\n  .zero 8\n" ++
  "bscv_toff:\n  .zero 8\n" ++ "bscv_tlen:\n  .zero 8\n" ++
  "bscv_noff:\n  .zero 8\n" ++ "bscv_nlen:\n  .zero 8\n"

/-- `zisk_bal_storage_change_values`: probe over a hand-encoded AccountChanges
    with two storage_changes entries:
      slot 0x07 -> [[0, 0x11], [1, 0x22]]   (post value = 0x22, last tuple)
      slot 0x09 -> [[0, 0x33]]              (post value = 0x33)
    Output: +0 count (2); +8 key0[31] (0x07); +16 val0[31] (0x22 = last);
            +24 key1[31] (0x09); +32 val1[31] (0x33). -/
def ziskBalStorageChangeValuesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Build AccountChanges RLP at bscv_acct. storage_changes (item 1) =
  --   [ [07, [[80(=0),11],[01,22]]], [09, [[80,33]]] ]
  -- Encoded inner-first below; we hand-assemble the bytes.
  --   tuple [80,11] = c2 80 11 ; [01,22] = c2 01 22
  --   value_list0 [c2 80 11, c2 01 22] = c6 c2 80 11 c2 01 22
  --   entry0 [07, value_list0] = c8 07 c6 c2 80 11 c2 01 22
  --   tuple [80,33] = c2 80 33 ; value_list1 [c2 80 33] = c3 c2 80 33
  --   entry1 [09, value_list1] = c5 09 c3 c2 80 33
  --   storage_changes = [entry0, entry1] = d0 <entry0(9)> <entry1(6)>  (len 15 -> 0xcf? 9+6=15 -> 0xcf)
  --   actually 0xc0+15 = 0xcf
  --   account = [addr(94+20), storage_changes, c0, c0, c0, c0]
  -- We only need item 1 (storage_changes) parsed; build a minimal account.
  "  la t0, bscv_sc\n" ++
  -- storage_changes list: cf | c8 07 c6 c2 80 11 c2 01 22 | c5 09 c3 c2 80 33
  "  li t1, 0xcf; sb t1, 0(t0)\n" ++
  "  li t1, 0xc8; sb t1, 1(t0); li t1, 0x07; sb t1, 2(t0); li t1, 0xc6; sb t1, 3(t0)\n" ++
  "  li t1, 0xc2; sb t1, 4(t0); li t1, 0x80; sb t1, 5(t0); li t1, 0x11; sb t1, 6(t0)\n" ++
  "  li t1, 0xc2; sb t1, 7(t0); li t1, 0x01; sb t1, 8(t0); li t1, 0x22; sb t1, 9(t0)\n" ++
  "  li t1, 0xc5; sb t1, 10(t0); li t1, 0x09; sb t1, 11(t0); li t1, 0xc3; sb t1, 12(t0)\n" ++
  "  li t1, 0xc2; sb t1, 13(t0); li t1, 0x80; sb t1, 14(t0); li t1, 0x33; sb t1, 15(t0)\n" ++
  -- account = [ <20-byte addr>, storage_changes, c0, c0, c0, c0 ].
  -- addr header 0x94 + 20 zero bytes = 21 bytes; storage_changes = 16 bytes;
  -- four empty lists c0 = 4 bytes; payload = 21+16+4 = 41 (0x29). header f8 29.
  "  la t0, bscv_acct\n" ++
  "  li t1, 0xf8; sb t1, 0(t0); li t1, 0x29; sb t1, 1(t0)\n" ++
  "  li t1, 0x94; sb t1, 2(t0)\n" ++
  "  li t2, 20; addi t3, t0, 3\n" ++
  ".Lbscv_addr0:\n  beqz t2, .Lbscv_addr0d\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j .Lbscv_addr0\n" ++
  ".Lbscv_addr0d:\n" ++
  -- copy the 16-byte storage_changes blob to bscv_acct+23.
  "  la t1, bscv_sc; addi t2, t0, 23; li t3, 16; li t4, 0\n" ++
  ".Lbscv_sccopy:\n  beq t4, t3, .Lbscv_sccopyd\n  add t5, t1, t4; lbu t6, 0(t5); add t5, t2, t4; sb t6, 0(t5); addi t4, t4, 1; j .Lbscv_sccopy\n" ++
  ".Lbscv_sccopyd:\n" ++
  -- four empty lists 0xc0 at +39..+42.
  "  li t1, 0xc0; sb t1, 39(t0); sb t1, 40(t0); sb t1, 41(t0); sb t1, 42(t0)\n" ++
  "  la a0, bscv_acct; li a1, 43; la a2, bscv_okeys; la a3, bscv_ovals\n" ++
  "  jal ra, bal_storage_change_values\n" ++
  "  sd a0, 0(s0)\n" ++                                  -- count (expect 2)
  "  la t0, bscv_okeys; lbu t1, 31(t0); sd t1, 8(s0)\n" ++   -- key0[31] (0x07)
  "  la t0, bscv_ovals; lbu t1, 31(t0); sd t1, 16(s0)\n" ++  -- val0[31] (0x22)
  "  la t0, bscv_okeys; lbu t1, 63(t0); sd t1, 24(s0)\n" ++  -- key1[31] (0x09)
  "  la t0, bscv_ovals; lbu t1, 63(t0); sd t1, 32(s0)\n" ++  -- val1[31] (0x33)
  "  j .Lbscv_probe_done\n" ++
  balStorageChangeValuesFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  ".Lbscv_probe_done:"

def ziskBalStorageChangeValuesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bscv_sc:\n  .zero 64\n" ++
  "bscv_acct:\n  .zero 128\n" ++
  "bscv_okeys:\n  .zero 256\n" ++
  "bscv_ovals:\n  .zero 256\n" ++
  balStorageChangeValuesData

def ziskBalStorageChangeValuesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalStorageChangeValuesPrologue
  dataAsm     := ziskBalStorageChangeValuesDataSection
}

end EvmAsm.Codegen
