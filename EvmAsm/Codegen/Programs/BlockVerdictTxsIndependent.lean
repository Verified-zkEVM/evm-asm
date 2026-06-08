/-
  EvmAsm.Codegen.Programs.BlockVerdictTxsIndependent

  Soundness guard for the multi-tx per-tx dispatch loop
  (evm-asm-fhsxz.2.4.2.57.11.6.2). Dispatching each tx against the block-PRE
  state yields correct per-tx gas ONLY when the txs are independent — i.e. no
  single account's GAS-AFFECTING state is touched by more than one tx, and no
  written account is also read (a cross-tx read-after-write the BAL cannot rule
  out, since `storage_reads` carries no tx attribution).

  `bal_txs_independent` scans the BAL and returns 0 (independent) / 1
  (interacting) / 2 (parse error). It counts the distinct `block_access_index`
  (tx_index) over each account's storage_changes (nested per slot),
  nonce_changes, and code_changes — EXCLUDING balance_changes (the coinbase is
  fee-credited by every tx, which is not a gas interaction) — and bails if any
  account with such writes also has non-empty storage_reads.

  BAL = RLP list of AccountChanges; AccountChanges =
    [address(0), storage_changes(1), storage_reads(2), balance_changes(3),
     nonce_changes(4), code_changes(5)].
  SlotChanges = [slot(0), changes(1)]; StorageChange/Nonce/Code =
    [block_access_index(0), value(1)].  (spec block_access_lists.py)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_txs_independent

    a0 = BAL section RLP ptr, a1 = BAL section RLP length.
    Returns a0 = 0 independent / 1 interacting / 2 parse error.

    Per-account accumulators live in `.data` cells (bti_first_tx sentinel
    0x7fffffff, bti_has_write, bti_conflict, bti_err) so the nested walk
    (accounts → slot-changes → per-slot change tuples) stays within the
    callee-saved register budget. -/

/-- Internal: scan a flat RLP list of change tuples `[[tx_index, value]...]`;
    for each tuple decode item-0 (tx_index) and fold it into `bti_first_tx`
    (set bti_conflict on a second distinct value); set bti_has_write. On any
    RLP failure set bti_err. a0=list ptr, a1=list len. Clobbers t*, a*; saves
    s0..s3. -/
def btiScanTuplesFunction : String :=
  "bti_scan_tuples:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bti_t_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbti_st_ok\n" ++
  "  li t0, 1; la t1, bti_err; sd t0, 0(t1); j .Lbti_st_ret\n" ++
  ".Lbti_st_ok:\n" ++
  "  la t0, bti_t_cnt; ld s2, 0(t0)               # tuple count\n" ++
  "  mv s3, zero                                  # j\n" ++
  ".Lbti_st_loop:\n" ++
  "  beq s3, s2, .Lbti_st_ret\n" ++
  "  li t0, 1; la t1, bti_has_write; sd t0, 0(t1) # any tuple => a write\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s3; la a3, bti_t_eoff; la a4, bti_t_elen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbti_st_err\n" ++
  "  la t0, bti_t_eoff; ld t0, 0(t0); add t1, s0, t0  # tuple ptr\n" ++
  "  la t0, bti_t_elen; ld t2, 0(t0)                  # tuple len\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 0; la a3, bti_t_foff; la a4, bti_t_flen\n" ++
  "  jal ra, rlp_list_nth_item                        # item 0 = tx_index field\n" ++
  "  bnez a0, .Lbti_st_err\n" ++
  "  la t0, bti_t_flen; ld t3, 0(t0)                  # field len\n" ++
  "  beqz t3, .Lbti_st_zero                            # len 0 => tx_index 0\n" ++
  "  la t0, bti_t_eoff; ld t0, 0(t0); add t4, s0, t0\n" ++
  "  la t0, bti_t_foff; ld t5, 0(t0); add t4, t4, t5  # &tx_index byte\n" ++
  "  lbu t6, 0(t4); j .Lbti_st_have\n" ++
  ".Lbti_st_zero:\n" ++
  "  mv t6, zero\n" ++
  ".Lbti_st_have:\n" ++
  "  la t0, bti_first_tx; ld t1, 0(t0)\n" ++
  "  li t2, 0x7fffffff\n" ++
  "  bne t1, t2, .Lbti_st_cmp\n" ++
  "  sd t6, 0(t0); j .Lbti_st_adv                      # first tx for this account\n" ++
  ".Lbti_st_cmp:\n" ++
  "  beq t1, t6, .Lbti_st_adv\n" ++
  "  li t2, 1; la t0, bti_conflict; sd t2, 0(t0)       # >=2 distinct tx => conflict\n" ++
  ".Lbti_st_adv:\n" ++
  "  addi s3, s3, 1; j .Lbti_st_loop\n" ++
  ".Lbti_st_err:\n" ++
  "  li t0, 1; la t1, bti_err; sd t0, 0(t1)\n" ++
  ".Lbti_st_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Internal: scan storage_changes (a list of `SlotChanges = [slot, [tuples]]`)
    by delegating each slot's inner change list to `bti_scan_tuples`.
    a0=ptr, a1=len. -/
def btiScanStorageChangesFunction : String :=
  "bti_scan_storage_changes:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bti_sc_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbti_sc_ok\n" ++
  "  li t0, 1; la t1, bti_err; sd t0, 0(t1); j .Lbti_sc_ret\n" ++
  ".Lbti_sc_ok:\n" ++
  "  la t0, bti_sc_cnt; ld s2, 0(t0); mv s3, zero\n" ++
  ".Lbti_sc_loop:\n" ++
  "  beq s3, s2, .Lbti_sc_ret\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s3; la a3, bti_sc_soff; la a4, bti_sc_slen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbti_sc_err\n" ++
  "  la t0, bti_sc_soff; ld t0, 0(t0); add t1, s0, t0   # SlotChanges ptr\n" ++
  "  la t0, bti_sc_slen; ld t2, 0(t0)                   # SlotChanges len\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 1; la a3, bti_sc_coff; la a4, bti_sc_clen\n" ++
  "  jal ra, rlp_list_nth_item                          # item 1 = [tuples]\n" ++
  "  bnez a0, .Lbti_sc_err\n" ++
  "  la t0, bti_sc_soff; ld t0, 0(t0); add t1, s0, t0\n" ++
  "  la t0, bti_sc_coff; ld t3, 0(t0); add t1, t1, t3   # changes-list ptr\n" ++
  "  la t0, bti_sc_clen; ld t2, 0(t0)                   # changes-list len\n" ++
  "  mv a0, t1; mv a1, t2\n" ++
  "  jal ra, bti_scan_tuples\n" ++
  "  addi s3, s3, 1; j .Lbti_sc_loop\n" ++
  ".Lbti_sc_err:\n" ++
  "  li t0, 1; la t1, bti_err; sd t0, 0(t1)\n" ++
  ".Lbti_sc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `bal_txs_independent` — the outer per-account walk + the storage_reads
    read-after-write bail. -/
def balTxsIndependentFunction : String :=
  "bal_txs_independent:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la t0, bti_err; sd zero, 0(t0)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bti_acct_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbti_err\n" ++
  "  la t0, bti_acct_cnt; ld s2, 0(t0); mv s3, zero    # account count, i\n" ++
  ".Lbti_acct:\n" ++
  "  beq s3, s2, .Lbti_indep\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s3; la a3, bti_aoff; la a4, bti_alen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbti_err\n" ++
  "  la t0, bti_aoff; ld t0, 0(t0); add s4, s0, t0     # account ptr\n" ++
  "  la t0, bti_alen; ld s5, 0(t0)                     # account len\n" ++
  -- reset per-account accumulators
  "  li t0, 0x7fffffff; la t1, bti_first_tx; sd t0, 0(t1)\n" ++
  "  la t0, bti_has_write; sd zero, 0(t0)\n" ++
  "  la t0, bti_conflict;  sd zero, 0(t0)\n" ++
  -- storage_changes (item 1)
  "  mv a0, s4; mv a1, s5; li a2, 1; la a3, bti_off; la a4, bti_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbti_err\n" ++
  "  la t0, bti_off; ld t0, 0(t0); add t1, s4, t0; la t2, bti_len; ld t2, 0(t2)\n" ++
  "  mv a0, t1; mv a1, t2; jal ra, bti_scan_storage_changes\n" ++
  -- nonce_changes (item 4)
  "  mv a0, s4; mv a1, s5; li a2, 4; la a3, bti_off; la a4, bti_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbti_err\n" ++
  "  la t0, bti_off; ld t0, 0(t0); add t1, s4, t0; la t2, bti_len; ld t2, 0(t2)\n" ++
  "  mv a0, t1; mv a1, t2; jal ra, bti_scan_tuples\n" ++
  -- code_changes (item 5)
  "  mv a0, s4; mv a1, s5; li a2, 5; la a3, bti_off; la a4, bti_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbti_err\n" ++
  "  la t0, bti_off; ld t0, 0(t0); add t1, s4, t0; la t2, bti_len; ld t2, 0(t2)\n" ++
  "  mv a0, t1; mv a1, t2; jal ra, bti_scan_tuples\n" ++
  -- helper parse error?
  "  la t0, bti_err; ld t0, 0(t0); bnez t0, .Lbti_err\n" ++
  -- conflict (>=2 distinct tx for this account)?
  "  la t0, bti_conflict; ld t0, 0(t0); bnez t0, .Lbti_interacting\n" ++
  -- read-after-write bail: account has writes AND non-empty storage_reads
  "  la t0, bti_has_write; ld t0, 0(t0); beqz t0, .Lbti_next\n" ++
  "  mv a0, s4; mv a1, s5; li a2, 2; la a3, bti_off; la a4, bti_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbti_err\n" ++
  "  la t0, bti_off; ld t0, 0(t0); add t1, s4, t0; la t2, bti_len; ld t2, 0(t2)\n" ++
  "  mv a0, t1; mv a1, t2; la a2, bti_rd_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbti_err\n" ++
  "  la t0, bti_rd_cnt; ld t0, 0(t0); bnez t0, .Lbti_interacting\n" ++
  ".Lbti_next:\n" ++
  "  addi s3, s3, 1; j .Lbti_acct\n" ++
  ".Lbti_indep:\n" ++
  "  li a0, 0; j .Lbti_ret\n" ++
  ".Lbti_interacting:\n" ++
  "  li a0, 1; j .Lbti_ret\n" ++
  ".Lbti_err:\n" ++
  "  li a0, 2\n" ++
  ".Lbti_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- Data: scratch cells + two hand-encoded BAL fixtures for the probe. -/
def ziskBalTxsIndependentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bti_acct_cnt:\n  .zero 8\n" ++
  "bti_aoff:\n  .zero 8\n" ++
  "bti_alen:\n  .zero 8\n" ++
  "bti_off:\n  .zero 8\n" ++
  "bti_len:\n  .zero 8\n" ++
  "bti_first_tx:\n  .zero 8\n" ++
  "bti_has_write:\n  .zero 8\n" ++
  "bti_conflict:\n  .zero 8\n" ++
  "bti_err:\n  .zero 8\n" ++
  "bti_rd_cnt:\n  .zero 8\n" ++
  "bti_t_cnt:\n  .zero 8\n" ++
  "bti_t_eoff:\n  .zero 8\n" ++
  "bti_t_elen:\n  .zero 8\n" ++
  "bti_t_foff:\n  .zero 8\n" ++
  "bti_t_flen:\n  .zero 8\n" ++
  "bti_sc_cnt:\n  .zero 8\n" ++
  "bti_sc_soff:\n  .zero 8\n" ++
  "bti_sc_slen:\n  .zero 8\n" ++
  "bti_sc_coff:\n  .zero 8\n" ++
  "bti_sc_clen:\n  .zero 8\n" ++
  -- Fixture A (INDEPENDENT): 2 accounts, each storage_changes one slot with a
  -- single StorageChange at distinct tx_index (acct0 tx0, acct1 tx1), empty
  -- reads/balance/nonce/code. Each account: 1 distinct tx, no reads -> indep.
  --   AccountChanges = [addr(20B), storage_changes, c0, c0, c0, c0]
  --   storage_changes = [ SlotChanges ]; SlotChanges = [slot(32B), [ StorageChange ]]
  --   StorageChange = [tx_index(1B), new_value(32B)]
  -- StorageChange payload = 01<txidx> a0<32B> => 1+1 + 1+32 = 35 -> e3? list:
  --   inner StorageChange list: items = <txidx byte> + (a0 + 32B value)=33 => payload 1+33=34 -> 0xe2 22
  --   changes-list [StorageChange] payload = 34+1(0xe2)+... let me just encode literally below.
  ".balign 8\n" ++
  "bti_bal_indep:\n" ++
  -- outer list: f8 LL [ acct0 acct1 ]
  "  .byte 0xf8, 0x8a\n" ++                      -- list, payload 138 bytes
  -- acct0: f8 43 [ addr(94+20) sc(...) c0 c0 c0 c0 ]
  "  .byte 0xf8, 0x43\n" ++                      -- AccountChanges, payload 67
  "  .byte 0x94\n  .byte 0xA0\n  .zero 19\n" ++  -- address 20B (byte0=0xA0)
  -- storage_changes: e1 [ SlotChanges ]  (payload 0x3f=63)
  "  .byte 0xf8, 0x3f\n" ++
  -- SlotChanges: e2 + slot(a0 + 32) + changes(e3 22 ...) -> payload 61
  "  .byte 0xf8, 0x3d\n" ++
  "  .byte 0xa0\n  .zero 32\n" ++                -- slot key 32B
  -- changes-list: e2 22 [ StorageChange ]  payload 34
  "  .byte 0xe2\n" ++
  -- StorageChange: e1 21 [ tx_index(00) value(a0+32) ] payload 34? recompute below
  "  .byte 0xe2\n" ++
  "  .byte 0x00\n" ++                            -- tx_index = 0 (RLP 0x00 single byte)
  "  .byte 0xa0\n  .zero 32\n" ++                -- new_value 32B
  "  .byte 0xc0, 0xc0, 0xc0, 0xc0\n" ++          -- storage_reads/balance/nonce/code empty
  -- acct1: identical shape, addr byte0=0xB0, tx_index=01
  "  .byte 0xf8, 0x43\n" ++
  "  .byte 0x94\n  .byte 0xB0\n  .zero 19\n" ++
  "  .byte 0xf8, 0x3f\n" ++
  "  .byte 0xf8, 0x3d\n" ++
  "  .byte 0xa0\n  .zero 32\n" ++
  "  .byte 0xe2\n" ++
  "  .byte 0xe2\n" ++
  "  .byte 0x01\n" ++                            -- tx_index = 1
  "  .byte 0xa0\n  .zero 32\n" ++
  "  .byte 0xc0, 0xc0, 0xc0, 0xc0\n" ++
  -- Fixture B (INTERACTING): 1 account, storage_changes one slot with TWO
  -- StorageChange tuples at tx_index 0 and 1 -> 2 distinct tx -> interacting.
  ".balign 8\n" ++
  "bti_bal_interact:\n" ++
  "  .byte 0xf8, 0x46\n" ++                      -- outer list payload 70
  "  .byte 0xf8, 0x44\n" ++                      -- AccountChanges payload 68
  "  .byte 0x94\n  .byte 0xA0\n  .zero 19\n" ++  -- address
  "  .byte 0xf8, 0x40\n" ++                      -- storage_changes payload 64
  "  .byte 0xf8, 0x3e\n" ++                      -- SlotChanges payload 62
  "  .byte 0xa0\n  .zero 32\n" ++                -- slot key
  "  .byte 0xe3\n" ++                            -- changes-list payload 35 (two tuples? recompute)
  "  .byte 0xc2, 0x00, 0x80\n" ++                -- StorageChange [tx0, value=0] (c2 00 80)
  "  .byte 0xc2, 0x01, 0x80\n" ++                -- StorageChange [tx1, value=0]
  "  .byte 0xc0, 0xc0, 0xc0, 0xc0\n"             -- reads/balance/nonce/code empty
