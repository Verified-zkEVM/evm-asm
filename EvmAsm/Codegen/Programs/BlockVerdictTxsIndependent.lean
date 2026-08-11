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

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! Probe-only local PC placeholder for the unlinked tuple scanner. -/
def btiScanTuplesPc : Nat := 0x80000000

/-! ## bal_txs_independent

    a0 = BAL section RLP ptr, a1 = BAL section RLP length.
    Returns a0 = 0 independent / 1 interacting / 2 parse error.

    Per-account accumulators live in `.data` cells (bti_first_tx sentinel
    0x7fffffff, bti_has_write, bti_conflict, bti_err) so the nested walk
    (accounts → slot-changes → per-slot change tuples) stays within the
    callee-saved register budget. -/

/-- Internal: scan a flat RLP list of change tuples `[[tx_index, value]...]`;
    for each tuple decode item-0 (tx_index) and fold it into `bti_first_tx`
    (set bti_conflict on a second distinct value); set bti_has_write ONLY when
    tx_index != 0 (fhsxz.2.4.2.57.11.6.3.3: EIP-7928 system-tx writes at index 0
    do not count toward the storage_reads read-after-write bail; conflict still
    counts all indices). On any RLP failure set bti_err. a0=list ptr, a1=list
    len. Clobbers t*, a*; saves s0..s3. -/
def btiScanTuples_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (btiScanTuplesPc + 24)),
    .BEQ .x12 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .AUIPC .x6 (laHi 0 (btiScanTuplesPc + 36)),
    .ADDI .x6 .x6 (laLo 0 (btiScanTuplesPc + 36)),
    .SD .x6 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (btiScanTuplesPc + 228) (btiScanTuplesPc + 48)),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .BEQ .x8 .x9 (brOff (btiScanTuplesPc + 228) (btiScanTuplesPc + 60)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (btiScanTuplesPc + 72)),
    .BNE .x11 .x0 (brOff (btiScanTuplesPc + 212) (btiScanTuplesPc + 76)),
    .MV .x8 .x10,
    .SUB .x18 .x10 .x12,
    .MV .x19 .x12,
    .MV .x10 .x18,
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (btiScanTuplesPc + 100)),
    .BNE .x12 .x0 (brOff (btiScanTuplesPc + 212) (btiScanTuplesPc + 104)),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (btiScanTuplesPc + 108)),
    .BNE .x11 .x0 (brOff (btiScanTuplesPc + 212) (btiScanTuplesPc + 112)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (btiScanTuplesPc + 124)),
    .BNE .x11 .x0 (brOff (btiScanTuplesPc + 212) (btiScanTuplesPc + 128)),
    .MV .x31 .x10,
    .BEQ .x31 .x0 (20 : BitVec 13),
    .LI .x5 (1 : Word),
    .AUIPC .x6 (laHi 0 (btiScanTuplesPc + 144)),
    .ADDI .x6 .x6 (laLo 0 (btiScanTuplesPc + 144)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi 0 (btiScanTuplesPc + 156)),
    .ADDI .x5 .x5 (laLo 0 (btiScanTuplesPc + 156)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (524288 : BitVec 20),
    .ADDIW .x7 .x7 (-1 : BitVec 12),
    .BNE .x6 .x7 (12 : BitVec 13),
    .SD .x5 .x31 (0 : BitVec 12),
    .JAL .x0 (24 : BitVec 21),
    .BEQ .x6 .x31 (20 : BitVec 13),
    .LI .x7 (1 : Word),
    .AUIPC .x5 (laHi 0 (btiScanTuplesPc + 196)),
    .ADDI .x5 .x5 (laLo 0 (btiScanTuplesPc + 196)),
    .SD .x5 .x7 (0 : BitVec 12),
    .JAL .x0 (jalOff (btiScanTuplesPc + 60) (btiScanTuplesPc + 208)),
    .LI .x5 (1 : Word),
    .AUIPC .x6 (laHi 0 (btiScanTuplesPc + 216)),
    .ADDI .x6 .x6 (laLo 0 (btiScanTuplesPc + 216)),
    .SD .x6 .x5 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `btiScanTuples_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def btiScanTuples_relocs : RelocTable :=
  [ (6, .jal .x1 "rlp_walk_init"),
    (9, .la .x6 "bti_err"),
    (18, .jal .x1 "rlp_walk_next"),
    (25, .jal .x1 "rlp_walk_init"),
    (27, .jal .x1 "rlp_walk_next"),
    (31, .jal .x1 "rlp_content_to_u64"),
    (36, .la .x6 "bti_has_write"),
    (39, .la .x5 "bti_first_tx"),
    (49, .la .x5 "bti_conflict"),
    (54, .la .x6 "bti_err") ]

def btiScanTuplesFunction : String :=
  "bti_scan_tuples:\n" ++ emitProgramR btiScanTuples_prog btiScanTuples_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `btiScanTuples_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem btiScanTuplesFunction_eq_prog :
    btiScanTuplesFunction = "bti_scan_tuples:\n" ++ emitProgramR btiScanTuples_prog btiScanTuples_relocs := rfl

#guard btiScanTuplesFunction.startsWith "bti_scan_tuples:\n"
#guard btiScanTuples_prog.length = 64
/-- Internal: scan storage_changes (a list of `SlotChanges = [slot, [tuples]]`)
    by delegating each slot's inner change list to `bti_scan_tuples`.
    a0=ptr, a1=len.
    Probe-only after #11183 (0 guest jal to bal_txs_independent). String body
    (not `_prog`/GuestAddrs) so unlink from guest does not break Lean. -/
def btiScanStorageChangesFunction : String :=
  "bti_scan_storage_changes:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  beqz a2, .Lbtxi_sc_ok\n" ++
  "  li t0, 1; la t1, bti_err; sd t0, 0(t1); j .Lbtxi_sc_ret\n" ++
  ".Lbtxi_sc_ok:\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  ".Lbtxi_sc_loop:\n" ++
  "  beq s0, s1, .Lbtxi_sc_ret\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbtxi_sc_err\n" ++
  "  mv s0, a0; sub s2, a0, a2; mv s3, a2              # SlotChanges ptr/len\n" ++
  "  mv a0, s2; mv a1, s3; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbtxi_sc_err\n" ++
  "  mv s3, a1                                         # SlotChanges end\n" ++
  "  jal ra, rlp_walk_next                              # item 0 = slot\n" ++
  "  bnez a1, .Lbtxi_sc_err\n" ++
  "  mv a1, s3\n" ++
  "  jal ra, rlp_walk_next                              # item 1 = [tuples]\n" ++
  "  bnez a1, .Lbtxi_sc_err\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, bti_scan_tuples\n" ++
  "  j .Lbtxi_sc_loop\n" ++
  ".Lbtxi_sc_err:\n" ++
  "  li t0, 1; la t1, bti_err; sd t0, 0(t1)\n" ++
  ".Lbtxi_sc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

#guard btiScanStorageChangesFunction.startsWith "bti_scan_storage_changes:\n"

/-- `bal_txs_independent` — the outer per-account walk + the storage_reads
    read-after-write bail. -/
def balTxsIndependentFunction : String :=
  "bal_txs_independent:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  la t0, bti_err; sd zero, 0(t0)\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbtxi_err\n" ++
  "  mv s0, a0; mv s1, a1                 # BAL cursor/end\n" ++
  ".Lbtxi_acct:\n" ++
  "  beq s0, s1, .Lbtxi_indep\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbtxi_err\n" ++
  "  mv s0, a0; sub s4, a0, a2; mv s5, a2              # AccountChanges ptr/len\n" ++
  -- reset per-account accumulators
  "  li t0, 0x7fffffff; la t1, bti_first_tx; sd t0, 0(t1)\n" ++
  "  la t0, bti_has_write; sd zero, 0(t0)\n" ++
  "  la t0, bti_conflict;  sd zero, 0(t0)\n" ++
  "  mv a0, s4; mv a1, s5; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbtxi_err\n" ++
  "  mv s6, a0; mv s7, a1                 # AccountChanges cursor/end\n" ++
  "  jal ra, rlp_walk_next                # item 0 = address\n" ++
  "  bnez a1, .Lbtxi_err\n" ++
  "  mv s6, a0\n" ++
  -- storage_changes (item 1)
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbtxi_err\n" ++
  "  mv s6, a0; sub a0, a0, a2; mv a1, a2; jal ra, bti_scan_storage_changes\n" ++
  -- storage_reads (item 2) saved for the read-after-write bail
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbtxi_err\n" ++
  "  mv s6, a0; sub s2, a0, a2; mv s3, a2\n" ++
  -- balance_changes (item 3) is ignored for gas independence
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbtxi_err\n" ++
  "  mv s6, a0\n" ++
  -- nonce_changes (item 4)
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbtxi_err\n" ++
  "  mv s6, a0; sub a0, a0, a2; mv a1, a2; jal ra, bti_scan_tuples\n" ++
  -- code_changes (item 5)
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbtxi_err\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, bti_scan_tuples\n" ++
  -- helper parse error?
  "  la t0, bti_err; ld t0, 0(t0); bnez t0, .Lbtxi_err\n" ++
  -- conflict (>=2 distinct tx for this account)?
  "  la t0, bti_conflict; ld t0, 0(t0); bnez t0, .Lbtxi_interacting\n" ++
  -- read-after-write bail: account has writes AND non-empty storage_reads
  "  la t0, bti_has_write; ld t0, 0(t0); beqz t0, .Lbtxi_next\n" ++
  "  mv a0, s2; mv a1, s3; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbtxi_err\n" ++
  "  bne a0, a1, .Lbtxi_interacting\n" ++
  ".Lbtxi_next:\n" ++
  "  j .Lbtxi_acct\n" ++
  ".Lbtxi_indep:\n" ++
  "  li a0, 0; j .Lbtxi_ret\n" ++
  ".Lbtxi_interacting:\n" ++
  "  li a0, 1; j .Lbtxi_ret\n" ++
  ".Lbtxi_err:\n" ++
  "  li a0, 2\n" ++
  ".Lbtxi_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"


/-- Data: scratch cells + two hand-encoded BAL fixtures for the probe. -/
def ziskBalTxsIndependentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bti_first_tx:\n  .zero 8\n" ++
  "bti_has_write:\n  .zero 8\n" ++
  "bti_conflict:\n  .zero 8\n" ++
  "bti_err:\n  .zero 8\n" ++
  -- Fixtures generated by a canonical RLP encoder (see PR notes). BAL =
  -- list[AccountChanges]; AccountChanges=[addr(20B), storage_changes,
  -- storage_reads, balance_changes, nonce_changes, code_changes];
  -- SlotChanges=[slot(32B),[StorageChange...]]; StorageChange=[tx_index,value(32B)].
  -- INDEPENDENT (202 B): 2 accounts, each one slot with a single StorageChange at
  -- a distinct tx_index (acct A=tx0, acct B=tx1), empty reads/bal/nonce/code ->
  -- each account 1 distinct tx, no reads -> independent (expect 0).
  ".balign 8\n" ++
  "bti_bal_indep:\n" ++
  "  .byte 0xf8, 0xc8, 0xf8, 0x62, 0x94, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0xf8, 0x47, 0xf8, 0x45, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0xe3, 0xe2, 0x80, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0xc0, 0xc0, 0xc0, 0xc0, 0xf8, 0x62, 0x94, 0xb0, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0xf8, 0x47, 0xf8, 0x45, 0xa0, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe3, 0xe2, 0x01, 0xa0, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0xc0, 0xc0, 0xc0\n" ++
  -- INTERACTING (138 B): 1 account, one slot with TWO StorageChange tuples at
  -- tx_index 0 and 1 -> 2 distinct tx in one account -> interacting (expect 1).
  ".balign 8\n" ++
  "bti_bal_interact:\n" ++
  "  .byte 0xf8, 0x88, 0xf8, 0x86, 0x94, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0xf8, 0x6b, 0xf8, 0x69, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0xf8, 0x46, 0xe2, 0x80, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0xe2, 0x01, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0xc0, 0xc0, 0xc0, 0xc0\n" ++
  -- SYSTEM-WRITE READ-AFTER-WRITE (135 B, fhsxz.2.4.2.57.11.6.3.3): 1 account, one slot
  -- with a single StorageChange at tx_index 0 (the EIP-7928 SYSTEM tx) AND a non-empty
  -- storage_reads (one slot). Pre-.6.3.3 the index-0 write set has_write -> the read-after-
  -- write bail fired -> interacting; post-.6.3.3 index-0 (system) writes are excluded from
  -- has_write, so a system-write + read with no USER-tx write -> independent (expect 0).
  -- Mirrors the beacon-roots account (0x000f3df6..) in multi_transaction_gas_accounting.
  ".balign 8\n" ++
  "bti_bal_sysread:\n" ++
  "  .byte 0xf8, 0x85, 0xf8, 0x83, 0x94, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0xf8, 0x47, 0xf8, 0x45, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0xe3, 0xe2, 0x80, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0xe1, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00\n" ++
  "  .byte 0xc0, 0xc0, 0xc0\n" ++
  -- Trailing pad: keep the fixtures off the .data/.bss tail boundary (ziskemu
  -- reads the final .data bytes adjacent to __bss_start as 0, which would
  -- corrupt the last fixture's bytes).
  ".balign 8\n" ++
  "bti_tail_pad:\n  .zero 256\n"

/-- `zisk_bal_txs_independent`: probe. Output:
      +0  bal_txs_independent(bti_bal_indep, 202)     (expect 0 = independent)
      +8  bal_txs_independent(bti_bal_interact, 138)  (expect 1 = interacting)
      +16 bal_txs_independent(bti_bal_sysread, 135)   (expect 0; fhsxz.2.4.2.57.11.6.3.3:
          system-tx (index-0) write + storage_read, no user write -> independent) -/
def ziskBalTxsIndependentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la a0, bti_bal_indep; li a1, 202\n" ++
  "  jal ra, bal_txs_independent\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la a0, bti_bal_interact; li a1, 138\n" ++
  "  jal ra, bal_txs_independent\n" ++
  "  sd a0, 8(s0)\n" ++
  "  la a0, bti_bal_sysread; li a1, 135\n" ++
  "  jal ra, bal_txs_independent\n" ++
  "  sd a0, 16(s0)\n" ++
  "  j .Lbtxi_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  btiScanTuplesFunction ++ "\n" ++
  btiScanStorageChangesFunction ++ "\n" ++
  balTxsIndependentFunction ++ "\n" ++
  ".Lbtxi_pdone:"

def ziskBalTxsIndependentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalTxsIndependentPrologue
  dataAsm     := ziskBalTxsIndependentDataSection
}
