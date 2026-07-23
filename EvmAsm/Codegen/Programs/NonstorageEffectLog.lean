/-
  EvmAsm.Codegen.Programs.NonstorageEffectLog

  Per-account NON-STORAGE exec-effect producer (bead bmvmx.1.6.4.4 / i3djw) — the
  execution-derived balance/nonce effect records that c2's all-accounts non-storage
  comparator consumes.

  c2's bal_all_accounts_nonstorage_consistent (#8588) takes an ARRAY of 112-byte
  exec effect records + count, and per-account bal_account_nonstorage_consistent
  (#8586) compares the BAL's declared balance/nonce finals against one such record.
  The record layout (c2#5, keyed by the plain 20-byte big-endian address — NOT
  keccak):
    +0   addr            (20-byte BE in the low/first 20 bytes, padded to 32)
    +32  pre_balance     (32B BE)
    +64  post_balance    (32B BE)
    +96  pre_nonce       (u64)
    +104 post_nonce      (u64)
    = 112 B (fixed stride)

  This module is the PRODUCER: execution appends one record per touched non-recipient
  account (CREATE-created accounts, CALL value-transfer callees, SELFDESTRUCT
  beneficiaries). The verdict then passes (exec_nonstorage_effect_log,
  exec_nonstorage_effect_count) to the all-accounts wrapper. The call sites that
  append (CREATE deposit, CALL value-transfer .61.6.8) + the wrapper wiring land as
  exec produces these effects; this slice is the log + producer + a known-answer
  probe. {sender, recipient, coinbase} are NOT recorded here (the wrapper skips them;
  they are pinned on the gas path).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.CreateCodeEffectLog

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Capacity (entries) of the non-storage effect log — touched non-recipient accounts per tx.
    Set to 65536 (bmvmx.5.5.7.3, final capacity-chain slice): now that BOTH exec-vs-BAL
    comparators are linear — the FORWARD binary-searches the sorted agg (#9018) and the REVERSE
    _covers uses a matched-bitmap over the sorted agg (#9021) — there is no remaining super-linear
    consumer, so the cap can cover the full 200M-gas worst case.

    Worst-case bound: a nonzero value-CALL appends TWO raw records, the caller debit and the callee
    credit (ChildFrameHandlers .61.6.8), while its cheapest regular-gas charge is an existing warm
    account: GAS_WARM_ACCESS(100) + GAS_CALL_VALUE(10300) = 10400. Thus the raw-record upper bound
    from the 200M block regular-gas limit is
      2 * floor(200_000_000 / 10400) = 38_460.
    CREATE and SELFDESTRUCT producer paths are more expensive per emitted effect; withdrawals are
    separately bounded to 16. This uses the regular-gas budget only: EIP-7928 state gas is a
    separate block budget and cannot reduce this bound. 40960 therefore covers the full raw stream
    with substantial margin. The overflow flag remains a fail-closed runtime guard, rather than a
    verdict assumption.

    Cost: the aggregate radix-sort and both comparators iterate over the live `count`, never `cap`,
    so a larger cap is pure reserved BSS (4 × cap×112 ≈ 28 MiB + cap-byte covered[]), comfortably
    inside the ~206 MiB .data→.sszscratch slack (CallFrameLayout). Zero runtime cost for normal
    blocks; 0-regress (buffer-size-only change for any non-overflow block). The
    exec_nonstorage_effect_log / exec_nonstorage_effect_agg / nea_sort_a / nea_sort_b buffers and
    the _covers covered[] bitmap are all sized from this cap, so they scale automatically. -/
def nonstorageEffectLogCap : Nat := 40960

/-! ## record_nonstorage_effect
    Append one per-account balance/nonce effect record (c2#5 layout, 112 B fixed).
    a0 = 20-byte big-endian address ptr   a1 = pre_balance ptr (32B BE)
    a2 = post_balance ptr (32B BE)        a3 = pre_nonce (u64)   a4 = post_nonce (u64)
    Returns a0 = 0 appended / 1 overflow (not written; exec_nonstorage_effect_overflow set).
    Clobbers t0-t6, a0; preserves s-regs (saved). -/
def recordNonstorageEffectFunction : String :=
  "record_nonstorage_effect:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd ra, 40(sp)\n" ++
  "  mv s0, a0                   # addr ptr\n" ++
  "  mv s1, a1                   # pre_balance ptr\n" ++
  "  mv s2, a2                   # post_balance ptr\n" ++
  "  mv s3, a3                   # pre_nonce\n" ++
  "  mv s4, a4                   # post_nonce\n" ++
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0)\n" ++
  "  li t2, " ++ toString nonstorageEffectLogCap ++ "\n" ++
  "  bgeu t1, t2, .Lrnse_overflow\n" ++
  "  li t2, 112; mul t2, t1, t2; la t3, exec_nonstorage_effect_log; add t3, t3, t2   # entry base\n" ++
  "  sd x0, 0(t3); sd x0, 8(t3); sd x0, 16(t3); sd x0, 24(t3)   # zero 32B addr\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lrnse_cpa:\n" ++
  "  beqz t6, .Lrnse_cpa_d\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lrnse_cpa\n" ++
  ".Lrnse_cpa_d:\n" ++
  "  ld t4, 0(s1); sd t4, 32(t3); ld t4, 8(s1); sd t4, 40(t3); ld t4, 16(s1); sd t4, 48(t3); ld t4, 24(s1); sd t4, 56(t3)\n" ++  -- pre_balance
  "  ld t4, 0(s2); sd t4, 64(t3); ld t4, 8(s2); sd t4, 72(t3); ld t4, 16(s2); sd t4, 80(t3); ld t4, 24(s2); sd t4, 88(t3)\n" ++  -- post_balance
  "  sd s3, 96(t3)               # pre_nonce\n" ++
  "  sd s4, 104(t3)              # post_nonce\n" ++
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  -- tqj1m: mirror the comparison trace into the full execution AccountState
  -- journal.  The legacy record remains intact for the BAL comparator until
  -- the final comparison-materialization switch; a bounded journal failure
  -- fails closed through this producer's established overflow path.
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4; jal ra, account_state_record_nonstorage; bnez a0, .Lrnse_overflow\n" ++
  "  li a0, 0\n" ++
  "  j .Lrnse_ret\n" ++
  ".Lrnse_overflow:\n" ++
  "  la t0, exec_nonstorage_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lrnse_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld ra, 40(sp); addi sp, sp, 48\n" ++
  "  ret"

/-! ## nonstorage_effect_latest_balance (yisv8 .spine.1)
    Scan the non-storage effect log from the start, keeping the LAST (most-recent-write-wins)
    record whose 20-byte address matches, and surface its post_balance. This is the BALANCE
    live-value read: an account's current balance during execution = its latest recorded
    post_balance, falling back to the pre-state when no value transfer touched it. Mirrors
    exec_log_latest_value (storage) at the 112-byte non-storage stride.
    a0 = address ptr (32B: 20-byte BE address in bytes 0..19, bytes 20..31 = 0 -- matches the
      record's zero-padded addr@0)   a1 = out ptr (32B BE post_balance, written only on a hit).
    Returns a0 = 1 found / 0 not found (out left untouched on a miss). Leaf; only t-regs + a0-a2. -/
def nonstorageEffectLatestBalance_prog : Program :=
  [ .LI .x31 (0 : Word),
    .AUIPC .x30 (laHi GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.nonstorage_effect_latest_balance + 4)),
    .ADDI .x30 .x30 (laLo GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.nonstorage_effect_latest_balance + 4)),
    .LD .x30 .x30 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.exec_nonstorage_effect_log (GuestAddrs.nonstorage_effect_latest_balance + 16)),
    .ADDI .x12 .x12 (laLo GuestAddrs.exec_nonstorage_effect_log (GuestAddrs.nonstorage_effect_latest_balance + 16)),
    .LI .x5 (0 : Word),
    .BEQ .x5 .x30 (108 : BitVec 13),
    .LI .x6 (112 : Word),
    .MUL .x6 .x5 .x6,
    .ADD .x7 .x12 .x6,
    .LD .x28 .x7 (0 : BitVec 12),
    .LD .x29 .x10 (0 : BitVec 12),
    .BNE .x28 .x29 (76 : BitVec 13),
    .LD .x28 .x7 (8 : BitVec 12),
    .LD .x29 .x10 (8 : BitVec 12),
    .BNE .x28 .x29 (64 : BitVec 13),
    .LD .x28 .x7 (16 : BitVec 12),
    .LD .x29 .x10 (16 : BitVec 12),
    .BNE .x28 .x29 (52 : BitVec 13),
    .LD .x28 .x7 (24 : BitVec 12),
    .LD .x29 .x10 (24 : BitVec 12),
    .BNE .x28 .x29 (40 : BitVec 13),
    .LD .x28 .x7 (64 : BitVec 12),
    .SD .x11 .x28 (0 : BitVec 12),
    .LD .x28 .x7 (72 : BitVec 12),
    .SD .x11 .x28 (8 : BitVec 12),
    .LD .x28 .x7 (80 : BitVec 12),
    .SD .x11 .x28 (16 : BitVec 12),
    .LD .x28 .x7 (88 : BitVec 12),
    .SD .x11 .x28 (24 : BitVec 12),
    .LI .x31 (1 : Word),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-104 : BitVec 21),
    .MV .x10 .x31,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `nonstorageEffectLatestBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def nonstorageEffectLatestBalance_relocs : RelocTable :=
  [ (1, .la .x30 "exec_nonstorage_effect_count"),
    (4, .la .x12 "exec_nonstorage_effect_log") ]

def nonstorageEffectLatestBalanceFunction : String :=
  "nonstorage_effect_latest_balance:\n" ++ emitProgramR nonstorageEffectLatestBalance_prog nonstorageEffectLatestBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `nonstorageEffectLatestBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem nonstorageEffectLatestBalanceFunction_eq_prog :
    nonstorageEffectLatestBalanceFunction = "nonstorage_effect_latest_balance:\n" ++ emitProgramR nonstorageEffectLatestBalance_prog nonstorageEffectLatestBalance_relocs := rfl

#guard nonstorageEffectLatestBalanceFunction.startsWith "nonstorage_effect_latest_balance:\n"
#guard nonstorageEffectLatestBalance_prog.length = 36

/-- `nonstorage_effect_latest_nonce`: bmvmx.5.5.10 — nonce analog of
`nonstorage_effect_latest_balance`. Sequential multi-tx CREATE address
derivation seeds `create_nonce` from the PRE-state witness
(`nonce_at_header_state_root`, ChildFrameCreateTail), and the per-tx
`create_creator_nonce_table` resets at every dispatch (`.61.8a`), so a
contract that CREATEs in tx i and again in tx j would re-derive with the
pre-state nonce. The non-storage effect log already records every creator
nonce bump (NoopHalt drj99.1 5a: pre=create_nonce, post=+1) and every
created-account record (post_nonce=1); the log persists across txs on the
mtx lane (truncated only for FAILED txs, whose nonce bumps revert per
protocol). This reader returns the log's latest post_nonce for an address
(last-write-wins over the whole log); the CREATE seed site consults it
between the witness seed and `create_creator_nonce_use`, so a hit overrides
the pre-state seed and a miss keeps today's behavior. ABI: a0 = address
pointer (only the first 20 bytes are compared — the log record's addr
field is 20B + 12 zero pad), a1 = out-u64 pointer; returns a0 = 1 + latest
post_nonce stored, or 0 when the log has no record. Clobbers a0-a2/t0-t6
(caller saves x10/x12/x13 per the ChildFrameCreateTail idiom). Plain
string (no `_eq_prog` guard): mirrors `nonstorageEffectLatestBalance_prog`'s
scan, last-write-wins by writing on every match. -/
def nonstorageEffectLatestNonceFunction : String :=
  "# a0 = addr ptr (20B compared), a1 = out u64 ptr -> a0 = 1/0\n" ++
  "nonstorage_effect_latest_nonce:\n" ++
  "  la t0, exec_nonstorage_effect_log\n" ++
  "  la t1, exec_nonstorage_effect_count\n  ld t1, 0(t1)\n" ++
  "  li t2, 112\n  mul t1, t1, t2\n  add t1, t0, t1\n" ++
  "  li a2, 0\n" ++
  ".Lneln_scan:\n" ++
  "  beq t0, t1, .Lneln_done\n" ++
  "  ld t3, 0(t0); ld t4, 0(a0); bne t3, t4, .Lneln_next\n" ++
  "  ld t3, 8(t0); ld t4, 8(a0); bne t3, t4, .Lneln_next\n" ++
  "  lw t3, 16(t0); lw t4, 16(a0); bne t3, t4, .Lneln_next\n" ++
  "  ld t3, 104(t0); sd t3, 0(a1)\n" ++
  "  li a2, 1\n" ++
  ".Lneln_next:\n" ++
  "  addi t0, t0, 112\n" ++
  "  j .Lneln_scan\n" ++
  ".Lneln_done:\n" ++
  "  mv a0, a2\n" ++
  "  ret\n"

/-- Data for the non-storage effect log (linked into the dispatcher data section when
    the CREATE/CALL-value append sites land, co-located with the CREATE child data). -/
def nonstorageEffectLogData : String :=
  ".balign 8\n" ++
  "exec_nonstorage_effect_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_overflow:\n  .zero 8\n" ++
  -- bmvmx.5.5.10: out cell for nonstorage_effect_latest_nonce (CREATE seed consult).
  "create_nonce_latest:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "exec_nonstorage_effect_log:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n"

/-- `zisk_nonstorage_effect_log`: known-answer probe. Appends two records and reads
    them back, surfacing to OUTPUT (0xa0010000):
      A = addr 0x11*20, pre_bal 10, post_bal 20, pre_nonce 1, post_nonce 2
      B = addr 0x22*20, pre_bal 0,  post_bal 5,  pre_nonce 0, post_nonce 1
      +0 count(2)  +8 A.pre_bal[31](10)  +16 A.post_bal[31](20)  +24 A.pre_nonce(1)
      +32 A.post_nonce(2)  +40 A.addr[0](0x11)  +48 B.post_bal[31](5)  +56 B.post_nonce(1) -/
def ziskNonstorageEffectLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, exec_nonstorage_effect_count; sd x0, 0(t0)\n" ++
  -- build addr A=0x11*20, B=0x22*20, and the four balance buffers.
  "  la t0, nsel_addr_a; li t1, 20\n" ++
  "1:\n  li t2, 0x11; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 1b\n" ++
  "  la t0, nsel_addr_b; li t1, 20\n" ++
  "2:\n  li t2, 0x22; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 2b\n" ++
  "  la t0, nsel_pa; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); li t1,10; sb t1,31(t0)\n" ++   -- pre_bal A = 10 (BE low byte)
  "  la t0, nsel_qa; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); li t1,20; sb t1,31(t0)\n" ++   -- post_bal A = 20
  "  la t0, nsel_pb; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); sd x0,24(t0)\n" ++              -- pre_bal B = 0
  "  la t0, nsel_qb; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); li t1,5; sb t1,31(t0)\n" ++     -- post_bal B = 5
  "  la a0, nsel_addr_a; la a1, nsel_pa; la a2, nsel_qa; li a3, 1; li a4, 2\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  "  la a0, nsel_addr_b; la a1, nsel_pb; la a2, nsel_qb; li a3, 0; li a4, 1\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  -- read back.
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); sd t1, 0(s0)\n" ++   -- count
  "  la t0, exec_nonstorage_effect_log\n" ++                                  -- record A @ +0
  "  lbu t1, 63(t0); sd t1, 8(s0)\n" ++                                       -- A.pre_balance[31] = 10
  "  lbu t1, 95(t0); sd t1, 16(s0)\n" ++                                      -- A.post_balance[31] = 20
  "  ld t1, 96(t0); sd t1, 24(s0)\n" ++                                       -- A.pre_nonce = 1
  "  ld t1, 104(t0); sd t1, 32(s0)\n" ++                                      -- A.post_nonce = 2
  "  lbu t1, 0(t0); sd t1, 40(s0)\n" ++                                       -- A.addr[0] = 0x11
  "  addi t0, t0, 112\n" ++                                                   -- record B @ +112
  "  lbu t1, 95(t0); sd t1, 48(s0)\n" ++                                      -- B.post_balance[31] = 5
  "  ld t1, 104(t0); sd t1, 56(s0)\n" ++                                      -- B.post_nonce = 1
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lnsel_done\n" ++
  recordNonstorageEffectFunction ++ "\n" ++
  accountStateFindFunction ++ "\n" ++
  accountStateCopyFunction ++ "\n" ++
  accountStateAppendPendingFunction ++ "\n" ++
  accountStateRecordNonstorageFunction ++ "\n" ++
  ".Lnsel_done:"

def ziskNonstorageEffectLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "nsel_addr_a:\n  .zero 20\n" ++
  "nsel_addr_b:\n  .zero 20\n" ++
  ".balign 32\n" ++
  "nsel_pa:\n  .zero 32\n" ++
  "nsel_qa:\n  .zero 32\n" ++
  "nsel_pb:\n  .zero 32\n" ++
  "nsel_qb:\n  .zero 32\n" ++
  nonstorageEffectLogData ++
  codeStateData

def ziskNonstorageEffectLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskNonstorageEffectLogPrologue
  dataAsm     := ziskNonstorageEffectLogDataSection
}

/-! ## nonstorage_effect_aggregate (bmvmx.5.5.7.3)

    Linear (radix-sort + run-compress) replacement for the O(raw*distinct)
    `.Lbv_agg_loop` per-account aggregation in blockVerdictMtxValidationTail.
    Groups 112-byte effect records by their 20-byte address (rec+0), keeping the
    FIRST-seen record's {addr, pre_balance@32, pre_nonce@96} and the LAST-seen
    record's {post_balance@64, post_nonce@104} — identical semantics to the inline
    loop (first-pre / last-post), but O(20*N) instead of O(N^2), so the effect-log
    cap can be lifted toward the 200M worst-case without a step-budget blowup.

    Determinism: a STABLE LSB-first counting radix sort over address bytes 19..0,
    so within each equal-address run the original tx/exec order is preserved
    (run[0] = first-seen, run[last] = last-seen). No hashing => no adversarial
    collision can weaken the downstream A2a comparator.

    Calling convention:
      a0 = raw 112-byte record array ptr
      a1 = raw record count (<= nonstorageEffectLogCap)
      a2 = output 112-byte aggregate array ptr (capacity a4 entries)
      a3 = output distinct-count ptr (u64)
      a4 = output capacity in entries
    Returns a0 = 0 ok, 1 if count > capacity (caller treats as overflow/skip). -/
def nonstorageEffectAggregateFunction : String :=
  "nonstorage_effect_aggregate:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++   -- s0=raw,s1=count,s2=out,s3=outcnt,s4=cap
  "  bgtu s1, s4, .Lnea_cap\n" ++
  "  li t0, " ++ toString nonstorageEffectLogCap ++ "; bgtu s1, t0, .Lnea_cap\n" ++
  "  beqz s1, .Lnea_zero\n" ++
  "  la s5, nea_sort_a; la s6, nea_sort_b\n" ++
  -- copy raw records (112B) into sort_a
  "  li s8, 0\n" ++
  ".Lnea_copy_loop:\n" ++
  "  bgeu s8, s1, .Lnea_copy_done\n" ++
  "  li t0, 112; mul t0, s8, t0; add t1, s0, t0\n" ++
  "  add t3, s5, t0\n" ++
  "  li t4, 0\n" ++
  ".Lnea_copy_bytes:\n" ++
  "  li t5, 112; beq t4, t5, .Lnea_copy_next\n" ++
  "  add t5, t1, t4; lbu t6, 0(t5); add t5, t3, t4; sb t6, 0(t5)\n" ++
  "  addi t4, t4, 1; j .Lnea_copy_bytes\n" ++
  ".Lnea_copy_next:\n" ++
  "  addi s8, s8, 1; j .Lnea_copy_loop\n" ++
  ".Lnea_copy_done:\n" ++
  -- stable LSB-first radix sort, address byte 19 down to 0.
  "  li s7, 19\n" ++
  ".Lnea_pass:\n" ++
  "  la s10, nea_counts; li t0, 0\n" ++
  ".Lnea_zero_counts:\n" ++
  "  li t1, 256; beq t0, t1, .Lnea_count_init\n" ++
  "  slli t2, t0, 3; add t3, s10, t2; sd zero, 0(t3); addi t0, t0, 1; j .Lnea_zero_counts\n" ++
  ".Lnea_count_init:\n" ++
  "  li s8, 0\n" ++
  ".Lnea_count_loop:\n" ++
  "  bgeu s8, s1, .Lnea_prefix_init\n" ++
  "  li t0, 112; mul t0, s8, t0; add t1, s5, t0; add t1, t1, s7; lbu t2, 0(t1)\n" ++
  "  slli t3, t2, 3; add t4, s10, t3; ld t5, 0(t4); addi t5, t5, 1; sd t5, 0(t4)\n" ++
  "  addi s8, s8, 1; j .Lnea_count_loop\n" ++
  ".Lnea_prefix_init:\n" ++
  "  li t0, 0; li t1, 0\n" ++
  ".Lnea_prefix_loop:\n" ++
  "  li t2, 256; beq t0, t2, .Lnea_scatter_init\n" ++
  "  slli t3, t0, 3; add t4, s10, t3; ld t5, 0(t4); sd t1, 0(t4); add t1, t1, t5\n" ++
  "  addi t0, t0, 1; j .Lnea_prefix_loop\n" ++
  ".Lnea_scatter_init:\n" ++
  "  li s8, 0\n" ++
  ".Lnea_scatter_loop:\n" ++
  "  bgeu s8, s1, .Lnea_swap\n" ++
  "  li t0, 112; mul t0, s8, t0; add t1, s5, t0\n" ++
  "  add t2, t1, s7; lbu t2, 0(t2)\n" ++
  "  slli t3, t2, 3; add t4, s10, t3; ld t5, 0(t4); addi t6, t5, 1; sd t6, 0(t4)\n" ++   -- t5 = dst index, counts[byte]++
  "  li t3, 112; mul t5, t5, t3; add t6, s6, t5\n" ++
  "  li t3, 0\n" ++
  ".Lnea_scatter_copy:\n" ++
  "  li t4, 112; beq t3, t4, .Lnea_scatter_next\n" ++
  "  add t4, t1, t3; lbu a0, 0(t4); add t4, t6, t3; sb a0, 0(t4)\n" ++
  "  addi t3, t3, 1; j .Lnea_scatter_copy\n" ++
  ".Lnea_scatter_next:\n" ++
  "  addi s8, s8, 1; j .Lnea_scatter_loop\n" ++
  ".Lnea_swap:\n" ++
  "  mv t0, s5; mv s5, s6; mv s6, t0\n" ++
  "  beqz s7, .Lnea_runs\n" ++
  "  addi s7, s7, -1; j .Lnea_pass\n" ++
  -- compress sorted runs (s5 = final sorted buffer) into the output array.
  ".Lnea_runs:\n" ++
  "  li s7, 0\n" ++                                                 -- distinct count
  "  li s8, 0\n" ++                                                 -- run start index i
  ".Lnea_run_loop:\n" ++
  "  bgeu s8, s1, .Lnea_done\n" ++
  "  li t0, 112; mul t0, s8, t0; add s9, s5, t0\n" ++              -- s9 = &run_start
  "  addi s10, s8, 1\n" ++                                          -- j = scan index
  ".Lnea_run_scan:\n" ++
  "  bgeu s10, s1, .Lnea_run_emit\n" ++
  "  li t0, 112; mul t0, s10, t0; add t1, s5, t0\n" ++
  "  li t2, 0\n" ++
  ".Lnea_run_eqcmp:\n" ++
  "  li t3, 20; beq t2, t3, .Lnea_run_eq\n" ++
  "  add t3, s9, t2; lbu t4, 0(t3); add t3, t1, t2; lbu t5, 0(t3); bne t4, t5, .Lnea_run_emit\n" ++
  "  addi t2, t2, 1; j .Lnea_run_eqcmp\n" ++
  ".Lnea_run_eq:\n" ++
  "  addi s10, s10, 1; j .Lnea_run_scan\n" ++
  ".Lnea_run_emit:\n" ++                                            -- run = [s8, s10); last = s5[s10-1]
  "  li t0, 112; mul t0, s7, t0; add s11, s2, t0\n" ++             -- s11 = &out[distinct]
  "  li t2, 0\n" ++
  ".Lnea_emit_copy:\n" ++
  "  li t3, 112; beq t2, t3, .Lnea_emit_post\n" ++
  "  add t3, s9, t2; lbu t4, 0(t3); add t3, s11, t2; sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1; j .Lnea_emit_copy\n" ++
  ".Lnea_emit_post:\n" ++                                           -- overwrite post_balance@64 (32B) + post_nonce@104 from last
  "  addi t0, s10, -1; li t1, 112; mul t1, t0, t1; add t0, s5, t1\n" ++
  "  ld t1, 64(t0); sd t1, 64(s11); ld t1, 72(t0); sd t1, 72(s11); ld t1, 80(t0); sd t1, 80(s11); ld t1, 88(t0); sd t1, 88(s11); ld t1, 104(t0); sd t1, 104(s11)\n" ++
  "  addi s7, s7, 1\n" ++
  "  mv s8, s10; j .Lnea_run_loop\n" ++
  ".Lnea_done:\n" ++
  "  sd s7, 0(s3); li a0, 0; j .Lnea_ret\n" ++
  ".Lnea_zero:\n" ++
  "  sd zero, 0(s3); li a0, 0; j .Lnea_ret\n" ++
  ".Lnea_cap:\n" ++
  "  li a0, 1\n" ++
  ".Lnea_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- Shared sort scratch for `nonstorage_effect_aggregate` (cap x 112 B each). -/
def nonstorageEffectAggregateScratch : String :=
  -- This is runtime scratch, not initialized input data.  Name the section
  -- explicitly because the main dispatcher appends it while emitting `.data`.
  -- In particular, AccountState's phase alias must cover both radix buffers
  -- in the same NOBITS region.
  ".section .bss, \"aw\", @nobits\n" ++
  ".balign 8\n" ++
  -- The per-transaction AccountState journal is dead before this post-dispatch
  -- radix scratch is first used. Durable AccountState remains separate.
  "account_state_pending:\nnea_sort_a:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n" ++
  "nea_sort_b:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n" ++
  ".set account_state_created, account_state_pending + " ++ toString accountStateTableBytes ++ "\n" ++
  ".set account_state_delete, account_state_pending + " ++ toString (accountStateTableBytes + accountStateCreatedCapacity * 32) ++ "\n" ++
  "nea_counts:\n  .zero 2048\n" ++
  -- Callers append initialized dispatcher storage after this shared scratch.
  ".section .data\n"

/-- `zisk_nonstorage_effect_aggregate`: known-answer probe. Three input records
    (A=0x11.., B=0x22.., A again) exercise dedup with first-pre / last-post:
      A: pre_bal 10, post_bal 20, pre_nonce 1, post_nonce 2
      B: pre_bal 5,  post_bal 8,  pre_nonce 0, post_nonce 1
      A: pre_bal 99, post_bal 30, pre_nonce 9, post_nonce 3   (dup of A)
    Expected aggregate (sorted A<B): count=2;
      A {pre_bal 10, post_bal 30, pre_nonce 1, post_nonce 3};
      B {pre_bal 5,  post_bal 8,  pre_nonce 0, post_nonce 1}.
    OUTPUT (0xa0010000): +0 status +8 count +16 A.pre_bal[31] +24 A.post_bal[31]
      +32 A.pre_nonce +40 A.post_nonce +48 A.addr[0] +56 B.pre_bal[31]
      +64 B.post_bal[31] +72 B.post_nonce +80 B.addr[0]. -/
def ziskNonstorageEffectAggregatePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- zero the 3-record input (336 B) then fill it.
  "  la t0, nea_probe_in; li t1, 42\n" ++
  "1:\n  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, 1b\n" ++
  -- record 0: addr 0x11*20, pre_bal=10, post_bal=20, pre_nonce=1, post_nonce=2
  "  la t0, nea_probe_in; li t2, 20\n" ++
  "2:\n  li t1, 0x11; sb t1, 0(t0); addi t0, t0, 1; addi t2, t2, -1; bnez t2, 2b\n" ++
  "  la t0, nea_probe_in; li t1, 10; sb t1, 63(t0); li t1, 20; sb t1, 95(t0); li t1, 1; sd t1, 96(t0); li t1, 2; sd t1, 104(t0)\n" ++
  -- record 1 @112: addr 0x22*20, pre_bal=5, post_bal=8, pre_nonce=0, post_nonce=1
  "  la t0, nea_probe_in; addi t0, t0, 112; li t2, 20\n" ++
  "3:\n  li t1, 0x22; sb t1, 0(t0); addi t0, t0, 1; addi t2, t2, -1; bnez t2, 3b\n" ++
  "  la t0, nea_probe_in; addi t0, t0, 112; li t1, 5; sb t1, 63(t0); li t1, 8; sb t1, 95(t0); sd zero, 96(t0); li t1, 1; sd t1, 104(t0)\n" ++
  -- record 2 @224: addr 0x11*20 (dup A), pre_bal=99, post_bal=30, pre_nonce=9, post_nonce=3
  "  la t0, nea_probe_in; addi t0, t0, 224; li t2, 20\n" ++
  "4:\n  li t1, 0x11; sb t1, 0(t0); addi t0, t0, 1; addi t2, t2, -1; bnez t2, 4b\n" ++
  "  la t0, nea_probe_in; addi t0, t0, 224; li t1, 99; sb t1, 63(t0); li t1, 30; sb t1, 95(t0); li t1, 9; sd t1, 96(t0); li t1, 3; sd t1, 104(t0)\n" ++
  -- call aggregate
  "  la a0, nea_probe_in; li a1, 3; la a2, nea_probe_out; la a3, nea_probe_cnt; li a4, " ++ toString nonstorageEffectLogCap ++ "\n" ++
  "  jal ra, nonstorage_effect_aggregate\n" ++
  "  sd a0, 0(s0)\n" ++                                             -- status
  "  la t0, nea_probe_cnt; ld t1, 0(t0); sd t1, 8(s0)\n" ++         -- distinct count
  "  la t0, nea_probe_out\n" ++                                     -- out[0] = A
  "  lbu t1, 63(t0); sd t1, 16(s0)\n" ++                            -- A.pre_bal[31]
  "  lbu t1, 95(t0); sd t1, 24(s0)\n" ++                            -- A.post_bal[31]
  "  ld t1, 96(t0); sd t1, 32(s0)\n" ++                             -- A.pre_nonce
  "  ld t1, 104(t0); sd t1, 40(s0)\n" ++                            -- A.post_nonce
  "  lbu t1, 0(t0); sd t1, 48(s0)\n" ++                             -- A.addr[0]
  "  la t0, nea_probe_out; addi t0, t0, 112\n" ++                   -- out[1] = B
  "  lbu t1, 63(t0); sd t1, 56(s0)\n" ++                            -- B.pre_bal[31]
  "  lbu t1, 95(t0); sd t1, 64(s0)\n" ++                            -- B.post_bal[31]
  "  ld t1, 104(t0); sd t1, 72(s0)\n" ++                            -- B.post_nonce
  "  lbu t1, 0(t0); sd t1, 80(s0)\n" ++                             -- B.addr[0]
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lnea_probe_done\n" ++
  nonstorageEffectAggregateFunction ++ "\n" ++
  ".Lnea_probe_done:"

def ziskNonstorageEffectAggregateDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "nea_probe_in:\n  .zero 336\n" ++
  "nea_probe_out:\n  .zero 336\n" ++
  "nea_probe_cnt:\n  .zero 8\n" ++
  nonstorageEffectAggregateScratch

def ziskNonstorageEffectAggregateProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskNonstorageEffectAggregatePrologue
  dataAsm     := ziskNonstorageEffectAggregateDataSection
}

end EvmAsm.Codegen
