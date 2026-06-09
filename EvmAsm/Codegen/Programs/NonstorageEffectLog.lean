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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Capacity (entries) of the non-storage effect log — touched non-recipient accounts per tx. -/
def nonstorageEffectLogCap : Nat := 64

/-! ## record_nonstorage_effect
    Append one per-account balance/nonce effect record (c2#5 layout, 112 B fixed).
    a0 = 20-byte big-endian address ptr   a1 = pre_balance ptr (32B BE)
    a2 = post_balance ptr (32B BE)        a3 = pre_nonce (u64)   a4 = post_nonce (u64)
    Returns a0 = 0 appended / 1 overflow (not written; exec_nonstorage_effect_overflow set).
    Clobbers t0-t6, a0; preserves s-regs (saved). -/
def recordNonstorageEffectFunction : String :=
  "record_nonstorage_effect:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp); sd s4, 32(sp)\n" ++
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
  "  li a0, 0\n" ++
  "  j .Lrnse_ret\n" ++
  ".Lrnse_overflow:\n" ++
  "  la t0, exec_nonstorage_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lrnse_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); addi sp, sp, 40\n" ++
  "  ret"

/-- Data for the non-storage effect log (linked into the dispatcher data section when
    the CREATE/CALL-value append sites land, co-located with the CREATE child data). -/
def nonstorageEffectLogData : String :=
  ".balign 8\n" ++
  "exec_nonstorage_effect_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_overflow:\n  .zero 8\n" ++
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
  nonstorageEffectLogData

def ziskNonstorageEffectLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskNonstorageEffectLogPrologue
  dataAsm     := ziskNonstorageEffectLogDataSection
}

end EvmAsm.Codegen
