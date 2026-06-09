/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageConsistent

  `bal_account_nonstorage_consistent` (bead i3djw / bmvmx.1.6.4.4 step .2) — the
  per-account NON-storage exec-vs-BAL FINAL comparator, the non-storage analog of
  the storage comparators bal_storage_matches_exec_log (#8564) +
  bal_storage_covers_exec_log (#8569). It parses a BAL AccountChanges' final
  balance/nonce (via bal_account_nonstorage_finals #8584, step .1) and checks them
  against an execution-derived non-storage effect record for the same account.

  SCOPE — this verifies the per-account *block-final* values, in both directions:
    forward : if the BAL declares a final balance/nonce, it must equal the exec
              block-post value (catches a BAL declaring a WRONG final);
    reverse : if exec net-changed the field (block-post != block-pre), the BAL must
              declare it with the right final (catches a BAL OMITTING a real change).
  It deliberately does NOT reject an account whose final equals its pre-value with a
  spurious declaration (a net-zero V->...->V account is final-consistent); the per-tx
  TUPLE-SEQUENCE completeness is a separate layer (bmvmx.1.6.6, gated on the exec log
  carrying a tx index). Code changes are likewise out of scope here — they only occur
  via CREATE/SELFDESTRUCT, verified once that exec lands (i3djw create/delete steps).

  Execution-derived non-storage effect record (112 B, 8-byte aligned; the all-accounts
  wrapper .3 keys BAL accounts to these via addrHash):
    +0   addrHash      (32 B keccak(address))  -- keying for .3; unused here
    +32  pre_balance   (32 B big-endian)
    +64  post_balance  (32 B big-endian)
    +96  pre_nonce     (u64)
    +104 post_nonce    (u64)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_nonstorage_consistent
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = exec non-storage effect record ptr (112 B, layout above)
    a0 (output) = 0 consistent / 1 inconsistent / 2 BAL parse failure.

    Internally calls bal_account_nonstorage_finals into a scratch buffer, then for
    balance and nonce applies the forward+reverse FINAL checks described above. -/
def balAccountNonstorageConsistentFunction : String :=
  "bal_account_nonstorage_consistent:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # exec effect record ptr\n" ++
  "  la s1, c2nsc_finals         # 88-byte finals scratch\n" ++
  "  mv a2, s1                   # finals out = scratch (a0/a1 still AccountChanges ptr/len)\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lc2nsc_parsefail  # BAL parse failure -> 2\n" ++
  "  # ---- balance: reverse (exec changed -> declared) + forward (declared -> BAL==exec post) ----\n" ++
  "  ld t0, 0(s1)                # has_balance\n" ++
  "  addi t2, s0, 32             # exec pre_balance\n" ++
  "  addi t3, s0, 64             # exec post_balance\n" ++
  "  li t1, 0                    # exec_balance_changed\n" ++
  "  ld t4, 0(t2);  ld t5, 0(t3);  bne t4, t5, .Lc2nsc_bal_chg\n" ++
  "  ld t4, 8(t2);  ld t5, 8(t3);  bne t4, t5, .Lc2nsc_bal_chg\n" ++
  "  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lc2nsc_bal_chg\n" ++
  "  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lc2nsc_bal_chg\n" ++
  "  j .Lc2nsc_bal_chk\n" ++
  ".Lc2nsc_bal_chg:\n" ++
  "  li t1, 1\n" ++
  ".Lc2nsc_bal_chk:\n" ++
  "  beqz t1, .Lc2nsc_bal_fwd    # exec unchanged -> no reverse obligation\n" ++
  "  beqz t0, .Lc2nsc_bad        # exec changed but BAL silent -> inconsistent\n" ++
  ".Lc2nsc_bal_fwd:\n" ++
  "  beqz t0, .Lc2nsc_nonce      # BAL silent -> nothing to forward-check\n" ++
  "  addi t2, s1, 8              # BAL final post_balance (32 B BE)\n" ++
  "  addi t3, s0, 64             # exec post_balance\n" ++
  "  ld t4, 0(t2);  ld t5, 0(t3);  bne t4, t5, .Lc2nsc_bad\n" ++
  "  ld t4, 8(t2);  ld t5, 8(t3);  bne t4, t5, .Lc2nsc_bad\n" ++
  "  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lc2nsc_bad\n" ++
  "  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lc2nsc_bad\n" ++
  ".Lc2nsc_nonce:\n" ++
  "  # ---- nonce: reverse + forward, u64 ----\n" ++
  "  ld t0, 40(s1)               # has_nonce\n" ++
  "  ld t2, 96(s0)               # exec pre_nonce\n" ++
  "  ld t3, 104(s0)              # exec post_nonce\n" ++
  "  beq t2, t3, .Lc2nsc_nonce_fwd  # exec unchanged -> no reverse obligation\n" ++
  "  beqz t0, .Lc2nsc_bad           # exec changed but BAL silent -> inconsistent\n" ++
  ".Lc2nsc_nonce_fwd:\n" ++
  "  beqz t0, .Lc2nsc_ok         # BAL silent -> nothing to forward-check\n" ++
  "  ld t4, 48(s1)               # BAL final post_nonce (u64)\n" ++
  "  bne t4, t3, .Lc2nsc_bad\n" ++
  ".Lc2nsc_ok:\n" ++
  "  li a0, 0; j .Lc2nsc_ret\n" ++
  ".Lc2nsc_bad:\n" ++
  "  li a0, 1; j .Lc2nsc_ret\n" ++
  ".Lc2nsc_parsefail:\n" ++
  "  li a0, 2\n" ++
  ".Lc2nsc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_bal_account_nonstorage_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8..16   : AccountChanges byte length
      bytes 16..128 : the 112-byte exec non-storage effect record (8-byte aligned)
      bytes 128..   : the AccountChanges RLP
    Output: bytes 0..8 = status (0 consistent / 1 inconsistent / 2 parse fail). -/
def ziskBalAccountNonstorageConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # AccountChanges len\n" ++
  "  addi a2, a5, 16             # exec effect record ptr (0x40000010, 8-aligned)\n" ++
  "  addi a0, a5, 128            # AccountChanges ptr (0x40000080, 8-aligned)\n" ++
  "  jal ra, bal_account_nonstorage_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lc2nsc_pdone\n" ++
  balAccountNonstorageConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lc2nsc_pdone:"

def ziskBalAccountNonstorageConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "c2nsc_finals:\n  .zero 88\n" ++
  ziskBalAccountNonstorageFinalsDataSection  -- c2nsf_* + rfu_* scratch for the inlined finals helper

def ziskBalAccountNonstorageConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountNonstorageConsistentPrologue
  dataAsm     := ziskBalAccountNonstorageConsistentDataSection
}

end EvmAsm.Codegen
