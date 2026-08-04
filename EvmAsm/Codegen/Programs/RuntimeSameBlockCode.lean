/-
  EvmAsm.Codegen.Programs.RuntimeSameBlockCode

  Runtime helper for EIP-7702 same-block code observations. EXTCODESIZE,
  EXTCODEHASH, and EXTCODECOPY observe an account's current code. During a
  set-code transaction, that current code can be the 0xef0100||address
  delegation marker even though the pre-state trie still has empty code.

  #11396: reads execution AccountState overlay only — never the
  supplied BAL. Spec pin e5a8caf1b amsterdam fork.py:928-930 builds BAL
  after execution; provided BAL is not an execution input.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## runtime_same_block_delegation_code

    Calling convention:
      a0 = 20-byte address ptr
    Returns:
      a0 = 0 if AccountState has authoritative same-tx code that is either
           empty (cleared EIP-7702 delegation) or exactly a 23-byte EIP-7702
           delegation marker; then rsbd_code_ptr/rsbd_code_len name those bytes.
      a0 = 1 otherwise (caller falls through to ordinary code lookup).

    Source: `account_state_lookup_current` → AccountState pending/durable overlay
    written by `eip7702_auth_state_prepare` / code deposits — not BAL. -/
def runtimeSameBlockDelegationCodeFunction : String :=
  "runtime_same_block_delegation_code:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  jal ra, account_state_lookup_current\n" ++
  -- status 2 = empty-code account (7702 clear) → hit with empty bytes
  "  li t0, 2; beq a0, t0, .Lrsbd_empty_hit\n" ++
  -- status 1 = has code
  "  li t0, 1; bne a0, t0, .Lrsbd_miss\n" ++
  "  mv s1, a1; mv s2, a2\n" ++
  "  beqz s2, .Lrsbd_empty_hit\n" ++
  "  li t0, 23; bne s2, t0, .Lrsbd_miss\n" ++
  "  lbu t0, 0(s1); li t1, 0xef; bne t0, t1, .Lrsbd_miss\n" ++
  "  lbu t0, 1(s1); li t1, 1; bne t0, t1, .Lrsbd_miss\n" ++
  "  lbu t0, 2(s1); bnez t0, .Lrsbd_miss\n" ++
  "  la t0, rsbd_code_ptr; sd s1, 0(t0)\n" ++
  "  la t0, rsbd_code_len; sd s2, 0(t0)\n" ++
  "  li a0, 0; j .Lrsbd_ret\n" ++
  ".Lrsbd_empty_hit:\n" ++
  "  la t0, rsbd_code_ptr; sd zero, 0(t0)\n" ++
  "  la t0, rsbd_code_len; sd zero, 0(t0)\n" ++
  "  li a0, 0; j .Lrsbd_ret\n" ++
  ".Lrsbd_miss:\n" ++
  "  li a0, 1\n" ++
  ".Lrsbd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32; ret\n"

#guard runtimeSameBlockDelegationCodeFunction.startsWith "runtime_same_block_delegation_code:\n"
#guard (runtimeSameBlockDelegationCodeFunction.splitOn "account_state_lookup_current").length == 2
#guard !(runtimeSameBlockDelegationCodeFunction.contains "runtime_current_bal_ptr")
#guard !(runtimeSameBlockDelegationCodeFunction.contains "rlp_list_count_items")
#guard !(runtimeSameBlockDelegationCodeFunction.contains "code_state_lookup_current")

/-- Scratch/output cells. `runtime_current_bal_*` kept zeroed (no producers after
    #11396) so any residual store is inert. `rsbd_hash` / `eahsr_*` / `ecc_*`
    are shared with EXTCODEHASH/COPY handlers. -/
def runtimeSameBlockDelegationCodeData : String :=
  ".balign 8\n" ++
  "runtime_current_bal_ptr:\n  .zero 8\n" ++
  "runtime_current_bal_len:\n  .zero 8\n" ++
  "rsbd_code_ptr:\n  .zero 8\n" ++
  "rsbd_code_len:\n  .zero 8\n" ++
  "rsbd_hash:\n  .zero 32\n" ++
  "eahsr_same_tx_empty_flag:\n  .zero 8\n" ++
  "ecc_old_active:\n  .zero 8\n" ++
  "ecc_same_block_hit:\n  .zero 8\n"

end EvmAsm.Codegen
