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
def runtimeSameBlockDelegationCode_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .JAL .x1 (jalOff GuestAddrs.account_state_lookup_current (GuestAddrs.runtime_same_block_delegation_code + 24)),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (96 : BitVec 13),
    .LI .x5 (1 : Word),
    .BNE .x10 .x5 (120 : BitVec 13),
    .MV .x9 .x11,
    .MV .x18 .x12,
    .BEQ .x18 .x0 (76 : BitVec 13),
    .LI .x5 (23 : Word),
    .BNE .x18 .x5 (100 : BitVec 13),
    .LBU .x5 .x9 (0 : BitVec 12),
    .LI .x6 (239 : Word),
    .BNE .x5 .x6 (88 : BitVec 13),
    .LBU .x5 .x9 (1 : BitVec 12),
    .LI .x6 (1 : Word),
    .BNE .x5 .x6 (76 : BitVec 13),
    .LBU .x5 .x9 (2 : BitVec 12),
    .BNE .x5 .x0 (68 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_ptr (GuestAddrs.runtime_same_block_delegation_code + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_ptr (GuestAddrs.runtime_same_block_delegation_code + 96)),
    .SD .x5 .x9 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_len (GuestAddrs.runtime_same_block_delegation_code + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_len (GuestAddrs.runtime_same_block_delegation_code + 108)),
    .SD .x5 .x18 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (40 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_ptr (GuestAddrs.runtime_same_block_delegation_code + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_ptr (GuestAddrs.runtime_same_block_delegation_code + 128)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rsbd_code_len (GuestAddrs.runtime_same_block_delegation_code + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rsbd_code_len (GuestAddrs.runtime_same_block_delegation_code + 140)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `runtimeSameBlockDelegationCode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def runtimeSameBlockDelegationCode_relocs : RelocTable :=
  [ (6, .jal .x1 "account_state_lookup_current"),
    (24, .la .x5 "rsbd_code_ptr"),
    (27, .la .x5 "rsbd_code_len"),
    (32, .la .x5 "rsbd_code_ptr"),
    (35, .la .x5 "rsbd_code_len") ]

def runtimeSameBlockDelegationCodeFunction : String :=
  "runtime_same_block_delegation_code:\n" ++ emitProgramR runtimeSameBlockDelegationCode_prog runtimeSameBlockDelegationCode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `runtimeSameBlockDelegationCode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem runtimeSameBlockDelegationCodeFunction_eq_prog :
    runtimeSameBlockDelegationCodeFunction = "runtime_same_block_delegation_code:\n" ++ emitProgramR runtimeSameBlockDelegationCode_prog runtimeSameBlockDelegationCode_relocs := rfl

#guard runtimeSameBlockDelegationCodeFunction.startsWith "runtime_same_block_delegation_code:\n"
#guard runtimeSameBlockDelegationCode_prog.length = 47
#guard (runtimeSameBlockDelegationCodeFunction.splitOn "account_state_lookup_current").length == 2
#guard !(runtimeSameBlockDelegationCodeFunction.contains "runtime_current_bal_ptr")
#guard !(runtimeSameBlockDelegationCodeFunction.contains "rlp_list_count_items")
#guard !(runtimeSameBlockDelegationCodeFunction.contains "code_state_lookup_current")

/-- Scratch/output cells. `rsbd_*` / `eahsr_*` / `ecc_*` are shared with
    EXTCODEHASH/COPY handlers. -/
def runtimeSameBlockDelegationCodeData : String :=
  ".balign 8\n" ++
  "rsbd_code_ptr:\n  .zero 8\n" ++
  "rsbd_code_len:\n  .zero 8\n" ++
  "rsbd_hash:\n  .zero 32\n" ++
  "eahsr_same_tx_empty_flag:\n  .zero 8\n" ++
  "ecc_old_active:\n  .zero 8\n" ++
  "ecc_same_block_hit:\n  .zero 8\n"

end EvmAsm.Codegen
