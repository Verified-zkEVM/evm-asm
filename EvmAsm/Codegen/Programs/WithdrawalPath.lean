/-
  EvmAsm.Codegen.Programs.WithdrawalPath

  withdrawal_to_path_delta (bead evm-asm-fhsxz.2.2.1): the non-engine
  preprocessing half of the withdrawal-driven post-state-root recompute
  (.2.2). Given a Shanghai+ withdrawal RLP `rlp([index, validator_index,
  address, amount])`, produce the two things the state-trie update needs:

    * path  = bytes_to_nibbles(keccak256(address))   -- 64 nibbles, the
              account's key path in the world-state trie;
    * delta = amount_gwei * 1e9                       -- 32-byte big-endian
              wei credit to add to the account balance.

  Composes only already-merged, tested helpers: withdrawal_decode
  (Programs/Withdrawal.lean), zkvm_keccak256 (HashBridge), bytes_to_nibbles
  (Programs/Mpt.lean), u256_from_u64_be + u256_mul_u64_be (Programs/U256.lean).

  The full .2.2 then loops: withdrawal_to_path_delta -> mpt_walk (read the
  current account) -> account_add_balance(delta) -> change list -> mpt_state_root
  (those parts wait on the MPT-engine PRs #7743/#7744). This piece is
  independent and verified now. All multi-byte work is on 8-aligned scratch;
  address/hash bytes are read byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.Withdrawal

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## withdrawal_to_path_delta -- withdrawal RLP -> (trie path, wei delta)

    a0 = withdrawal RLP ptr        a1 = withdrawal RLP length
    a2 = out path ptr (64 bytes, one nibble each)
    a3 = out delta ptr (32 bytes, big-endian wei)
    a0 (output) = 0 (ok) / 1 (parse fail or amount*1e9 overflow)

    path  = bytes_to_nibbles(keccak256(address))
    delta = amount_gwei * 1_000_000_000 -/
def withdrawalToPathDelta_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .AUIPC .x12 (laHi GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 24)),
    .ADDI .x12 .x12 (laLo GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 24)),
    .JAL .x1 (jalOff GuestAddrs.withdrawal_decode (GuestAddrs.withdrawal_to_path_delta + 32)),
    .BNE .x10 .x0 (104 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 40)),
    .ADDI .x10 .x10 (laLo GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 40)),
    .ADDI .x10 .x10 (16 : BitVec 12),
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.wtpd_hash (GuestAddrs.withdrawal_to_path_delta + 56)),
    .ADDI .x12 .x12 (laLo GuestAddrs.wtpd_hash (GuestAddrs.withdrawal_to_path_delta + 56)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.withdrawal_to_path_delta + 64)),
    .AUIPC .x10 (laHi GuestAddrs.wtpd_hash (GuestAddrs.withdrawal_to_path_delta + 68)),
    .ADDI .x10 .x10 (laLo GuestAddrs.wtpd_hash (GuestAddrs.withdrawal_to_path_delta + 68)),
    .LI .x11 (32 : Word),
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.withdrawal_to_path_delta + 84)),
    .AUIPC .x5 (laHi GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 88)),
    .LD .x10 .x5 (40 : BitVec 12),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_from_u64_be (GuestAddrs.withdrawal_to_path_delta + 104)),
    .MV .x10 .x9,
    .LUI .x11 (244141 : BitVec 20),
    .ADDIW .x11 .x11 (-1536 : BitVec 12),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be (GuestAddrs.withdrawal_to_path_delta + 124)),
    .BNE .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `withdrawalToPathDelta_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def withdrawalToPathDelta_relocs : RelocTable :=
  [ (6, .la .x12 "wtpd_struct"),
    (8, .jal .x1 "withdrawal_decode"),
    (10, .la .x10 "wtpd_struct"),
    (14, .la .x12 "wtpd_hash"),
    (16, .jal .x1 "zkvm_keccak256"),
    (17, .la .x10 "wtpd_hash"),
    (21, .jal .x1 "bytes_to_nibbles"),
    (22, .la .x5 "wtpd_struct"),
    (26, .jal .x1 "u256_from_u64_be"),
    (31, .jal .x1 "u256_mul_u64_be") ]

def withdrawalToPathDeltaFunction : String :=
  "withdrawal_to_path_delta:\n" ++ emitProgramR withdrawalToPathDelta_prog withdrawalToPathDelta_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `withdrawalToPathDelta_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem withdrawalToPathDeltaFunction_eq_prog :
    withdrawalToPathDeltaFunction = "withdrawal_to_path_delta:\n" ++ emitProgramR withdrawalToPathDelta_prog withdrawalToPathDelta_relocs := rfl

#guard withdrawalToPathDeltaFunction.startsWith "withdrawal_to_path_delta:\n"
#guard withdrawalToPathDelta_prog.length = 41
/-- `zisk_withdrawal_to_path_delta`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  withdrawal RLP length (u64)
      +16 withdrawal RLP bytes
    Output layout:
      OUTPUT+0  : status (0 ok / 1 fail)
      OUTPUT+8  : path (64 nibble bytes)
      OUTPUT+72 : delta (32-byte big-endian wei) -/
def ziskWithdrawalToPathDeltaPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # withdrawal RLP length\n" ++
  "  addi a0, t0, 16             # withdrawal RLP ptr\n" ++
  "  li a2, 0xa0010008           # out path at OUTPUT+8\n" ++
  "  li a3, 0xa0010048           # out delta at OUTPUT+72\n" ++
  "  jal ra, withdrawal_to_path_delta\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)   # status at OUTPUT+0\n" ++
  "  j .Lwtpd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  withdrawalToPathDeltaFunction ++ "\n" ++
  ".Lwtpd_pdone:"

def ziskWithdrawalToPathDeltaDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "wd_offset:\n  .zero 8\n" ++
  "wd_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  ".balign 8\n" ++
  "wtpd_struct:\n  .zero 48\n" ++
  ".balign 32\n" ++
  "wtpd_hash:\n  .zero 32"

def ziskWithdrawalToPathDeltaProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalToPathDeltaPrologue
  dataAsm     := ziskWithdrawalToPathDeltaDataSection
}

end EvmAsm.Codegen
