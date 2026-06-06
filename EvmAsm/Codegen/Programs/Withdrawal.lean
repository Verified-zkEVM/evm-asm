/-
  EvmAsm.Codegen.Programs.Withdrawal

  EIP-4895 Withdrawal helpers extracted from `EvmAsm.Codegen.Programs`
  per the file-size hard cap. Hosts the canonical Withdrawal record
  encoder and its keccak-hash shortcut:

    K130  withdrawal_rlp_encode
    K132  withdrawal_compute_hash

  Both helpers are referenced by the withdrawal pipeline (K49 / K65 /
  K77 / K78) in `Programs/Block.lean` and by the withdrawals-MPT-root
  validators in `Programs/Mpt.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Block

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## withdrawal_rlp_encode -- PR-K130

    RLP-encode an EIP-4895 `Withdrawal`:

      Withdrawal = [index, validator_index, address, amount]

    Field types:
    - index           : u64 (RLP uint, canonical form)
    - validator_index : u64 (RLP uint, canonical form)
    - address         : 20-byte bytestring (0x94 prefix + 20 bytes)
    - amount          : u64 in Gwei (RLP uint, canonical form)

    Output is the full `rlp.encode(withdrawal)` bytes — a short
    list (payload always < 56 bytes), so the outer prefix is the
    1-byte `0xc0 + payload_len` form.

    Used by:
    - the withdrawals MPT root computation (value field of each
      `[rlp(i), rlp(withdrawal)]` leaf)
    - PR-K77 `process_withdrawal`'s receipt-log path
    - block-body re-serialization

    Composes:
      - PR-K30 `rlp_encode_uint_be` — for u64 uint fields
      - hardcoded `0x94 || address` — for the 20-byte string field
      - 1-byte list prefix — computed inline

    Calling convention:
      a0 (input)  : index (u64)
      a1 (input)  : validator_index (u64)
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : amount (u64, Gwei)
      a4 (input)  : output bytes ptr (caller supplies ≥ 56 bytes)
      a5 (input)  : u64 out ptr (output byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function). -/
def withdrawalRlpEncodeFunction : String :=
  "withdrawal_rlp_encode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # index\n" ++
  "  mv s1, a1                   # validator_index\n" ++
  "  mv s2, a2                   # address ptr\n" ++
  "  mv s3, a3                   # amount\n" ++
  "  mv s4, a4                   # output bytes ptr\n" ++
  "  mv s5, a5                   # output length out\n" ++
  "  # Write index as 8 BE bytes to wre_idx_be, then RLP-encode.\n" ++
  "  la t0, wre_idx_be\n" ++
  "  srli t1, s0, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s0, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s0, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s0, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s0, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s0, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s0,  8; sb t1, 6(t0)\n" ++
  "  sb s0, 7(t0)\n" ++
  "  mv a0, t0\n" ++
  "  li a1, 8\n" ++
  "  la a2, wre_idx_rlp\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, wre_idx_len\n" ++
  "  sd a0, 0(t0)                # save returned length\n" ++
  "  # Write validator_index as 8 BE bytes.\n" ++
  "  la t0, wre_val_be\n" ++
  "  srli t1, s1, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s1, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s1, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s1, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s1, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s1, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s1,  8; sb t1, 6(t0)\n" ++
  "  sb s1, 7(t0)\n" ++
  "  mv a0, t0\n" ++
  "  li a1, 8\n" ++
  "  la a2, wre_val_rlp\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, wre_val_len\n" ++
  "  sd a0, 0(t0)\n" ++
  "  # Write amount as 8 BE bytes.\n" ++
  "  la t0, wre_amt_be\n" ++
  "  srli t1, s3, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s3, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s3, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s3, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s3, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s3, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s3,  8; sb t1, 6(t0)\n" ++
  "  sb s3, 7(t0)\n" ++
  "  mv a0, t0\n" ++
  "  li a1, 8\n" ++
  "  la a2, wre_amt_rlp\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, wre_amt_len\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t0, wre_idx_len; ld t1, 0(t0)\n" ++
  "  la t0, wre_val_len; ld t2, 0(t0)\n" ++
  "  la t0, wre_amt_len; ld t3, 0(t0)\n" ++
  "  add t4, t1, t2\n" ++
  "  addi t4, t4, 21\n" ++
  "  add t4, t4, t3\n" ++
  "  mv s6, t4\n" ++
  "  addi t5, t4, 0xc0\n" ++
  "  sb t5, 0(s4)\n" ++
  "  addi t6, s4, 1\n" ++
  "  la t5, wre_idx_rlp\n" ++
  "  mv t4, t1\n" ++
  ".Lwre_copy_idx:\n" ++
  "  beqz t4, .Lwre_idx_done\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lwre_copy_idx\n" ++
  ".Lwre_idx_done:\n" ++
  "  la t5, wre_val_rlp\n" ++
  "  mv t4, t2\n" ++
  ".Lwre_copy_val:\n" ++
  "  beqz t4, .Lwre_val_done\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lwre_copy_val\n" ++
  ".Lwre_val_done:\n" ++
  "  li t0, 0x94\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t6, t6, 1\n" ++
  "  ld t0,  0(s2); sd t0,  0(t6)\n" ++
  "  ld t0,  8(s2); sd t0,  8(t6)\n" ++
  "  lwu t0, 16(s2); sw t0, 16(t6)\n" ++
  "  addi t6, t6, 20\n" ++
  "  la t5, wre_amt_rlp\n" ++
  "  mv t4, t3\n" ++
  ".Lwre_copy_amt:\n" ++
  "  beqz t4, .Lwre_amt_done\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  sb t0, 0(t6)\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi t6, t6, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lwre_copy_amt\n" ++
  ".Lwre_amt_done:\n" ++
  "  addi t0, s6, 1\n" ++
  "  sd t0, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_withdrawal_rlp_encode`: probe BuildUnit. Reads
    (index, validator_index, amount, address_20B) from host input,
    writes (status, out_len, rlp_bytes...) to OUTPUT.
    Input layout:
      bytes  0.. 8 : index
      bytes  8..16 : validator_index
      bytes 16..24 : amount
      bytes 24..44 : address (20 bytes)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : out_len
      bytes 16..   : withdrawal_rlp bytes -/
def ziskWithdrawalRlpEncodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a0, 8(a6)                # index\n" ++
  "  ld a1, 16(a6)               # validator_index\n" ++
  "  ld a3, 24(a6)               # amount\n" ++
  "  addi a2, a6, 40             # address ptr (INPUT + 40)\n" ++
  "  li a4, 0xa0010010           # out bytes\n" ++
  "  li a5, 0xa0010008           # out_len out\n" ++
  "  jal ra, withdrawal_rlp_encode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwre_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  withdrawalRlpEncodeFunction ++ "\n" ++
  ".Lwre_pdone:"

def ziskWithdrawalRlpEncodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "wre_idx_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_idx_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_idx_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_val_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_amt_len:\n" ++
  "  .zero 8"

def ziskWithdrawalRlpEncodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalRlpEncodePrologue
  dataAsm     := ziskWithdrawalRlpEncodeDataSection
}

/-! ## withdrawal_compute_hash -- PR-K132

    Compute the keccak256 hash of an EIP-4895 Withdrawal record:

      hash = keccak256(rlp.encode([index, validator_index, address, amount]))

    Used as the leaf value when building/walking the withdrawals
    trie, and for receipt-side `process_withdrawal` bookkeeping.
    Direct composition of:

      - PR-K130 `withdrawal_rlp_encode` — produce the RLP bytes
      - PR-K3   `zkvm_keccak256`        — hash them

    Calling convention:
      a0 (input)  : index (u64)
      a1 (input)  : validator_index (u64)
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : amount (u64, Gwei)
      a4 (input)  : 32-byte output ptr (hash)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — both legs are total).

    Uses 64 bytes of `.data` scratch (`wch_rlp_buf` for the encoded
    withdrawal, ≤ 49 bytes max; `wch_rlp_len` for the length). -/
def withdrawalComputeHashFunction : String :=
  "withdrawal_compute_hash:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a4                   # output ptr (stash)\n" ++
  "  # Call withdrawal_rlp_encode(index, validator_idx, addr, amt,\n" ++
  "  #                           wch_rlp_buf, wch_rlp_len)\n" ++
  "  # a0, a1, a2, a3 already hold the four input fields.\n" ++
  "  la a4, wch_rlp_buf\n" ++
  "  la a5, wch_rlp_len\n" ++
  "  jal ra, withdrawal_rlp_encode\n" ++
  "  # Call zkvm_keccak256(wch_rlp_buf, wch_rlp_len, s0)\n" ++
  "  la a0, wch_rlp_buf\n" ++
  "  la t0, wch_rlp_len; ld a1, 0(t0)\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_withdrawal_compute_hash`: probe BuildUnit. Reads
    (index, validator_index, amount, address_20B) from host input,
    writes (status, hash[32]) to OUTPUT (40 bytes total). -/
def ziskWithdrawalComputeHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a0, 8(a6)                # index\n" ++
  "  ld a1, 16(a6)               # validator_index\n" ++
  "  ld a3, 24(a6)               # amount\n" ++
  "  addi a2, a6, 40             # address ptr (INPUT + 40)\n" ++
  "  li a4, 0xa0010008           # 32B hash output\n" ++
  "  jal ra, withdrawal_compute_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwch_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  withdrawalRlpEncodeFunction ++ "\n" ++
  withdrawalComputeHashFunction ++ "\n" ++
  ".Lwch_pdone:"

def ziskWithdrawalComputeHashDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "wre_idx_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_idx_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_idx_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_val_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_val_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wre_amt_rlp:\n" ++
  "  .zero 16\n" ++
  ".balign 8\n" ++
  "wre_amt_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wch_rlp_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "wch_rlp_len:\n" ++
  "  .zero 8"

def ziskWithdrawalComputeHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalComputeHashPrologue
  dataAsm     := ziskWithdrawalComputeHashDataSection
}

/-! ## withdrawal_decode -- PR-K49 4-field withdrawal RLP decoder

    Decode a post-Shanghai Withdrawal record into a flat struct.
    Each withdrawal is an RLP list with 4 fields (Python:
    `ethereum.forks.shanghai.fork_types.Withdrawal`):

      rlp([index, validator_index, address, amount])

    `apply_body` iterates `block.withdrawals`, decodes each one
    via this helper, and applies the credit to the recipient's
    balance (amount is in Gwei).

    Output struct (48 bytes; 8-byte aligned for sd):

       0..  8  index           (u64 LE)
       8.. 16  validator_index (u64 LE)
      16.. 36  address         (20 B)
      36.. 40  zero pad
      40.. 48  amount          (u64 LE; in Gwei)

    Calling convention:
      a0 (input)  : withdrawal_rlp ptr
      a1 (input)  : withdrawal_rlp byte length
      a2 (input)  : 48-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a 4-item list,
                    field too long, or address not 20 bytes). -/
def withdrawalDecodeFunction : String :=
  "withdrawal_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # wd_rlp ptr\n" ++
  "  mv s1, a1                  # wd_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: index (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  # Field 1: validator_index (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  # Field 2: address (20 bytes at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, wd_offset; la a4, wd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  la t0, wd_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lwd_fail\n" ++
  "  la t0, wd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 16\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  # Pad bytes 20..24 of address slot (struct 36..40) are zero (from caller zeroing).\n" ++
  "  # Field 3: amount (u64 at offset 40)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 40\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lwd_ret\n" ++
  ".Lwd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lwd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_withdrawal_decode`: probe BuildUnit. Reads (wd_len,
    wd_bytes) from host input, writes (status, 48-byte struct)
    to OUTPUT. -/
def ziskWithdrawalDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # wd_len\n" ++
  "  addi a0, a3, 16             # wd ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 48 bytes (6 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 6\n" ++
  ".Lwd_zinit:\n" ++
  "  beqz t1, .Lwd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lwd_zinit\n" ++
  ".Lwd_zdone:\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  ".Lwd_pdone:"

def ziskWithdrawalDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8"

def ziskWithdrawalDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalDecodePrologue
  dataAsm     := ziskWithdrawalDecodeDataSection
}

/-! ## process_withdrawal -- PR-K77

    Apply a Shanghai+ Withdrawal credit to a recipient's account
    balance. Per Python's `process_withdrawal`:

      account.balance += withdrawal.amount * 10^9

    The withdrawal amount is denominated in Gwei; the balance is
    in wei. We convert by multiplying by `GWEI_TO_WEI = 10^9`.

    Composes:
      - PR-K56 `u256_from_u64_be` — zero-extend amount to u256
      - PR-K54 `u256_mul_u64_be`  — × 10^9 to convert Gwei → wei
      - PR-K51 `u256_add_be`      — fold credit into balance

    The mul step can't realistically overflow u256: amount ≤ 2^41
    Gwei (full validator balance ~32 ETH ≈ 2^35 Gwei; ≤ 2^41
    even for stake-pool aggregates), so amount × 10^9 < 2^71 ≪
    2^256. The add can't realistically overflow either since
    mainnet total wei < 2^87. Both are checked as safety nets.

    Calling convention:
      a0 (input)  : withdrawal struct ptr (48 B; from PR-K49
                    `withdrawal_decode`, with amount at offset 40)
      a1 (input)  : account.balance ptr (32 B u256 BE; modified
                    in place)
      ra (input)  : return
      a0 (output) : 0 success / 1 overflow on mul or add.

    Uses 32 bytes of `.data` scratch (`pw_amount_wei`) plus the
    40-byte `u256m_acc` scratch from PR-K54. -/
def processWithdrawalFunction : String :=
  "process_withdrawal:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # withdrawal struct ptr\n" ++
  "  mv s1, a1                   # balance ptr\n" ++
  "  # Step 1: zero-extend amount (Gwei) to u256.\n" ++
  "  ld t0, 40(s0)               # amount (u64)\n" ++
  "  mv a0, t0\n" ++
  "  la a1, pw_amount_wei\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  # Step 2: amount_wei = amount × 10^9 (in place).\n" ++
  "  la a0, pw_amount_wei\n" ++
  "  li a1, 1000000000\n" ++
  "  la a2, pw_amount_wei\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lpw_fail\n" ++
  "  # Step 3: balance += amount_wei.\n" ++
  "  mv a0, s1\n" ++
  "  la a1, pw_amount_wei\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lpw_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lpw_ret\n" ++
  ".Lpw_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_process_withdrawal`: probe BuildUnit. Reads (48 B
    withdrawal struct, 32 B initial balance) from host input;
    copies initial balance to OUTPUT + 8, calls
    process_withdrawal on it, then writes status to OUTPUT. -/
def ziskProcessWithdrawalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8              # withdrawal struct ptr\n" ++
  "  li a1, 0xa0010008           # balance buffer at OUTPUT + 8\n" ++
  "  # Copy initial balance (input offset 48..80) to OUTPUT + 8.\n" ++
  "  addi t0, a2, 56             # initial balance ptr\n" ++
  "  ld t1,  0(t0); sd t1,  0(a1)\n" ++
  "  ld t1,  8(t0); sd t1,  8(a1)\n" ++
  "  ld t1, 16(t0); sd t1, 16(a1)\n" ++
  "  ld t1, 24(t0); sd t1, 24(a1)\n" ++
  "  jal ra, process_withdrawal\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpw_pdone\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  processWithdrawalFunction ++ "\n" ++
  ".Lpw_pdone:"

def ziskProcessWithdrawalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "pw_amount_wei:\n" ++
  "  .zero 32"

def ziskProcessWithdrawalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskProcessWithdrawalPrologue
  dataAsm     := ziskProcessWithdrawalDataSection
}

/-! ## process_withdrawals_block -- PR-K78

    Iterate over a block's RLP-encoded withdrawals list and apply
    each Gwei→wei credit to a parallel pre-fetched balance array.
    Mirrors the inner loop of Python's `apply_body`:

      for wd in block.withdrawals:
          process_withdrawal(state, wd)

    Caller responsibilities:
      1. Pre-fetch the current balance of each withdrawal recipient
         from the state trie (via PR-K28 `account_at_address` etc.)
         into a parallel `balances[N]` array (each 32 B u256 BE).
      2. After this helper returns, write each updated `balances[i]`
         back to state (via the still-pending MPT mutation path).

    The parallel-array indirection lets this PR ship without
    requiring the MPT mutation infrastructure that
    `compute_state_root_and_trie_changes` will add.

    Composes:
      - PR-K47 `rlp_list_count_items` — outer cardinality
      - PR-K20 `rlp_list_nth_item`    — per-entry bounds
      - PR-K49 `withdrawal_decode`    — extract amount
      - PR-K77 `process_withdrawal`   — credit `balances[i]`

    Calling convention:
      a0 (input)  : withdrawals_rlp ptr
      a1 (input)  : withdrawals_rlp byte length
      a2 (input)  : balances array ptr (N × 32 B; in-place updated)
      ra (input)  : return
      a0 (output) :
        0  : success (every entry credited)
        1  : RLP parse failure at outer count or entry walk
        2  : `withdrawal_decode` failed on an entry
        3  : `process_withdrawal` overflow on credit step

    Uses 64 bytes of `.data` scratch (`pwb_count`,
    `pwb_entry_offset`, `pwb_entry_length`, `pwb_struct[48]`)
    plus `pw_amount_wei` and `u256m_acc` carried in from K77. -/
def processWithdrawalsBlockFunction : String :=
  "process_withdrawals_block:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # rlp_ptr\n" ++
  "  mv s1, a1                   # rlp_len\n" ++
  "  mv s2, a2                   # balances ptr\n" ++
  "  # Step 1: count outer entries\n" ++
  "  la a2, pwb_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lpwb_fail_parse\n" ++
  "  la t0, pwb_count; ld s3, 0(t0)\n" ++
  "  li s5, 0                    # current entry index i\n" ++
  ".Lpwb_loop:\n" ++
  "  beq s5, s3, .Lpwb_done\n" ++
  "  # Get entry i bounds\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, pwb_entry_offset\n" ++
  "  la a4, pwb_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lpwb_fail_parse\n" ++
  "  # Decode entry into pwb_struct (48 B)\n" ++
  "  la t0, pwb_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, pwb_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  la a2, pwb_struct\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  bnez a0, .Lpwb_fail_decode\n" ++
  "  # process_withdrawal(struct, &balances[i])\n" ++
  "  la a0, pwb_struct\n" ++
  "  # balances[i] = s2 + i * 32\n" ++
  "  slli s4, s5, 5\n" ++
  "  add a1, s2, s4\n" ++
  "  jal ra, process_withdrawal\n" ++
  "  bnez a0, .Lpwb_fail_credit\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lpwb_loop\n" ++
  ".Lpwb_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_parse:\n" ++
  "  li a0, 1\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_decode:\n" ++
  "  li a0, 2\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_credit:\n" ++
  "  li a0, 3\n" ++
  ".Lpwb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_process_withdrawals_block`: probe BuildUnit. Reads
    (wd_count u64, balances initial N × 32 B, rlp_len u64,
    rlp_bytes) from host input. Writes (status, balances after
    credits) to OUTPUT. -/
def ziskProcessWithdrawalsBlockPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld t1, 8(a4)                # wd_count (N)\n" ++
  "  # Copy initial balances (input offset 16..16+N*32) to OUTPUT + 8.\n" ++
  "  addi t2, a4, 16             # source ptr\n" ++
  "  li t3, 0xa0010008           # dst ptr\n" ++
  "  slli t4, t1, 5              # N × 32 bytes\n" ++
  "  add t5, t3, t4              # dst end\n" ++
  ".Lpwb_copy:\n" ++
  "  beq t3, t5, .Lpwb_copy_done\n" ++
  "  ld t6, 0(t2)\n" ++
  "  sd t6, 0(t3)\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, 8\n" ++
  "  j .Lpwb_copy\n" ++
  ".Lpwb_copy_done:\n" ++
  "  # Now read rlp_len and rlp ptr.\n" ++
  "  add t0, a4, t4              # 0x40000000 + 16 + N*32\n" ++
  "  ld a1, 16(t0)               # rlp_len at offset 16+N*32\n" ++
  "  addi a0, t0, 24             # rlp ptr after the length\n" ++
  "  li a2, 0xa0010008           # balances array\n" ++
  "  jal ra, process_withdrawals_block\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpwb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  processWithdrawalFunction ++ "\n" ++
  processWithdrawalsBlockFunction ++ "\n" ++
  ".Lpwb_pdone:"

def ziskProcessWithdrawalsBlockDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "pw_amount_wei:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "pwb_count:\n" ++
  "  .zero 8\n" ++
  "pwb_entry_offset:\n" ++
  "  .zero 8\n" ++
  "pwb_entry_length:\n" ++
  "  .zero 8\n" ++
  "pwb_struct:\n" ++
  "  .zero 48"

def ziskProcessWithdrawalsBlockProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskProcessWithdrawalsBlockPrologue
  dataAsm     := ziskProcessWithdrawalsBlockDataSection
}

/-! ## withdrawals_sum_amounts -- PR-K65 block withdrawal-credit total

    Walk an RLP-encoded list of Shanghai+ Withdrawal records
    (one Withdrawal = `rlp([index, validator_index, address,
    amount])`) and return the total of all `amount` fields
    (in Gwei) as a `u64`.

    Used by `apply_body` to compute the block's total
    withdrawal credit before applying it to recipient
    balances — useful as a sanity check against the
    `withdrawals_root` MPT computation and for tracking
    coinbase credits per block.

    First multi-helper composition on the K-stack:
    - PR-K47 `rlp_list_count_items` — outer cardinality
    - PR-K20 `rlp_list_nth_item` — per-entry bounds
    - PR-K49 `withdrawal_decode` — extract `amount` (u64 at
      struct offset 40)

    Each entry's `amount` is added to a u64 accumulator with
    overflow detection (unsigned-wrap check: if `sum < prev`,
    we overflowed). On overflow the function returns status=2
    so the caller can react (in practice withdrawals per block
    are capped at 16 with amounts ≤ ~2^41 Gwei, so overflow
    can't occur on valid chains, but the check makes garbage
    input safe).

    Calling convention:
      a0 (input)  : withdrawals_rlp ptr
      a1 (input)  : withdrawals_rlp byte length
      a2 (input)  : u64 out ptr (sum of all amounts in Gwei)
      ra (input)  : return
      a0 (output) :
        0  : success
        1  : parse fail (output zeroed)
        2  : sum overflowed u64 (output zeroed)

    Uses 64 bytes of `.data` scratch
    (`wsa_count`, `wsa_entry_offset`, `wsa_entry_length`,
    `wsa_struct[48]`). -/
def withdrawalsSumAmountsFunction : String :=
  "withdrawals_sum_amounts:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # rlp_ptr\n" ++
  "  mv s1, a1                   # rlp_len\n" ++
  "  mv s2, a2                   # out_ptr\n" ++
  "  # Step 1: count = rlp_list_count_items(...)\n" ++
  "  la a2, wsa_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  la t0, wsa_count; ld s3, 0(t0)\n" ++
  "  li s4, 0                    # acc (u64)\n" ++
  "  li s5, 0                    # i\n" ++
  ".Lwsa_loop:\n" ++
  "  beq s5, s3, .Lwsa_done\n" ++
  "  # Step 2: get entry i bounds.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, wsa_entry_offset\n" ++
  "  la a4, wsa_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  # Step 3: decode entry into wsa_struct.\n" ++
  "  la t0, wsa_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, wsa_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  la a2, wsa_struct\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  # Step 4: accumulate amount (at struct offset 40) with overflow.\n" ++
  "  la t0, wsa_struct; ld t1, 40(t0)\n" ++
  "  add t2, s4, t1\n" ++
  "  bltu t2, s4, .Lwsa_overflow\n" ++
  "  mv s4, t2\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwsa_loop\n" ++
  ".Lwsa_done:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lwsa_ret\n" ++
  ".Lwsa_overflow:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lwsa_ret\n" ++
  ".Lwsa_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lwsa_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_withdrawals_sum_amounts`: probe BuildUnit. Reads
    (rlp_len, rlp_bytes) from host input, writes (status, sum)
    to OUTPUT (16 bytes total). -/
def ziskWithdrawalsSumAmountsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # rlp_len\n" ++
  "  addi a0, a3, 16             # rlp ptr\n" ++
  "  li a2, 0xa0010008           # out ptr\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwsa_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  ".Lwsa_pdone:"

def ziskWithdrawalsSumAmountsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48"

def ziskWithdrawalsSumAmountsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalsSumAmountsPrologue
  dataAsm     := ziskWithdrawalsSumAmountsDataSection
}

/-! ## block_withdrawals_total -- PR-K85

    Extract the withdrawals sub-list from a block body RLP and
    return the total of all withdrawal `amount` fields (in Gwei)
    as a u64.

    Composes:
      - PR-K83 `block_body_decode` — split body → 3 (off, len) pairs
      - PR-K65 `withdrawals_sum_amounts` — sum amount across the
        decoded withdrawals sub-list

    Useful for cross-checking block-level invariants (e.g., the
    `withdrawals_root` MPT computation) and for receipt analysis.

    Status encoding lets callers floor(status / 100) to identify
    the failing step:

      0          : success — total written to *out
      1          : block_body_decode failed (not a 3-item list)
      101..102   : withdrawals_sum_amounts failed
                   (101 = parse error, 102 = u64 overflow)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out ptr (total Gwei across all
                    withdrawals)
      ra (input)  : return
      a0 (output) : composite status code.

    Uses 48 bytes of `.data` scratch (`bwt_struct`) — separate
    from K83's probe-only struct so the two compose cleanly. -/
def blockWithdrawalsTotalFunction : String :=
  "block_withdrawals_total:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # out ptr\n" ++
  "  # Step 1: block_body_decode\n" ++
  "  la a2, bwt_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbwt_body_fail\n" ++
  "  # Step 2: withdrawals_sum_amounts on withdrawals sub-list.\n" ++
  "  la t0, bwt_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  beqz a0, .Lbwt_ret\n" ++
  "  li t3, 100\n" ++
  "  add a0, a0, t3              # 1 → 101, 2 → 102\n" ++
  "  j .Lbwt_ret\n" ++
  ".Lbwt_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbwt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_withdrawals_total`: probe BuildUnit. Reads
    (body_len, body_bytes) from host input, writes (status,
    total_gwei u64) to OUTPUT (16 bytes total). -/
def ziskBlockWithdrawalsTotalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # out ptr\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, block_withdrawals_total\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbwt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockWithdrawalsTotalFunction ++ "\n" ++
  ".Lbwt_pdone:"

def ziskBlockWithdrawalsTotalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bwt_struct:\n" ++
  "  .zero 48"

def ziskBlockWithdrawalsTotalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockWithdrawalsTotalPrologue
  dataAsm     := ziskBlockWithdrawalsTotalDataSection
}

end EvmAsm.Codegen
