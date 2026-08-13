/-
  EvmAsm.Codegen.Programs.ChainEndpoints

  Chain-segment trie-root endpoint commitments carved out of
  `EvmAsm.Codegen.Programs.Chain` per the file-size hard cap.
  Hosts:

    K250  chain_extract_first_last_state_root
    K252  chain_extract_first_last_receipts_root
    K253  chain_extract_first_last_transactions_root
    K254  chain_extract_first_last_withdrawals_root

  All four extract the 32-byte field at the head and tail of an
  N-element header chain — useful as compact endpoint commitments
  for proving state/receipts/txs/withdrawals trie audits across
  a chain range.

  Compose K201/K203/K204/K205 (HeaderFields.lean) + K20
  rlp_list_nth_item (RlpRead.lean).

  Companion endpoint primitives K251 (block hashes), K255
  (prev_randao), K256 (beneficiary) live in HeaderChain.lean
  and HeaderFields.lean respectively due to file-size routing.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_extract_first_last_state_root -- PR-K250

    Extract `(headers[0].state_root, headers[N-1].state_root)`
    from an N-element header chain. Useful as a compact
    chain-segment endpoint commitment for proving state
    transition across a range. Composes K201
    `header_extract_state_root` (HeaderFields.lean) at the head
    and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_state_root)
      a4 (input)  : 32-byte out (last_state_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x8 .x0 (brOff 2147483784 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root 2147483712),
    .BNE .x10 .x0 (brOff 2147483792 2147483716),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root 2147483768),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractFirstLastStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractFirstLastStateRoot_relocs : RelocTable :=
  [ (16, .jal .x1 "header_extract_state_root"),
    (30, .jal .x1 "header_extract_state_root") ]

def chainExtractFirstLastStateRootFunction : String :=
  "chain_extract_first_last_state_root:\n" ++ emitProgramR chainExtractFirstLastStateRoot_prog chainExtractFirstLastStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractFirstLastStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractFirstLastStateRootFunction_eq_prog :
    chainExtractFirstLastStateRootFunction = "chain_extract_first_last_state_root:\n" ++ emitProgramR chainExtractFirstLastStateRoot_prog chainExtractFirstLastStateRoot_relocs := rfl

#guard chainExtractFirstLastStateRootFunction.startsWith "chain_extract_first_last_state_root:\n"
#guard chainExtractFirstLastStateRoot_prog.length = 45
def ziskChainExtractFirstLastStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflsr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  chainExtractFirstLastStateRootFunction ++ "\n" ++
  ".Lceflsr_pdone:"

def ziskChainExtractFirstLastStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_first_last_receipts_root -- PR-K252

    Extract `(headers[0].receipts_root, headers[N-1].receipts_root)`
    from an N-element header chain. Sister to K250
    `chain_extract_first_last_state_root`; receipts-trie endpoint
    commitment.

    Composes K203 `header_extract_receipts_root` (HeaderFields.lean)
    at the head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_receipts_root)
      a4 (input)  : 32-byte out (last_receipts_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastReceiptsRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x8 .x0 (brOff 2147483784 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.header_extract_receipts_root 2147483712),
    .BNE .x10 .x0 (brOff 2147483792 2147483716),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.header_extract_receipts_root 2147483768),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractFirstLastReceiptsRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractFirstLastReceiptsRoot_relocs : RelocTable :=
  [ (16, .jal .x1 "header_extract_receipts_root"),
    (30, .jal .x1 "header_extract_receipts_root") ]

def chainExtractFirstLastReceiptsRootFunction : String :=
  "chain_extract_first_last_receipts_root:\n" ++ emitProgramR chainExtractFirstLastReceiptsRoot_prog chainExtractFirstLastReceiptsRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractFirstLastReceiptsRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractFirstLastReceiptsRootFunction_eq_prog :
    chainExtractFirstLastReceiptsRootFunction = "chain_extract_first_last_receipts_root:\n" ++ emitProgramR chainExtractFirstLastReceiptsRoot_prog chainExtractFirstLastReceiptsRoot_relocs := rfl

#guard chainExtractFirstLastReceiptsRootFunction.startsWith "chain_extract_first_last_receipts_root:\n"
#guard chainExtractFirstLastReceiptsRoot_prog.length = 45
def ziskChainExtractFirstLastReceiptsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_receipts_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflrr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractReceiptsRootFunction ++ "\n" ++
  chainExtractFirstLastReceiptsRootFunction ++ "\n" ++
  ".Lceflrr_pdone:"

def ziskChainExtractFirstLastReceiptsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "herr_offset:\n" ++
  "  .zero 8\n" ++
  "herr_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_first_last_transactions_root -- PR-K253

    Extract `(headers[0].transactions_root,
    headers[N-1].transactions_root)` from an N-element header
    chain. Completes the trie-endpoint family alongside K250
    (state_root field 3), K251 (block hashes), K252
    (receipts_root field 5). Useful as a compact endpoint
    commitment for txs-trie audit across a chain range.

    Composes K204 `header_extract_transactions_root`
    (HeaderFields.lean) at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_transactions_root)
      a4 (input)  : 32-byte out (last_transactions_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastTransactionsRootFunction : String :=
  "chain_extract_first_last_transactions_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lcefltr_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_transactions_root\n" ++
  "  bnez a0, .Lcefltr_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lcefltr_skip:\n" ++
  "  beqz t3, .Lcefltr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcefltr_skip\n" ++
  ".Lcefltr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_transactions_root\n" ++
  "  bnez a0, .Lcefltr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lcefltr_ret\n" ++
  ".Lcefltr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcefltr_ret\n" ++
  ".Lcefltr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcefltr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastTransactionsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_transactions_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcefltr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractTransactionsRootFunction ++ "\n" ++
  chainExtractFirstLastTransactionsRootFunction ++ "\n" ++
  ".Lcefltr_pdone:"

def ziskChainExtractFirstLastTransactionsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hetr_offset:\n" ++
  "  .zero 8\n" ++
  "hetr_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_first_last_withdrawals_root -- PR-K254

    Extract `(headers[0].withdrawals_root,
    headers[N-1].withdrawals_root)` from an N-element header
    chain. Completes the trie-endpoint family alongside K250
    (state_root), K251 (block hashes), K252 (receipts_root),
    K253 (transactions_root). Withdrawals are Shanghai+; pre-
    Shanghai headers don't have field 16 and return parse-fail.

    Composes K205 `header_extract_withdrawals_root`
    (HeaderFields.lean) at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_withdrawals_root)
      a4 (input)  : 32-byte out (last_withdrawals_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header
            (pre-Shanghai header missing withdrawals_root) -/
def chainExtractFirstLastWithdrawalsRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x8 .x0 (brOff 2147483784 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.header_extract_withdrawals_root 2147483712),
    .BNE .x10 .x0 (brOff 2147483792 2147483716),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.header_extract_withdrawals_root 2147483768),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractFirstLastWithdrawalsRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractFirstLastWithdrawalsRoot_relocs : RelocTable :=
  [ (16, .jal .x1 "header_extract_withdrawals_root"),
    (30, .jal .x1 "header_extract_withdrawals_root") ]

def chainExtractFirstLastWithdrawalsRootFunction : String :=
  "chain_extract_first_last_withdrawals_root:\n" ++ emitProgramR chainExtractFirstLastWithdrawalsRoot_prog chainExtractFirstLastWithdrawalsRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractFirstLastWithdrawalsRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractFirstLastWithdrawalsRootFunction_eq_prog :
    chainExtractFirstLastWithdrawalsRootFunction = "chain_extract_first_last_withdrawals_root:\n" ++ emitProgramR chainExtractFirstLastWithdrawalsRoot_prog chainExtractFirstLastWithdrawalsRoot_relocs := rfl

#guard chainExtractFirstLastWithdrawalsRootFunction.startsWith "chain_extract_first_last_withdrawals_root:\n"
#guard chainExtractFirstLastWithdrawalsRoot_prog.length = 45
def ziskChainExtractFirstLastWithdrawalsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_withdrawals_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflwr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  chainExtractFirstLastWithdrawalsRootFunction ++ "\n" ++
  ".Lceflwr_pdone:"

def ziskChainExtractFirstLastWithdrawalsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hewr_offset:\n" ++
  "  .zero 8\n" ++
  "hewr_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_first_last_ommers_hash -- PR-K257

    Extract `(headers[0].ommers_hash, headers[N-1].ommers_hash)`
    from an N-element header chain. Post-merge, ommers_hash is
    always `EMPTY_OMMERS_HASH = keccak256(rlp([]))`; pre-merge it
    keccaks the (now-removed) ommers/uncles list. Useful as a
    consistency check that no header in the segment has uncles
    (paired with K222 chain_validate_full's K179 K84 invariants).

    Sister to K250-K256 endpoint family. Composes K206
    `header_extract_ommers_hash` at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_ommers_hash)
      a4 (input)  : 32-byte out (last_ommers_hash)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastOmmersHashFunction : String :=
  "chain_extract_first_last_ommers_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lcefloh_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_ommers_hash\n" ++
  "  bnez a0, .Lcefloh_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lcefloh_skip:\n" ++
  "  beqz t3, .Lcefloh_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcefloh_skip\n" ++
  ".Lcefloh_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_ommers_hash\n" ++
  "  bnez a0, .Lcefloh_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lcefloh_ret\n" ++
  ".Lcefloh_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcefloh_ret\n" ++
  ".Lcefloh_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcefloh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastOmmersHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_ommers_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcefloh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractOmmersHashFunction ++ "\n" ++
  chainExtractFirstLastOmmersHashFunction ++ "\n" ++
  ".Lcefloh_pdone:"

def ziskChainExtractFirstLastOmmersHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "heoh_offset:\n" ++
  "  .zero 8\n" ++
  "heoh_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_first_last_block_hash -- PR-K251

    Extract `(keccak256(headers[0]), keccak256(headers[N-1]))`
    from an N-element header chain. Useful as a compact
    chain-segment endpoint commitment (the consensus-visible
    block hashes at the chain tip and the chain start).
    Companion to K200 `chain_block_hashes_commitment` (which
    keccak-folds ALL block hashes); this is the lighter
    endpoints-only variant.

    Composes K172 `block_hash_from_header` (Header.lean) on the
    head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_block_hash)
      a4 (input)  : 32-byte out (last_block_hash)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0) -/
def chainExtractFirstLastBlockHash_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x8 .x0 (brOff 2147483776 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.block_hash_from_header 2147483712),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.block_hash_from_header 2147483764),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractFirstLastBlockHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractFirstLastBlockHash_relocs : RelocTable :=
  [ (16, .jal .x1 "block_hash_from_header"),
    (29, .jal .x1 "block_hash_from_header") ]

def chainExtractFirstLastBlockHashFunction : String :=
  "chain_extract_first_last_block_hash:\n" ++ emitProgramR chainExtractFirstLastBlockHash_prog chainExtractFirstLastBlockHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractFirstLastBlockHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractFirstLastBlockHashFunction_eq_prog :
    chainExtractFirstLastBlockHashFunction = "chain_extract_first_last_block_hash:\n" ++ emitProgramR chainExtractFirstLastBlockHash_prog chainExtractFirstLastBlockHash_relocs := rfl

#guard chainExtractFirstLastBlockHashFunction.startsWith "chain_extract_first_last_block_hash:\n"
#guard chainExtractFirstLastBlockHash_prog.length = 41
def ziskChainExtractFirstLastBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  chainExtractFirstLastBlockHashFunction ++ "\n" ++
  ".Lceflbh_pdone:"

def ziskChainExtractFirstLastBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200"


/-! ## chain_extract_first_last_prev_randao -- PR-K255

    Extract `(headers[0].prev_randao, headers[N-1].prev_randao)`
    from an N-element header chain. The post-merge `prev_randao`
    field (header field 13, 32 B) is the value returned by the
    PREVRANDAO opcode and is committed to via the consensus
    beacon-chain randomness mix. Useful as an endpoint commitment
    for randomness-trace audits across a chain range.

    Sister to K250 (state_root), K251 (block hashes), K252
    (receipts_root), K253 (transactions_root), K254
    (withdrawals_root).

    Composes K207 `header_extract_prev_randao` (HeaderFields.lean)
    at head and tail headers.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_prev_randao)
      a4 (input)  : 32-byte out (last_prev_randao)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastPrevRandaoFunction : String :=
  "chain_extract_first_last_prev_randao:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflpr_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_prev_randao\n" ++
  "  bnez a0, .Lceflpr_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflpr_skip:\n" ++
  "  beqz t3, .Lceflpr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflpr_skip\n" ++
  ".Lceflpr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_prev_randao\n" ++
  "  bnez a0, .Lceflpr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflpr_ret\n" ++
  ".Lceflpr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflpr_ret\n" ++
  ".Lceflpr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflpr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastPrevRandaoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_prev_randao\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflpr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractPrevRandaoFunction ++ "\n" ++
  chainExtractFirstLastPrevRandaoFunction ++ "\n" ++
  ".Lceflpr_pdone:"

def ziskChainExtractFirstLastPrevRandaoDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hepr_offset:\n" ++
  "  .zero 8\n" ++
  "hepr_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_first_last_parent_beacon_block_root -- PR-K282

    Extract `(headers[0].parent_beacon_block_root,
    headers[N-1].parent_beacon_block_root)` from an N-element
    header chain. EIP-4788 / Cancun+ endpoint: useful for
    proving beacon-chain anchoring across a chain segment, where
    each EL block commits to its parent CL block's hash_tree_root.

    Composes K281 `header_extract_parent_beacon_block_root`
    (HeaderFields.lean) at the head and tail headers; mirrors
    K250 `chain_extract_first_last_state_root` in shape.

    Pre-Cancun headers (<20 fields) raise parse-failure status.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_parent_beacon_block_root)
      a4 (input)  : 32-byte out (last_parent_beacon_block_root)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastParentBeaconBlockRootFunction : String :=
  "chain_extract_first_last_parent_beacon_block_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflpbbr_empty\n" ++
  "  # first = headers[0].parent_beacon_block_root\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_parent_beacon_block_root\n" ++
  "  bnez a0, .Lceflpbbr_parse_fail\n" ++
  "  # Advance to last header\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflpbbr_skip:\n" ++
  "  beqz t3, .Lceflpbbr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflpbbr_skip\n" ++
  ".Lceflpbbr_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_parent_beacon_block_root\n" ++
  "  bnez a0, .Lceflpbbr_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflpbbr_ret\n" ++
  ".Lceflpbbr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflpbbr_ret\n" ++
  ".Lceflpbbr_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflpbbr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastParentBeaconBlockRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_parent_beacon_block_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflpbbr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentBeaconBlockRootFunction ++ "\n" ++
  chainExtractFirstLastParentBeaconBlockRootFunction ++ "\n" ++
  ".Lceflpbbr_pdone:"

def ziskChainExtractFirstLastParentBeaconBlockRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hepbbr_offset:\n" ++
  "  .zero 8\n" ++
  "hepbbr_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_first_last_requests_hash -- PR-K284

    Extract `(headers[0].requests_hash, headers[N-1].requests_hash)`
    from an N-element header chain. EIP-7685 / Prague+
    endpoint: useful for proving execution-layer request bundles
    are referenced at both ends of a chain segment.

    Composes K283 `header_extract_requests_hash`
    (HeaderFields.lean) at the head and tail headers; mirrors
    K282 `chain_extract_first_last_parent_beacon_block_root` in
    shape.

    Pre-Prague headers (<21 fields) raise parse-failure status.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte out (first_requests_hash)
      a4 (input)  : 32-byte out (last_requests_hash)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastRequestsHashFunction : String :=
  "chain_extract_first_last_requests_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflrh_empty\n" ++
  "  # first = headers[0].requests_hash\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_requests_hash\n" ++
  "  bnez a0, .Lceflrh_parse_fail\n" ++
  "  # Advance to last header\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflrh_skip:\n" ++
  "  beqz t3, .Lceflrh_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflrh_skip\n" ++
  ".Lceflrh_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_requests_hash\n" ++
  "  bnez a0, .Lceflrh_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflrh_ret\n" ++
  ".Lceflrh_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflrh_ret\n" ++
  ".Lceflrh_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflrh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractFirstLastRequestsHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010028\n" ++
  "  jal ra, chain_extract_first_last_requests_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceflrh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractRequestsHashFunction ++ "\n" ++
  chainExtractFirstLastRequestsHashFunction ++ "\n" ++
  ".Lceflrh_pdone:"

def ziskChainExtractFirstLastRequestsHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "herh_offset:\n" ++
  "  .zero 8\n" ++
  "herh_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
