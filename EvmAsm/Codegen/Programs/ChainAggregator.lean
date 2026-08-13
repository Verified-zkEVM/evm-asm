/-
  EvmAsm.Codegen.Programs.ChainAggregator

  Original chain aggregators (PR-K196..K200) carved out of
  `EvmAsm.Codegen.Programs.Chain` per the file-size hard cap.
  Hosts:

    K196  chain_compute_total_gas_used
    K197  chain_extract_number_range
    K198  header_extract_basefee
    K199  chain_extract_basefee_range
    K200  chain_block_hashes_commitment

  Compose K172 `block_hash_from_header` (Header.lean) + K20 / K34
  + `zkvm_keccak256`. K198 stays adjacent to K199 (K199 inlines
  the basefee extractor). `ChainAggregator.lean` imports Header
  + Tx + RlpRead + HashBridge.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_total_gas_used -- PR-K196

    Aggregate `gas_used` (header field 10) across an N-element
    header chain into a single u64 sum. Useful for chain-state
    commitments and protocol-level invariants such as
    \"this chain segment burned at most G gas total\".

    No chain validation is performed here -- the caller is
    responsible for combining this with K175 (or K195) for
    chain integrity. K196 is purely an aggregator over the
    headers; the inputs and accumulator math are kept in plain
    u64, so the sum saturates / wraps modulo 2^64 like any
    RISC-V add.

    For real mainnet blocks, gas_used <= ~30M and N <= ~256 in
    a single witness; the sum stays well below 2^64.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (total_gas_used; running sum)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse error on some header (sum is partial,
            up to the failing header)
        2 : a header's gas_used field exceeds 8 bytes BE -/
def chainComputeTotalGasUsedFunction : String :=
  "chain_compute_total_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0                    # i = 0\n" ++
  "  beqz s0, .Lccgu_done\n" ++
  ".Lccgu_loop:\n" ++
  "  beq s4, s0, .Lccgu_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)                # header_len\n" ++
  "  mv a0, s2                   # header_ptr\n" ++
  "  li a2, 10                   # field 10 = gas_used\n" ++
  "  la a3, ccgu_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccgu_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccgu_size_fail\n" ++
  "  # Accumulate\n" ++
  "  la t0, ccgu_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  add t2, t2, t1\n" ++
  "  sd t2, 0(s3)\n" ++
  "  # Advance to next header\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccgu_loop\n" ++
  ".Lccgu_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccgu_ret\n" ++
  ".Lccgu_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccgu_ret\n" ++
  ".Lccgu_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccgu_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_compute_total_gas_used`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : total_gas_used -/
def ziskChainComputeTotalGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a2, a1, t0              # headers ptr\n" ++
  "  li a3, 0xa0010008           # total_gas_used out\n" ++
  "  jal ra, chain_compute_total_gas_used\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccgu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeTotalGasUsedFunction ++ "\n" ++
  ".Lccgu_pdone:"

def ziskChainComputeTotalGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccgu_field:\n" ++
  "  .zero 8"


/-! ## chain_extract_number_range -- PR-K197

    Extract `(min_number, max_number)` from an N-element header
    chain. With K175 validated parent-hash invariants, the chain
    has strictly increasing numbers, so this is simply
    `(headers[0].number, headers[N-1].number)`. We return both
    edges so callers can verify `max - min + 1 == N` (the chain
    is dense) or directly use the range as a chain-segment
    identifier.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (min_number)
      a4 (input)  : u64 out (max_number)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's number field exceeds 8 bytes BE -/
def chainExtractNumberRange_prog : Program :=
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
    .BEQ .x8 .x0 (brOff 2147483792 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (8 : Word),
    .MV .x13 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483716),
    .BNE .x10 .x0 (brOff 2147483800 2147483720),
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
    .LI .x12 (8 : Word),
    .MV .x13 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483776),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractNumberRange_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractNumberRange_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_field_to_u64_strict"),
    (32, .jal .x1 "rlp_field_to_u64_strict") ]

def chainExtractNumberRangeFunction : String :=
  "chain_extract_number_range:\n" ++ emitProgramR chainExtractNumberRange_prog chainExtractNumberRange_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractNumberRange_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractNumberRangeFunction_eq_prog :
    chainExtractNumberRangeFunction = "chain_extract_number_range:\n" ++ emitProgramR chainExtractNumberRange_prog chainExtractNumberRange_relocs := rfl

#guard chainExtractNumberRangeFunction.startsWith "chain_extract_number_range:\n"
#guard chainExtractNumberRange_prog.length = 47
/-- `zisk_chain_extract_number_range`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : min_number
      bytes 16..24 : max_number -/
def ziskChainExtractNumberRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0              # headers\n" ++
  "  li a3, 0xa0010008           # min out\n" ++
  "  li a4, 0xa0010010           # max out\n" ++
  "  jal ra, chain_extract_number_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcenr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainExtractNumberRangeFunction ++ "\n" ++
  ".Lcenr_pdone:"

def ziskChainExtractNumberRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"


/-! ## header_extract_basefee -- PR-K198

    Extract `base_fee_per_gas` (field 15, present from London
    onwards) from a header RLP. Returns the value as a u64; the
    EIP-1559 base_fee is bounded by `2^256-1` in principle but
    in practice never exceeds u64 in any chain we care about.
    Callers that need the full uint256 form should use the more
    general `rlp_field_to_u256` (not yet implemented) instead.

    Field index 15 is the **first** post-London field; on
    pre-London headers (`len(fields) <= 15`) the call yields
    a parse-failure status.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (base_fee_per_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 15 missing (pre-London)
        2 : base_fee field exceeds 8 bytes BE -/
def headerExtractBasefee_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x13 .x12,
    .LI .x12 (15 : Word),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483664),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractBasefee_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractBasefee_relocs : RelocTable :=
  [ (4, .jal .x1 "rlp_field_to_u64_strict") ]

def headerExtractBasefeeFunction : String :=
  "header_extract_basefee:\n" ++ emitProgramR headerExtractBasefee_prog headerExtractBasefee_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractBasefee_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractBasefeeFunction_eq_prog :
    headerExtractBasefeeFunction = "header_extract_basefee:\n" ++ emitProgramR headerExtractBasefee_prog headerExtractBasefee_relocs := rfl

#guard headerExtractBasefeeFunction.startsWith "header_extract_basefee:\n"
#guard headerExtractBasefee_prog.length = 8
/-- `zisk_header_extract_basefee`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp_len
      bytes 8..   : header_rlp
    Output layout:
      bytes 0..8  : status
      bytes 8..16 : base_fee_per_gas -/
def ziskHeaderExtractBasefeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # base_fee out\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBasefeeFunction ++ "\n" ++
  ".Lheb_pdone:"

def ziskHeaderExtractBasefeeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_basefee_range -- PR-K199

    Walk an N-element header chain and compute `(min, max)` of
    `base_fee_per_gas` (field 15). London+ only. Useful for
    chain-level base_fee bounds analysis.

    Returns vacuous `(0, 0)` on N == 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (min)
      a4 (input)  : u64 out (max)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : a header parse failure (e.g., pre-London header)
        2 : a base_fee field exceeds 8 bytes BE -/
def chainExtractBasefeeRangeFunction : String :=
  "chain_extract_basefee_range:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # min out\n" ++
  "  mv s4, a4                   # max out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd zero, 0(s4)\n" ++
  "  beqz s0, .Lcebr_done\n" ++
  "  # Initialize min/max with headers[0].basefee\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  bnez a0, .Lcebr_ret\n" ++
  "  ld t0, 0(s3)\n" ++
  "  sd t0, 0(s4)                # max = min = first value\n" ++
  "  # Walk remaining headers\n" ++
  "  ld t1, 0(s1)\n" ++
  "  add t2, s2, t1              # next header ptr\n" ++
  "  addi t3, s1, 8              # next length ptr\n" ++
  "  li t4, 1                    # i\n" ++
  ".Lcebr_loop:\n" ++
  "  beq t4, s0, .Lcebr_done\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t2\n" ++
  "  la a2, cebr_cur\n" ++
  "  # Stash t2/t3/t4 in s-regs since rlp_field_to_u64 will\n" ++
  "  # save/restore s0..s4 around it; pin them here.\n" ++
  "  # Actually simpler: keep t2/t3/t4 across the call by\n" ++
  "  # using callee-saved regs. We'll re-derive them after.\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  bnez a0, .Lcebr_ret\n" ++
  "  # cur < min -> update min; cur > max -> update max\n" ++
  "  la t0, cebr_cur; ld t1, 0(t0)\n" ++
  "  ld t5, 0(s3)\n" ++
  "  bgeu t1, t5, .Lcebr_skip_min\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lcebr_skip_min:\n" ++
  "  ld t5, 0(s4)\n" ++
  "  bleu t1, t5, .Lcebr_skip_max\n" ++
  "  sd t1, 0(s4)\n" ++
  ".Lcebr_skip_max:\n" ++
  "  # Re-derive iteration state. Since we don't have callee-\n" ++
  "  # saved scratch left (s0..s4 all used), maintain t-regs\n" ++
  "  # before the call by stashing on .data.\n" ++
  "  la t0, cebr_i; ld t4, 0(t0)\n" ++
  "  la t0, cebr_hdr_ptr; ld t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr; ld t3, 0(t0)\n" ++
  "  ld t1, 0(t3)\n" ++
  "  add t2, t2, t1\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, 1\n" ++
  "  la t0, cebr_i;        sd t4, 0(t0)\n" ++
  "  la t0, cebr_hdr_ptr;  sd t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr;  sd t3, 0(t0)\n" ++
  "  j .Lcebr_loop\n" ++
  ".Lcebr_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcebr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_extract_basefee_range`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : min_basefee
      bytes 16..24 : max_basefee -/
def ziskChainExtractBasefeeRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  # Pre-init iteration scratch only when N > 0.\n" ++
  "  beqz a0, .Lcebr_skip_init\n" ++
  "  ld t1, 0(a1)                # first header_len\n" ++
  "  add t2, a2, t1              # second header ptr\n" ++
  "  addi t3, a1, 8\n" ++
  "  la t0, cebr_hdr_ptr; sd t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr; sd t3, 0(t0)\n" ++
  "  la t0, cebr_i; li t4, 1; sd t4, 0(t0)\n" ++
  ".Lcebr_skip_init:\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_basefee_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBasefeeFunction ++ "\n" ++
  chainExtractBasefeeRangeFunction ++ "\n" ++
  ".Lcebr_pdone:"

def ziskChainExtractBasefeeRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cebr_cur:\n" ++
  "  .zero 8\n" ++
  "cebr_hdr_ptr:\n" ++
  "  .zero 8\n" ++
  "cebr_len_ptr:\n" ++
  "  .zero 8\n" ++
  "cebr_i:\n" ++
  "  .zero 8"


/-! ## chain_block_hashes_commitment -- PR-K200

    Compute a 32-byte commitment over the block_hashes of an
    N-element header chain:

      commitment = keccak256( H[0] || H[1] || ... || H[N-1] )

    where `H[i] = keccak256(headers[i])`. This is the natural
    succinct commitment to a chain of block hashes, useful for
    bridges, light clients, and inter-prover commitments.

    For N == 0 the commitment is `keccak256("")` (the empty-
    string hash), which equals
    `0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte output ptr (commitment)
      ra (input)  : return
      a0 (output) :
        0 : success

    Uses a scratch buffer (`cbhc_concat_buf`) of size 32*MAX_N
    bytes for the intermediate concatenation. MAX_N is fixed
    at 64 in this implementation (sufficient for typical
    stateless witnesses of ~32 headers). -/
def chainBlockHashesCommitmentFunction : String :=
  "chain_block_hashes_commitment:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # output ptr\n" ++
  "  la s4, cbhc_concat_buf      # concat buffer start\n" ++
  "  # Walk and hash each header into the concat buffer.\n" ++
  "  li t6, 0                    # i = 0\n" ++
  "  mv t5, s2                   # current header ptr\n" ++
  "  la t4, cbhc_concat_buf\n" ++
  ".Lcbhc_loop:\n" ++
  "  beq t6, s0, .Lcbhc_done\n" ++
  "  # Stash iteration state into .data\n" ++
  "  la t0, cbhc_i; sd t6, 0(t0)\n" ++
  "  la t0, cbhc_hdr_ptr; sd t5, 0(t0)\n" ++
  "  la t0, cbhc_concat_cursor; sd t4, 0(t0)\n" ++
  "  slli t0, t6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)                # header_len\n" ++
  "  mv a0, t5\n" ++
  "  mv a2, t4                   # write into concat buf\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Reload iteration state\n" ++
  "  la t0, cbhc_i; ld t6, 0(t0)\n" ++
  "  la t0, cbhc_hdr_ptr; ld t5, 0(t0)\n" ++
  "  la t0, cbhc_concat_cursor; ld t4, 0(t0)\n" ++
  "  # Advance: concat += 32; header += header_len; i += 1\n" ++
  "  slli t0, t6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add t5, t5, t1\n" ++
  "  addi t4, t4, 32\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Lcbhc_loop\n" ++
  ".Lcbhc_done:\n" ++
  "  # commit = keccak256(concat buf, 32*N) -> output\n" ++
  "  la a0, cbhc_concat_buf\n" ++
  "  slli a1, s0, 5              # 32*N\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_block_hashes_commitment`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes 0..32 : 32-byte commitment -/
def ziskChainBlockHashesCommitmentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010000           # 32 B commitment out\n" ++
  "  jal ra, chain_block_hashes_commitment\n" ++
  "  j .Lcbhc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  chainBlockHashesCommitmentFunction ++ "\n" ++
  ".Lcbhc_pdone:"

def ziskChainBlockHashesCommitmentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "cbhc_concat_buf:\n" ++
  "  .zero 2048                  # 32 * 64 = 2048\n" ++
  "cbhc_i:\n" ++
  "  .zero 8\n" ++
  "cbhc_hdr_ptr:\n" ++
  "  .zero 8\n" ++
  "cbhc_concat_cursor:\n" ++
  "  .zero 8"



end EvmAsm.Codegen
