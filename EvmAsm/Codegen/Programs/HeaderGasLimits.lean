/-
  EvmAsm.Codegen.Programs.HeaderGasLimits

  Chain-level header gas-limit helpers split out of HeaderU64.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_max_gas_limit -- PR-K262

    Find max(`gas_limit`) (header field 9) across an N-element
    header chain. Cross-fork — every header has gas_limit.
    Useful for capacity-planning / network-policy monitoring.

    Mirrors K236 chain_compute_max_gas_used (field 10). The chain-level
    basefee counterparts are K260/K261 (in Programs/ChainBasefee.lean).

    Vacuous on empty chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_limit field > 8 bytes BE -/
def chainComputeMaxGasLimitFunction : String :=
  "chain_compute_max_gas_limit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmgl_done\n" ++
  ".Lccmgl_loop:\n" ++
  "  beq s4, s0, .Lccmgl_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, ccmgl_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmgl_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmgl_size_fail\n" ++
  "  la t0, ccmgl_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmgl_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmgl_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmgl_loop\n" ++
  ".Lccmgl_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmgl_ret\n" ++
  ".Lccmgl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmgl_ret\n" ++
  ".Lccmgl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmgl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_gas_limit\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmgl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMaxGasLimitFunction ++ "\n" ++
  ".Lccmgl_pdone:"

def ziskChainComputeMaxGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmgl_field:\n" ++
  "  .zero 8"


/-! ## chain_compute_min_gas_limit -- PR-K263

    Find min(`gas_limit`) (header field 9) across an N-element
    header chain. Min counterpart to K262 chain_compute_max_gas_limit.

    Useful for spotting capacity bottlenecks across a chain segment.

    Vacuous on empty chain: min = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_limit field > 8 bytes BE -/
def chainComputeMinGasLimitFunction : String :=
  "chain_compute_min_gas_limit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmingl_done\n" ++
  ".Lccmingl_loop:\n" ++
  "  beq s4, s0, .Lccmingl_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, ccmingl_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmingl_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmingl_size_fail\n" ++
  "  la t0, ccmingl_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccmingl_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccmingl_no_update\n" ++
  ".Lccmingl_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmingl_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmingl_loop\n" ++
  ".Lccmingl_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmingl_ret\n" ++
  ".Lccmingl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmingl_ret\n" ++
  ".Lccmingl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmingl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_gas_limit\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmingl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMinGasLimitFunction ++ "\n" ++
  ".Lccmingl_pdone:"

def ziskChainComputeMinGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmingl_field:\n" ++
  "  .zero 8"


/-! ## chain_compute_total_gas_limit -- PR-K264

    Sum `gas_limit` (header field 9) across an N-element header chain.
    Vacuous on empty chain: sum = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (total gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_limit field > 8 bytes BE -/
def chainComputeTotalGasLimitFunction : String :=
  "chain_compute_total_gas_limit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcctgl_done\n" ++
  ".Lcctgl_loop:\n" ++
  "  beq s4, s0, .Lcctgl_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, cctgl_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcctgl_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcctgl_size_fail\n" ++
  "  la t0, cctgl_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcctgl_loop\n" ++
  ".Lcctgl_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcctgl_ret\n" ++
  ".Lcctgl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcctgl_ret\n" ++
  ".Lcctgl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcctgl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeTotalGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_total_gas_limit\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcctgl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeTotalGasLimitFunction ++ "\n" ++
  ".Lcctgl_pdone:"

def ziskChainComputeTotalGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cctgl_field:\n" ++
  "  .zero 8"


/-! ## chain_extract_gas_limit_first_last -- PR-K265

    Extract `(first_gas_limit, last_gas_limit)` (header field 9)
    from an N-element header chain.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_gas_limit)
      a4 (input)  : u64 out (last_gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's gas_limit field exceeds 8 bytes BE -/
def chainExtractGasLimitFirstLast_prog : Program :=
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
    .LI .x12 (9 : Word),
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
    .LI .x12 (9 : Word),
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

/-- Reloc side-table for `chainExtractGasLimitFirstLast_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractGasLimitFirstLast_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_field_to_u64_strict"),
    (32, .jal .x1 "rlp_field_to_u64_strict") ]

def chainExtractGasLimitFirstLastFunction : String :=
  "chain_extract_gas_limit_first_last:\n" ++ emitProgramR chainExtractGasLimitFirstLast_prog chainExtractGasLimitFirstLast_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractGasLimitFirstLast_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractGasLimitFirstLastFunction_eq_prog :
    chainExtractGasLimitFirstLastFunction = "chain_extract_gas_limit_first_last:\n" ++ emitProgramR chainExtractGasLimitFirstLast_prog chainExtractGasLimitFirstLast_relocs := rfl

#guard chainExtractGasLimitFirstLastFunction.startsWith "chain_extract_gas_limit_first_last:\n"
#guard chainExtractGasLimitFirstLast_prog.length = 47
def ziskChainExtractGasLimitFirstLastPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_gas_limit_first_last\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceglfl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainExtractGasLimitFirstLastFunction ++ "\n" ++
  ".Lceglfl_pdone:"

def ziskChainExtractGasLimitFirstLastDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"


/-! ## chain_extract_excess_blob_gas_first_last -- PR-K271

    Extract `(first_excess_blob_gas, last_excess_blob_gas)`
    (header field 18, Cancun+) from an N-element header chain.

    Pre-Cancun headers (<19 fields) raise parse-failure status.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_excess_blob_gas)
      a4 (input)  : u64 out (last_excess_blob_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : excess_blob_gas field > 8 bytes BE on some header -/
def chainExtractExcessBlobGasFirstLast_prog : Program :=
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
    .LI .x12 (18 : Word),
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
    .LI .x12 (18 : Word),
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

/-- Reloc side-table for `chainExtractExcessBlobGasFirstLast_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractExcessBlobGasFirstLast_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_field_to_u64_strict"),
    (32, .jal .x1 "rlp_field_to_u64_strict") ]

def chainExtractExcessBlobGasFirstLastFunction : String :=
  "chain_extract_excess_blob_gas_first_last:\n" ++ emitProgramR chainExtractExcessBlobGasFirstLast_prog chainExtractExcessBlobGasFirstLast_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractExcessBlobGasFirstLast_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractExcessBlobGasFirstLastFunction_eq_prog :
    chainExtractExcessBlobGasFirstLastFunction = "chain_extract_excess_blob_gas_first_last:\n" ++ emitProgramR chainExtractExcessBlobGasFirstLast_prog chainExtractExcessBlobGasFirstLast_relocs := rfl

#guard chainExtractExcessBlobGasFirstLastFunction.startsWith "chain_extract_excess_blob_gas_first_last:\n"
#guard chainExtractExcessBlobGasFirstLast_prog.length = 47
def ziskChainExtractExcessBlobGasFirstLastPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_excess_blob_gas_first_last\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceebgfl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainExtractExcessBlobGasFirstLastFunction ++ "\n" ++
  ".Lceebgfl_pdone:"

def ziskChainExtractExcessBlobGasFirstLastDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
