/-
  EvmAsm.Codegen.Programs.TxExtract

  Per-field transaction extractors + typed-tx dispatcher carved
  out of `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap.
  Hosts:

    K40   tx_type_dispatch         (typed-tx prefix detector)
    K101  tx_extract_to_address    (to address)
    K102  tx_extract_nonce_and_gas (nonce + gas_limit)
    K103  tx_extract_value         (value u256)
    K104  tx_extract_data_section  (calldata bytes)
    K108  tx_extract_gas_pricing   (gas_price / max_fee / priority_fee)

  Each takes a tx-bytes ptr + length and returns the specific
  field via caller-supplied output buffer(s). Newer extractors use
  `RlpWalk.lean` cursor helpers for ordered field access; older
  access-list helpers still compose K20 / K34 / K35 helpers from
  `RlpRead.lean` + `Tx.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.U256GasPricing

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

private def repeatAsm : Nat -> String -> String
  | 0, _ => ""
  | n + 1, s => s ++ repeatAsm n s

private def txExtractWalkSkipAsm (failLabel : String) (n : Nat) : String :=
  repeatAsm n <|
    "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++ "; mv s5, a0\n"

private def txExtractWalkFieldAsm (failLabel : String) (n : Nat) : String :=
  txExtractWalkSkipAsm failLabel n ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++ "\n" ++
  "  sub t6, a0, a2              # content ptr\n"

/-! ## tx_type_dispatch -- PR-K40 typed-tx prefix detector

    Read the first byte of an RLP/typed-tx-encoded transaction
    and return the type code + inner-RLP offset:

      byte 0 in 0xc0..0xfe → legacy (type=0, inner_offset=0)
      byte 0 == 0x01    → EIP-2930 access list (type=1, inner_offset=1)
      byte 0 == 0x02    → EIP-1559 dynamic fee  (type=2, inner_offset=1)
      byte 0 == 0x03    → EIP-4844 blob         (type=3, inner_offset=1)
      byte 0 == 0x04    → EIP-7702 set code     (type=4, inner_offset=1)
      else              → invalid (status=1)

    Callers consume `inner_offset` to skip the type prefix
    before passing the remaining bytes to the type-specific
    decoder.

    Calling convention:
      a0 (input)  : tx_bytes ptr
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 type code out
      a3 (input)  : u64 inner_offset out
      ra (input)  : return
      a0 (output) : 0 success / 1 unknown / empty input

    Leaf-callable, no scratch. -/
def txTypeDispatch_prog : Program :=
  [ .BEQ .x11 .x0 (164 : BitVec 13),
    .LBU .x5 .x10 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BGEU .x5 .x6 (brOff (GuestAddrs.tx_type_dispatch + 180) (GuestAddrs.tx_type_dispatch + 12)),
    .LI .x6 (1 : Word),
    .BEQ .x5 .x6 (48 : BitVec 13),
    .LI .x6 (2 : Word),
    .BEQ .x5 .x6 (64 : BitVec 13),
    .LI .x6 (3 : Word),
    .BEQ .x5 .x6 (80 : BitVec 13),
    .LI .x6 (4 : Word),
    .BEQ .x5 .x6 (96 : BitVec 13),
    .JAL .x0 (116 : BitVec 21),
    .SD .x12 .x0 (0 : BitVec 12),
    .SD .x13 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (2 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (3 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (4 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x12 .x0 (0 : BitVec 12),
    .SD .x13 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (255 : Word),
    .BEQ .x5 .x6 (-20 : BitVec 13),
    .JAL .x0 (-136 : BitVec 21) ]

def txTypeDispatchFunction : String :=
  "tx_type_dispatch:\n" ++ emitProgram txTypeDispatch_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `txTypeDispatch_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem txTypeDispatchFunction_eq_prog :
    txTypeDispatchFunction = "tx_type_dispatch:\n" ++ emitProgram txTypeDispatch_prog := rfl

#guard txTypeDispatchFunction.startsWith "tx_type_dispatch:\n"
#guard txTypeDispatch_prog.length = 48

/-! ## tx_extract_nonce_and_gas -- PR-K102

    Extract the (`nonce`, `gas_limit`) pair from any encoded tx
    type. Both are u64-bounded by EIP-2681 / EIP-1559 / EIP-4844.

    Per-type field indices (post type-byte stripping):

      type 0 legacy   : nonce = 0,  gas_limit = 2
      type 1 EIP-2930 : nonce = 1,  gas_limit = 3
      type 2 EIP-1559 : nonce = 1,  gas_limit = 4
      type 3 EIP-4844 : nonce = 1,  gas_limit = 4
      type 4 EIP-7702 : nonce = 1,  gas_limit = 4

    Composes:
      - PR-K40 `tx_type_dispatch`  — typed-tx detector
      - RlpWalk cursor helpers     — ordered field extraction
      - canonical content-to-u64   — u64 decoding

    Useful as a fast prelude to `check_transaction` (nonce
    ordering + gas-availability) without a full per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 nonce out ptr
      a3 (input)  : u64 gas_limit out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : nonce field extraction failed
        3 : gas_limit field extraction failed
        4 : nonce exceeds EIP-2681 maximum (`2^64 - 2`)

    Both outputs are zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`teng_type`, `teng_inner_off`). -/
def txExtractNonceAndGasFunction : String :=
  "tx_extract_nonce_and_gas:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # nonce out\n" ++
  "  mv s3, a3                   # gas out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Step 1: tx_type_dispatch\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, teng_type\n" ++
  "  la a3, teng_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lteng_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Lteng_ret\n" ++
  ".Lteng_after_dispatch:\n" ++
  "  la t0, teng_type;      ld s4, 0(t0)    # type → s4\n" ++
  "  la t0, teng_inner_off; ld t5, 0(t0)\n" ++
  "  add a0, s0, t5                          # inner_ptr\n" ++
  "  sub a1, s1, t5                          # inner_len\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteng_nonce_fail\n" ++
  "  mv s5, a0                               # cursor\n" ++
  "  mv s6, a1                               # end\n" ++
  "  # Step 2: extract nonce.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Lteng_n_legacy\n" ++
  txExtractWalkFieldAsm ".Lteng_nonce_fail" 1 ++
  "  j .Lteng_n_have_field\n" ++
  ".Lteng_n_legacy:\n" ++
  txExtractWalkFieldAsm ".Lteng_nonce_fail" 0 ++
  ".Lteng_n_have_field:\n" ++
  "  mv s7, a0                              # cursor after nonce\n" ++
  "  mv a0, t6\n" ++
  "  mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64_strict\n" ++
  "  beqz a1, .Lteng_step3\n" ++
  ".Lteng_nonce_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lteng_ret\n" ++
  ".Lteng_step3:\n" ++
  "  sd a0, 0(s2)\n" ++
  "  ld t0, 0(s2)\n" ++
  "  li t1, -1                              # EIP-2681 rejects u64 max\n" ++
  "  bne t0, t1, .Lteng_nonce_under_cap\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 4\n" ++
  "  j .Lteng_ret\n" ++
  ".Lteng_nonce_under_cap:\n" ++
  "  mv s5, s7                              # continue from after nonce\n" ++
  "  # Step 3: extract gas_limit.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Lteng_g_legacy\n" ++
  "  li t0, 1\n" ++
  "  beq s4, t0, .Lteng_g_2930\n" ++
  txExtractWalkFieldAsm ".Lteng_gas_fail" 2 ++
  "  j .Lteng_g_have_field\n" ++
  ".Lteng_g_legacy:\n" ++
  txExtractWalkFieldAsm ".Lteng_gas_fail" 1 ++
  "  j .Lteng_g_have_field\n" ++
  ".Lteng_g_2930:\n" ++
  txExtractWalkFieldAsm ".Lteng_gas_fail" 1 ++
  ".Lteng_g_have_field:\n" ++
  "  mv a0, t6\n" ++
  "  mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64_strict\n" ++
  "  beqz a1, .Lteng_store_gas\n" ++
  ".Lteng_gas_fail:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lteng_ret\n" ++
  ".Lteng_store_gas:\n" ++
  "  sd a0, 0(s3)\n" ++
  "  j .Lteng_ok\n" ++
  ".Lteng_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lteng_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-! ## tx_extract_to_address -- PR-K101

    For any encoded tx (legacy or typed), extract the `to`
    (recipient) field and a contract-creation flag:

      is_creation = (to_field_length == 0)
      to_bytes    = 20 raw bytes when not creation, zeros otherwise

    Per-type RLP layout — the field index of `to`:

      type 0 legacy   : field 3 of the outer list
      type 1 EIP-2930 : field 4 of the inner RLP
      type 2 EIP-1559 : field 5 of the inner RLP
      type 3 EIP-4844 : field 5 of the inner RLP
      type 4 EIP-7702 : field 5 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`   — typed-tx detector
      - RlpWalk cursor helpers      — field extractor

    Useful for `apply_body` (CREATE vs CALL routing) and for any
    pre-EVM check that needs the recipient without doing a full
    per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 20-byte output ptr (zeros on creation / fail)
      a3 (input)  : u64 out ptr (is_creation flag, 0 or 1)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : `to` field extraction failed (not 0 or 20 B)

    Uses two 8-byte `.data` scratch slots (`tea_type` + `tea_inner_off`). -/
def txExtractToAddressFunction : String :=
  "tx_extract_to_address:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # tx_bytes ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # 20B out ptr\n" ++
  "  mv s3, a3                   # is_creation out ptr\n" ++
  "  # Pre-zero outputs in case of failure.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sw zero, 16(s2)\n" ++
  "  sd zero,  0(s3)\n" ++
  "  # Step 1: tx_type_dispatch(tx, len, &type, &inner_off)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tea_type\n" ++
  "  la a3, tea_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Ltea_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Ltea_ret\n" ++
  ".Ltea_after_dispatch:\n" ++
  "  la t0, tea_type;      ld s4, 0(t0)    # type\n" ++
  "  la t0, tea_inner_off; ld t5, 0(t0)    # inner_off\n" ++
  "  add a0, s0, t5                         # inner_ptr\n" ++
  "  sub a1, s1, t5                         # inner_len\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Ltea_field_fail\n" ++
  "  mv s5, a0                              # cursor\n" ++
  "  mv s6, a1                              # end\n" ++
  "  # Determine field index based on type: 0 -> 3, 1 -> 4, 2/3/4 -> 5.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Ltea_legacy_idx\n" ++
  "  li t0, 1\n" ++
  "  beq s4, t0, .Ltea_t1_idx\n" ++
  txExtractWalkFieldAsm ".Ltea_field_fail" 5 ++
  "  j .Ltea_have_field\n" ++
  ".Ltea_legacy_idx:\n" ++
  txExtractWalkFieldAsm ".Ltea_field_fail" 3 ++
  "  j .Ltea_have_field\n" ++
  ".Ltea_t1_idx:\n" ++
  txExtractWalkFieldAsm ".Ltea_field_fail" 4 ++
  ".Ltea_have_field:\n" ++
  "  mv t2, a2                    # content length\n" ++
  "  beqz t2, .Ltea_creation\n" ++
  "  li t1, 20\n" ++
  "  bne t2, t1, .Ltea_field_fail\n" ++
  "  # Copy 20 bytes from content pointer t6 to s2.\n" ++
  "  ld t0,  0(t6); sd t0,  0(s2)\n" ++
  "  ld t0,  8(t6); sd t0,  8(s2)\n" ++
  "  lwu t0, 16(t6); sw t0, 16(s2)\n" ++
  "  sd zero, 0(s3)              # is_creation = 0\n" ++
  "  li a0, 0\n" ++
  "  j .Ltea_ret\n" ++
  ".Ltea_creation:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)                # is_creation = 1\n" ++
  "  li a0, 0\n" ++
  "  j .Ltea_ret\n" ++
  ".Ltea_field_fail:\n" ++
  "  li a0, 2\n" ++
  ".Ltea_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-! ## tx_extract_value -- PR-K103

    Extract the `value` field (u256 BE) from any encoded tx type.
    `value` is the amount of wei the tx transfers to its `to`
    recipient (or contributes to the new account's balance on
    CREATE).

    Per-type RLP layout — the field index of `value`:

      type 0 legacy   : field 4 of the outer list
      type 1 EIP-2930 : field 5 of the inner RLP
      type 2 EIP-1559 : field 6 of the inner RLP
      type 3 EIP-4844 : field 6 of the inner RLP
      type 4 EIP-7702 : field 6 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`        — typed-tx detector
      - RlpWalk cursor helpers           — field extraction
      - canonical content-to-u256 helper — u256 BE decoding

    Useful for balance checks (`sender_balance >= value + gas_cost`)
    and for the priority-fee credit path. Together with PR-K101
    (`to` address) and PR-K102 (nonce + gas), this covers the
    fields `check_transaction` and `process_transaction` need from
    a tx without doing a full per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 32-byte output ptr (u256 BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed (unknown / empty input)
        2 : value field extraction failed (parse error or > 256 bits)

    Output zeroed on failure. Uses two 8-byte `.data` scratch
    slots (`tev_type`, `tev_inner_off`). -/
def txExtractValueFunction : String :=
  "tx_extract_value:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # 32B out ptr\n" ++
  "  # Pre-zero output.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # Step 1: tx_type_dispatch.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tev_type\n" ++
  "  la a3, tev_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Ltev_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Ltev_ret\n" ++
  ".Ltev_after_dispatch:\n" ++
  "  la t0, tev_type;      ld s3, 0(t0)    # type → s3\n" ++
  "  la t0, tev_inner_off; ld t5, 0(t0)\n" ++
  "  add a0, s0, t5                          # inner_ptr\n" ++
  "  sub a1, s1, t5                          # inner_len\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Ltev_field_fail\n" ++
  "  mv s5, a0                               # cursor\n" ++
  "  mv s6, a1                               # end\n" ++
  "  # Determine field index.\n" ++
  "  li t0, 0\n" ++
  "  beq s3, t0, .Ltev_legacy_idx\n" ++
  "  li t0, 1\n" ++
  "  beq s3, t0, .Ltev_t1_idx\n" ++
  txExtractWalkFieldAsm ".Ltev_field_fail" 6 ++
  "  j .Ltev_have_field\n" ++
  ".Ltev_legacy_idx:\n" ++
  txExtractWalkFieldAsm ".Ltev_field_fail" 4 ++
  "  j .Ltev_have_field\n" ++
  ".Ltev_t1_idx:\n" ++
  txExtractWalkFieldAsm ".Ltev_field_fail" 5 ++
  ".Ltev_have_field:\n" ++
  "  mv a0, t6\n" ++
  "  mv a1, a2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, rlp_content_to_u256_be_strict\n" ++
  "  beqz a0, .Ltev_ok\n" ++
  ".Ltev_field_fail:\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Ltev_ret\n" ++
  ".Ltev_ok:\n" ++
  "  li a0, 0\n" ++
  ".Ltev_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-! ## tx_extract_data_section -- PR-K104

    Extract the `data` (calldata / init-code) field's absolute
    pointer and byte length from any encoded tx type. The data
    field is variable-length: 0 bytes for value transfers, up to
    `MAX_INIT_CODE_SIZE` bytes for contract creations, longer for
    `CALL`-style payloads.

    Per-type RLP layout — the field index of `data`:

      type 0 legacy   : field 5 of the outer list
      type 1 EIP-2930 : field 6 of the inner RLP
      type 2 EIP-1559 : field 7 of the inner RLP
      type 3 EIP-4844 : field 7 of the inner RLP
      type 4 EIP-7702 : field 7 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`   — typed-tx detector
      - RlpWalk cursor helpers      — byte-string content bounds

    Useful for:
    - intrinsic-gas pricing (zero/non-zero byte counts)
    - EIP-3860 init-code size check (CREATE / CREATE2)
    - feeding the EVM's `calldata` region pre-execution

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 out ptr (data_ptr — absolute address)
      a3 (input)  : u64 out ptr (data_len)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : data field extraction failed (parse error)

    Both outputs zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`teds_type`, `teds_inner_off`). -/
def txExtractDataSectionFunction : String :=
  "tx_extract_data_section:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # data_ptr out\n" ++
  "  mv s3, a3                   # data_len out\n" ++
  "  sd zero, 0(s2); sd zero, 0(s3)\n" ++
  "  # Step 1: tx_type_dispatch.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, teds_type\n" ++
  "  la a3, teds_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lteds_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Lteds_ret\n" ++
  ".Lteds_after_dispatch:\n" ++
  "  la t0, teds_type;      ld s4, 0(t0)     # type\n" ++
  "  la t0, teds_inner_off; ld t5, 0(t0)\n" ++
  "  add a0, s0, t5                           # inner_ptr\n" ++
  "  sub a1, s1, t5                           # inner_len\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteds_field_fail\n" ++
  "  mv s5, a0                                # cursor\n" ++
  "  mv s6, a1                                # end\n" ++
  "  # Determine field index.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Lteds_legacy_idx\n" ++
  "  li t0, 1\n" ++
  "  beq s4, t0, .Lteds_t1_idx\n" ++
  txExtractWalkFieldAsm ".Lteds_field_fail" 7 ++
  "  j .Lteds_have_field\n" ++
  ".Lteds_legacy_idx:\n" ++
  txExtractWalkFieldAsm ".Lteds_field_fail" 5 ++
  "  j .Lteds_have_field\n" ++
  ".Lteds_t1_idx:\n" ++
  txExtractWalkFieldAsm ".Lteds_field_fail" 6 ++
  ".Lteds_have_field:\n" ++
  "  # data_ptr = content ptr; data_len = content length.\n" ++
  "  sd t6, 0(s2)\n" ++
  "  sd a2, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lteds_ret\n" ++
  ".Lteds_field_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lteds_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-! ## tx_extract_gas_pricing -- PR-K108

    Extract a tx's gas-pricing fields, normalised to the EIP-1559
    `(max_priority_fee, max_fee)` shape. For pre-EIP-1559 tx types
    that carry a single `gas_price`, both outputs receive the same
    value.

    Per-type RLP layout:

      type 0 legacy   : gas_price = field 1 → fill both outputs
      type 1 EIP-2930 : gas_price = field 2 → fill both outputs
      type 2 EIP-1559 : max_priority_fee = field 2, max_fee = field 3
      type 3 EIP-4844 : max_priority_fee = field 2, max_fee = field 3
      type 4 EIP-7702 : max_priority_fee = field 2, max_fee = field 3

    Both outputs are 32-byte big-endian (u256). Useful for
    `priority_fee_per_gas` (K62), `effective_gas_price` (K70),
    and `tx_cost_compute` (K71) which take this pair as input.

    Composes:
      - PR-K40 `tx_type_dispatch`        — typed-tx detector
      - RlpWalk cursor helpers           — field bounds
      - `rlp_content_to_u256_be_strict` helper  — canonical u256 content decoder

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 32-byte out (max_priority_fee BE)
      a3 (input)  : 32-byte out (max_fee BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : first u256 field extraction failed
        3 : max_fee field extraction failed (typed only)

    Both outputs zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`tegp_type`, `tegp_inner_off`). Non-canonical integer
    encodings are rejected by the content decoder. -/
def txExtractGasPricingFunction : String :=
  "tx_extract_gas_pricing:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # max_priority_fee out (32B)\n" ++
  "  mv s3, a3                   # max_fee out (32B)\n" ++
  "  # Pre-zero both outputs.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  # Step 1: tx_type_dispatch.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tegp_type\n" ++
  "  la a3, tegp_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Ltegp_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_after_dispatch:\n" ++
  "  la t0, tegp_type;      ld s4, 0(t0)    # type → s4\n" ++
  "  la t0, tegp_inner_off; ld t5, 0(t0)\n" ++
  "  add a0, s0, t5                          # inner_ptr\n" ++
  "  sub a1, s1, t5                          # inner_len\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Ltegp_p_fail\n" ++
  "  mv s5, a0                               # cursor\n" ++
  "  mv s6, a1                               # end\n" ++
  "  # Determine first u256 field index.\n" ++
  "  # Legacy: gas_price=1. 2930: gas_price=2. 1559/4844/7702: max_priority=2.\n" ++
  "  li t0, 0\n" ++
  "  beq s4, t0, .Ltegp_p_legacy\n" ++
  txExtractWalkFieldAsm ".Ltegp_p_fail" 2 ++
  "  j .Ltegp_p_have\n" ++
  ".Ltegp_p_legacy:\n" ++
  txExtractWalkFieldAsm ".Ltegp_p_fail" 1 ++
  ".Ltegp_p_have:\n" ++
  "  mv s7, a0                               # cursor after first fee field\n" ++
  "  mv a0, t6\n" ++
  "  mv a1, a2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, rlp_content_to_u256_be_strict\n" ++
  "  beqz a0, .Ltegp_after_p\n" ++
  ".Ltegp_p_fail:\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_after_p:\n" ++
  "  # If legacy or 2930, copy max_priority_fee → max_fee.\n" ++
  "  li t0, 2\n" ++
  "  bgeu s4, t0, .Ltegp_typed_fee\n" ++
  "  ld t0,  0(s2); sd t0,  0(s3)\n" ++
  "  ld t0,  8(s2); sd t0,  8(s3)\n" ++
  "  ld t0, 16(s2); sd t0, 16(s3)\n" ++
  "  ld t0, 24(s2); sd t0, 24(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_typed_fee:\n" ++
  "  # Type 2/3/4: max_fee = next field after max_priority.\n" ++
  "  mv s5, s7\n" ++
  txExtractWalkFieldAsm ".Ltegp_fee_fail" 0 ++
  "  mv a0, t6\n" ++
  "  mv a1, a2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, rlp_content_to_u256_be_strict\n" ++
  "  beqz a0, .Ltegp_ok\n" ++
  ".Ltegp_fee_fail:\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Ltegp_ret\n" ++
  ".Ltegp_ok:\n" ++
  "  li a0, 0\n" ++
  ".Ltegp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-! ## tx_effective_gas_pricing -- EEST reusable fee pricing

    Compose `tx_extract_gas_pricing` with the u256 fee-pricing helpers to
    produce the values needed by general transaction settlement:

      priority_fee_per_gas = min(max_priority_fee, max_fee - base_fee)
      effective_gas_price  = base_fee + priority_fee_per_gas

    `tx_extract_gas_pricing` normalizes legacy and EIP-2930 `gas_price` by
    writing it to both max-priority and max-fee outputs, so the same formula
    gives `effective_gas_price = gas_price` and
    `priority_fee_per_gas = gas_price - base_fee`.

    Calling convention:
      a0 (input)  : tx bytes ptr
      a1 (input)  : tx byte length
      a2 (input)  : base_fee_per_gas ptr (32 B BE)
      a3 (input)  : effective_gas_price out ptr (32 B BE)
      a4 (input)  : priority_fee_per_gas out ptr (32 B BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx pricing extraction failed
        2 : max_fee_per_gas < max_priority_fee_per_gas
        3 : max_fee_per_gas < base_fee_per_gas
        4 : effective_gas_price addition overflowed -/
def txEffectiveGasPricing_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .MV .x18 .x14,
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 68)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 68)),
    .AUIPC .x13 (laHi GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 76)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 76)),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_gas_pricing (GuestAddrs.tx_effective_gas_pricing + 84)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (148 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 100)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 100)),
    .AUIPC .x11 (laHi GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 108)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 108)),
    .AUIPC .x12 (laHi GuestAddrs.tefgp_tmp (GuestAddrs.tx_effective_gas_pricing + 116)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tefgp_tmp (GuestAddrs.tx_effective_gas_pricing + 116)),
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.tx_effective_gas_pricing + 124)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (108 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 140)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 140)),
    .AUIPC .x11 (laHi GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 148)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 148)),
    .MV .x12 .x8,
    .MV .x13 .x18,
    .JAL .x1 (jalOff GuestAddrs.priority_fee_per_gas_eip1559 (GuestAddrs.tx_effective_gas_pricing + 164)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (52 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.tx_effective_gas_pricing + 208)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .LI .x10 (4 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEffectiveGasPricing_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEffectiveGasPricing_relocs : RelocTable :=
  [ (17, .la .x12 "tefgp_max_priority"),
    (19, .la .x13 "tefgp_max_fee"),
    (21, .jal .x1 "tx_extract_gas_pricing"),
    (25, .la .x10 "tefgp_max_fee"),
    (27, .la .x11 "tefgp_max_priority"),
    (29, .la .x12 "tefgp_tmp"),
    (31, .jal .x1 "u256_sub_be"),
    (35, .la .x10 "tefgp_max_priority"),
    (37, .la .x11 "tefgp_max_fee"),
    (41, .jal .x1 "priority_fee_per_gas_eip1559"),
    (52, .jal .x1 "u256_add_be") ]

def txEffectiveGasPricingFunction : String :=
  "tx_effective_gas_pricing:\n" ++ emitProgramR txEffectiveGasPricing_prog txEffectiveGasPricing_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEffectiveGasPricing_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEffectiveGasPricingFunction_eq_prog :
    txEffectiveGasPricingFunction = "tx_effective_gas_pricing:\n" ++ emitProgramR txEffectiveGasPricing_prog txEffectiveGasPricing_relocs := rfl

#guard txEffectiveGasPricingFunction.startsWith "tx_effective_gas_pricing:\n"
#guard txEffectiveGasPricing_prog.length = 68

/-! ## access_list_count -- PR-K48 EIP-2930+ access-list cardinality

    Walk an RLP-encoded EIP-2930+ access_list and return
    `(num_addresses, num_storage_keys)`. These are the two
    inputs to the EIP-2930+ intrinsic-gas formula:

      gas_access_list = 2400 × num_addresses + 1900 × num_storage_keys

    Access-list shape:

      access_list = [
        [address (20 B), [slot1 (32 B), slot2 (32 B), ...]],
        ...
      ]

    Both `access_list` and each per-address `[slots...]` sub-list
    are RLP lists. This helper composes:

      1. PR-K47 `rlp_list_count_items` on the outer access_list to
         get N = num_addresses (and validate the outer shape).
      2. PR-K20 `rlp_list_nth_item` to extract each entry's bounds.
      3. PR-K20 `rlp_list_nth_item` on each entry to get field 1
         (the slots sub-list).
      4. PR-K47 `rlp_list_count_items` on the slots sub-list to add
         to num_storage_keys.

    Empty access_list (`0xc0`) → (0, 0).

    Calling convention:
      a0 (input)  : access_list bytes ptr (whole encoded item incl.
                    outer RLP list prefix)
      a1 (input)  : access_list byte length
      a2 (input)  : u64 out ptr for num_addresses
      a3 (input)  : u64 out ptr for num_storage_keys
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail.

    Uses three 8-byte `.data` scratch slots
    (`alc_scratch`, `alc_entry_offset`, `alc_entry_length`,
    `alc_keys_offset`, `alc_keys_length`). -/
def accessListCount_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 64)),
    .ADDI .x12 .x12 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 64)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.access_list_count + 72)),
    .BNE .x10 .x0 (228 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 80)),
    .LD .x20 .x5 (0 : BitVec 12),
    .BEQ .x20 .x0 (200 : BitVec 13),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x20 (192 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x21,
    .AUIPC .x13 (laHi GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 116)),
    .AUIPC .x14 (laHi GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 124)),
    .ADDI .x14 .x14 (laLo GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 124)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.access_list_count + 132)),
    .BNE .x10 .x0 (168 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 140)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 152)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x6,
    .MV .x11 .x7,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 176)),
    .ADDI .x13 .x13 (laLo GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 176)),
    .AUIPC .x14 (laHi GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 184)),
    .ADDI .x14 .x14 (laLo GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 184)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.access_list_count + 192)),
    .BNE .x10 .x0 (108 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 200)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 212)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x28,
    .ADD .x10 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 232)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 244)),
    .ADDI .x12 .x12 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 244)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.access_list_count + 252)),
    .BNE .x10 .x0 (48 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 260)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 260)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x19 (0 : BitVec 12),
    .ADD .x7 .x7 .x6,
    .SD .x19 .x7 (0 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-188 : BitVec 21),
    .SD .x18 .x20 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accessListCount_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accessListCount_relocs : RelocTable :=
  [ (16, .la .x12 "alc_scratch"),
    (18, .jal .x1 "rlp_list_count_items"),
    (20, .la .x5 "alc_scratch"),
    (29, .la .x13 "alc_entry_offset"),
    (31, .la .x14 "alc_entry_length"),
    (33, .jal .x1 "rlp_list_nth_item"),
    (35, .la .x5 "alc_entry_offset"),
    (38, .la .x5 "alc_entry_length"),
    (44, .la .x13 "alc_keys_offset"),
    (46, .la .x14 "alc_keys_length"),
    (48, .jal .x1 "rlp_list_nth_item"),
    (50, .la .x5 "alc_entry_offset"),
    (53, .la .x5 "alc_keys_offset"),
    (58, .la .x5 "alc_keys_length"),
    (61, .la .x12 "alc_scratch"),
    (63, .jal .x1 "rlp_list_count_items"),
    (65, .la .x5 "alc_scratch") ]

def accessListCountFunction : String :=
  "access_list_count:\n" ++ emitProgramR accessListCount_prog accessListCount_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accessListCount_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accessListCountFunction_eq_prog :
    accessListCountFunction = "access_list_count:\n" ++ emitProgramR accessListCount_prog accessListCount_relocs := rfl

#guard accessListCountFunction.startsWith "access_list_count:\n"
#guard accessListCount_prog.length = 88

end EvmAsm.Codegen
