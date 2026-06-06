/-
  EvmAsm.Codegen.Programs.HeaderChain

  Header-chain validators carved out of
  `EvmAsm.Codegen.Programs.Header` per the file-size hard cap.
  Hosts:

    K173  validate_parent_hash_link
    K174  validate_header_pair
    K175  validate_header_chain
    K187  block_hash_array_from_chain
    K195  validate_block_hash_chain_match

  These compose K172 `block_hash_from_header` and K72
  `check_gas_limit` (which stay in `Programs/Header.lean`) plus
  the usual K20 / K34 RLP helpers and the Keccak bridge.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## validate_parent_hash_link -- PR-K173

    Given a parent header (parent_rlp) and a child header
    (child_rlp), verify that
    `child.parent_hash == keccak256(parent_rlp)`.

    This is the per-step check inside `validate_headers`: each
    pair of consecutive headers in the chain must satisfy this
    invariant; the full chain follows by induction.

    Algorithm:
      1. K20 extract field 0 (parent_hash) from child_rlp.
         Verify field length == 32.
      2. K172 `block_hash_from_header(parent_rlp)` ->
         computed_hash.
      3. 32-byte memcmp(claimed, computed).
      4. Write verdict (1 = matches, 0 = mismatch); status
         disambiguates parse vs. size vs. predicate failure.

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : child_rlp ptr
      a3 (input)  : child_rlp byte length
      a4 (input)  : u64 out (is_valid: 1 if links, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : child RLP parse failure / field 0 missing
        2 : child.parent_hash length != 32 -/
def validateParentHashLinkFunction : String :=
  "validate_parent_hash_link:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # parent_rlp ptr\n" ++
  "  mv s1, a1                   # parent_rlp len\n" ++
  "  mv s2, a2                   # child_rlp ptr\n" ++
  "  mv s3, a3                   # child_rlp len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Extract child.parent_hash (field 0) ----\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 0\n" ++
  "  la a3, vphl_offset; la a4, vphl_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lvphl_parse_fail\n" ++
  "  la t0, vphl_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lvphl_size_fail\n" ++
  "  # Copy claimed parent_hash into vphl_claimed\n" ++
  "  la t0, vphl_offset; ld t1, 0(t0)\n" ++
  "  add t3, s2, t1                              # &child[off]\n" ++
  "  la t4, vphl_claimed\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # ---- Compute keccak256(parent_rlp) ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, vphl_computed\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # ---- 32-byte compare ----\n" ++
  "  la t0, vphl_claimed\n" ++
  "  la t1, vphl_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvphl_ret\n" ++
  ".Lvphl_neq:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvphl_ret\n" ++
  ".Lvphl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lvphl_ret\n" ++
  ".Lvphl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lvphl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_validate_parent_hash_link`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : child_rlp_len
      bytes 16..   : parent_rlp || child_rlp
    Output layout:
      bytes  0.. 8 : status (0=ok, 1=child parse, 2=size fail)
      bytes  8..16 : is_valid (1 if links, else 0) -/
def ziskValidateParentHashLinkPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)               # child_rlp_len\n" ++
  "  addi a0, a7, 24             # parent_rlp ptr\n" ++
  "  add a2, a0, a1              # child_rlp ptr = parent_rlp + parent_len\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, validate_parent_hash_link\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvphl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  ".Lvphl_pdone:"

def ziskValidateParentHashLinkDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32"

def ziskValidateParentHashLinkProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateParentHashLinkPrologue
  dataAsm     := ziskValidateParentHashLinkDataSection
}

/-! ## validate_header_pair -- PR-K174

    Per-step pair validator inside `validate_headers`: given a
    parent header and a child header, verify the four
    invariants the EELS `validate_header` function checks
    between consecutive headers:

      1. child.parent_hash == keccak256(parent_rlp)         (K173)
      2. child.number == parent.number + 1
      3. child.timestamp > parent.timestamp
      4. check_gas_limit(child.gas_limit, parent.gas_limit) == 0
         (gas_limit >= 5000 and |new - parent| < parent/1024)

    Per-header field-shape checks (`validate_header_basic`,
    `validate_header_post_merge`, etc.) live in their own
    helpers; this primitive is the **pair** check only.

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : child_rlp ptr
      a3 (input)  : child_rlp byte length
      a4 (input)  : u64 out (is_valid: 1 if all 4 invariants hold)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : child RLP parse failure
        2 : child.parent_hash length != 32
        3 : parent number/timestamp/gas_limit field parse failure
        4 : child number/timestamp/gas_limit field parse failure -/
def validateHeaderPairFunction : String :=
  "validate_header_pair:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # parent_rlp ptr\n" ++
  "  mv s1, a1                   # parent_rlp len\n" ++
  "  mv s2, a2                   # child_rlp ptr\n" ++
  "  mv s3, a3                   # child_rlp len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- (1) Parent-hash link ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, vhp_link_valid\n" ++
  "  jal ra, validate_parent_hash_link\n" ++
  "  beqz a0, .Lvhp_link_ok\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lvhp_child_parse_fail\n" ++
  "  j .Lvhp_size_fail\n" ++
  ".Lvhp_link_ok:\n" ++
  "  la t0, vhp_link_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvhp_pred_false\n" ++
  "  # ---- (2/3/4) Extract parent number/timestamp/gas_limit ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, vhp_parent_number\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_parent_field_fail\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  la a3, vhp_parent_timestamp\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_parent_field_fail\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  la a3, vhp_parent_gas_limit\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_parent_field_fail\n" ++
  "  # ---- Extract child number/timestamp/gas_limit ----\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 8\n" ++
  "  la a3, vhp_child_number\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_child_field_fail\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 11\n" ++
  "  la a3, vhp_child_timestamp\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_child_field_fail\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 9\n" ++
  "  la a3, vhp_child_gas_limit\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_child_field_fail\n" ++
  "  # (2) child.number == parent.number + 1\n" ++
  "  la t0, vhp_parent_number; ld t1, 0(t0)\n" ++
  "  la t0, vhp_child_number;  ld t2, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  bne t1, t2, .Lvhp_pred_false\n" ++
  "  # (3) child.timestamp > parent.timestamp\n" ++
  "  la t0, vhp_parent_timestamp; ld t1, 0(t0)\n" ++
  "  la t0, vhp_child_timestamp;  ld t2, 0(t0)\n" ++
  "  bgeu t1, t2, .Lvhp_pred_false\n" ++
  "  # (4) check_gas_limit(child, parent) == 0\n" ++
  "  la t0, vhp_child_gas_limit;  ld a0, 0(t0)\n" ++
  "  la t0, vhp_parent_gas_limit; ld a1, 0(t0)\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  bnez a0, .Lvhp_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_child_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_size_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_parent_field_fail:\n" ++
  "  li a0, 3\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_child_field_fail:\n" ++
  "  li a0, 4\n" ++
  ".Lvhp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_validate_header_pair`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : child_rlp_len
      bytes 16..   : parent_rlp || child_rlp
    Output layout:
      bytes  0.. 8 : status code (0..4)
      bytes  8..16 : is_valid (1 if all four invariants hold) -/
def ziskValidateHeaderPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)               # child_rlp_len\n" ++
  "  addi a0, a7, 24             # parent_rlp ptr\n" ++
  "  add a2, a0, a1              # child_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvhp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  ".Lvhp_pdone:"

def ziskValidateHeaderPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8"

def ziskValidateHeaderPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderPairPrologue
  dataAsm     := ziskValidateHeaderPairDataSection
}

/-! ## validate_header_chain -- PR-K175

    Iterate `validate_header_pair` (K174) over N consecutive
    headers (parent, child) and verify every link in the
    chain. This is the EELS `validate_headers` function: walk
    the witness list and assert each successive pair of
    headers satisfies the four pair invariants:

      1. child.parent_hash == keccak256(parent)
      2. child.number == parent.number + 1
      3. child.timestamp > parent.timestamp
      4. check_gas_limit(child, parent) == 0

    Stops on the first failing pair and reports the failing
    index. Empty (N == 0) and singleton (N == 1) chains are
    accepted vacuously -- there is no pair to check.

    Header layout (one length-prefix table + flat byte blob):
      headers[0] starts at headers_ptr + offsets[0]
      headers[i] has length lengths[i]
      offsets[i+1] = offsets[i] + lengths[i]
    The caller supplies `lengths` (a `u64[N]`); offsets are
    computed inline.

    Calling convention:
      a0 (input)  : header count N
      a1 (input)  : lengths ptr (u64[N], byte lengths)
      a2 (input)  : headers ptr (flat concatenated RLPs)
      a3 (input)  : u64 out (is_valid: 1 if every link OK)
      a4 (input)  : u64 out (first_bad_index: index of the
                    failing pair; 0 if all pairs pass)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status from validate_header_pair
                  for the first failing pair (1..4) -/
def validateHeaderChainFunction : String :=
  "validate_header_chain:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # is_valid out\n" ++
  "  mv s4, a4                   # first_bad_index out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # Vacuous-true for N == 0 or N == 1.\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lvhc_vacuous\n" ++
  "  # parent ptr/len start (i = 0)\n" ++
  "  mv s5, s2                   # current parent ptr\n" ++
  "  li s6, 0                    # current index i\n" ++
  ".Lvhc_loop:\n" ++
  "  # Pre-compute child index = i + 1\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s0, .Lvhc_done       # i+1 == N -> finished\n" ++
  "  # parent_len = lengths[i], child_len = lengths[i+1]\n" ++
  "  slli t1, s6, 3\n" ++
  "  add t1, s1, t1                              # &lengths[i]\n" ++
  "  ld t2, 0(t1)                                # parent_len\n" ++
  "  ld t3, 8(t1)                                # child_len\n" ++
  "  add t4, s5, t2                              # child_ptr = parent_ptr + parent_len\n" ++
  "  mv a0, s5; mv a1, t2\n" ++
  "  mv a2, t4; mv a3, t3\n" ++
  "  la a4, vhc_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  bnez a0, .Lvhc_pair_status_fail\n" ++
  "  la t0, vhc_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvhc_pred_false\n" ++
  "  # Advance: parent <- child\n" ++
  "  slli t1, s6, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)                                # parent_len (just used)\n" ++
  "  add s5, s5, t2                              # parent_ptr += parent_len\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lvhc_loop\n" ++
  ".Lvhc_done:\n" ++
  ".Lvhc_vacuous:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhc_ret\n" ++
  ".Lvhc_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s6, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhc_ret\n" ++
  ".Lvhc_pair_status_fail:\n" ++
  "  sd s6, 0(s4)\n" ++
  ".Lvhc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_validate_header_chain`: probe BuildUnit.
    Input layout:
      bytes  0..  8 : N (header count)
      bytes  8..  8 + 8*N : lengths (u64[N])
      bytes  8 + 8*N .. : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status code
      bytes  8..16 : is_valid (1 if every link OK)
      bytes 16..24 : first_bad_index -/
def ziskValidateHeaderChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a2, a1, t0              # headers ptr\n" ++
  "  li a3, 0xa0010008           # is_valid out\n" ++
  "  li a4, 0xa0010010           # first_bad_index out\n" ++
  "  jal ra, validate_header_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvhc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  validateHeaderChainFunction ++ "\n" ++
  ".Lvhc_pdone:"

def ziskValidateHeaderChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhc_pair_valid:\n" ++
  "  .zero 8"

def ziskValidateHeaderChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderChainPrologue
  dataAsm     := ziskValidateHeaderChainDataSection
}

/-! ## block_hash_array_from_chain -- PR-K187

    Validate an N-element header chain (K175) and, for each
    header, output its block_hash (K172) into a 32*N-byte
    output buffer. Combined output the caller can use to feed
    downstream chain-state machinery (block_hash precompile
    inputs, witness mapping, etc.).

    Iterates over the chain twice in spirit but only once in
    practice: walks `parent <- child` pairs, and for each
    header writes `keccak256(header_rlp)` to the corresponding
    32-byte slot.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : block_hash_out ptr (32*N bytes)
      a4 (input)  : u64 out (is_valid: 1 if chain accepts)
      a5 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate + block_hashes written
        nonzero : propagated status from validate_header_pair
                  for the first failing link (block_hashes for
                  headers up to and including the failure point
                  are still written)

    Special: for N == 0, write nothing and report is_valid=1.
    For N == 1, validate trivially and write only block_hash[0]. -/
def blockHashArrayFromChainFunction : String :=
  "block_hash_array_from_chain:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # block_hash_out ptr\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  mv s5, a5                   # first_bad_index out\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)                # default is_valid = 1\n" ++
  "  sd zero, 0(s5)\n" ++
  "  beqz s0, .Lbhac_done\n" ++
  "  # Write block_hash[0]\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2; mv a2, s3\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  li t0, 1\n" ++
  "  beq s0, t0, .Lbhac_done     # N == 1 -> trivially valid\n" ++
  "  # Walk the chain, validating each link and writing block_hashes.\n" ++
  "  mv s6, s2                   # parent ptr = headers[0]\n" ++
  "  li s7, 0                    # i = 0\n" ++
  "  addi s8, s3, 32             # next block_hash slot = block_hash_out + 32\n" ++
  ".Lbhac_loop:\n" ++
  "  addi t0, s7, 1\n" ++
  "  beq t0, s0, .Lbhac_done\n" ++
  "  # parent_len = header_lengths[i]; child_len = header_lengths[i+1]\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld a1, 0(t1)                # parent_len\n" ++
  "  ld a3, 8(t1)                # child_len\n" ++
  "  add t2, s6, a1              # child ptr\n" ++
  "  mv a0, s6\n" ++
  "  mv a2, t2\n" ++
  "  la a4, bhac_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  bnez a0, .Lbhac_status_fail\n" ++
  "  la t0, bhac_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbhac_pred_false\n" ++
  "  # Write block_hash[i+1]\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)                # parent_len[i]\n" ++
  "  ld t3, 8(t1)                # child_len[i+1] (= header[i+1] len)\n" ++
  "  add t4, s6, t2              # child ptr\n" ++
  "  mv a0, t4; mv a1, t3; mv a2, s8\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Advance\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)\n" ++
  "  add s6, s6, t2              # parent ptr += parent_len\n" ++
  "  addi s8, s8, 32             # next block_hash slot\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lbhac_loop\n" ++
  ".Lbhac_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbhac_ret\n" ++
  ".Lbhac_status_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  j .Lbhac_ret\n" ++
  ".Lbhac_done:\n" ++
  "  li a0, 0\n" ++
  ".Lbhac_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_hash_array_from_chain`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths (u64[N])
      bytes  8+8N.. : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid
      bytes 16..24 : first_bad_index
      bytes 24..   : block_hash[0], block_hash[1], ... (32*N B)
    Caveat: ziskemu output is capped at 256 B, so this probe
    test is meaningful only for N <= 7 (status+valid+bad = 24,
    remaining 232 B fits 7 hashes). -/
def ziskBlockHashArrayFromChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a2, a1, t0              # headers ptr\n" ++
  "  li a3, 0xa0010018           # block_hash_out at OUTPUT + 24\n" ++
  "  li a4, 0xa0010008           # is_valid\n" ++
  "  li a5, 0xa0010010           # first_bad_index\n" ++
  "  jal ra, block_hash_array_from_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhac_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockHashArrayFromChainFunction ++ "\n" ++
  ".Lbhac_pdone:"

def ziskBlockHashArrayFromChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "bhac_pair_valid:\n" ++
  "  .zero 8"

def ziskBlockHashArrayFromChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashArrayFromChainPrologue
  dataAsm     := ziskBlockHashArrayFromChainDataSection
}

/-! ## validate_block_hash_chain_match -- PR-K195

    Validate an N-element header chain (K175 invariants) AND
    check that the block_hash of each header (K172) matches a
    caller-supplied claim array. This is the natural primitive
    for chain-anchor proofs: \"the prover claims these are
    block_hashes B[0..N) for blocks H[0..N); verify both that
    the chain is well-formed and that the claimed hashes are
    correct\".

    The two checks (chain validity + hash match) are returned
    via a single is_valid u64; a status code distinguishes
    structural-fail (chain links broken) from hash-mismatch.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : claimed_hashes ptr (32*N bytes)
      a4 (input)  : u64 out (is_valid)
      a5 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status from validate_header_pair
                  for the first failing link -/
def validateBlockHashChainMatchFunction : String :=
  "validate_block_hash_chain_match:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # claimed_hashes ptr (32*N)\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  mv s5, a5                   # first_bad_index out\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  sd zero, 0(s5)\n" ++
  "  beqz s0, .Lvbhcm_done       # N==0: vacuous true\n" ++
  "  # ---- Verify block_hash[0] matches ----\n" ++
  "  ld a1, 0(s1)                # header_lengths[0]\n" ++
  "  mv a0, s2                   # header_rlp[0]\n" ++
  "  la a2, vbhcm_hash_buf\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  la t0, vbhcm_hash_buf; mv t1, s3\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  li t0, 1\n" ++
  "  beq s0, t0, .Lvbhcm_done    # N==1: just hash check, no chain\n" ++
  "  # ---- Walk chain ----\n" ++
  "  mv s6, s2                   # parent_ptr = headers[0]\n" ++
  "  li s7, 0                    # i = 0\n" ++
  "  addi s8, s3, 32             # next claimed_hash slot\n" ++
  ".Lvbhcm_loop:\n" ++
  "  addi t0, s7, 1\n" ++
  "  beq t0, s0, .Lvbhcm_done\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld a1, 0(t1)                # parent_len\n" ++
  "  ld a3, 8(t1)                # child_len\n" ++
  "  add t2, s6, a1              # child_ptr\n" ++
  "  mv a0, s6\n" ++
  "  mv a2, t2\n" ++
  "  la a4, vbhcm_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  bnez a0, .Lvbhcm_status_fail\n" ++
  "  la t0, vbhcm_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvbhcm_pred_false\n" ++
  "  # Hash child and compare to claimed\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)                # parent_len\n" ++
  "  ld t3, 8(t1)                # child_len\n" ++
  "  add t4, s6, t2              # child_ptr\n" ++
  "  mv a0, t4; mv a1, t3\n" ++
  "  la a2, vbhcm_hash_buf\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  la t0, vbhcm_hash_buf; mv t1, s8\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  # Advance\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)\n" ++
  "  add s6, s6, t2\n" ++
  "  addi s8, s8, 32\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lvbhcm_loop\n" ++
  ".Lvbhcm_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvbhcm_ret\n" ++
  ".Lvbhcm_status_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  j .Lvbhcm_ret\n" ++
  ".Lvbhcm_done:\n" ++
  "  li a0, 0\n" ++
  ".Lvbhcm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_validate_block_hash_chain_match`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N        : header_lengths
      bytes  8+8N..8+8N+32N : claimed_hashes (32 B each)
      bytes  8+40N..        : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid
      bytes 16..24 : first_bad_index -/
def ziskValidateBlockHashChainMatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a3, a1, t0              # claimed_hashes ptr\n" ++
  "  slli t1, a0, 5              # 32*N\n" ++
  "  add a2, a3, t1              # headers ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  li a5, 0xa0010010           # first_bad_index out\n" ++
  "  jal ra, validate_block_hash_chain_match\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvbhcm_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  validateBlockHashChainMatchFunction ++ "\n" ++
  ".Lvbhcm_pdone:"

def ziskValidateBlockHashChainMatchDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vbhcm_pair_valid:\n" ++
  "  .zero 8\n" ++
  "vbhcm_hash_buf:\n" ++
  "  .zero 32"

def ziskValidateBlockHashChainMatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateBlockHashChainMatchPrologue
  dataAsm     := ziskValidateBlockHashChainMatchDataSection
}


end EvmAsm.Codegen
