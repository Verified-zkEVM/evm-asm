/-
  EvmAsm.Codegen.Programs.ValidateHeaderPair

  validate_header_rlp_pair (bead evm-asm-fhsxz.2.3): the guest-callable
  "is this block header a valid child of its parent?" check, composed from
  already-verified primitives. The stateless guest's Block/ValidateHeader is
  currently a scaffold; this is the sound validator it needs before the
  Step-2 verdict (.2.4) can set successful_validation.

  Given two RLP headers (this, parent) it:
    1. header_extended_decode (K39) each into a 144-byte field struct;
    2. validate_header_full (K75) — post-merge + extra_data + gas/number/
       timestamp + gas-limit drift + EIP-1559 base-fee, all against the
       parent struct;
    3. header_validate_parent_hash (K94) — this.parent_hash == keccak256(parent).

  Composing the FULL K75 validation (not a subset) keeps the verdict sound:
  a partial check could pass a header with a wrong base-fee and false-positive
  an invalid block. Status (so callers can see which gate failed):
    0          valid child
    1          this-header parse fail        2  parent-header parse fail
    100..602   validate_header_full failure  (K75's decade encoding)
    701..702   parent-hash failure           (K94 sub-status + 700)

  Bundles only existing, tested functions; their scratch is the union of the
  K75 / K39 / K94 probe data sections (all label-disjoint) plus two 128-byte
  decode structs. All reads aligned (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.HeadersKeccak

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## validate_header_rlp_pair -- full validity of a header vs its parent

    a0 = this header RLP ptr     a1 = this header RLP length
    a2 = parent header RLP ptr   a3 = parent header RLP length
    a0 (output) = status (see module doc). -/
def validateHeaderRlpPairFunction : String :=
  "validate_header_rlp_pair:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # this rlp\n" ++
  "  mv s1, a1                   # this len\n" ++
  "  mv s2, a2                   # parent rlp\n" ++
  "  mv s3, a3                   # parent len\n" ++
  "  # decode this header -> vhrp_this_struct (144 B).\n" ++
  "  la a2, vhrp_this_struct\n" ++
  "  jal ra, header_extended_decode\n" ++
  "  bnez a0, .Lvhrp_this_parse\n" ++
  "  # decode parent header -> vhrp_parent_struct.\n" ++
  "  mv a0, s2; mv a1, s3; la a2, vhrp_parent_struct\n" ++
  "  jal ra, header_extended_decode\n" ++
  "  bnez a0, .Lvhrp_parent_parse\n" ++
  "  # full field validation (this vs parent).\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, vhrp_this_struct; la a3, vhrp_parent_struct\n" ++
  "  jal ra, validate_header_full\n" ++
  "  bnez a0, .Lvhrp_ret         # already >=100, decade-encoded\n" ++
  "  # parent_hash linkage: this.parent_hash == keccak256(parent_rlp).\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3\n" ++
  "  jal ra, header_validate_parent_hash\n" ++
  "  beqz a0, .Lvhrp_ret         # 0 = valid\n" ++
  "  addi a0, a0, 700            # 701 parse / 702 mismatch\n" ++
  "  j .Lvhrp_ret\n" ++
  ".Lvhrp_this_parse:\n" ++
  "  li a0, 1\n" ++
  "  j .Lvhrp_ret\n" ++
  ".Lvhrp_parent_parse:\n" ++
  "  li a0, 2\n" ++
  ".Lvhrp_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_validate_header_rlp_pair`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  this header RLP length (u64)
      +16 parent header RLP length (u64)
      +24 this header RLP bytes, immediately followed by parent header RLP
    Output: OUTPUT+0 = status (u64). -/
def ziskValidateHeaderRlpPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # this rlp length\n" ++
  "  ld a3, 16(t0)               # parent rlp length\n" ++
  "  addi a0, t0, 24             # this rlp ptr\n" ++
  "  add a2, a0, a1              # parent rlp ptr = this + this_len\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)   # status at OUTPUT+0\n" ++
  "  j .Lvhrp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  amsterdamBlobGasPriceFunction ++ "\n" ++
  amsterdamBlobGasPriceU256Function ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  headerValidateExcessBlobGasFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  validateHeaderRlpPairFunction ++ "\n" ++
  ".Lvhrp_pdone:"

/-- Data section: union of the K75 / K39 / K94 probe scratch (all
    label-disjoint) plus the two extended-decode structs. -/
def ziskValidateHeaderRlpPairDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "hvebg_threshold:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  "hvpm_off:\n  .zero 8\n" ++
  "hvpm_len:\n  .zero 8\n" ++
  "hved_off:\n  .zero 8\n" ++
  "hved_len:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "hmd_offset:\n  .zero 8\n" ++
  "hmd_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 32\n" ++
  "hvph_claimed:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "hvph_computed:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "vhrp_this_struct:\n  .zero 144\n" ++
  ".balign 8\n" ++
  "vhrp_parent_struct:\n  .zero 144"

def ziskValidateHeaderRlpPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderRlpPairPrologue
  dataAsm     := ziskValidateHeaderRlpPairDataSection
}

end EvmAsm.Codegen
