/-
  EvmAsm.Codegen.Programs.EvmNonce

  Witness-side NONCE opcode probe split out of `EvmOpcodes.lean`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## nonce_at_header_state_root

    Witness-side getter for `account.nonce` as a u64. Same
    "absent → 0" flattening as BALANCE and SLOAD. Useful for:
      * CREATE/CREATE2 address derivation
        (`keccak(rlp([sender, sender.nonce]))[12:]`)
      * EIP-684 collision checks (`nonce > 0` arm)
      * Nonce monotonicity checks on EOAs

    Distinct from `account_at_header_state_root` (which surfaces
    missing accounts as status 1): NONCE flattens absence to
    `(status=0, nonce=0)` per the spec's "uninitialised accounts
    have nonce 0" rule.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : u64 out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (nonce written to output; 0 for absent)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

      (Code 1 is intentionally absent: missing accounts map to
      `status=0, nonce=0` per the spec.)
-/
def nonceAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .SD .x21 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.nonce_state_root (GuestAddrs.nonce_at_header_state_root + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.nonce_state_root (GuestAddrs.nonce_at_header_state_root + 72)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.nonce_at_header_state_root + 80)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (80 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.nonce_state_root (GuestAddrs.nonce_at_header_state_root + 104)),
    .ADDI .x12 .x12 (laLo GuestAddrs.nonce_state_root (GuestAddrs.nonce_at_header_state_root + 104)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x22 (laHi GuestAddrs.nonce_acct_struct (GuestAddrs.nonce_at_header_state_root + 120)),
    .ADDI .x22 .x22 (laLo GuestAddrs.nonce_acct_struct (GuestAddrs.nonce_at_header_state_root + 120)),
    .MV .x15 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.nonce_at_header_state_root + 132)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LD .x6 .x22 (0 : BitVec 12),
    .SD .x21 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `nonceAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def nonceAtHeaderStateRoot_relocs : RelocTable :=
  [ (18, .la .x12 "nonce_state_root"),
    (20, .jal .x1 "header_extract_state_root"),
    (26, .la .x12 "nonce_state_root"),
    (30, .la .x22 "nonce_acct_struct"),
    (33, .jal .x1 "account_at_address") ]

def nonceAtHeaderStateRootFunction : String :=
  "nonce_at_header_state_root:\n" ++ emitProgramR nonceAtHeaderStateRoot_prog nonceAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `nonceAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem nonceAtHeaderStateRootFunction_eq_prog :
    nonceAtHeaderStateRootFunction = "nonce_at_header_state_root:\n" ++ emitProgramR nonceAtHeaderStateRoot_prog nonceAtHeaderStateRoot_relocs := rfl

#guard nonceAtHeaderStateRootFunction.startsWith "nonce_at_header_state_root:\n"
#guard nonceAtHeaderStateRoot_prog.length = 53
/-- `zisk_nonce_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..16 : nonce (u64 LE; 0 on absent) -/
def ziskNonceAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a5, 0xa0010008           # u64 output\n" ++
  "  jal ra, nonce_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lnonce_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  nonceAtHeaderStateRootFunction ++ "\n" ++
  ".Lnonce_pdone:"

def ziskNonceAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "nonce_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "nonce_acct_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
