/-
  EvmAsm.Codegen.Programs.StatePredicates

  Account-level boolean predicates over a stateless witness +
  parent header. Distinct from `StateCompose.lean` (full-record
  composites returning the account struct or specific fields)
  in that each function here returns a u64 predicate (0 or 1)
  based on a single spec-defined check.

  Hosts probes for spec primitives such as `account_exists`
  (this PR), with room to grow for EIP-161 `account_is_empty`,
  `account_alive`, and similar one-bit checks.

  Each probe composes K201 `header_extract_state_root` and K28
  `account_at_address` from `State.lean`, then applies the
  spec-specific predicate to the resulting account struct or
  status code.

  No proofs yet -- codegen `String` defs only.
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

/-! ## account_exists_at_header_state_root

    Witness-side implementation of the spec's `account_exists`
    predicate: returns 1 iff the address has any record in the
    state trie referenced by the parent header's `state_root`,
    else 0.

    This is the most fundamental account-level predicate, used
    by the spec wherever `apply_body` distinguishes a fresh
    (never-touched) account from a previously-recorded one
    regardless of the account's contents. It does NOT inspect
    nonce, balance, code_hash, or storage_root -- it only asks
    "is the account in the trie?". That makes it distinct from:

      * EIP-1052 `extcodehash_at_header_state_root` -- returns
        0 for absent OR empty accounts but non-zero for
        non-empty ones (looks at contents).
      * EIP-684 `has_code_or_nonce_at_header_state_root` --
        looks at `nonce` and `code_hash` only.
      * EIP-161 `account_is_empty` -- returns 1 for both
        fully-empty AND absent accounts.

    The clean separation is on purpose: stateless verifiers that
    care about pure existence (e.g. SELFDESTRUCT-target
    accounting in some EIPs) need exactly this predicate, not
    one of the content-aware variants.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      ra (input)  : return

      a0 (output) :
        0 = success (`aex_predicate` holds 0 or 1)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

    The probe BuildUnit copies `aex_predicate` to OUTPUT + 8.
-/
def accountExistsAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
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
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.aex_predicate (GuestAddrs.account_exists_at_header_state_root + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aex_predicate (GuestAddrs.account_exists_at_header_state_root + 52)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.aex_state_root (GuestAddrs.account_exists_at_header_state_root + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aex_state_root (GuestAddrs.account_exists_at_header_state_root + 72)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.account_exists_at_header_state_root + 80)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (88 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.aex_state_root (GuestAddrs.account_exists_at_header_state_root + 104)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aex_state_root (GuestAddrs.account_exists_at_header_state_root + 104)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x21 (laHi GuestAddrs.aex_acct_struct (GuestAddrs.account_exists_at_header_state_root + 120)),
    .ADDI .x21 .x21 (laLo GuestAddrs.aex_acct_struct (GuestAddrs.account_exists_at_header_state_root + 120)),
    .MV .x15 .x21,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.account_exists_at_header_state_root + 132)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.aex_predicate (GuestAddrs.account_exists_at_header_state_root + 160)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aex_predicate (GuestAddrs.account_exists_at_header_state_root + 160)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountExistsAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountExistsAtHeaderStateRoot_relocs : RelocTable :=
  [ (13, .la .x5 "aex_predicate"),
    (18, .la .x12 "aex_state_root"),
    (20, .jal .x1 "header_extract_state_root"),
    (26, .la .x12 "aex_state_root"),
    (30, .la .x21 "aex_acct_struct"),
    (33, .jal .x1 "account_at_address"),
    (40, .la .x5 "aex_predicate") ]

def accountExistsAtHeaderStateRootFunction : String :=
  "account_exists_at_header_state_root:\n" ++ emitProgramR accountExistsAtHeaderStateRoot_prog accountExistsAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountExistsAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountExistsAtHeaderStateRootFunction_eq_prog :
    accountExistsAtHeaderStateRootFunction = "account_exists_at_header_state_root:\n" ++ emitProgramR accountExistsAtHeaderStateRoot_prog accountExistsAtHeaderStateRoot_relocs := rfl

#guard accountExistsAtHeaderStateRootFunction.startsWith "account_exists_at_header_state_root:\n"
#guard accountExistsAtHeaderStateRoot_prog.length = 54
/-- `zisk_account_exists_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..16 : predicate (u64; 0 or 1) -/
def ziskAccountExistsAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  jal ra, account_exists_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  la t1, aex_predicate; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Laex_pdone\n" ++
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
  accountExistsAtHeaderStateRootFunction ++ "\n" ++
  ".Laex_pdone:"

def ziskAccountExistsAtHeaderStateRootDataSection : String :=
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
  "aex_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aex_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aex_predicate:\n" ++
  "  .zero 8"

def ziskAccountExistsAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExistsAtHeaderStateRootPrologue
  dataAsm     := ziskAccountExistsAtHeaderStateRootDataSection
}

/-! ## account_is_empty_at_header_state_root  (EIP-161)

    Witness-side implementation of the EIP-161 `account_is_empty`
    predicate: returns 1 iff the account is present in the state
    trie AND has `nonce == 0` AND `balance == 0` AND
    `code_hash == EMPTY_CODE_HASH`.

    This is the predicate used by spec primitives that need
    EIP-161's notion of emptiness:
      * SELFDESTRUCT touched-account refund accounting.
      * SSTORE refund rules (EIP-2200 / Berlin).
      * CALL value-transfer "touch" semantics.

    Completes the boolean-predicate trio with:
      * `account_exists_at_header_state_root` (presence only;
        ignores contents).
      * `has_code_or_nonce_at_header_state_root` (EIP-684
        CREATE collision; nonce OR code, no balance).

    Spec-distinguishing rows (account_in_trie = present):

        | account contents             | exists | EIP-684 | EIP-161 |
        |------------------------------|--------|---------|---------|
        | fully empty                  |   1    |    0    |    1    |
        | balance only (n=0, c=EMPTY)  |   1    |    0    |    0    |
        | nonce only  (b=0, c=EMPTY)   |   1    |    1    |    0    |
        | contract    (c != EMPTY)     |   1    |    1    |    0    |
        | (not in trie)                |   0    |    0    |    0    |

    The `fully empty` row is where EIP-161 and EIP-684 give
    OPPOSITE results: EIP-161 says empty (1), EIP-684 says no
    collision (0). The `balance only` row is where EIP-161 and
    `account_exists` give opposite results (0 vs 1).

    Composes K201 `header_extract_state_root` + K28
    `account_at_address` + an inline 9 x u64 check (1 nonce + 4
    balance + 4 code_hash) against the baked-in EMPTY_CODE_HASH
    constant.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      ra (input)  : return

      a0 (output) :
        0 = success (`aie_predicate` holds 0 or 1)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

    Account-not-in-trie maps to predicate 0 (EIP-161 says empty
    only when account is PRESENT but trivially zero; an absent
    account is NOT empty per the strict spec read, because
    `state[addr]` is undefined rather than equal to the empty
    record). The probe BuildUnit copies `aie_predicate` to
    OUTPUT + 8.
-/
def accountIsEmptyAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
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
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.aie_predicate (GuestAddrs.account_is_empty_at_header_state_root + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aie_predicate (GuestAddrs.account_is_empty_at_header_state_root + 52)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.aie_state_root (GuestAddrs.account_is_empty_at_header_state_root + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aie_state_root (GuestAddrs.account_is_empty_at_header_state_root + 72)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.account_is_empty_at_header_state_root + 80)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (192 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.aie_state_root (GuestAddrs.account_is_empty_at_header_state_root + 104)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aie_state_root (GuestAddrs.account_is_empty_at_header_state_root + 104)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x21 (laHi GuestAddrs.aie_acct_struct (GuestAddrs.account_is_empty_at_header_state_root + 120)),
    .ADDI .x21 .x21 (laLo GuestAddrs.aie_acct_struct (GuestAddrs.account_is_empty_at_header_state_root + 120)),
    .MV .x15 .x21,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.account_is_empty_at_header_state_root + 132)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (136 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (128 : BitVec 21),
    .LD .x6 .x21 (0 : BitVec 12),
    .BNE .x6 .x0 (116 : BitVec 13),
    .LD .x6 .x21 (8 : BitVec 12),
    .BNE .x6 .x0 (108 : BitVec 13),
    .LD .x6 .x21 (16 : BitVec 12),
    .BNE .x6 .x0 (100 : BitVec 13),
    .LD .x6 .x21 (24 : BitVec 12),
    .BNE .x6 .x0 (92 : BitVec 13),
    .LD .x6 .x21 (32 : BitVec 12),
    .BNE .x6 .x0 (84 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aie_empty_code_hash (GuestAddrs.account_is_empty_at_header_state_root + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aie_empty_code_hash (GuestAddrs.account_is_empty_at_header_state_root + 200)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x21 (72 : BitVec 12),
    .BNE .x6 .x7 (64 : BitVec 13),
    .LD .x6 .x5 (8 : BitVec 12),
    .LD .x7 .x21 (80 : BitVec 12),
    .BNE .x6 .x7 (52 : BitVec 13),
    .LD .x6 .x5 (16 : BitVec 12),
    .LD .x7 .x21 (88 : BitVec 12),
    .BNE .x6 .x7 (40 : BitVec 13),
    .LD .x6 .x5 (24 : BitVec 12),
    .LD .x7 .x21 (96 : BitVec 12),
    .BNE .x6 .x7 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aie_predicate (GuestAddrs.account_is_empty_at_header_state_root + 256)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aie_predicate (GuestAddrs.account_is_empty_at_header_state_root + 256)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountIsEmptyAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountIsEmptyAtHeaderStateRoot_relocs : RelocTable :=
  [ (13, .la .x5 "aie_predicate"),
    (18, .la .x12 "aie_state_root"),
    (20, .jal .x1 "header_extract_state_root"),
    (26, .la .x12 "aie_state_root"),
    (30, .la .x21 "aie_acct_struct"),
    (33, .jal .x1 "account_at_address"),
    (50, .la .x5 "aie_empty_code_hash"),
    (64, .la .x5 "aie_predicate") ]

def accountIsEmptyAtHeaderStateRootFunction : String :=
  "account_is_empty_at_header_state_root:\n" ++ emitProgramR accountIsEmptyAtHeaderStateRoot_prog accountIsEmptyAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountIsEmptyAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountIsEmptyAtHeaderStateRootFunction_eq_prog :
    accountIsEmptyAtHeaderStateRootFunction = "account_is_empty_at_header_state_root:\n" ++ emitProgramR accountIsEmptyAtHeaderStateRoot_prog accountIsEmptyAtHeaderStateRoot_relocs := rfl

#guard accountIsEmptyAtHeaderStateRootFunction.startsWith "account_is_empty_at_header_state_root:\n"
#guard accountIsEmptyAtHeaderStateRoot_prog.length = 80
/-- `zisk_account_is_empty_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..16 : predicate (u64; 0 or 1) -/
def ziskAccountIsEmptyAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  jal ra, account_is_empty_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, aie_predicate; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Laiehsr_pdone\n" ++
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
  accountIsEmptyAtHeaderStateRootFunction ++ "\n" ++
  ".Laiehsr_pdone:"

def ziskAccountIsEmptyAtHeaderStateRootDataSection : String :=
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
  "aie_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aie_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aie_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskAccountIsEmptyAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountIsEmptyAtHeaderStateRootPrologue
  dataAsm     := ziskAccountIsEmptyAtHeaderStateRootDataSection
}

end EvmAsm.Codegen
