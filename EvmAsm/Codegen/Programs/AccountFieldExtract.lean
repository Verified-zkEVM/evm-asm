/-
  EvmAsm.Codegen.Programs.AccountFieldExtract

  Ethereum-account RLP field extractors split out of `Account.lean`.

  Hosts:
    K121  account_extract_nonce    (field 0, u64)
    K120  account_extract_balance  (field 1, u256 BE)

  Both decode through the verified cursor-walk helpers from
  `Programs/RlpWalk.lean` (bead evm-asm-22pwv.4) instead of the
  legacy `rlp_field_to_*` / `rlp_list_nth_item` re-walkers.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_extract_nonce -- PR-K121

    Extract the u64 `nonce` field (RLP field 0) from a fully
    RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The nonce counts the number of outbound transactions an EOA
    has issued (or contract creations for a contract). EIP-2681
    caps it at `2^64 - 1` so a u64 fits.

    K27 `account_decode` already extracts the full account record;
    this narrower accessor avoids the 96-byte struct when only the
    nonce is needed (e.g., the tx-replay-protection check inside
    `check_transaction`, or to thread the nonce-mismatch error path
    without unpacking balance / storage_root / code_hash).

    Composes the verified cursor-walk helpers (`rlp_walk_init` ->
    `rlp_walk_next` for field 0 -> `rlp_content_to_u64`) from
    `Programs/RlpWalk.lean` instead of the legacy index-based
    `rlp_field_to_u64` / `rlp_list_nth_item` re-walk (bead
    evm-asm-22pwv.4). The content decode is canonical-strict
    (execution-specs `_deserialize_to_uint`).

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 0 missing / > 64 bits /
            non-canonical scalar -/
def accountExtractNonce_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x12,
    .SD .x8 .x0 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.account_extract_nonce + 20)),
    .BNE .x12 .x0 (44 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.account_extract_nonce + 28)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.account_extract_nonce + 48)),
    .BNE .x11 .x0 (16 : BitVec 13),
    .SD .x8 .x10 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .SD .x8 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountExtractNonce_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountExtractNonce_relocs : RelocTable :=
  [ (5, .jal .x1 "rlp_walk_init"),
    (7, .jal .x1 "rlp_walk_next"),
    (12, .jal .x1 "rlp_content_to_u64") ]

def accountExtractNonceFunction : String :=
  "account_extract_nonce:\n" ++ emitProgramR accountExtractNonce_prog accountExtractNonce_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountExtractNonce_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountExtractNonceFunction_eq_prog :
    accountExtractNonceFunction = "account_extract_nonce:\n" ++ emitProgramR accountExtractNonce_prog accountExtractNonce_relocs := rfl

#guard accountExtractNonceFunction.startsWith "account_extract_nonce:\n"
#guard accountExtractNonce_prog.length = 23
/-- `zisk_account_extract_nonce`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, nonce u64) to
    OUTPUT (16 bytes). -/
def ziskAccountExtractNoncePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # nonce out\n" ++
  "  jal ra, account_extract_nonce\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laen_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  ".Laen_pdone:"

def ziskAccountExtractNonceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskAccountExtractNonceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractNoncePrologue
  dataAsm     := ziskAccountExtractNonceDataSection
}

/-! ## account_extract_balance -- PR-K120

    Extract the u256 BE `balance` field (RLP field 1) from a fully
    RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The balance is the account's wei holdings, ranged in
    `[0, 2^256)`. Direct input to balance-check predicates
    (`balance >= value + gas_cost`), priority-fee credit, and
    the trie-rebuild path after value transfers.

    K27 `account_decode` already extracts the full account record;
    K120 (with PR-K119 `account_extract_storage_root`) is the
    narrower accessor for callers that only need a single field.

    Composes the verified cursor-walk helpers (`rlp_walk_init` ->
    `rlp_walk_next` x2 for field 1 -> `rlp_content_to_u256_be`)
    from `Programs/RlpWalk.lean` instead of the legacy index-based
    `rlp_field_to_u256_be` / `rlp_list_nth_item` re-walk (bead
    evm-asm-22pwv.4). The content decode is canonical-strict
    (execution-specs `_deserialize_to_uint`).

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : 32-byte output ptr (u256 BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 1 missing / > 256 bits /
            non-canonical scalar -/
def accountExtractBalance_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x12,
    .SD .x8 .x0 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.account_extract_balance + 36)),
    .BNE .x12 .x0 (60 : BitVec 13),
    .MV .x9 .x11,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.account_extract_balance + 48)),
    .BNE .x11 .x0 (48 : BitVec 13),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.account_extract_balance + 60)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.account_extract_balance + 84)),
    .BNE .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .SD .x8 .x0 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountExtractBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountExtractBalance_relocs : RelocTable :=
  [ (9, .jal .x1 "rlp_walk_init"),
    (12, .jal .x1 "rlp_walk_next"),
    (15, .jal .x1 "rlp_walk_next"),
    (21, .jal .x1 "rlp_content_to_u256_be") ]

def accountExtractBalanceFunction : String :=
  "account_extract_balance:\n" ++ emitProgramR accountExtractBalance_prog accountExtractBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountExtractBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountExtractBalanceFunction_eq_prog :
    accountExtractBalanceFunction = "account_extract_balance:\n" ++ emitProgramR accountExtractBalance_prog accountExtractBalance_relocs := rfl

#guard accountExtractBalanceFunction.startsWith "account_extract_balance:\n"
#guard accountExtractBalance_prog.length = 35
/-- `zisk_account_extract_balance`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, 32-byte balance
    BE) to OUTPUT (40 bytes). -/
def ziskAccountExtractBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32B u256 output\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laeb_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  ".Laeb_pdone:"

def ziskAccountExtractBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8"

def ziskAccountExtractBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractBalancePrologue
  dataAsm     := ziskAccountExtractBalanceDataSection
}

end EvmAsm.Codegen
