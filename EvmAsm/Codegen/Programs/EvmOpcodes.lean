/-
  EvmAsm.Codegen.Programs.EvmOpcodes

  Witness-side implementations of EVM opcode semantics carved
  out of `EvmAsm.Codegen.Programs.State` per the file-size hard
  cap. Hosts probes that translate a stateless witness +
  parent-header tuple into the value an EVM frame would push
  onto the stack for a given opcode, applying the opcode's
  spec-correct edge cases (e.g. EIP-1052's "empty-account → 0"
  rule for EXTCODEHASH).

  These compose K201 `header_extract_state_root`, K28
  `account_at_address`, and friends from
  `EvmAsm.Codegen.Programs.State` -- they add the
  opcode-specific edge-case handling layered on top of the
  trie walk.

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

/-! ## extcodehash_at_header_state_root  (EIP-1052)

    Witness-side implementation of the EVM `EXTCODEHASH` opcode
    semantics. Given a parent header RLP, an address, and an SSZ
    `witness.state` list section, return the 32-byte hash an
    EXTCODEHASH(addr) frame would push onto the stack.

    Per EIP-1052, EXTCODEHASH returns:
      * 0 if the account does not exist OR is "empty"
        (an empty account has nonce = 0, balance = 0,
         code_hash = keccak("") = EMPTY_CODE_HASH).
      * the account's `code_hash` otherwise.

    Distinct from PR-K? `code_at_header_state_root`, which
    resolves `account.code_hash` against `witness.codes`.
    EXTCODEHASH only reads the state trie's account record --
    it does NOT touch `witness.codes`; it just inspects the
    four account fields and applies the EIP-1052
    zero-on-empty rule.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : 32-byte output ptr (the EXTCODEHASH result)
      ra (input)  : return

      a0 (output) :
        0 = success (output filled per EIP-1052 semantics)
        2 = state-trie mpt parse error  (output zeroed)
        3 = account_decode failure      (output zeroed)
        4 = header parse / state_root size fail (output zeroed)

      Note: "account not in trie" returns SUCCESS with 32 zeros
      (NOT a separate status), matching EIP-1052 exactly. Pure
      RLP/MPT structural failures still propagate as 2/3.

    Composes K201 `header_extract_state_root` + K28
    `account_at_address` + 4 u64 compares against the
    pre-baked EMPTY_CODE_HASH constant.
-/
def extcodehashAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
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
    .SD .x21 .x0 (8 : BitVec 12),
    .SD .x21 .x0 (16 : BitVec 12),
    .SD .x21 .x0 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.eahsr_state_root (GuestAddrs.extcodehash_at_header_state_root + 84)),
    .ADDI .x12 .x12 (laLo GuestAddrs.eahsr_state_root (GuestAddrs.extcodehash_at_header_state_root + 84)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.extcodehash_at_header_state_root + 92)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (208 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.eahsr_state_root (GuestAddrs.extcodehash_at_header_state_root + 116)),
    .ADDI .x12 .x12 (laLo GuestAddrs.eahsr_state_root (GuestAddrs.extcodehash_at_header_state_root + 116)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x22 (laHi GuestAddrs.eahsr_acct_struct (GuestAddrs.extcodehash_at_header_state_root + 132)),
    .ADDI .x22 .x22 (laLo GuestAddrs.eahsr_acct_struct (GuestAddrs.extcodehash_at_header_state_root + 132)),
    .MV .x15 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.extcodehash_at_header_state_root + 144)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (152 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (144 : BitVec 21),
    .LD .x6 .x22 (0 : BitVec 12),
    .BNE .x6 .x0 (100 : BitVec 13),
    .LD .x6 .x22 (8 : BitVec 12),
    .BNE .x6 .x0 (92 : BitVec 13),
    .LD .x6 .x22 (16 : BitVec 12),
    .BNE .x6 .x0 (84 : BitVec 13),
    .LD .x6 .x22 (24 : BitVec 12),
    .BNE .x6 .x0 (76 : BitVec 13),
    .LD .x6 .x22 (32 : BitVec 12),
    .BNE .x6 .x0 (68 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.eahsr_empty_code_hash (GuestAddrs.extcodehash_at_header_state_root + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.eahsr_empty_code_hash (GuestAddrs.extcodehash_at_header_state_root + 212)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x22 (72 : BitVec 12),
    .BNE .x6 .x7 (48 : BitVec 13),
    .LD .x6 .x5 (8 : BitVec 12),
    .LD .x7 .x22 (80 : BitVec 12),
    .BNE .x6 .x7 (36 : BitVec 13),
    .LD .x6 .x5 (16 : BitVec 12),
    .LD .x7 .x22 (88 : BitVec 12),
    .BNE .x6 .x7 (24 : BitVec 13),
    .LD .x6 .x5 (24 : BitVec 12),
    .LD .x7 .x22 (96 : BitVec 12),
    .BNE .x6 .x7 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LD .x6 .x22 (72 : BitVec 12),
    .SD .x21 .x6 (0 : BitVec 12),
    .LD .x6 .x22 (80 : BitVec 12),
    .SD .x21 .x6 (8 : BitVec 12),
    .LD .x6 .x22 (88 : BitVec 12),
    .SD .x21 .x6 (16 : BitVec 12),
    .LD .x6 .x22 (96 : BitVec 12),
    .SD .x21 .x6 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `extcodehashAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def extcodehashAtHeaderStateRoot_relocs : RelocTable :=
  [ (21, .la .x12 "eahsr_state_root"),
    (23, .jal .x1 "header_extract_state_root"),
    (29, .la .x12 "eahsr_state_root"),
    (33, .la .x22 "eahsr_acct_struct"),
    (36, .jal .x1 "account_at_address"),
    (53, .la .x5 "eahsr_empty_code_hash") ]

def extcodehashAtHeaderStateRootFunction : String :=
  "extcodehash_at_header_state_root:\n" ++ emitProgramR extcodehashAtHeaderStateRoot_prog extcodehashAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `extcodehashAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem extcodehashAtHeaderStateRootFunction_eq_prog :
    extcodehashAtHeaderStateRootFunction = "extcodehash_at_header_state_root:\n" ++ emitProgramR extcodehashAtHeaderStateRoot_prog extcodehashAtHeaderStateRoot_relocs := rfl

#guard extcodehashAtHeaderStateRootFunction.startsWith "extcodehash_at_header_state_root:\n"
#guard extcodehashAtHeaderStateRoot_prog.length = 88
/-- `zisk_extcodehash_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..40 : EXTCODEHASH result (per EIP-1052) -/
def ziskExtcodehashAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a5, 0xa0010008           # 32 B output\n" ++
  "  jal ra, extcodehash_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Leahsr_pdone\n" ++
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
  extcodehashAtHeaderStateRootFunction ++ "\n" ++
  ".Leahsr_pdone:"

def ziskExtcodehashAtHeaderStateRootDataSection : String :=
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
  "eahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "eahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "eahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskExtcodehashAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtcodehashAtHeaderStateRootPrologue
  dataAsm     := ziskExtcodehashAtHeaderStateRootDataSection
}

/-! ## balance_live_else_header_state_root  (EVM BALANCE opcode)

    **LIVE-FIRST, not header-only.** Every production caller wants
    live-else-header; the helper reads live effects first and falls back to
    the header witness only on a miss (#11019).

    Spec baseline (execution-specs Amsterdam): one mutable
    `TransactionState`; `BALANCE` reads
    `get_account(tx_state, address).balance`
    (`vm/instructions/environment.py`) and `is_account_alive` uses the
    same `get_account_optional(tx_state, …)`
    (`state_tracker.py`). Reads return the last write — not a frozen
    header snapshot. Live-first matches that baseline.

    Behaviour:
    1. Pad the 20B address and call `account_writes_latest_balance`
       (transaction map, then block map). On a hit, write that post balance
       and return success — **no header path**.
    2. On a miss only: K201 `header_extract_state_root` + K28
       `account_at_address`, copy balance (struct + 8 .. + 40), flatten
       missing account (status 1) to `(0, balance=0)`.

    **Contrast — do not confuse with header-only helpers:**
    - `account_at_header_state_root` **is** a true header-only source
      (header → state root → account_at_address, no live overlay) with
      many callers.
    - A pure **balance**-header-only helper **does not exist**. Anyone
      who genuinely needs pre-state balance must build it from
      `account_at_header_state_root` (or accept this miss path). The
      name of *this* routine must not be read as that helper.
    - Callers that need a non-settlement snapshot deliberately **avoid**
      this symbol (e.g. DispatchTx SELFBALANCE staging).

    BALANCE absent → 0 flattening matches SLOAD: missing accounts are
    conceptually defined with zero balance (no status-1 to the caller).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : 32-byte u256 BE output ptr
      ra (input)  : return

      a0 (output) :
        0 = success (balance written to output; 0 for absent)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

      (Code 1 is intentionally absent: missing accounts map to
      `status=0, balance=0` per the EVM BALANCE semantic.)

    This helper is named `balance_live_else_header_state_root` to reflect its
    live-first, header-fallback control flow.
-/
def balanceLiveElseHeaderStateRoot_prog : Program :=
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
    .SD .x21 .x0 (8 : BitVec 12),
    .SD .x21 .x0 (16 : BitVec 12),
    .SD .x21 .x0 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_addr_padded (GuestAddrs.balance_live_else_header_state_root + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_addr_padded (GuestAddrs.balance_live_else_header_state_root + 76)),
    .SD .x5 .x0 (0 : BitVec 12),
    .SD .x5 .x0 (8 : BitVec 12),
    .SD .x5 .x0 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .MV .x6 .x18,
    .MV .x7 .x5,
    .LI .x28 (20 : Word),
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x6 (0 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.bal_addr_padded (GuestAddrs.balance_live_else_header_state_root + 140)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_addr_padded (GuestAddrs.balance_live_else_header_state_root + 140)),
    .MV .x11 .x21,
    .LI .x12 (2 : Word),
    .JAL .x1 (jalOff GuestAddrs.account_writes_latest_balance (GuestAddrs.balance_live_else_header_state_root + 156)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.balance_live_else_header_state_root + 304) (GuestAddrs.balance_live_else_header_state_root + 168)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.bal_state_root (GuestAddrs.balance_live_else_header_state_root + 180)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bal_state_root (GuestAddrs.balance_live_else_header_state_root + 180)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.balance_live_else_header_state_root + 188)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (jalOff (GuestAddrs.balance_live_else_header_state_root + 304) (GuestAddrs.balance_live_else_header_state_root + 200)),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bal_state_root (GuestAddrs.balance_live_else_header_state_root + 212)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bal_state_root (GuestAddrs.balance_live_else_header_state_root + 212)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x22 (laHi GuestAddrs.bal_acct_struct (GuestAddrs.balance_live_else_header_state_root + 228)),
    .ADDI .x22 .x22 (laLo GuestAddrs.bal_acct_struct (GuestAddrs.balance_live_else_header_state_root + 228)),
    .MV .x15 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.balance_live_else_header_state_root + 240)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (48 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LD .x6 .x22 (8 : BitVec 12),
    .SD .x21 .x6 (0 : BitVec 12),
    .LD .x6 .x22 (16 : BitVec 12),
    .SD .x21 .x6 (8 : BitVec 12),
    .LD .x6 .x22 (24 : BitVec 12),
    .SD .x21 .x6 (16 : BitVec 12),
    .LD .x6 .x22 (32 : BitVec 12),
    .SD .x21 .x6 (24 : BitVec 12),
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

/-- Reloc side-table for `balanceLiveElseHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balanceLiveElseHeaderStateRoot_relocs : RelocTable :=
  [ (19, .la .x5 "bal_addr_padded"),
    (35, .la .x10 "bal_addr_padded"),
    (39, .jal .x1 "account_writes_latest_balance"),
    (45, .la .x12 "bal_state_root"),
    (47, .jal .x1 "header_extract_state_root"),
    (53, .la .x12 "bal_state_root"),
    (57, .la .x22 "bal_acct_struct"),
    (60, .jal .x1 "account_at_address") ]

def balanceLiveElseHeaderStateRootFunction : String :=
  "balance_live_else_header_state_root:\n" ++ emitProgramR balanceLiveElseHeaderStateRoot_prog balanceLiveElseHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balanceLiveElseHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balanceLiveElseHeaderStateRootFunction_eq_prog :
    balanceLiveElseHeaderStateRootFunction = "balance_live_else_header_state_root:\n" ++ emitProgramR balanceLiveElseHeaderStateRoot_prog balanceLiveElseHeaderStateRoot_relocs := rfl

#guard balanceLiveElseHeaderStateRootFunction.startsWith "balance_live_else_header_state_root:\n"
#guard balanceLiveElseHeaderStateRoot_prog.length = 86
/-- `zisk_balance_live_else_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..40 : balance (u256 BE; 0 on absent) -/
def ziskBalanceLiveElseHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a5, 0xa0010008           # 32 B output\n" ++
  "  jal ra, balance_live_else_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbal_pdone\n" ++
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
  balanceLiveElseHeaderStateRootFunction ++ "\n" ++
  ".Lbal_pdone:"

def ziskBalanceLiveElseHeaderStateRootDataSection : String :=
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
  "bal_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "bal_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "bal_addr_padded:\n" ++   -- yisv8 .spine.2: 32B padded query addr (20B BE + 12B zero) for the live-balance scan
  "  .zero 32"

def ziskBalanceLiveElseHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalanceLiveElseHeaderStateRootPrologue
  dataAsm     := ziskBalanceLiveElseHeaderStateRootDataSection
}


/-! ## sload_at_header_state_root  (EVM SLOAD opcode)

    Witness-side implementation of the EVM `SLOAD` opcode. Given
    a parent header RLP, an address, a 32-byte slot index, an
    SSZ `witness.state` list, and an SSZ `witness.storage` list,
    return the u256 value an `SLOAD(slot)` frame in `addr`'s
    context would push.

    Per the spec, SLOAD returns 0 if:
      * the account is not present in the state trie, OR
      * `account.storage_root == EMPTY_TRIE_ROOT`
        (mpt_walk -> "not found" inside `slot_at_index`), OR
      * the storage slot is simply not present in the trie
        (any uninitialised slot is implicitly zero).

    This is the SLOAD-side complement of PR
    `slot_at_header_state_root` (which surfaces those "not
    found" cases as distinct statuses 1 and 5). The EVM-level
    semantic flattens both into "value = 0, status = 0";
    callers using this primitive shouldn't have to special-case
    absence. Structural failures (mpt parse, RLP decode, header
    parse) still propagate so witness integrity can be checked.

    Calling convention (8 args, fits in a0..a7):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : slot_idx ptr (32-byte BE u256)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : witness.storage ptr
      a7 (input)  : witness.storage len
      ra (input)  : return

      a0 (output) :
        0 = success (slot value at `sload_u256`; may be 0)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure

      (Codes 1 and 5 are intentionally absent: those map to
      `status=0, value=0` per SLOAD semantics.)

    The probe BuildUnit copies `sload_u256` (32 B BE) to
    OUTPUT + 8.
-/
def sloadAtHeaderStateRootFunction : String :=
  "sload_at_header_state_root:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # slot_idx ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # witness.storage ptr\n" ++
  "  mv s7, a7                  # witness.storage len\n" ++
  "  # Pre-zero the 32-byte output -- SLOAD default value.\n" ++
  "  la t0, sload_u256\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  # Step 1: header.state_root -> sload_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, sload_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsload_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lsload_ret\n" ++
  ".Lsload_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, sload_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la s8, sload_acct_struct\n" ++
  "  mv a5, s8\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsload_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsload_missing_acct  # 1 -> SLOAD returns 0\n" ++
  "  j .Lsload_ret                     # 2/3 propagate\n" ++
  ".Lsload_missing_acct:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsload_ret\n" ++
  ".Lsload_step3:\n" ++
  "  # Step 3: slot_at_index over witness.storage with acct.storage_root.\n" ++
  "  mv a0, s3                  # slot_idx ptr\n" ++
  "  li a1, 32                  # slot_idx_len\n" ++
  "  addi a2, s8, 40            # &acct.storage_root\n" ++
  "  mv a3, s6                  # witness.storage ptr\n" ++
  "  mv a4, s7                  # witness.storage len\n" ++
  "  la a5, sload_u256          # u256 BE out\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lsload_ret       # 0 -> value at sload_u256\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsload_missing_slot # 1 -> SLOAD returns 0\n" ++
  "  # 2 -> 6, 3 -> 7\n" ++
  "  addi a0, a0, 4\n" ++
  "  # value buffer was zeroed by slot_at_index on failure.\n" ++
  "  j .Lsload_ret\n" ++
  ".Lsload_missing_slot:\n" ++
  "  li a0, 0\n" ++
  ".Lsload_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_sload_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len      (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..64 : slot_idx (32-byte BE u256)
      bytes 64..84 : address (20 bytes)
      bytes 84..84+H              : header_rlp
      bytes 84+H..84+H+WS         : witness.state
      bytes 84+H+WS..             : witness.storage
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4 / 6 / 7)
      bytes  8..40 : slot value (u256 BE; 0 on missing/absent) -/
def ziskSloadAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # witness_storage_len\n" ++
  "  addi a3, t1, 32             # slot_idx ptr\n" ++
  "  addi a2, t1, 64             # address ptr\n" ++
  "  addi a0, t1, 84             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a4, a0, t2              # witness.state ptr\n" ++
  "  mv a5, t3                   # witness_state_len\n" ++
  "  add a6, a4, t3              # witness.storage ptr\n" ++
  "  mv a7, t4                   # witness_storage_len\n" ++
  "  jal ra, sload_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  # Copy sload_u256 (32 B) to OUTPUT + 8.\n" ++
  "  la t1, sload_u256\n" ++
  "  ld t2,  0(t1); sd t2,  8(t0)\n" ++
  "  ld t2,  8(t1); sd t2, 16(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 24(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 32(t0)\n" ++
  "  j .Lsload_pdone\n" ++
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
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  sloadAtHeaderStateRootFunction ++ "\n" ++
  ".Lsload_pdone:"

def ziskSloadAtHeaderStateRootDataSection : String :=
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
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sload_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sload_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "sload_u256:\n" ++
  "  .zero 32"

def ziskSloadAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSloadAtHeaderStateRootPrologue
  dataAsm     := ziskSloadAtHeaderStateRootDataSection
}
end EvmAsm.Codegen
