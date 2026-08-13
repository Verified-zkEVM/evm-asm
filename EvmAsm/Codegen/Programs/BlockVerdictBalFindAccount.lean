/-
  EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount

  Locate a recipient's BAL AccountChanges entry by address, for contract-recipient
  runtime execution (evm-asm-fhsxz.2.4.2.57.11.6.4.3). The BAL section is an RLP
  list of AccountChanges, each [address, storage_changes, storage_reads, ...];
  block_state_root iterates them by index but never matches by address. The
  contract-dispatch wiring needs the recipient's specific AccountChanges entry
  (to enumerate its storage_changes via bal_recipient_storage_keys), so this
  helper scans the list and returns the entry whose item-0 address (20 bytes)
  matches the target.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_find_account_by_address

    Calling convention:
      a0 = BAL section RLP ptr   a1 = BAL section RLP length
      a2 = target address ptr (20 bytes)
      a3 = out account ptr cell (8 bytes; matched AccountChanges RLP ptr)
      a4 = out account len cell (8 bytes; matched AccountChanges RLP length)
    Returns:
      a0 = 0 found / 1 not found / 2 parse error.

    Scans the BAL list; for each AccountChanges entry reads item 0 (the 20-byte
    address) and compares to the target. Entries whose address field is not
    exactly 20 bytes are skipped. -/
def balFindAccountByAddress_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_find_account_by_address + 76)),
    .BNE .x12 .x0 (brOff (GuestAddrs.bal_find_account_by_address + 252) (GuestAddrs.bal_find_account_by_address + 80)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x23 .x0,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_find_account_by_address + 104)),
    .LI .x5 (2 : Word),
    .BEQ .x11 .x5 (brOff (GuestAddrs.bal_find_account_by_address + 244) (GuestAddrs.bal_find_account_by_address + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_find_account_by_address + 252) (GuestAddrs.bal_find_account_by_address + 116)),
    .MV .x21 .x10,
    .SUB .x24 .x10 .x12,
    .MV .x25 .x12,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_find_account_by_address + 140)),
    .BNE .x12 .x0 (brOff (GuestAddrs.bal_find_account_by_address + 236) (GuestAddrs.bal_find_account_by_address + 144)),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_find_account_by_address + 148)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_find_account_by_address + 236) (GuestAddrs.bal_find_account_by_address + 152)),
    .LI .x29 (20 : Word),
    .BNE .x12 .x29 (brOff (GuestAddrs.bal_find_account_by_address + 236) (GuestAddrs.bal_find_account_by_address + 160)),
    .SUB .x6 .x10 .x12,
    .MV .x28 .x18,
    .LI .x29 (20 : Word),
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x6 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (48 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x31 (laHi GuestAddrs.bfa_index (GuestAddrs.bal_find_account_by_address + 208)),
    .ADDI .x31 .x31 (laLo GuestAddrs.bfa_index (GuestAddrs.bal_find_account_by_address + 208)),
    .SD .x31 .x23 (0 : BitVec 12),
    .SD .x19 .x24 (0 : BitVec 12),
    .SD .x20 .x25 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .ADDI .x23 .x23 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_find_account_by_address + 96) (GuestAddrs.bal_find_account_by_address + 240)),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balFindAccountByAddress_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balFindAccountByAddress_relocs : RelocTable :=
  [ (19, .jal .x1 "rlp_walk_init"),
    (26, .jal .x1 "rlp_walk_next"),
    (35, .jal .x1 "rlp_walk_init"),
    (37, .jal .x1 "rlp_walk_next"),
    (52, .la .x31 "bfa_index") ]

def balFindAccountByAddressFunction : String :=
  "bal_find_account_by_address:\n" ++ emitProgramR balFindAccountByAddress_prog balFindAccountByAddress_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balFindAccountByAddress_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balFindAccountByAddressFunction_eq_prog :
    balFindAccountByAddressFunction = "bal_find_account_by_address:\n" ++ emitProgramR balFindAccountByAddress_prog balFindAccountByAddress_relocs := rfl

#guard balFindAccountByAddressFunction.startsWith "bal_find_account_by_address:\n"
#guard balFindAccountByAddress_prog.length = 77
/-- `zisk_bal_find_account_by_address`: probe over a hand-encoded BAL with one
    AccountChanges (address byte0 = 0xAA, 63-byte account). Output:
      +0  status finding 0xAA.. (expect 0 found)
      +8  matched account length (expect 63)
      +16 status finding 0xCC.. (expect 1 not found) -/
def ziskBalFindAccountByAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, bfa_addr_hit; li t1, 0xAA; sb t1, 0(t0)\n" ++
  "  la t0, bfa_addr_miss; li t1, 0xCC; sb t1, 0(t0)\n" ++
  "  li s0, 0xa0010000\n" ++
  -- find 0xAA.. (present).
  "  la a0, bfa_bal; li a1, 65; la a2, bfa_addr_hit; la a3, bfa_out_ptr; la a4, bfa_out_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, bfa_out_len; ld t1, 0(t0); sd t1, 8(s0)\n" ++
  -- find 0xCC.. (absent).
  "  la a0, bfa_bal; li a1, 65; la a2, bfa_addr_miss; la a3, bfa_out_ptr; la a4, bfa_out_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  sd a0, 16(s0)\n" ++
  "  j .Lbfap_done\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balFindAccountByAddressFunction ++ "\n" ++
  ".Lbfap_done:"

def ziskBalFindAccountByAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bfa_index:\n  .zero 8\n" ++
  "bfa_out_ptr:\n  .zero 8\n" ++
  "bfa_out_len:\n  .zero 8\n" ++
  "bfa_addr_hit:\n  .zero 20\n" ++
  "bfa_addr_miss:\n  .zero 20\n" ++
  ".balign 8\n" ++
  -- BAL = list[account]; account = f8 3d 94 [20B addr, byte0=0xAA] e3 e2 a0 [31*00] 07 c0 c0 c0 c0 c0.
  -- BAL list payload = 63 bytes -> f8 3f.
  "bfa_bal:\n" ++
  "  .byte 0xf8, 0x3f\n" ++
  "  .byte 0xf8, 0x3d\n" ++
  "  .byte 0x94\n" ++
  "  .byte 0xAA\n" ++
  "  .zero 19\n" ++
  "  .byte 0xe3, 0xe2, 0xa0\n" ++
  "  .zero 31\n" ++
  "  .byte 0x07\n" ++
  "  .byte 0xc0\n" ++
  "  .byte 0xc0, 0xc0, 0xc0, 0xc0\n"


end EvmAsm.Codegen
