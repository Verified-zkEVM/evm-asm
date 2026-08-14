/-
  EvmAsm.Codegen.Programs.SszPayloadWithdrawals

  extract_payload_and_withdrawals (bead evm-asm-fhsxz.2.4.2.3): locate the
  `ExecutionPayload` and its `withdrawals` list within an `SszStatelessInput`,
  the two inputs the Step-2 verdict still needs from the real guest input:
    * the ExecutionPayload ptr feeds `block_header_ssz_to_rlp` (this header);
    * each 44-byte SSZ Withdrawal feeds `ssz_withdrawal_to_rlp` ->
      `withdrawals_state_root`.

  Navigation (per the NPR-root epilogue, StatelessGuestEpilogue.lean):
    NPR          = SSZ_BASE + outer.offsets[0]      (OUTER_NPR_OFFSET = 0)
    exec_payload = NPR + NPR.offsets[0]             (execution_payload, NPR+44)
    wd_off       = u32 @ exec_payload+508           (withdrawals offset)
    bal_off      = u32 @ exec_payload+528           (block_access_list offset =
                                                     end of the withdrawals data)
    vh_off       = u32 @ NPR+4                      (versioned_hashes offset =
                                                     end of the ExecutionPayload)
    withdrawals_ptr = exec_payload + wd_off
    withdrawals_len = bal_off - wd_off              (requires bal_off >= wd_off)
    count           = withdrawals_len / 44          (requires no remainder; Withdrawal is fixed 44 B,
                                                     so the list has no inner
                                                     offset table)
  All u32 offsets are read byte-wise (LBU+shift) for the no-misaligned
  invariant (the SSZ blob base is unaligned in the real guest input). Since
  `bal_off` is relative to `exec_payload = NPR+44` while `vh_off` is relative
  to NPR, reject unless `vh_off >= 44 + bal_off`. This is exactly
  `bal_end >= bal_start`, so the derived BAL length is a real in-payload range
  rather than a wrapping unsigned subtraction.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## spw_u32le -- read a little-endian u32 byte-wise (a0 = ptr -> a0). Leaf. -/
def spwU32le_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LBU .x6 .x10 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (2 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (3 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x5 .x5 .x6,
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def spwU32leFunction : String :=
  "spw_u32le:\n" ++ emitProgram spwU32le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `spwU32le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem spwU32leFunction_eq_prog :
    spwU32leFunction = "spw_u32le:\n" ++ emitProgram spwU32le_prog := rfl

#guard spwU32leFunction.startsWith "spw_u32le:\n"
/-- `extract_payload_and_withdrawals`.
    a0 = SSZ_BASE ptr
    a1 = out: ExecutionPayload ptr (u64)
    a2 = out: withdrawals list ptr (u64)
    a3 = out: withdrawals count (u64)
    a0 (output) = status: 0 ok, 1 malformed SSZ offsets/length. -/
def extractPayloadAndWithdrawals_prog : Program :=
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
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.spw_u32le (GuestAddrs.extract_payload_and_withdrawals + 48)),
    .ADD .x7 .x8 .x10,
    .MV .x10 .x7,
    .JAL .x1 (jalOff GuestAddrs.spw_u32le (GuestAddrs.extract_payload_and_withdrawals + 60)),
    .LI .x5 (44 : Word),
    .BNE .x10 .x5 (120 : BitVec 13),
    .ADD .x20 .x7 .x10,
    .SD .x9 .x20 (0 : BitVec 12),
    .ADDI .x10 .x20 (508 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.spw_u32le (GuestAddrs.extract_payload_and_withdrawals + 84)),
    .MV .x29 .x10,
    .ADDI .x10 .x20 (528 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.spw_u32le (GuestAddrs.extract_payload_and_withdrawals + 96)),
    .MV .x31 .x10,
    .ADDI .x10 .x7 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.spw_u32le (GuestAddrs.extract_payload_and_withdrawals + 108)),
    .ADDI .x5 .x31 (44 : BitVec 12),
    .BLTU .x10 .x5 (72 : BitVec 13),
    .MV .x10 .x31,
    .LI .x5 (540 : Word),
    .BLTU .x29 .x5 (60 : BitVec 13),
    .BLTU .x10 .x29 (56 : BitVec 13),
    .ADD .x30 .x20 .x29,
    .SD .x18 .x30 (0 : BitVec 12),
    .SUB .x31 .x10 .x29,
    .LI .x5 (0 : Word),
    .LI .x6 (44 : Word),
    .BLTU .x31 .x6 (16 : BitVec 13),
    .SUB .x31 .x31 .x6,
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .BNE .x31 .x0 (16 : BitVec 13),
    .SD .x19 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (20 : BitVec 21),
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `extractPayloadAndWithdrawals_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def extractPayloadAndWithdrawals_relocs : RelocTable :=
  [ (12, .jal .x1 "spw_u32le"),
    (15, .jal .x1 "spw_u32le"),
    (21, .jal .x1 "spw_u32le"),
    (24, .jal .x1 "spw_u32le"),
    (27, .jal .x1 "spw_u32le") ]

def extractPayloadAndWithdrawalsFunction : String :=
  "extract_payload_and_withdrawals:\n" ++ emitProgramR extractPayloadAndWithdrawals_prog extractPayloadAndWithdrawals_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `extractPayloadAndWithdrawals_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem extractPayloadAndWithdrawalsFunction_eq_prog :
    extractPayloadAndWithdrawalsFunction = "extract_payload_and_withdrawals:\n" ++ emitProgramR extractPayloadAndWithdrawals_prog extractPayloadAndWithdrawals_relocs := rfl

#guard extractPayloadAndWithdrawalsFunction.startsWith "extract_payload_and_withdrawals:\n"
/-- `zisk_extract_payload_and_withdrawals`: probe. Input file (-> INPUT+8) is
    the SszStatelessInput SSZ blob (SSZ_BASE = INPUT+8 for the probe).
    Output: OUTPUT+0 = payload offset from SSZ_BASE, OUTPUT+8 = withdrawals
    offset from SSZ_BASE, OUTPUT+16 = withdrawals count, OUTPUT+24 = status. -/
def ziskExtractPayloadAndWithdrawalsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008           # SSZ_BASE = input start (probe)\n" ++
  "  la a1, spw_payload_ptr\n" ++
  "  la a2, spw_wd_ptr\n" ++
  "  la a3, spw_wd_count\n" ++
  "  jal ra, extract_payload_and_withdrawals\n" ++
  "  li t2, 0xa0010018; sd a0, 0(t2)\n" ++
  "  li t2, 0xa0010000; sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2)\n" ++
  "  bnez a0, .Lspw_pdone\n" ++
  "  li t6, 0x40000008           # SSZ_BASE for relative offsets\n" ++
  "  la t0, spw_payload_ptr; ld t1, 0(t0); sub t1, t1, t6\n" ++
  "  li t2, 0xa0010000; sd t1, 0(t2)\n" ++
  "  la t0, spw_wd_ptr; ld t1, 0(t0); sub t1, t1, t6\n" ++
  "  li t2, 0xa0010008; sd t1, 0(t2)\n" ++
  "  la t0, spw_wd_count; ld t1, 0(t0)\n" ++
  "  li t2, 0xa0010010; sd t1, 0(t2)\n" ++
  "  j .Lspw_pdone\n" ++
  spwU32leFunction ++ "\n" ++
  extractPayloadAndWithdrawalsFunction ++ "\n" ++
  ".Lspw_pdone:"

def ziskExtractPayloadAndWithdrawalsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "spw_payload_ptr:\n  .zero 8\n" ++
  "spw_wd_ptr:\n  .zero 8\n" ++
  "spw_wd_count:\n  .zero 8"


end EvmAsm.Codegen
