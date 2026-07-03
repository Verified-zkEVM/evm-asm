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
    withdrawals_ptr = exec_payload + wd_off
    withdrawals_len = bal_off - wd_off              (requires bal_off >= wd_off)
    count           = withdrawals_len / 44          (requires no remainder; Withdrawal is fixed 44 B,
                                                     so the list has no inner
                                                     offset table)
  All u32 offsets are read byte-wise (LBU+shift) for the no-misaligned
  invariant (the SSZ blob base is unaligned in the real guest input).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

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
#guard spwU32le_prog.length = 12
/-- `extract_payload_and_withdrawals`.
    a0 = SSZ_BASE ptr
    a1 = out: ExecutionPayload ptr (u64)
    a2 = out: withdrawals list ptr (u64)
    a3 = out: withdrawals count (u64)
    a0 (output) = status: 0 ok, 1 malformed SSZ offsets/length. -/
def extractPayloadAndWithdrawalsFunction : String :=
  "extract_payload_and_withdrawals:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s1, a1                   # out payload ptr\n" ++
  "  mv s2, a2                   # out withdrawals ptr\n" ++
  "  mv s3, a3                   # out withdrawals count\n" ++
  "  # NPR = SSZ_BASE + outer.offsets[0]\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, spw_u32le\n" ++
  "  add t2, s0, a0              # NPR addr\n" ++
  "  # exec_payload = NPR + NPR.offsets[0]\n" ++
  "  mv a0, t2\n" ++
  "  jal ra, spw_u32le\n" ++
  "  li t0, 44\n" ++
  "  bne a0, t0, .Lspw_fail      # SszNewPayloadRequest fixed header before payload\n" ++
  "  # a0 = NPR.offsets[0]; recompute NPR (t2 clobbered by call? spw_u32le uses only t0/t1)\n" ++
  "  add s4, t2, a0              # s4 = exec_payload addr\n" ++
  "  sd s4, 0(s1)                # out payload ptr\n" ++
  "  # wd_off = u32 @ exec_payload+508\n" ++
  "  addi a0, s4, 508\n" ++
  "  jal ra, spw_u32le\n" ++
  "  mv t4, a0                   # wd_off\n" ++
  "  # bal_off = u32 @ exec_payload+528\n" ++
  "  addi a0, s4, 528\n" ++
  "  jal ra, spw_u32le\n" ++
  "  # a0 = bal_off ; t4 = wd_off\n" ++
  "  li t0, 540\n" ++
  "  bltu t4, t0, .Lspw_fail     # withdrawals must start after the fixed payload part\n" ++
  "  bltu a0, t4, .Lspw_fail     # block_access_list offset bounds withdrawals end\n" ++
  "  add t5, s4, t4              # withdrawals_ptr = exec_payload + wd_off\n" ++
  "  sd t5, 0(s2)\n" ++
  "  sub t6, a0, t4              # withdrawals_len = bal_off - wd_off\n" ++
  "  # count = withdrawals_len / 44 (repeated subtraction; count is small)\n" ++
  "  li t0, 0                    # count\n" ++
  "  li t1, 44\n" ++
  ".Lspw_cnt:\n" ++
  "  bltu t6, t1, .Lspw_cnt_done\n" ++
  "  sub t6, t6, t1\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lspw_cnt\n" ++
  ".Lspw_cnt_done:\n" ++
  "  bnez t6, .Lspw_fail         # fixed-size SSZ withdrawals must be N*44 bytes\n" ++
  "  sd t0, 0(s3)                # out count\n" ++
  "  li a0, 0\n" ++
  "  j .Lspw_ret\n" ++
  ".Lspw_fail:\n" ++
  "  sd zero, 0(s1)\n" ++
  "  sd zero, 0(s2)\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 1\n" ++
  ".Lspw_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

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

def ziskExtractPayloadAndWithdrawalsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtractPayloadAndWithdrawalsPrologue
  dataAsm     := ziskExtractPayloadAndWithdrawalsDataSection
}

end EvmAsm.Codegen
