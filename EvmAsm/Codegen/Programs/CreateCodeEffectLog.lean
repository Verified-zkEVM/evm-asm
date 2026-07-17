/-
  EvmAsm.Codegen.Programs.CreateCodeEffectLog

  Per-created-account CODE-effect log + record/lookup helpers (bead
  fhsxz.2.4.2.61.8b, the CREATE deposit slice — step .8b-1).

  When CREATE/CREATE2 deploys a contract, execution has the deployed code bytes
  (create_child_code / create_child_code_len, create_child_status == 2). The
  block verdict's all-accounts CODE comparator `bal_account_code_consistent`
  (#8591, c2's i3djw) validates each BAL account's declared `code_changes` bytes
  against an execution-derived CODE-effect record. This module is the PRODUCER +
  LOOKUP for those records, keyed by the created account's 20-byte big-endian
  address (NOT keccak — same keying as c2's non-storage effect record, per c2#5).

  Per-created-account record layout (variable stride, 8-aligned), agreed with c2
  (c2#11):
    +0   addr            (20-byte BE address in the low/first 20 bytes, padded to 32 — the key)
    +32  has_code_change (u64; always 1 for a deployed record)
    +40  code_len        (u64)
    +48  code bytes      (the deployed bytecode, code_len bytes)
  The all-accounts wrapper passes `a2 = record+32` to `bal_account_code_consistent`
  (whose record is exactly the +32.. tail: has_code_change / code_len / code bytes).

  The CREATE-tail deposit call site (`create_record_code_effect(create_address_be,
  create_child_code, create_child_code_len)`) + EIP-3541 / MAX_CODE_SIZE / nonce
  updates land in step .8b-2; this slice is the log + helpers + a known-answer probe.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Capacity (bytes) of the code-effect log heap. Each entry is
    `round8(48 + code_len)`; deployed code is ≤ 32768 (Amsterdam EIP-7907).

    Gas-derived bound for the full 200M block target. Code deposit charges
    `CODE_DEPOSIT_PER_BYTE = 200` gas/byte, so the total deployed bytecode in a
    `bsrStateRootBlockGasLimit`-gas block is at most `200M / 200 = 1,000,000`
    bytes. Accounting for the 32,000-gas CREATE base (which lowers the realized
    byte budget) and the per-record `+48` overhead, the worst case is reached by
    ~30 near-max (32,768-byte) deploys: `Σcᵢ ≤ 200M/200 - 160·N` gives
    `Σcᵢ ≈ 983,040` and arena `Σ round8(48+cᵢ) ≈ 984 KiB` (~0.94 MiB realized,
    1.0 MiB absolute ceiling); the EIP-7907 large-code extra gas only lowers
    this, and the empty-CREATE / EIP-7702 delegation marker paths (48-byte
    records) are less arena-bytes-per-gas-efficient so cannot exceed it. The
    cap therefore reserves 1.5 MiB (≈50% margin over the 1.0 MiB ceiling).

    On overflow the producer sets `exec_code_effect_overflow` and the consumer
    must stay conservative. -/
def execCodeEffectLogCap : Nat := 1572864

/-! ## create_record_code_effect

    Append one deployed-code record to the code-effect log.

    Calling convention:
      a0 = 20-byte big-endian address ptr (the created account)
      a1 = deployed code ptr
      a2 = deployed code length (bytes)
    Returns:
      a0 = 0 appended ok / 1 capacity overflow (record NOT written; overflow flag set)
    Clobbers t0-t6, a0; preserves s-regs (saved). -/
def createRecordCodeEffectFunction : String :=
  "create_record_code_effect:\n" ++
  -- Record empty-code CREATEs with has_code_change=0 so that EXTCODEHASH/EXTCODESIZE
  -- (#9525 fix) can find the address and return keccak("")/0 respectively, while the
  -- bv_fail=46 code-consistency comparator skips records with has_code_change=0.
  ".Lcrce_nonempty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp)\n" ++
  "  mv s0, a0                   # addr ptr (20B BE)\n" ++
  "  mv s1, a1                   # code ptr\n" ++
  "  mv s2, a2                   # code_len\n" ++
  "  la t0, exec_code_effect_next; ld s3, 0(t0)        # s3 = current free offset\n" ++
  "  addi t0, s2, 55; andi t0, t0, -8                  # t0 = round8(48 + code_len)\n" ++
  "  add t1, s3, t0                                    # t1 = new free offset\n" ++
  "  li t2, " ++ toString execCodeEffectLogCap ++ "\n" ++
  "  bgtu t1, t2, .Lcrce_overflow\n" ++
  "  la t3, exec_code_effect_log; add t3, t3, s3       # t3 = entry base\n" ++
  "  sd x0, 0(t3); sd x0, 8(t3); sd x0, 16(t3); sd x0, 24(t3)   # zero 32B addr field\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lcrce_cpa:\n" ++
  "  beqz t6, .Lcrce_cpa_d\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lcrce_cpa\n" ++
  ".Lcrce_cpa_d:\n" ++
  "  li t4, 0; beqz s2, .Lcrce_hcc; li t4, 1\n" ++
  ".Lcrce_hcc:\n" ++
  "  sd t4, 32(t3)                           # has_code_change = (code_len != 0) ? 1 : 0\n" ++
  "  sd s2, 40(t3)                                     # code_len\n" ++
  "  addi t5, t3, 48; mv t4, s1; mv t6, s2\n" ++
  ".Lcrce_cpc:\n" ++
  "  beqz t6, .Lcrce_cpc_d\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lcrce_cpc\n" ++
  ".Lcrce_cpc_d:\n" ++
  "  la t0, exec_code_effect_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, exec_code_effect_next; addi t1, s2, 55; andi t1, t1, -8; add t1, s3, t1; sd t1, 0(t0)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcrce_ret\n" ++
  ".Lcrce_overflow:\n" ++
  "  la t0, exec_code_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lcrce_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); addi sp, sp, 32\n" ++
  "  ret"

/-! ## find_code_effect_by_address

    Locate the code-effect record for an account by its 20-byte BE address.

    Calling convention:
      a0 = code-effect log base ptr
      a1 = entry count
      a2 = 20-byte big-endian address ptr
    Returns:
      a0 = record ptr (at the +0 addr field; pass record+32 to
           bal_account_code_consistent) or 0 if not found.
    Walks variable-stride entries (round8(48 + code_len)). Clobbers t0-t6, a0. -/
def findCodeEffectByAddress_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .BEQ .x6 .x0 (80 : BitVec 13),
    .MV .x7 .x5,
    .MV .x28 .x12,
    .LI .x29 (20 : Word),
    .BEQ .x29 .x0 (56 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x30 .x5 (40 : BitVec 12),
    .ADDI .x30 .x30 (55 : BitVec 12),
    .ANDI .x30 .x30 (-8 : BitVec 12),
    .ADD .x5 .x5 .x30,
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-68 : BitVec 21),
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def findCodeEffectByAddressFunction : String :=
  "find_code_effect_by_address:\n" ++ emitProgram findCodeEffectByAddress_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `findCodeEffectByAddress_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem findCodeEffectByAddressFunction_eq_prog :
    findCodeEffectByAddressFunction = "find_code_effect_by_address:\n" ++ emitProgram findCodeEffectByAddress_prog := rfl

#guard findCodeEffectByAddressFunction.startsWith "find_code_effect_by_address:\n"
#guard findCodeEffectByAddress_prog.length = 24
/-- Data region for the code-effect log (linked wherever CREATE deposit runs;
    included in this probe and, in step .8b-2, the runtime dispatcher data). -/
def createCodeEffectLogData : String :=
  ".balign 8\n" ++
  "exec_code_effect_count:\n  .zero 8\n" ++
  "exec_code_effect_next:\n  .zero 8\n" ++
  "exec_code_effect_overflow:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "exec_code_effect_log:\n  .zero " ++ toString execCodeEffectLogCap ++ "\n"

/-- `zisk_create_code_effect_log`: known-answer probe. Appends two records
    (addr A = 0x11*20, code = {0x60,0xff}; addr B = 0x22*20, code = {0x00}), then
    looks up A, B, and a missing addr C = 0x33*20, surfacing the found fields and
    the miss to OUTPUT (0xa0010000):
      +0 find(A)!=0    +8 A.has_code_change  +16 A.code_len  +24 A.code[0]  +32 A.code[1]
      +40 B.code_len   +48 B.code[0]         +56 find(C)==0  +64 count -/
def ziskCreateCodeEffectLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Build addr A (0x11*20), addr B (0x22*20), addr C (0x33*20), code A {0x60,0xff}, code B {0x00}.
  "  la t0, ccel_addr_a; li t1, 20\n" ++
  "1:\n  li t2, 0x11; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 1b\n" ++
  "  la t0, ccel_addr_b; li t1, 20\n" ++
  "2:\n  li t2, 0x22; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 2b\n" ++
  "  la t0, ccel_addr_c; li t1, 20\n" ++
  "3:\n  li t2, 0x33; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 3b\n" ++
  "  la t0, ccel_code_a; li t1, 0x60; sb t1, 0(t0); li t1, 0xff; sb t1, 1(t0)\n" ++
  "  la t0, ccel_code_b; sb x0, 0(t0)\n" ++
  -- Append A (len 2) and B (len 1).
  "  la a0, ccel_addr_a; la a1, ccel_code_a; li a2, 2; jal ra, create_record_code_effect\n" ++
  "  la a0, ccel_addr_b; la a1, ccel_code_b; li a2, 1; jal ra, create_record_code_effect\n" ++
  -- Look up A.
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, ccel_addr_a\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  snez t1, a0; sd t1, 0(s0)\n" ++                 -- find(A)!=0
  "  beqz a0, 4f\n" ++
  "  ld t1, 32(a0); sd t1, 8(s0)\n" ++               -- A.has_code_change
  "  ld t1, 40(a0); sd t1, 16(s0)\n" ++              -- A.code_len
  "  lbu t1, 48(a0); sd t1, 24(s0)\n" ++             -- A.code[0]
  "  lbu t1, 49(a0); sd t1, 32(s0)\n" ++             -- A.code[1]
  "4:\n" ++
  -- Look up B.
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, ccel_addr_b\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  beqz a0, 5f\n" ++
  "  ld t1, 40(a0); sd t1, 40(s0)\n" ++              -- B.code_len
  "  lbu t1, 48(a0); sd t1, 48(s0)\n" ++             -- B.code[0]
  "5:\n" ++
  -- Look up missing C.
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, ccel_addr_c\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  seqz t1, a0; sd t1, 56(s0)\n" ++                -- find(C)==0
  "  la t0, exec_code_effect_count; ld t1, 0(t0); sd t1, 64(s0)\n" ++  -- count
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lccel_done\n" ++
  createRecordCodeEffectFunction ++ "\n" ++
  findCodeEffectByAddressFunction ++ "\n" ++
  ".Lccel_done:"

def ziskCreateCodeEffectLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ccel_addr_a:\n  .zero 20\n" ++
  "ccel_addr_b:\n  .zero 20\n" ++
  "ccel_addr_c:\n  .zero 20\n" ++
  "ccel_code_a:\n  .zero 8\n" ++
  "ccel_code_b:\n  .zero 8\n" ++
  createCodeEffectLogData

def ziskCreateCodeEffectLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCreateCodeEffectLogPrologue
  dataAsm     := ziskCreateCodeEffectLogDataSection
}

end EvmAsm.Codegen
