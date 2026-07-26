/-
  EvmAsm.Codegen.Programs.BalStorageReadsExecLog

  `bal_storage_reads_in_exec_log` (bead bmvmx.1.6.7) — verify a BAL account's
  `storage_reads` (AccountChanges item 2) against execution. EIP-7928 records
  storage_reads (slots accessed but not net-changed) and commits them via the block
  access-list hash — but reads do NOT affect the state root, so this is NOT covered
  by the post-state-root comparison. Checking it against the persistent exec log
  (which records every SLOAD) catches a BAL that fabricates a read of a slot the
  account never accessed.

  Direction (forward): every BAL storage_read slot must appear in the exec log keyed
  on the account. (The converse — every exec access is a BAL read-or-change — is a
  follow-up.) Single-tx scope; the multi-tx (block_access_index) tuple layer is
  bmvmx.1.6.6.

  Exec-log entry (Storage.lean): 128 B = addrHash@0, slotKey@32, original@64,
  current@96. storage_reads keys are RLP-minimal big-endian U256; this byte-reverses
  them into EVM-stack order (4 LE u64 limbs) to match the exec-log slotKey.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_reads_in_exec_log

    Calling convention:
      a0 = account address ptr (32-byte addrHash, as keyed in the exec log)
      a1 = AccountChanges RLP ptr   a2 = AccountChanges RLP length
      a3 = exec storage-log base    a4 = exec storage-log length (entry count)
    Returns:
      a0 = 0 if every storage_read slot the BAL claims for the account appears in the
           exec log keyed on the account; 1 on any claimed read absent from the log
           (or parse failure → conservative reject). An empty/absent storage_reads
           list trivially returns 0. -/
def balStorageReadsInExecLog_prog : Program :=
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
    .MV .x9 .x13,
    .MV .x18 .x14,
    .MV .x21 .x15,
    .MV .x10 .x11,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_reads_in_exec_log + 60)),
    .BNE .x12 .x0 (336 : BitVec 13),
    .MV .x22 .x11,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 72)),
    .BNE .x11 .x0 (324 : BitVec 13),
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 84)),
    .BNE .x11 .x0 (312 : BitVec 13),
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 96)),
    .BNE .x11 .x0 (300 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_reads_in_exec_log + 112)),
    .BNE .x12 .x0 (284 : BitVec 13),
    .MV .x19 .x10,
    .MV .x20 .x11,
    .BEQ .x19 .x20 (264 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 140)),
    .BNE .x11 .x0 (256 : BitVec 13),
    .MV .x19 .x10,
    .SUB .x6 .x10 .x12,
    .MV .x7 .x12,
    .LI .x5 (32 : Word),
    .BLTU .x5 .x7 (236 : BitVec 13),
    .BEQ .x7 .x0 (12 : BitVec 13),
    .LBU .x5 .x6 (0 : BitVec 12),
    .BEQ .x5 .x0 (224 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 180)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 180)),
    .SD .x5 .x0 (0 : BitVec 12),
    .SD .x5 .x0 (8 : BitVec 12),
    .SD .x5 .x0 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .ADD .x28 .x6 .x7,
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .MV .x29 .x5,
    .MV .x30 .x7,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x15 .x28 (0 : BitVec 12),
    .SB .x29 .x15 (0 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x7 .x18,
    .BEQ .x7 .x0 (148 : BitVec 13),
    .MUL .x28 .x7 .x21,
    .ADD .x28 .x9 .x28,
    .AUIPC .x31 (laHi GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 264)),
    .ADDI .x31 .x31 (laLo GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 264)),
    .SUB .x28 .x28 .x21,
    .LD .x29 .x28 (0 : BitVec 12),
    .LD .x30 .x8 (0 : BitVec 12),
    .BNE .x29 .x30 (92 : BitVec 13),
    .LD .x29 .x28 (8 : BitVec 12),
    .LD .x30 .x8 (8 : BitVec 12),
    .BNE .x29 .x30 (80 : BitVec 13),
    .LD .x29 .x28 (16 : BitVec 12),
    .LD .x30 .x8 (16 : BitVec 12),
    .BNE .x29 .x30 (68 : BitVec 13),
    .LD .x29 .x28 (24 : BitVec 12),
    .LD .x30 .x8 (24 : BitVec 12),
    .BNE .x29 .x30 (56 : BitVec 13),
    .LD .x29 .x28 (32 : BitVec 12),
    .LD .x30 .x31 (0 : BitVec 12),
    .BNE .x29 .x30 (44 : BitVec 13),
    .LD .x29 .x28 (40 : BitVec 12),
    .LD .x30 .x31 (8 : BitVec 12),
    .BNE .x29 .x30 (32 : BitVec 13),
    .LD .x29 .x28 (48 : BitVec 12),
    .LD .x30 .x31 (16 : BitVec 12),
    .BNE .x29 .x30 (20 : BitVec 13),
    .LD .x29 .x28 (56 : BitVec 12),
    .LD .x30 .x31 (24 : BitVec 12),
    .BNE .x29 .x30 (8 : BitVec 13),
    .JAL .x0 (16 : BitVec 21),
    .MV .x29 .x9,
    .BNE .x28 .x29 (-108 : BitVec 13),
    .JAL .x0 (16 : BitVec 21),
    .JAL .x0 (-260 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
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

/-- Reloc side-table for `balStorageReadsInExecLog_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balStorageReadsInExecLog_relocs : RelocTable :=
  [ (15, .jal .x1 "rlp_walk_init"),
    (18, .jal .x1 "rlp_walk_next"),
    (21, .jal .x1 "rlp_walk_next"),
    (24, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_init"),
    (35, .jal .x1 "rlp_walk_next"),
    (45, .la .x5 "bsr_krev"),
    (66, .la .x31 "bsr_krev") ]

def balStorageReadsInExecLogFunction : String :=
  "bal_storage_reads_in_exec_log:\n" ++ emitProgramR balStorageReadsInExecLog_prog balStorageReadsInExecLog_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balStorageReadsInExecLog_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balStorageReadsInExecLogFunction_eq_prog :
    balStorageReadsInExecLogFunction = "bal_storage_reads_in_exec_log:\n" ++ emitProgramR balStorageReadsInExecLog_prog balStorageReadsInExecLog_relocs := rfl

#guard balStorageReadsInExecLogFunction.startsWith "bal_storage_reads_in_exec_log:\n"
#guard balStorageReadsInExecLog_prog.length = 111
/-- Scratch for `bal_storage_reads_in_exec_log`. -/
def balStorageReadsInExecLogData : String :=
  ".balign 8\n" ++
  ".balign 32\n" ++
  "bsr_krev:\n  .zero 32\n"

/-- `zisk_bal_storage_reads_in_exec_log`: probe. Exec log (addrHash A=0xAA): slot 7
    accessed (read), slot 9 accessed. AccountChanges with storage_reads [7, 9]:
      +0  both reads present                -> 0
      +8  storage_reads [7, 0x0b] (0x0b absent from the log) -> 1 -/
def ziskBalStorageReadsExecLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- 2-entry exec log: (A, slot7, _, _), (A, slot9, _, _).
  "  la t0, bsre_log\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x07; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  sd x0, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  "  addi t0, t0, 128\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x09; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  sd x0, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  "  la t0, bsre_addr; li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  -- AccountChanges: f8 LL  94 <20 zero>  c0(storage_changes)  c2 07 09(storage_reads)  c0 c0 c0
  -- content: addr(21) + c0(1) + [c2 07 09](3) + c0 c0 c0(3) = 28 -> 0xf8 0x1c.
  "  la t0, bsre_acct\n" ++
  "  li t1, 0xf8; sb t1, 0(t0); li t1, 0x1c; sb t1, 1(t0); li t1, 0x94; sb t1, 2(t0)\n" ++
  "  li t2, 20; addi t3, t0, 3\n" ++
  "1:\n  beqz t2, 2f\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j 1b\n" ++
  "2:\n" ++
  "  li t1, 0xc0; sb t1, 23(t0)\n" ++                          -- storage_changes = []
  "  li t1, 0xc2; sb t1, 24(t0); li t1, 0x07; sb t1, 25(t0); li t1, 0x09; sb t1, 26(t0)\n" ++  -- storage_reads = [7,9]
  "  li t1, 0xc0; sb t1, 27(t0); sb t1, 28(t0); sb t1, 29(t0)\n" ++   -- balance/nonce/code = []
  -- stash AccountChanges ptr for the helper.
  "  la a0, bsre_addr; la a1, bsre_acct; li a2, 30; la a3, bsre_log; li a4, 2; li a5, 128\n" ++
  "  jal ra, bal_storage_reads_in_exec_log\n" ++
  "  sd a0, 0(s0)\n" ++
  -- Scenario 2: storage_reads = [7, 0x0b] (0x0b absent) -> reject.
  "  la t0, bsre_acct; li t1, 0x0b; sb t1, 26(t0)\n" ++         -- change second read key 0x09 -> 0x0b
  "  la a0, bsre_addr; la a1, bsre_acct; li a2, 30; la a3, bsre_log; li a4, 2; li a5, 128\n" ++
  "  jal ra, bal_storage_reads_in_exec_log\n" ++
  "  sd a0, 8(s0)\n" ++
  "  j .Lbsre_done\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balStorageReadsInExecLogFunction ++ "\n" ++
  ".Lbsre_done:"

def ziskBalStorageReadsExecLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bsre_log:\n  .zero 512\n" ++
  "bsre_addr:\n  .zero 32\n" ++
  "bsre_acct:\n  .zero 64\n" ++
  balStorageReadsInExecLogData

def ziskBalStorageReadsExecLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalStorageReadsExecLogPrologue
  dataAsm     := ziskBalStorageReadsExecLogDataSection
}

end EvmAsm.Codegen
