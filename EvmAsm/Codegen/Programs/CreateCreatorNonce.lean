/-
  EvmAsm.Codegen.Programs.CreateCreatorNonce

  Per-creator running-nonce table for multi-CREATE address correctness (bead
  fhsxz.2.4.2.61.8, the CREATE nonce slice .8b-3a).

  CREATE/CREATE2 derives the new address from the creator's CURRENT nonce, then
  increments the creator's nonce: address_N uses nonce N, then the creator's nonce
  becomes N+1, so a SECOND CREATE by the same creator in the same tx uses N+1 (a
  distinct address). The inline CREATE tail today re-sources the creator's nonce
  from the PRE-STATE on every CREATE (nonce_at_header_state_root), so two CREATEs by
  one creator compute the SAME address -- a bug that surfaces once CREATE is
  activated (.8c) on a multi-CREATE row.

  This is the running-nonce bookkeeping. It must be PER-CREATOR (keyed by the 20-byte
  creator address), not a single counter: a self-contained recipient may CALL another
  contract that also CREATEs, and that callee is a different creator whose own nonce
  runs independently. So a small table maps creator address -> next nonce:

    create_creator_nonce_use(creator_be, pre_nonce):
      if creator already in the table at entry E:  ret = E.nonce; E.nonce += 1; return ret
      else (first CREATE by this creator):         append {creator, pre_nonce + 1}; return pre_nonce

  The table is reset per transaction (count := 0) by the dispatcher setup; the tail
  integration (replace the pre-state nonce with create_creator_nonce_use's result) +
  the per-tx reset land in .8b-3b. On table overflow the creator's nonce falls back to
  pre_nonce (no store) and sets create_nonce_table_overflow so block_verdict rejects.
  Entries are 40 bytes: addr (20B BE in the low/first 20, padded to 32)
  + next nonce (u64).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Capacity (entries) of the per-creator nonce table — distinct creators per tx. -/
def createNonceTableCap : Nat := 64

/-! ## create_creator_nonce_use
    a0 = creator address ptr (20-byte big-endian)
    a1 = creator pre-state nonce (u64; used only on the creator's FIRST CREATE)
    a0 (output) = the nonce to use for this CREATE (and the table is advanced).
    Clobbers t0-t6; preserves s-regs (saved). -/
def createCreatorNonceUseFunction : String :=
  "create_creator_nonce_use:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp)\n" ++
  "  mv s0, a0                   # creator ptr\n" ++
  "  mv s1, a1                   # pre-state nonce\n" ++
  "  la t0, create_nonce_table; la t1, create_nonce_table_count; ld t1, 0(t1)\n" ++
  "  li t2, 0                    # index\n" ++
  ".Lccnu_loop:\n" ++
  "  beq t2, t1, .Lccnu_new\n" ++
  "  li t3, 40; mul t3, t2, t3; add t3, t0, t3   # entry = base + idx*40\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lccnu_cmp:\n" ++
  "  beqz t6, .Lccnu_found\n" ++
  "  lbu a0, 0(t4); lbu a1, 0(t5); bne a0, a1, .Lccnu_advance\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lccnu_cmp\n" ++
  ".Lccnu_advance:\n" ++
  "  addi t2, t2, 1; j .Lccnu_loop\n" ++
  ".Lccnu_found:\n" ++
  "  ld a0, 32(t3)               # ret = entry.nonce\n" ++
  "  li t4, -1; beq a0, t4, .Lccnu_ret  # max nonce: CREATE must fail; do not wrap table\n" ++
  "  addi t4, a0, 1; sd t4, 32(t3)   # entry.nonce += 1\n" ++
  "  j .Lccnu_ret\n" ++
  ".Lccnu_new:\n" ++
  "  li t3, " ++ toString createNonceTableCap ++ "\n" ++
  "  bgeu t1, t3, .Lccnu_overflow\n" ++
  "  li t3, 40; mul t3, t1, t3; add t3, t0, t3   # new entry = base + count*40\n" ++
  "  sd x0, 0(t3); sd x0, 8(t3); sd x0, 16(t3); sd x0, 24(t3)   # zero 32B addr\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lccnu_cpaddr:\n" ++
  "  beqz t6, .Lccnu_cpaddr_d\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lccnu_cpaddr\n" ++
  ".Lccnu_cpaddr_d:\n" ++
  "  addi t4, s1, 1; sd t4, 32(t3)   # entry.nonce = pre_nonce + 1 (next CREATE)\n" ++
  "  la t4, create_nonce_table_count; ld t5, 0(t4); addi t5, t5, 1; sd t5, 0(t4)\n" ++
  "  mv a0, s1                   # ret = pre_nonce (this CREATE)\n" ++
  "  j .Lccnu_ret\n" ++
  ".Lccnu_overflow:\n" ++
  "  la t3, create_nonce_table_overflow; li t4, 1; sd t4, 0(t3)\n" ++
  "  mv a0, s1                   # conservative fallback: pre_nonce, no store\n" ++
  ".Lccnu_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); addi sp, sp, 16\n" ++
  "  ret\n" ++
  -- Read the current (next-to-use) nonce for an already-seeded creator without
  -- advancing the table.  A CREATE child uses this at return time: initcode can
  -- itself CREATE, so the child final nonce is the table value rather than
  -- necessarily the initial EIP-161 nonce 1.  A missing table entry is only a
  -- standalone fallback and returns 1.
  -- a0 = creator address ptr (20-byte big-endian); a0 = current nonce (or 1 on miss).
  -- Clobbers t0-t6 and a0-a1; preserves s-registers.
  "create_creator_nonce_current:\n" ++
  "  mv t6, a0\n" ++
  "  la t0, create_nonce_table; la t1, create_nonce_table_count; ld t1, 0(t1)\n" ++
  "  li t2, 0\n" ++
  ".Lccnc_loop:\n" ++
  "  beq t2, t1, .Lccnc_miss\n" ++
  "  li t3, 40; mul t3, t2, t3; add t3, t0, t3\n" ++
  "  mv t4, t6; mv t5, t3; li a1, 20\n" ++
  ".Lccnc_cmp:\n" ++
  "  beqz a1, .Lccnc_found\n" ++
  "  lbu a0, 0(t4); lbu t0, 0(t5); bne a0, t0, .Lccnc_next\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi a1, a1, -1; j .Lccnc_cmp\n" ++
  ".Lccnc_next:\n" ++
  "  addi t2, t2, 1; la t0, create_nonce_table; j .Lccnc_loop\n" ++
  ".Lccnc_found:\n" ++
  "  ld a0, 32(t3); ret\n" ++
  ".Lccnc_miss:\n" ++
  "  li a0, 1; ret\n" ++
  -- A successfully entered CREATE child is initialized with nonce 1 before
  -- its initcode executes (`process_create_message`). Seed/upsert that child
  -- as a potential creator so a recursive CREATE derives its first target
  -- from nonce 1 rather than the prefunded account's pre-state nonce 0.
  -- a0 = created address ptr (20-byte BE); preserves s-regs.
  "create_creator_nonce_seed_one:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  la t0, create_nonce_table; la t1, create_nonce_table_count; ld t1, 0(t1)\n" ++
  "  li t2, 0\n" ++
  ".Lccns_loop:\n" ++
  "  beq t2, t1, .Lccns_new\n" ++
  "  li t3, 40; mul t3, t2, t3; add t3, t0, t3\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lccns_cmp:\n" ++
  "  beqz t6, .Lccns_set\n" ++
  "  lbu a0, 0(t4); lbu a1, 0(t5); bne a0, a1, .Lccns_next\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lccns_cmp\n" ++
  ".Lccns_next:\n" ++
  "  addi t2, t2, 1; j .Lccns_loop\n" ++
  ".Lccns_set:\n" ++
  "  li t4, 1; sd t4, 32(t3); j .Lccns_ret\n" ++
  ".Lccns_new:\n" ++
  "  li t3, " ++ toString createNonceTableCap ++ "\n" ++
  "  bgeu t1, t3, .Lccns_overflow\n" ++
  "  li t3, 40; mul t3, t1, t3; add t3, t0, t3\n" ++
  "  sd x0, 0(t3); sd x0, 8(t3); sd x0, 16(t3); sd x0, 24(t3)\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lccns_copy:\n" ++
  "  beqz t6, .Lccns_copy_done\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lccns_copy\n" ++
  ".Lccns_copy_done:\n" ++
  "  li t4, 1; sd t4, 32(t3)\n" ++
  "  la t4, create_nonce_table_count; ld t5, 0(t4); addi t5, t5, 1; sd t5, 0(t4); j .Lccns_ret\n" ++
  ".Lccns_overflow:\n" ++
  "  la t3, create_nonce_table_overflow; li t4, 1; sd t4, 0(t3)\n" ++
  ".Lccns_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); addi sp, sp, 16\n" ++
  "  ret"

/-- Data for the per-creator nonce table (linked into the dispatcher data section in
    .8b-3b, co-located with the CREATE child data). -/
def createNonceTableData : String :=
  ".balign 8\n" ++
  "create_nonce_table_count:\n  .zero 8\n" ++
  "create_nonce_table_overflow:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "create_nonce_table:\n  .zero " ++ toString (createNonceTableCap * 40) ++ "\n"

/-- `zisk_create_creator_nonce_use`: known-answer probe. Two creators (A=0x11*20,
    B=0x22*20); the running nonce advances per creator independently:
      +0  use(A, 5)  -> 5   (A first; A.next=6)
      +8  use(A, 5)  -> 6   (A found; A.next=7)
      +16 use(B, 0)  -> 0   (B first; B.next=1)
      +24 use(A, 5)  -> 7   (A found; A.next=8)
      +32 use(B, 0)  -> 1   (B found; B.next=2)
      +40 table count -> 2 -/
def ziskCreateCreatorNonceUsePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, create_nonce_table_count; sd x0, 0(t0)\n" ++       -- reset per "tx"
  "  la t0, ccnu_a; li t1, 20\n" ++
  "1:\n  li t2, 0x11; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 1b\n" ++
  "  la t0, ccnu_b; li t1, 20\n" ++
  "2:\n  li t2, 0x22; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 2b\n" ++
  "  la a0, ccnu_a; li a1, 5; jal ra, create_creator_nonce_use; sd a0, 0(s0)\n" ++
  "  la a0, ccnu_a; li a1, 5; jal ra, create_creator_nonce_use; sd a0, 8(s0)\n" ++
  "  la a0, ccnu_b; li a1, 0; jal ra, create_creator_nonce_use; sd a0, 16(s0)\n" ++
  "  la a0, ccnu_a; li a1, 5; jal ra, create_creator_nonce_use; sd a0, 24(s0)\n" ++
  "  la a0, ccnu_b; li a1, 0; jal ra, create_creator_nonce_use; sd a0, 32(s0)\n" ++
  "  la t0, create_nonce_table_count; ld t1, 0(t0); sd t1, 40(s0)\n" ++
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lccnu_done\n" ++
  createCreatorNonceUseFunction ++ "\n" ++
  ".Lccnu_done:"

def ziskCreateCreatorNonceUseDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ccnu_a:\n  .zero 20\n" ++
  "ccnu_b:\n  .zero 20\n" ++
  createNonceTableData

def ziskCreateCreatorNonceUseProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCreateCreatorNonceUsePrologue
  dataAsm     := ziskCreateCreatorNonceUseDataSection
}

end EvmAsm.Codegen
