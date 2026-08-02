/-
  EvmAsm.Codegen.Programs.BalGasValid

  bal_gas_valid (bead evm-asm-fhsxz.2.4.2.5, task #23): the EIP-7928 block-access-
  list gas-limit rule — the binding constraint that makes the Step-2 verdict reject
  blocks like `bal_gas_limit_boundary[below_boundary]` (which header-validation and
  the state recompute cannot catch, since it is a semantic rule not reflected in any
  header field or the state root).

  Spec (execution-specs amsterdam/block_access_lists.py:validate_block_access_list_gas_limit):
    bal_items = Σ over accounts of (1 + #unique storage slots)
    INVALID iff bal_items > block_gas_limit // BLOCK_ACCESS_LIST_ITEM (=2000).
  The BAL encoder makes `storage_reads` DISJOINT from `storage_changes` (it omits
  read slots already in storage_changes), so #unique slots = len(storage_changes) +
  len(storage_reads) — no dedup needed, just element counts.

  BAL RLP = list of AccountChanges; each AccountChanges =
    [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes].
  So per account: bal_items += 1 + count(item 1) + count(item 2).

  Division-free test: bal_items > gas_limit/2000  ⟺  bal_items*2000 > gas_limit.

  Uses the cursor walker to count the BAL rows and the per-account storage lists.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Probe-only entry PC for `bal_gas_valid` (#11172). Unlinked from
    `stateless_guest`; concrete `jalOff` immediates in `balGasValid_prog` use this
    placeholder. Emitting uses `balGasValid_relocs` (symbolic). Do NOT invent a
    guest-linked offset — drift is covered by `balGasValidFunction_eq_prog`. -/
def balGasValidPc : Nat := 0x80000000

/-! ## bal_gas_valid
    a0 = BAL RLP ptr   a1 = BAL RLP length   a2 = block_gas_limit
    a0 (output) = 0 (valid) / 1 (gas-limit exceeded) / 2 (parse error).

    #11172: unlinked from guest (superseded by `bal_gas_valid_from_builder`).
    Kept for `zisk_bal_gas_valid` probe + verified Program. -/
def balGasValid_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
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
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balGasValidPc + 76)),
    .BNE .x12 .x0 (280 : BitVec 13),
    .MV .x19 .x10,
    .MV .x21 .x11,
    .LI .x20 (0 : Word),
    .MV .x10 .x19,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balGasValidPc + 104)),
    .LI .x5 (2 : Word),
    .BEQ .x11 .x5 (220 : BitVec 13),
    .BNE .x11 .x0 (244 : BitVec 13),
    .MV .x19 .x10,
    .SUB .x22 .x10 .x12,
    .MV .x23 .x12,
    .ADDI .x20 .x20 (1 : BitVec 12),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balGasValidPc + 144)),
    .BNE .x12 .x0 (212 : BitVec 13),
    .MV .x24 .x10,
    .MV .x25 .x11,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balGasValidPc + 160)),
    .BNE .x11 .x0 (196 : BitVec 13),
    .MV .x24 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balGasValidPc + 180)),
    .BNE .x11 .x0 (176 : BitVec 13),
    .MV .x24 .x10,
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balGasValidPc + 200)),
    .BNE .x12 .x0 (156 : BitVec 13),
    .MV .x26 .x10,
    .MV .x27 .x11,
    .MV .x10 .x26,
    .MV .x11 .x27,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balGasValidPc + 224)),
    .LI .x5 (2 : Word),
    .BEQ .x11 .x5 (20 : BitVec 13),
    .BNE .x11 .x0 (124 : BitVec 13),
    .MV .x26 .x10,
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balGasValidPc + 260)),
    .BNE .x11 .x0 (96 : BitVec 13),
    .MV .x24 .x10,
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balGasValidPc + 280)),
    .BNE .x12 .x0 (76 : BitVec 13),
    .MV .x26 .x10,
    .MV .x27 .x11,
    .MV .x10 .x26,
    .MV .x11 .x27,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balGasValidPc + 304)),
    .LI .x5 (2 : Word),
    .BEQ .x11 .x5 (-216 : BitVec 13),
    .BNE .x11 .x0 (44 : BitVec 13),
    .MV .x26 .x10,
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x5 (2000 : Word),
    .MUL .x6 .x20 .x5,
    .BLTU .x18 .x6 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
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
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balGasValid_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balGasValid_relocs : RelocTable :=
  [ (19, .jal .x1 "rlp_walk_init"),
    (26, .jal .x1 "rlp_walk_next"),
    (36, .jal .x1 "rlp_walk_init"),
    (40, .jal .x1 "rlp_walk_next"),
    (45, .jal .x1 "rlp_walk_next"),
    (50, .jal .x1 "rlp_walk_init"),
    (56, .jal .x1 "rlp_walk_next"),
    (65, .jal .x1 "rlp_walk_next"),
    (70, .jal .x1 "rlp_walk_init"),
    (76, .jal .x1 "rlp_walk_next") ]

def balGasValidFunction : String :=
  "bal_gas_valid:\n" ++ emitProgramR balGasValid_prog balGasValid_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balGasValid_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balGasValidFunction_eq_prog :
    balGasValidFunction = "bal_gas_valid:\n" ++ emitProgramR balGasValid_prog balGasValid_relocs := rfl

#guard balGasValidFunction.startsWith "bal_gas_valid:\n"
#guard balGasValid_prog.length = 106

/-! ## `bal_gas_valid_from_builder` (#11120)

    Count `bal_items` from the **built** BAL builder after
    `bal_serializer_rebuild_hash` (incorporate touched + sorts), then apply the
    same gas predicate as `bal_gas_valid` / execution-specs
    `validate_block_access_list_gas_limit`:

      bal_items = Σ_accounts (1 + #unique storage slots)
      unique slots = distinct slots in storage_changes ∪ surviving storage_reads
      INVALID iff bal_items * 2000 > block_gas_limit

    Shape C (count from builder), not materialise-then-walk. Rebuild is
    stream-only into keccak; there is no rebuilt RLP buffer to hand the RLP
    walker. After sort, change rows are ordered by (addr, slot, bai) so unique
    change slots are a linear scan; surviving reads reuse
    `bal_serializer_slot_written` (spec `:544-547` drop when also written).

    a0 = block_gas_limit
    a0 (out) = 0 valid / 1 exceeded

    PRE: `bal_serializer_rebuild_hash` returned 0 (builder incorporated + sorted).
    #11172: RLP walker `bal_gas_valid` is probe-only (unlinked from guest). -/
def balGasValidFromBuilderFunction : String :=
  "bal_gas_valid_from_builder:\n" ++
  -- Frame 96 B: saves 0..56 + BE20 scratch at 64..83 (must not overflow into caller).
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0\n" ++                                              -- s0 = gas_limit
  -- items starts at account_count (one item per address, including empty touches)
  "  la t0, bal_builder_account_count; ld s1, 0(t0)\n" ++         -- s1 = bal_items
  -- Unique slots among storage_changes (sorted by addr BE, slot BE, bai LE)
  "  la t0, bal_builder_storage_change_count; ld s2, 0(t0)\n" ++
  "  li s3, 0\n" ++                                              -- i
  "  li s4, 0\n" ++                                              -- prev_valid
  "  li s6, 0\n" ++                                              -- prev index
  ".Lbgvfb_ch:\n" ++
  "  bgeu s3, s2, .Lbgvfb_ch_done\n" ++
  "  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add s5, t2, t1\n" ++
  "  beqz s4, .Lbgvfb_ch_new\n" ++
  "  li t0, 96; mul t1, s6, t0; la t2, bal_builder_storage_changes; add t4, t2, t1\n" ++
  "  li t5, 0\n" ++
  ".Lbgvfb_ch_acmp:\n" ++
  "  li t0, 20; beq t5, t0, .Lbgvfb_ch_scmp\n" ++
  "  add t0, s5, t5; add t1, t4, t5\n" ++
  "  lbu t2, 0(t0); lbu t3, 0(t1); bne t2, t3, .Lbgvfb_ch_new\n" ++
  "  addi t5, t5, 1; j .Lbgvfb_ch_acmp\n" ++
  ".Lbgvfb_ch_scmp:\n" ++
  "  li t5, 0\n" ++
  ".Lbgvfb_ch_scmp_loop:\n" ++
  "  li t0, 32; beq t5, t0, .Lbgvfb_ch_next\n" ++
  "  addi t0, s5, 32; add t0, t0, t5\n" ++
  "  addi t1, t4, 32; add t1, t1, t5\n" ++
  "  lbu t2, 0(t0); lbu t3, 0(t1); bne t2, t3, .Lbgvfb_ch_new\n" ++
  "  addi t5, t5, 1; j .Lbgvfb_ch_scmp_loop\n" ++
  ".Lbgvfb_ch_new:\n" ++
  "  addi s1, s1, 1\n" ++
  "  mv s6, s3\n" ++
  "  li s4, 1\n" ++
  ".Lbgvfb_ch_next:\n" ++
  "  addi s3, s3, 1; j .Lbgvfb_ch\n" ++
  ".Lbgvfb_ch_done:\n" ++
  -- Surviving storage_reads: count reads whose (addr,slot) is not also written
  "  la t0, storage_reads_count; ld s2, 0(t0)\n" ++
  "  li s3, 0\n" ++
  ".Lbgvfb_rd:\n" ++
  "  bgeu s3, s2, .Lbgvfb_test\n" ++
  "  slli t0, s3, 6; li t1, 0xa1ba0000; add s5, t1, t0\n" ++
  -- reverse LE stack-word low 20 bytes → BE20 scratch at sp+64 (fits in 96 B frame)
  "  li t5, 0\n" ++
  ".Lbgvfb_rd_rev:\n" ++
  "  li t0, 20; beq t5, t0, .Lbgvfb_rd_chk\n" ++
  "  li t0, 19; sub t0, t0, t5; add t0, s5, t0; lbu t1, 0(t0)\n" ++
  "  addi t0, sp, 64; add t0, t0, t5; sb t1, 0(t0)\n" ++
  "  addi t5, t5, 1; j .Lbgvfb_rd_rev\n" ++
  ".Lbgvfb_rd_chk:\n" ++
  "  addi a0, s5, 32\n" ++
  "  addi a1, sp, 64\n" ++
  "  jal ra, bal_serializer_slot_written\n" ++
  "  bnez a0, .Lbgvfb_rd_next\n" ++
  "  addi s1, s1, 1\n" ++
  ".Lbgvfb_rd_next:\n" ++
  "  addi s3, s3, 1; j .Lbgvfb_rd\n" ++
  ".Lbgvfb_test:\n" ++
  -- bal_items * 2000 > gas_limit  ⟺  gas_limit < bal_items * 2000
  "  li t0, 2000\n" ++
  "  mul t1, s1, t0\n" ++
  "  bltu s0, t1, .Lbgvfb_exceed\n" ++
  "  li a0, 0; j .Lbgvfb_ret\n" ++
  ".Lbgvfb_exceed:\n" ++
  "  li a0, 1\n" ++
  ".Lbgvfb_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n"

#guard balGasValidFromBuilderFunction.startsWith "bal_gas_valid_from_builder:\n"
/-! ## bgv_u32le -- read a little-endian u32 byte-wise (a0=ptr -> a0). Leaf. -/
def bgvU32le_prog : Program :=
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

def bgvU32leFunction : String :=
  "bgv_u32le:\n" ++ emitProgram bgvU32le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bgvU32le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bgvU32leFunction_eq_prog :
    bgvU32leFunction = "bgv_u32le:\n" ++ emitProgram bgvU32le_prog := rfl

#guard bgvU32leFunction.startsWith "bgv_u32le:\n"
#guard bgvU32le_prog.length = 12
/-! ## bgv_u64le -- read a little-endian u64 byte-wise (a0=ptr -> a0). Leaf. -/
def bgvU64le_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x7 (0 : Word),
    .LI .x28 (8 : Word),
    .BEQ .x7 .x28 (32 : BitVec 13),
    .ADD .x29 .x10 .x7,
    .LBU .x30 .x29 (0 : BitVec 12),
    .SLLI .x31 .x7 (3 : BitVec 6),
    .SLL .x30 .x30 .x31,
    .OR .x5 .x5 .x30,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bgvU64leFunction : String :=
  "bgv_u64le:\n" ++ emitProgram bgvU64le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bgvU64le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bgvU64leFunction_eq_prog :
    bgvU64leFunction = "bgv_u64le:\n" ++ emitProgram bgvU64le_prog := rfl

#guard bgvU64leFunction.startsWith "bgv_u64le:\n"
#guard bgvU64le_prog.length = 13
/-! ## bal_section_info -- locate BAL RLP inside an SszStatelessInput.
    a0 = SSZ_BASE   a1 = out BAL ptr   a2 = out BAL len   a3 = out account count
    a0 (output) = 0 ok / 1 parse error. -/
def balSectionInfo_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x19 .x11,
    .MV .x20 .x12,
    .MV .x21 .x13,
    .ADDI .x9 .x8 (16 : BitVec 12),
    .ADDI .x18 .x8 (60 : BitVec 12),
    .ADDI .x10 .x18 (528 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.bal_section_info + 60)),
    .ADD .x5 .x18 .x10,
    .SD .x19 .x5 (0 : BitVec 12),
    .ADDI .x10 .x9 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.bal_section_info + 76)),
    .ADD .x6 .x9 .x10,
    .LD .x5 .x19 (0 : BitVec 12),
    .SUB .x6 .x6 .x5,
    .SD .x20 .x6 (0 : BitVec 12),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_section_info + 104)),
    .BNE .x12 .x0 (64 : BitVec 13),
    .MV .x9 .x10,
    .MV .x18 .x11,
    .LI .x8 (0 : Word),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_section_info + 132)),
    .LI .x5 (2 : Word),
    .BEQ .x11 .x5 (20 : BitVec 13),
    .BNE .x11 .x0 (28 : BitVec 13),
    .MV .x9 .x10,
    .ADDI .x8 .x8 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SD .x21 .x8 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSectionInfo_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSectionInfo_relocs : RelocTable :=
  [ (15, .jal .x1 "bgv_u32le"),
    (19, .jal .x1 "bgv_u32le"),
    (26, .jal .x1 "rlp_walk_init"),
    (33, .jal .x1 "rlp_walk_next") ]

def balSectionInfoFunction : String :=
  "bal_section_info:\n" ++ emitProgramR balSectionInfo_prog balSectionInfo_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSectionInfo_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSectionInfoFunction_eq_prog :
    balSectionInfoFunction = "bal_section_info:\n" ++ emitProgramR balSectionInfo_prog balSectionInfo_relocs := rfl

#guard balSectionInfoFunction.startsWith "bal_section_info:\n"
#guard balSectionInfo_prog.length = 53
/-- `zisk_bal_section_info`: probe. Fed the SAME `-i` input as the guest.
    Output: OUTPUT+0 = status, OUTPUT+8 = BAL ptr, OUTPUT+16 = BAL len,
    OUTPUT+24 = account count. -/
def ziskBalSectionInfoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000000; addi a0, a0, 18    # SSZ_BASE\n" ++
  "  li a1, 0xa0010008\n" ++
  "  li a2, 0xa0010010\n" ++
  "  li a3, 0xa0010018\n" ++
  "  jal ra, bal_section_info\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lbsi_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++

  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  balSectionInfoFunction ++ "\n" ++
  ".Lbsi_pdone:"

/-- `zisk_bal_gas_valid`: probe. Fed the SAME `-i` input as the guest. Navigates
    to the block_access_list section + block_gas_limit and runs bal_gas_valid.
    Output: OUTPUT+0 = result (0 valid / 1 exceeded / 2 parse error). -/
def ziskBalGasValidPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000; addi s0, s0, 18    # SSZ_BASE\n" ++
  "  addi s1, s0, 16                       # NPR = SSZ_BASE+16\n" ++
  "  addi s2, s1, 44                       # exec_payload = NPR+44\n" ++
  "  # bal_off = u32 @ exec_payload+528 ; bal_start = exec_payload + bal_off\n" ++
  "  addi a0, s2, 528; jal ra, bgv_u32le\n" ++
  "  add s3, s2, a0                        # bal_start\n" ++
  "  # bal_end = NPR + (u32 @ NPR+4)\n" ++
  "  addi a0, s1, 4; jal ra, bgv_u32le\n" ++
  "  add s4, s1, a0                        # bal_end\n" ++
  "  sub s4, s4, s3                        # bal_len\n" ++
  "  # gas_limit = u64 @ exec_payload+412\n" ++
  "  addi a0, s2, 412; jal ra, bgv_u64le\n" ++
  "  mv a2, a0                             # gas_limit\n" ++
  "  mv a0, s3; mv a1, s4                  # BAL ptr, len\n" ++
  "  jal ra, bal_gas_valid\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lbgv_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++

  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  balGasValidFunction ++ "\n" ++
  balGasValidFromBuilderFunction ++ "\n" ++
  ".Lbgv_pdone:"

def ziskBalGasValidDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bgv_count:\n  .zero 8\n" ++
  "bgv_off:\n  .zero 8\n" ++
  "bgv_size:\n  .zero 8\n" ++
  "bgv_acctlen:\n  .zero 8"

def ziskBalGasValidProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalGasValidPrologue
  dataAsm     := ziskBalGasValidDataSection
}

def ziskBalSectionInfoProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalSectionInfoPrologue
  dataAsm     := ziskBalGasValidDataSection
}

end EvmAsm.Codegen
