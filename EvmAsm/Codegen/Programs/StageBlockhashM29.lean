/-
  EvmAsm.Codegen.Programs.StageBlockhashM29

  `stage_blockhash_m29` (bead evm-asm-3vc2p.3) — build the M29 recent-blockhash
  table for a contract-recipient runtime execution, from the stateless witness
  headers.

  The runtime BLOCKHASH (0x40) handler (EvmBlockHashHandlers.lean) reads three
  cells: `env+552` = current block number `cur`, `env+560` = loaded hash `count`
  (clamped to 256), and the `evm_block_hashes` table = `count` 32-byte hashes in
  INCREASING block-number order, indexed `block_hashes[count - (cur - target)]`
  for a `BLOCKHASH(target)` with `cur-count <= target < cur`. So the table holds
  the `count` most-recent contiguous ancestors: `block_hashes[i]` = hash of block
  `cur-count+i`.

  The table entries are 32-byte EVM stack words (numeric value, low limb
  first) — NOT the canonical big-endian digest byte order — matching the
  payload-trailer boundary convention (cf. `parse_block_hashes` in
  scripts/pack-bytecode.py, which reverses each hash) and the verified
  `evm_blockhash` spec, which models the table as `List EvmWord`.

  This helper reconstructs that table from `witness.headers` (the SSZ
  `[N×u32 inner offsets][concat header bytes]` section), via
  `blockhash_from_witness_headers` (BlockHashPredicates.lean) which finds the
  header whose RLP NUMBER field equals a target and returns `keccak256(header)`.
  Pass 2 reverses each raw digest in place before publishing it, converting
  canonical digest order into the stack-word order the table contract expects.

  Pure / fully parameterized (no global coupling): the caller supplies the output
  table base + the cur/count out-ptrs. The `.3b` wiring will pass the dispatcher's
  `evm_block_hashes` table and the staging cells the shared callable-dispatcher
  setup loads into `env+552/+560` (which today ZEROES them — see the bead and the
  `contract-dispatcher-zeroes-m28-m29` note). This is the INERT computation core;
  wiring it into `block_verdict` + the shared setup is the sweep-gated follow-up.

  Contiguity: the table indexing assumes the `count` ancestors are contiguous
  ending at `cur-1`, so we count consecutive hits from `age=1` and STOP at the
  first miss — a gap (a missing intermediate ancestor) bounds `count` there, never
  produces a holey table.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockHashPredicates
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_blockhash_m29
    a0 = exec ptr (block NUMBER at +404)
    a1 = witness.headers section ptr
    a2 = witness.headers section length (0 ⇒ count stays 0)
    a3 = output block-hash table base (≥ 256×32 bytes; written block_hashes[i],
         each a 32-byte EVM stack word — numeric, low limb first)
    a4 = u64 out ptr for `cur` (the current block number)
    a5 = u64 out ptr for `count` (number of contiguous recent ancestors found)
    a0 (output) = 0. -/
def stageBlockhashM29_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .LBU .x8 .x10 (404 : BitVec 12),
    .LBU .x6 .x10 (405 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x8 .x8 .x6,
    .LBU .x6 .x10 (406 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x8 .x8 .x6,
    .LBU .x6 .x10 (407 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x8 .x8 .x6,
    .LBU .x6 .x10 (408 : BitVec 12),
    .SLLI .x6 .x6 (32 : BitVec 6),
    .OR .x8 .x8 .x6,
    .LBU .x6 .x10 (409 : BitVec 12),
    .SLLI .x6 .x6 (40 : BitVec 6),
    .OR .x8 .x8 .x6,
    .LBU .x6 .x10 (410 : BitVec 12),
    .SLLI .x6 .x6 (48 : BitVec 6),
    .OR .x8 .x8 .x6,
    .LBU .x6 .x10 (411 : BitVec 12),
    .SLLI .x6 .x6 (56 : BitVec 6),
    .OR .x8 .x8 .x6,
    .SD .x14 .x8 (0 : BitVec 12),
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x22 .x13,
    .MV .x19 .x15,
    .LI .x5 (256 : Word),
    .BGEU .x8 .x5 (8 : BitVec 13),
    .MV .x5 .x8,
    .MV .x20 .x5,
    .LI .x21 (0 : Word),
    .BGEU .x21 .x20 (60 : BitVec 13),
    .ADDI .x5 .x21 (1 : BitVec 12),
    .SUB .x10 .x8 .x5,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.m29_hash_tmp (GuestAddrs.stage_blockhash_m29 + 184)),
    .ADDI .x13 .x13 (laLo GuestAddrs.m29_hash_tmp (GuestAddrs.stage_blockhash_m29 + 184)),
    .AUIPC .x14 (laHi GuestAddrs.m29_off_tmp (GuestAddrs.stage_blockhash_m29 + 192)),
    .ADDI .x14 .x14 (laLo GuestAddrs.m29_off_tmp (GuestAddrs.stage_blockhash_m29 + 192)),
    .AUIPC .x15 (laHi GuestAddrs.m29_len_tmp (GuestAddrs.stage_blockhash_m29 + 200)),
    .ADDI .x15 .x15 (laLo GuestAddrs.m29_len_tmp (GuestAddrs.stage_blockhash_m29 + 200)),
    .JAL .x1 (jalOff GuestAddrs.blockhash_from_witness_headers (GuestAddrs.stage_blockhash_m29 + 208)),
    .BNE .x10 .x0 (12 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-56 : BitVec 21),
    .SD .x19 .x21 (0 : BitVec 12),
    .LI .x20 (1 : Word),
    .BLTU .x21 .x20 (brOff (GuestAddrs.stage_blockhash_m29 + 336) (GuestAddrs.stage_blockhash_m29 + 232)),
    .SUB .x10 .x8 .x20,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .SUB .x5 .x21 .x20,
    .SLLI .x5 .x5 (5 : BitVec 6),
    .ADD .x13 .x22 .x5,
    .MV .x19 .x13,
    .AUIPC .x14 (laHi GuestAddrs.m29_off_tmp (GuestAddrs.stage_blockhash_m29 + 264)),
    .ADDI .x14 .x14 (laLo GuestAddrs.m29_off_tmp (GuestAddrs.stage_blockhash_m29 + 264)),
    .AUIPC .x15 (laHi GuestAddrs.m29_len_tmp (GuestAddrs.stage_blockhash_m29 + 272)),
    .ADDI .x15 .x15 (laLo GuestAddrs.m29_len_tmp (GuestAddrs.stage_blockhash_m29 + 272)),
    .JAL .x1 (jalOff GuestAddrs.blockhash_from_witness_headers (GuestAddrs.stage_blockhash_m29 + 280)),
    .MV .x5 .x19,
    .ADDI .x6 .x19 (31 : BitVec 12),
    .LI .x7 (16 : Word),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .SB .x5 .x29 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-28 : BitVec 13),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.stage_blockhash_m29 + 232) (GuestAddrs.stage_blockhash_m29 + 332)),
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

/-- Reloc side-table for `stageBlockhashM29_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def stageBlockhashM29_relocs : RelocTable :=
  [ (46, .la .x13 "m29_hash_tmp"),
    (48, .la .x14 "m29_off_tmp"),
    (50, .la .x15 "m29_len_tmp"),
    (52, .jal .x1 "blockhash_from_witness_headers"),
    (66, .la .x14 "m29_off_tmp"),
    (68, .la .x15 "m29_len_tmp"),
    (70, .jal .x1 "blockhash_from_witness_headers") ]

def stageBlockhashM29Function : String :=
  "stage_blockhash_m29:\n" ++ emitProgramR stageBlockhashM29_prog stageBlockhashM29_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `stageBlockhashM29_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem stageBlockhashM29Function_eq_prog :
    stageBlockhashM29Function = "stage_blockhash_m29:\n" ++ emitProgramR stageBlockhashM29_prog stageBlockhashM29_relocs := rfl

#guard stageBlockhashM29Function.startsWith "stage_blockhash_m29:\n"
#guard stageBlockhashM29_prog.length = 95
/-- `zisk_stage_blockhash_m29`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : cur (current block number)
      bytes 16..24 : witness.headers section length
      bytes 24..    : witness.headers section (SSZ [N×u32 offsets][headers])
    Output:
      +0  cur
      +8  count
      +16 block_hashes[0] (32B), +48 block_hashes[1], +80 block_hashes[2]. -/
def ziskStageBlockhashM29Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld t0, 8(a6)                # cur\n" ++
  "  la t1, sbm_exec; sd t0, 404(t1)   # synth exec record: NUMBER @ +404\n" ++
  "  mv a0, t1                   # exec ptr\n" ++
  "  addi a1, a6, 24             # headers section ptr\n" ++
  "  ld a2, 16(a6)               # headers section len\n" ++
  "  la a3, sbm_table            # output table\n" ++
  "  la a4, sbm_cur_out; la a5, sbm_count_out\n" ++
  "  jal ra, stage_blockhash_m29\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, sbm_cur_out; ld t2, 0(t1); sd t2, 0(t0)     # OUTPUT+0 = cur\n" ++
  "  la t1, sbm_count_out; ld t2, 0(t1); sd t2, 8(t0)   # OUTPUT+8 = count\n" ++
  -- dump first 3 table entries (96 bytes) to OUTPUT+16.
  "  la t1, sbm_table; mv t3, t0; addi t3, t3, 16; li t4, 96\n" ++
  ".Lsbm_dump:\n" ++
  "  beqz t4, .Lsbm_dump_done\n" ++
  "  ld t5, 0(t1); sd t5, 0(t3); addi t1, t1, 8; addi t3, t3, 8; addi t4, t4, -8; j .Lsbm_dump\n" ++
  ".Lsbm_dump_done:\n" ++
  "  j .Lsbm_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64Function ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  blockhashFromWitnessHeadersFunction ++ "\n" ++
  stageBlockhashM29Function ++ "\n" ++
  ".Lsbm_pdone:"

def ziskStageBlockhashM29DataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "sbm_table:\n  .zero 8192\n" ++          -- 256 × 32-byte block hashes
  "sbm_exec:\n  .zero 512\n" ++            -- synthetic exec record (NUMBER @ +404)
  ".balign 8\n" ++
  "sbm_cur_out:\n  .zero 8\n" ++
  "sbm_count_out:\n  .zero 8\n" ++
  -- stage_blockhash_m29 scratch (the ignored offset/length outs + the pass-1 hash sink).
  "m29_off_tmp:\n  .zero 8\n" ++
  "m29_len_tmp:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "m29_hash_tmp:\n  .zero 32\n" ++
  -- deps for blockhash_from_witness_headers / header_extract_number / keccak.
  ".balign 32\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bhfwh_number_buf:\n  .zero 8\n"


end EvmAsm.Codegen
