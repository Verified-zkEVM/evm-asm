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
def stageBlockhashM29Function : String :=
  "stage_blockhash_m29:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  # #12057 aligned: u64 LE from a0+404 via LBU pack\n  lbu s0, 404(a0)\n  lbu t1, 405(a0); slli t1, t1, 8; or s0, s0, t1\n  lbu t1, 406(a0); slli t1, t1, 16; or s0, s0, t1\n  lbu t1, 407(a0); slli t1, t1, 24; or s0, s0, t1\n  lbu t1, 408(a0); slli t1, t1, 32; or s0, s0, t1\n  lbu t1, 409(a0); slli t1, t1, 40; or s0, s0, t1\n  lbu t1, 410(a0); slli t1, t1, 48; or s0, s0, t1\n  lbu t1, 411(a0); slli t1, t1, 56; or s0, s0, t1\n" ++
  "  sd s0, 0(a4)                # *cur_out = cur\n" ++
  "  mv s1, a1                   # headers ptr\n" ++
  "  mv s2, a2                   # headers len\n" ++
  "  mv s6, a3                   # output table base\n" ++
  "  mv s3, a5                   # count_out ptr (a5 reused as call arg below)\n" ++
  -- window = min(256, cur)
  "  li t0, 256\n" ++
  "  bgeu s0, t0, .Lsbm_wincap\n" ++
  "  mv t0, s0\n" ++
  ".Lsbm_wincap:\n" ++
  "  mv s4, t0                   # s4 = window\n" ++
  "  li s5, 0                    # s5 = count\n" ++
  -- Pass 1: count consecutive hits for age = 1..window (stop at first miss).
  ".Lsbm_count:\n" ++
  "  bgeu s5, s4, .Lsbm_count_done\n" ++
  "  addi t0, s5, 1              # age = count + 1\n" ++
  "  sub a0, s0, t0              # target = cur - age\n" ++
  "  mv a1, s1; mv a2, s2\n" ++
  "  la a3, m29_hash_tmp; la a4, m29_off_tmp; la a5, m29_len_tmp\n" ++
  "  jal ra, blockhash_from_witness_headers\n" ++
  "  bnez a0, .Lsbm_count_done   # first miss -> contiguous stop\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lsbm_count\n" ++
  ".Lsbm_count_done:\n" ++
  "  sd s5, 0(s3)                # *count_out = count\n" ++
  -- Pass 2: for age = 1..count, write block_hashes[count-age] = hash(cur-age).
  -- (All hit, since pass 1 confirmed ages 1..count.) Reuse s4 as the age counter.
  "  li s4, 1\n" ++
  ".Lsbm_fill:\n" ++
  "  bgtu s4, s5, .Lsbm_done     # age > count -> done\n" ++
  "  sub a0, s0, s4              # target = cur - age\n" ++
  "  mv a1, s1; mv a2, s2\n" ++
  "  sub t0, s5, s4             # idx = count - age\n" ++
  "  slli t0, t0, 5             # idx * 32\n" ++
  "  add a3, s6, t0             # a3 = &block_hashes[idx]\n" ++
  "  mv s3, a3                  # keep the slot ptr across the call (s3 dead after count store)\n" ++
  "  la a4, m29_off_tmp; la a5, m29_len_tmp\n" ++
  "  jal ra, blockhash_from_witness_headers\n" ++
  -- The callee returns the raw keccak digest in canonical big-endian byte-string
  -- order; the table contract is the EVM stack-word layout (numeric, low limb
  -- first). Reverse the 32 bytes in place before publishing the entry.
  "  mv t0, s3                  # lo ptr\n" ++
  "  addi t1, s3, 31            # hi ptr\n" ++
  "  li t2, 16                  # pair count\n" ++
  ".Lsbm_rev:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1)\n" ++
  "  sb t4, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, -1\n" ++
  "  addi t2, t2, -1; bnez t2, .Lsbm_rev\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lsbm_fill\n" ++
  ".Lsbm_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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

def ziskStageBlockhashM29ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStageBlockhashM29Prologue
  dataAsm     := ziskStageBlockhashM29DataSection
}

end EvmAsm.Codegen
