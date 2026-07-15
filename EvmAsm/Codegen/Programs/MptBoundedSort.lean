/-
  EvmAsm.Codegen.Programs.MptBoundedSort

  sd13v's first executable component: an in-place MSD radix sort for the
  normalized final state-change descriptors.  It deliberately has no route
  from the verdict yet; the root builder is attached only after its
  committed-final-value proof obligation is closed.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.MptWitnessLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## `mpt_bounded_sort_changes`

The input is an array of 40-byte state-change descriptors (`path` at offset
zero).  All accepted state keys have exactly 64 nibbles.  The routine performs
an in-place MSD partition at each depth and pushes only non-singleton ranges.
The pending stack contains `(start, end, depth, _)` records.  At most 16 ranges
are introduced at a depth, so the 64 * 16 depth/fanout capacity is sufficient;
the routine checks both the change and stack bounds before every write.

ABI: `a0 = descriptors`, `a1 = count`; returns `a0 = 0` on success, `1` on a
malformed nibble or capacity violation. -/
def mptBoundedSortChangesFunction : String :=
  "  .globl mpt_bounded_sort_changes\n" ++
  "mpt_bounded_sort_changes:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  li t0, " ++ toString bsrMaxStateChanges ++ "; bgtu a1, t0, .Lmbs_fail\n" ++
  "  mv s0, a0; mv s1, a1; li s4, 0\n" ++
  ".Lmbs_validate_rec:\n" ++
  "  beq s4, s1, .Lmbs_validated\n" ++
  "  slli t0, s4, 5; slli t1, s4, 3; add t0, t0, t1; add t0, s0, t0; ld t2, 0(t0); li s5, 0\n" ++
  ".Lmbs_validate_nibble:\n" ++
  "  li t0, " ++ toString bsrMptKeyNibbles ++ "; beq s5, t0, .Lmbs_validate_next\n" ++
  "  add t0, t2, s5; lbu t1, 0(t0); li t0, " ++ toString bsrMptRadixFanout ++ "; bgeu t1, t0, .Lmbs_fail\n" ++
  "  addi s5, s5, 1; j .Lmbs_validate_nibble\n" ++
  ".Lmbs_validate_next:\n" ++
  "  addi s4, s4, 1; j .Lmbs_validate_rec\n" ++
  ".Lmbs_validated:\n" ++
  "  la s2, bsr_sort_ranges; li s3, 0\n" ++
  "  beqz s1, .Lmbs_ok\n" ++
  "  sd zero, 0(s2); sd s1, 8(s2); sd zero, 16(s2); sd zero, 24(s2); li s3, 1\n" ++
  ".Lmbs_pop:\n" ++
  "  beqz s3, .Lmbs_ok\n" ++
  "  addi s3, s3, -1; slli t0, s3, 5; add t0, s2, t0\n" ++
  "  ld s4, 0(t0); ld s5, 8(t0); ld s6, 16(t0)\n" ++
  "  addi t1, s4, 1; bgeu t1, s5, .Lmbs_pop\n" ++
  "  li t1, " ++ toString bsrMptKeyNibbles ++ "; bgeu s6, t1, .Lmbs_pop\n" ++
  "  mv s7, s4; li t6, 0\n" ++
  ".Lmbs_digit:\n" ++
  "  li t0, " ++ toString bsrMptRadixFanout ++ "; beq t6, t0, .Lmbs_pop\n" ++
  "  mv t1, s7\n" ++
  ".Lmbs_scan:\n" ++
  "  beq t1, s5, .Lmbs_group\n" ++
  "  slli t0, t1, 5; slli t2, t1, 3; add t0, t0, t2; add t0, s0, t0; ld t2, 0(t0); add t2, t2, s6; lbu t3, 0(t2)\n" ++
  "  li t4, " ++ toString bsrMptRadixFanout ++ "; bgeu t3, t4, .Lmbs_fail\n" ++
  "  bne t3, t6, .Lmbs_scan_next\n" ++
  "  beq t1, s7, .Lmbs_scan_match\n" ++
  "  slli t2, s7, 5; slli t3, s7, 3; add t2, t2, t3; add t2, s0, t2\n" ++
  "  la t3, bsr_builder_frames; li t4, 5\n" ++
  ".Lmbs_swap:\n" ++
  "  ld t5, 0(t0); sd t5, 0(t3); ld t5, 0(t2); sd t5, 0(t0); ld t5, 0(t3); sd t5, 0(t2); addi t0, t0, 8; addi t2, t2, 8; addi t3, t3, 8; addi t4, t4, -1; bnez t4, .Lmbs_swap\n" ++
  ".Lmbs_scan_match:\n" ++
  "  addi s7, s7, 1\n" ++
  ".Lmbs_scan_next:\n" ++
  "  addi t1, t1, 1; j .Lmbs_scan\n" ++
  ".Lmbs_group:\n" ++
  "  addi t0, s4, 1; bgeu t0, s7, .Lmbs_digit_next\n" ++
  "  li t0, " ++ toString bsrMptSortRangeStackCapacity ++ "; bgeu s3, t0, .Lmbs_fail\n" ++
  "  slli t0, s3, 5; add t0, s2, t0; sd s4, 0(t0); sd s7, 8(t0); addi t1, s6, 1; sd t1, 16(t0); sd zero, 24(t0); addi s3, s3, 1\n" ++
  ".Lmbs_digit_next:\n" ++
  "  mv s4, s7; addi t6, t6, 1; j .Lmbs_digit\n" ++
  ".Lmbs_fail:\n" ++
  "  li a0, 1; j .Lmbs_ret\n" ++
  ".Lmbs_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lmbs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 80; ret\n"

/-! ## `mpt_bounded_prepare_changes`

The frontier builder consumes a **normalized final-distinct** change set, not
the raw execution-access staging area.  This front end makes that contract
executable before any builder frame is touched: it sorts, rejects a duplicate
64-nibble key, and admits only the three value-bearing mutation modes used by
the MPT mutators (`set`, `insert`, `delete`).  In particular mode 3 is the
legacy access-only no-op and must never reach the builder.

ABI: `a0 = descriptors`, `a1 = count`; returns `0` on success, `1` for the
sort/capacity failure, `2` for a non-distinct final key, and `3` for a non
value-bearing/unknown mode.  It does not build or route a root yet. -/
def mptBoundedPrepareChangesFunction : String :=
  "  .globl mpt_bounded_prepare_changes\n" ++
  "mpt_bounded_prepare_changes:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; jal ra, mpt_bounded_sort_changes; bnez a0, .Lmbp_sort_fail\n" ++
  "  li s2, 0\n" ++
  ".Lmbp_desc:\n" ++
  "  beq s2, s1, .Lmbp_ok\n" ++
  "  slli t0, s2, 5; slli t1, s2, 3; add t0, t0, t1; add t0, s0, t0; ld t1, 32(t0); li t2, 3; bgeu t1, t2, .Lmbp_bad_mode\n" ++
  "  beqz s2, .Lmbp_next\n" ++
  "  addi t0, s2, -1; slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; add t1, s0, t1; ld t1, 0(t1)\n" ++
  "  slli t2, s2, 5; slli t3, s2, 3; add t2, t2, t3; add t2, s0, t2; ld t2, 0(t2); li s3, 0\n" ++
  ".Lmbp_cmp:\n" ++
  "  li t3, " ++ toString bsrMptKeyNibbles ++ "; beq s3, t3, .Lmbp_dup\n" ++
  "  add t3, t1, s3; lbu t4, 0(t3); add t3, t2, s3; lbu t5, 0(t3); bne t4, t5, .Lmbp_next\n" ++
  "  addi s3, s3, 1; j .Lmbp_cmp\n" ++
  ".Lmbp_next:\n" ++
  "  addi s2, s2, 1; j .Lmbp_desc\n" ++
  ".Lmbp_sort_fail:\n  li a0, 1; j .Lmbp_ret\n" ++
  ".Lmbp_dup:\n  li a0, 2; j .Lmbp_ret\n" ++
  ".Lmbp_bad_mode:\n  li a0, 3; j .Lmbp_ret\n" ++
  ".Lmbp_ok:\n  li a0, 0\n" ++
  ".Lmbp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 48; ret\n"

/-! ## `mpt_bounded_capture_branch_refs`

Capture exactly the canonical pre-state child references of a branch before a
frontier frame rebuilds the changed subset.  The helper reads each RLP field
directly, preserving the reference's true length: empty, inline (<32 bytes),
or a 32-byte hash.  It never consults the mutable NodeDb.  Each output record
is `{ u64 raw_ref_len, raw_ref[32] }` at `frame + 40*i`; the caller uses the
length when it later turns the reference back into an RLP branch slot.

ABI: `a0 = branch RLP`, `a1 = branch length`, `a2 = frame`; returns `0` on a
valid 17-item branch with canonical child references, `1` otherwise. -/
def mptBoundedCaptureBranchRefsFunction : String :=
  "  .globl mpt_bounded_capture_branch_refs\n" ++
  "mpt_bounded_capture_branch_refs:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; addi a2, sp, 40; jal ra, rlp_list_count_items; bnez a0, .Lmbcr_fail\n" ++
  "  ld t0, 40(sp); li t1, 17; bne t0, t1, .Lmbcr_fail; li s3, 0\n" ++
  ".Lmbcr_child:\n" ++
  "  li t0, " ++ toString bsrMptRadixFanout ++ "; beq s3, t0, .Lmbcr_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s3; addi a3, sp, 48; addi a4, sp, 56; jal ra, rlp_list_nth_item; bnez a0, .Lmbcr_fail\n" ++
  "  ld t0, 56(sp); li t1, " ++ toString bsrMptFrameChildRefBytes ++ "; bgtu t0, t1, .Lmbcr_fail\n" ++
  "  slli t1, s3, 5; slli t2, s3, 3; add t1, t1, t2; add t1, s2, t1; sd t0, 0(t1); addi t1, t1, 8\n" ++
  "  ld t2, 48(sp); add t2, s0, t2\n" ++
  ".Lmbcr_copy:\n" ++
  "  beqz t0, .Lmbcr_next; lbu t3, 0(t2); sb t3, 0(t1); addi t2, t2, 1; addi t1, t1, 1; addi t0, t0, -1; j .Lmbcr_copy\n" ++
  ".Lmbcr_next:\n" ++
  "  addi s3, s3, 1; j .Lmbcr_child\n" ++
  ".Lmbcr_fail:\n  li a0, 1; j .Lmbcr_ret\n" ++
  ".Lmbcr_ok:\n  li a0, 0\n" ++
  ".Lmbcr_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 64; ret\n"

/-! ## `mpt_bounded_resolve_witness`

The bounded builder's descent may resolve a 32-byte child hash only against
the immutable pre-state witness.  This intentionally does *not* reuse
`mpt_node_resolve`: that legacy helper probes the append-only NodeDb first,
which is exactly the unbounded state the sd13v route must retire.

ABI mirrors `mpt_node_resolve`: `a0 = witness`, `a1 = witness_len`, `a2 =
hash`, `a3 = out absolute ptr`, `a4 = out len`; returns `0` on found and `1`
on a missing/malformed witness entry. -/
def mptBoundedResolveWitnessFunction : String :=
  "  .globl mpt_bounded_resolve_witness\n" ++
  "mpt_bounded_resolve_witness:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, sp, 48; addi a4, sp, 56; jal ra, witness_lookup_by_hash; bnez a0, .Lmbw_fail\n" ++
  "  ld t0, 48(sp); add t0, s0, t0; sd t0, 0(s3); ld t0, 56(sp); sd t0, 0(s4); li a0, 0; j .Lmbw_ret\n" ++
  ".Lmbw_fail:\n  li a0, 1\n" ++
  ".Lmbw_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); addi sp, sp, 72; ret\n"

/-! ## `mpt_bounded_classify_node`

Classify a node fetched from the immutable witness without involving any
stateful replay helper.  The kind encoding is the frontier dispatch encoding:
`0 = branch`, `1 = extension`, `2 = leaf`.  It validates the 17-item/2-item
shape and the compact-path flag before a frame is populated.

ABI: `a0 = node RLP`, `a1 = node length`, `a2 = u64 kind out`; returns `0`
on success and `1` on malformed/non-MPT input. -/
def mptBoundedClassifyNodeFunction : String :=
  "  .globl mpt_bounded_classify_node\n" ++
  "mpt_bounded_classify_node:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; sd zero, 0(s2); mv a0, s0; mv a1, s1; addi a2, sp, 32; jal ra, rlp_list_count_items; bnez a0, .Lmbcn_fail\n" ++
  "  ld t0, 32(sp); li t1, 17; beq t0, t1, .Lmbcn_branch; li t1, 2; bne t0, t1, .Lmbcn_fail\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; addi a3, sp, 32; addi a4, sp, 40; jal ra, rlp_list_nth_item; bnez a0, .Lmbcn_fail\n" ++
  "  ld t0, 40(sp); beqz t0, .Lmbcn_fail; ld t0, 32(sp); add t0, s0, t0; lbu t0, 0(t0); srli t0, t0, 5; andi t0, t0, 1; addi t0, t0, 1; sd t0, 0(s2); li a0, 0; j .Lmbcn_ret\n" ++
  ".Lmbcn_branch:\n  sd zero, 0(s2); li a0, 0; j .Lmbcn_ret\n" ++
  ".Lmbcn_fail:\n  li a0, 1\n" ++
  ".Lmbcn_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 48; ret\n"

/-! ## `mpt_bounded_open_root_frame`

Open the pre-state root into depth-zero of the bounded frontier: resolve it
from the witness only, classify its MPT shape, and retain every branch child
reference before any changed range is rebuilt.  Extension and leaf frames
record their resolved node/kind and are expanded by the next frontier slice.

ABI: `a0 = root hash`, `a1 = witness`, `a2 = witness length`, `a3 = frame`;
returns `0` on success and `1` on any witness/node-shape failure. -/
def mptBoundedOpenRootFrameFunction : String :=
  "  .globl mpt_bounded_open_root_frame\n" ++
  "mpt_bounded_open_root_frame:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s0; addi a3, sp, 40; addi a4, sp, 48; jal ra, mpt_bounded_resolve_witness; bnez a0, .Lmbor_fail\n" ++
  "  ld t0, 40(sp); sd t0, " ++ toString bsrMptFrameNodePtrOffset ++ "(s3); ld t0, 48(sp); sd t0, " ++ toString bsrMptFrameNodeLenOffset ++ "(s3)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); addi a2, sp, 56; jal ra, mpt_bounded_classify_node; bnez a0, .Lmbor_fail\n" ++
  "  ld t0, 56(sp); sd t0, " ++ toString bsrMptFrameNodeKindOffset ++ "(s3); bnez t0, .Lmbor_ok\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); mv a2, s3; jal ra, mpt_bounded_capture_branch_refs; bnez a0, .Lmbor_fail\n" ++
  ".Lmbor_ok:\n  li a0, 0; j .Lmbor_ret\n" ++
  ".Lmbor_fail:\n  li a0, 1\n" ++
  ".Lmbor_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 72; ret\n"

/-! ## `mpt_bounded_partition_frame`

Given a sorted, final-distinct descriptor interval, materialize the sixteen
contiguous child intervals for one Patricia depth directly in a frame.  No
bucket array is indexed by an attacker-controlled count: this is exactly 16
`{start,end}` pairs inside the already depth-bounded frame.

ABI: `a0 = descriptors`, `a1 = start`, `a2 = end`, `a3 = depth`, `a4 = frame`;
returns `0` on success and `1` for invalid bounds/digits. -/
def mptBoundedPartitionFrameFunction : String :=
  "  .globl mpt_bounded_partition_frame\n" ++
  "mpt_bounded_partition_frame:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; li t0, " ++ toString bsrMaxStateChanges ++ "; bgtu s2, t0, .Lmbpf_fail; bltu s2, s1, .Lmbpf_fail; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgeu s3, t0, .Lmbpf_fail\n" ++
  "  mv s5, s1; li t6, 0\n" ++
  ".Lmbpf_digit:\n" ++
  "  li t0, " ++ toString bsrMptRadixFanout ++ "; beq t6, t0, .Lmbpf_ok\n" ++
  "  slli t0, t6, 4; addi t1, s4, " ++ toString bsrMptFrameRangeTableOffset ++ "; add t1, t1, t0; sd s5, 0(t1)\n" ++
  ".Lmbpf_scan:\n" ++
  "  beq s5, s2, .Lmbpf_store; slli t0, s5, 5; slli t1, s5, 3; add t0, t0, t1; add t0, s0, t0; ld t0, 0(t0); add t0, t0, s3; lbu t1, 0(t0); li t0, " ++ toString bsrMptRadixFanout ++ "; bgeu t1, t0, .Lmbpf_fail; bltu t1, t6, .Lmbpf_fail; bne t1, t6, .Lmbpf_store; addi s5, s5, 1; j .Lmbpf_scan\n" ++
  ".Lmbpf_store:\n" ++
  "  slli t0, t6, 4; addi t1, s4, " ++ toString bsrMptFrameRangeTableOffset ++ "; add t1, t1, t0; sd s5, 8(t1); addi t6, t6, 1; j .Lmbpf_digit\n" ++
  ".Lmbpf_fail:\n  li a0, 1; j .Lmbpf_ret\n" ++
  ".Lmbpf_ok:\n  li a0, 0\n" ++
  ".Lmbpf_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp); addi sp, sp, 48; ret\n"

/-- The linked sd13v front end.  Keeping this aggregation explicit prevents a
    future caller from accidentally using the sorter without the final-distinct
    boundary. -/
def mptBoundedBuilderFrontEndFunction : String :=
  mptBoundedSortChangesFunction ++ "\n" ++ mptBoundedPrepareChangesFunction ++ "\n" ++
    mptBoundedCaptureBranchRefsFunction ++ "\n" ++ mptBoundedResolveWitnessFunction ++ "\n" ++
    mptBoundedClassifyNodeFunction ++ "\n" ++ mptBoundedOpenRootFrameFunction
    ++ "\n" ++ mptBoundedPartitionFrameFunction

/-- Probe input: `u64 count` at INPUT+8 followed by `count` 64-byte nibble
    paths at INPUT+16. The probe deliberately limits itself to 16 records; it
    exercises the production sorter without allocating an attacker-sized test
    arena. Output is `status:u64`, `count:u64`, then the sorted paths. -/
def ziskMptBoundedSortPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld s0, 8(t0); li t1, 17; bgeu s0, t1, .Lmbsp_fail\n" ++
  "  addi s1, t0, 16; la s2, mbs_changes; li s3, 0\n" ++
  ".Lmbsp_desc:\n" ++
  "  beq s3, s0, .Lmbsp_sort\n" ++
  "  slli t0, s3, 5; slli t1, s3, 3; add t0, t0, t1; add t0, s2, t0\n" ++
  "  sd s1, 0(t0); li t1, 64; sd t1, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++
  "  addi s1, s1, 64; addi s3, s3, 1; j .Lmbsp_desc\n" ++
  ".Lmbsp_sort:\n" ++
  "  mv a0, s2; mv a1, s0; jal ra, mpt_bounded_prepare_changes; mv s4, a0; j .Lmbsp_out\n" ++
  ".Lmbsp_fail:\n" ++
  "  li s4, 1\n" ++
  ".Lmbsp_out:\n" ++
  "  li t0, 0xa0010000; sd s4, 0(t0); sd s0, 8(t0); bnez s4, .Lmbsp_done\n" ++
  "  addi s5, t0, 16; li s3, 0\n" ++
  ".Lmbsp_copy_desc:\n" ++
  "  beq s3, s0, .Lmbsp_done\n" ++
  "  slli t0, s3, 5; slli t1, s3, 3; add t0, t0, t1; add t0, s2, t0; ld s6, 0(t0); li s7, 64\n" ++
  ".Lmbsp_copy_path:\n" ++
  "  beqz s7, .Lmbsp_copy_next; lbu t1, 0(s6); sb t1, 0(s5); addi s6, s6, 1; addi s5, s5, 1; addi s7, s7, -1; j .Lmbsp_copy_path\n" ++
  ".Lmbsp_copy_next:\n" ++
  "  addi s3, s3, 1; j .Lmbsp_copy_desc"

def ziskMptBoundedSortDataSection : String :=
  ".section .bss\n" ++
  ".balign 8\n" ++
  "mbs_changes:\n  .zero 640\n" ++
  "bsr_sort_ranges:\n  .zero " ++ toString (bsrMptSortRangeStackCapacity * bsrMptSortRangeFrameBytes) ++ "\n" ++
  "bsr_builder_frames:\n  .zero " ++ toString (bsrMptBuilderFrameCapacity * bsrMptBuilderFrameBytes) ++ "\n" ++
  ziskWitnessLookupByHashDataSection

def ziskMptBoundedSortProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedSortPrologue ++ "\n" ++
    zkvmKeccak256Function ++ "\n" ++ witnessLookupByHashFunction ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++ rlpListCountItemsFunction ++ "\n" ++
    mptBoundedBuilderFrontEndFunction ++ "\n.Lmbsp_done:"
  dataAsm := ziskMptBoundedSortDataSection
}

/-- Probe for the frontier frame's canonical branch-reference capture.  It
    reports the first three `{length, raw[32]}` records; that covers an empty,
    an inline, and a hashed reference in one compact regression vector. -/
def ziskMptBoundedCaptureBranchRefsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld a1, 8(t0); addi a0, t0, 16; la a2, mbc_probe_frame; jal ra, mpt_bounded_capture_branch_refs; mv s0, a0\n" ++
  "  li t0, 0xa0010000; sd s0, 0(t0); bnez s0, .Lmbcp_done; la t1, mbc_probe_frame; addi t0, t0, 8; li t2, 3\n" ++
  ".Lmbcp_slot:\n" ++
  "  beqz t2, .Lmbcp_done; ld t3, 0(t1); sd t3, 0(t0); addi t0, t0, 8; addi t1, t1, 8; li t4, 32\n" ++
  ".Lmbcp_copy:\n" ++
  "  beqz t4, .Lmbcp_next; lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lmbcp_copy\n" ++
  ".Lmbcp_next:\n" ++
  "  addi t1, t1, " ++ toString (bsrMptFrameChildRefStride - (8 + bsrMptFrameChildRefBytes)) ++ "; addi t2, t2, -1; j .Lmbcp_slot\n" ++
  ""

def ziskMptBoundedCaptureBranchRefsDataSection : String :=
  ".section .bss\n" ++
  ".balign 8\n" ++
  "mbc_probe_frame:\n  .zero " ++ toString bsrMptBuilderFrameBytes

def ziskMptBoundedCaptureBranchRefsProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedCaptureBranchRefsPrologue ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++ rlpListCountItemsFunction ++ "\n" ++
    mptBoundedCaptureBranchRefsFunction ++ "\n.Lmbcp_done:"
  dataAsm := ziskMptBoundedCaptureBranchRefsDataSection
}

/-- Probe the witness-only resolver with the same compact SSZ-list input shape
    as `zisk_witness_lookup_by_hash`; the output pointer is converted back to
    a section-relative offset for a stable regression oracle. -/
def ziskMptBoundedResolveWitnessPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000; ld s1, 8(s0); addi s2, s0, 16; addi s3, s0, 48\n" ++
  "  mv a0, s3; mv a1, s1; mv a2, s2; li a3, 0xa0010008; li a4, 0xa0010010; jal ra, mpt_bounded_resolve_witness; mv s4, a0\n" ++
  "  li t0, 0xa0010000; sd s4, 0(t0); bnez s4, .Lmbwr_done; li t0, 0xa0010008; ld t1, 0(t0); sub t1, t1, s3; sd t1, 0(t0)\n" ++
  ""

def ziskMptBoundedResolveWitnessProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedResolveWitnessPrologue ++ "\n" ++
    zkvmKeccak256Function ++ "\n" ++ witnessLookupByHashFunction ++ "\n" ++
    mptBoundedResolveWitnessFunction ++ "\n.Lmbwr_done:"
  dataAsm := ziskWitnessLookupByHashDataSection
}

def ziskMptBoundedClassifyNodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld a1, 8(t0); addi a0, t0, 16; li a2, 0xa0010008; jal ra, mpt_bounded_classify_node\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0); j .Lmbcnp_done"

def ziskMptBoundedClassifyNodeProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedClassifyNodePrologue ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++ rlpListCountItemsFunction ++ "\n" ++
    mptBoundedClassifyNodeFunction ++ "\n.Lmbcnp_done:"
  dataAsm := ""
}

def ziskMptBoundedOpenRootFramePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000; ld s1, 8(s0); addi a0, s0, 16; addi a1, s0, 48; mv a2, s1; la a3, mbor_probe_frame; jal ra, mpt_bounded_open_root_frame; mv s2, a0\n" ++
  "  li t0, 0xa0010000; sd s2, 0(t0); bnez s2, .Lmborp_done; la t1, mbor_probe_frame; ld t2, " ++ toString bsrMptFrameNodePtrOffset ++ "(t1); addi t3, s0, 48; sub t2, t2, t3; sd t2, 8(t0); ld t2, " ++ toString bsrMptFrameNodeLenOffset ++ "(t1); sd t2, 16(t0); ld t2, " ++ toString bsrMptFrameNodeKindOffset ++ "(t1); sd t2, 24(t0); addi t0, t0, 32; li t2, 3\n" ++
  ".Lmborp_slot:\n" ++
  "  beqz t2, .Lmborp_done; ld t3, 0(t1); sd t3, 0(t0); addi t0, t0, 8; addi t1, t1, 8; li t4, 32\n" ++
  ".Lmborp_copy:\n" ++
  "  beqz t4, .Lmborp_next; lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lmborp_copy\n" ++
  ".Lmborp_next:\n" ++
  "  addi t2, t2, -1; j .Lmborp_slot\n" ++
  ""

def ziskMptBoundedOpenRootFrameDataSection : String :=
  ".section .bss\n.balign 8\nmbor_probe_frame:\n  .zero " ++ toString bsrMptBuilderFrameBytes ++ "\n" ++
    ziskWitnessLookupByHashDataSection

def ziskMptBoundedOpenRootFrameProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedOpenRootFramePrologue ++ "\n" ++
    zkvmKeccak256Function ++ "\n" ++ witnessLookupByHashFunction ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++ rlpListCountItemsFunction ++ "\n" ++
    mptBoundedCaptureBranchRefsFunction ++ "\n" ++ mptBoundedResolveWitnessFunction ++ "\n" ++
    mptBoundedClassifyNodeFunction ++ "\n" ++ mptBoundedOpenRootFrameFunction ++ "\n.Lmborp_done:"
  dataAsm := ziskMptBoundedOpenRootFrameDataSection
}

def ziskMptBoundedPartitionFramePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld s0, 8(t0); li t1, 17; bgeu s0, t1, .Lmbpp_fail; addi s1, t0, 16; la s2, mbp_changes; li s3, 0\n" ++
  ".Lmbpp_desc:\n" ++
  "  beq s3, s0, .Lmbpp_prepare; slli t0, s3, 5; slli t1, s3, 3; add t0, t0, t1; add t0, s2, t0; sd s1, 0(t0); li t1, 64; sd t1, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0); addi s1, s1, 64; addi s3, s3, 1; j .Lmbpp_desc\n" ++
  ".Lmbpp_prepare:\n" ++
  "  mv a0, s2; mv a1, s0; jal ra, mpt_bounded_prepare_changes; bnez a0, .Lmbpp_fail; mv a0, s2; li a1, 0; mv a2, s0; li a3, 0; la a4, mbp_frame; jal ra, mpt_bounded_partition_frame; mv s4, a0; j .Lmbpp_out\n" ++
  ".Lmbpp_fail:\n  li s4, 1\n" ++
  ".Lmbpp_out:\n" ++
  "  li t0, 0xa0010000; sd s4, 0(t0); bnez s4, .Lmbpp_done; la t1, mbp_frame; addi t1, t1, " ++ toString bsrMptFrameRangeTableOffset ++ "; addi t0, t0, 8; li t2, 10\n" ++
  ".Lmbpp_copy:\n" ++
  "  beqz t2, .Lmbpp_done; ld t3, 0(t1); sd t3, 0(t0); ld t3, 8(t1); sd t3, 8(t0); addi t1, t1, 16; addi t0, t0, 16; addi t2, t2, -1; j .Lmbpp_copy\n" ++
  ""

def ziskMptBoundedPartitionFrameDataSection : String :=
  ".section .bss\n.balign 8\nmbp_changes:\n  .zero 640\n" ++
  "bsr_sort_ranges:\n  .zero " ++ toString (bsrMptSortRangeStackCapacity * bsrMptSortRangeFrameBytes) ++ "\n" ++
  "bsr_builder_frames:\n  .zero " ++ toString (bsrMptBuilderFrameCapacity * bsrMptBuilderFrameBytes) ++ "\n" ++
  "mbp_frame:\n  .zero " ++ toString bsrMptBuilderFrameBytes

def ziskMptBoundedPartitionFrameProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedPartitionFramePrologue ++ "\n" ++
    mptBoundedSortChangesFunction ++ "\n" ++ mptBoundedPrepareChangesFunction ++ "\n" ++
    mptBoundedPartitionFrameFunction ++ "\n.Lmbpp_done:"
  dataAsm := ziskMptBoundedPartitionFrameDataSection
}

end EvmAsm.Codegen
