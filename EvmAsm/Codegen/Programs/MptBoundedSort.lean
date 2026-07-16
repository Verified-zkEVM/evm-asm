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
import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

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
  "  addi sp, sp, -96\n" ++
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
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 96; ret\n"

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

/-! ## `mpt_bounded_node_ref`

Turn one freshly encoded node into the canonical *raw* child reference used
inside a bounded frame.  This deliberately does not append the node anywhere:
the parent only needs inline RLP for nodes shorter than 32 bytes, or their
32-byte Keccak hash otherwise.  The caller retains the encoded bytes in its
depth-bounded frame until its parent has consumed this reference.

ABI: `a0 = node RLP`, `a1 = node length`, `a2 = raw-ref out[32]`, `a3 = u64
raw-ref-length out`; returns `0` or `1` when the node exceeds the SSZ/frame
node bound. -/
def mptBoundedNodeRefFunction : String :=
  "  .globl mpt_bounded_node_ref\n" ++
  "mpt_bounded_node_ref:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; sd zero, 0(s3); li t0, " ++ toString bsrMptNodeMaxBytes ++ "; bgtu s1, t0, .Lmbnr_fail; li t0, 32; bgeu s1, t0, .Lmbnr_hash\n" ++
  "  mv t0, s0; mv t1, s2; mv t2, s1\n" ++
  ".Lmbnr_copy:\n" ++
  "  beqz t2, .Lmbnr_inline_ok; lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lmbnr_copy\n" ++
  ".Lmbnr_inline_ok:\n  sd s1, 0(s3); li a0, 0; j .Lmbnr_ret\n" ++
  ".Lmbnr_hash:\n  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, zkvm_keccak256; li t0, 32; sd t0, 0(s3); li a0, 0; j .Lmbnr_ret\n" ++
  ".Lmbnr_fail:\n  li a0, 1\n" ++
  ".Lmbnr_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 48; ret\n"

/-! ## `mpt_bounded_encode_branch`

Re-encode a branch from the sixteen canonical raw references retained in one
fixed frame.  State-trie keys are all 64 nibbles, so a state-trie branch never
has a value at its own prefix; its seventeenth slot is therefore canonically
empty.  This is a deliberate state-root-only primitive, not a general MPT
branch encoder.  It uses no mutable node database and writes at most the
structural maximum `16 * 33 + 1 + 3 < 1024` bytes.

ABI: `a0 = frame`, `a1 = output[1024]`, `a2 = u64 output length`; returns 0
on success and 1 for malformed retained references. -/
def mptBoundedEncodeBranchFunction : String :=
  "  .globl mpt_bounded_encode_branch\n" ++
  "mpt_bounded_encode_branch:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; sd zero, 0(s2); li s3, 0; li s4, 1\n" ++
  ".Lmbeb_measure:\n" ++
  "  li t0, 16; beq s3, t0, .Lmbeb_prefix; slli t0, s3, 5; slli t1, s3, 3; add t0, t0, t1; add t0, s0, t0; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lmbeb_fail; beqz t0, .Lmbeb_empty_measure; beq t0, t1, .Lmbeb_hash_measure; add t1, s4, t0; bltu t1, s4, .Lmbeb_fail; mv s4, t1; j .Lmbeb_measure_next\n" ++
  ".Lmbeb_empty_measure:\n  addi s4, s4, 1; j .Lmbeb_measure_next\n" ++
  ".Lmbeb_hash_measure:\n  addi s4, s4, 33\n" ++
  ".Lmbeb_measure_next:\n  addi s3, s3, 1; j .Lmbeb_measure\n" ++
  ".Lmbeb_prefix:\n  mv a0, s4; mv a1, s1; addi a2, sp, 64; jal ra, rlp_encode_list_prefix; bnez a0, .Lmbeb_fail; ld t0, 64(sp); add t1, s4, t0; li t2, " ++ toString bsrMptNodeMaxBytes ++ "; bgtu t1, t2, .Lmbeb_fail; add s5, s1, t0; li s3, 0\n" ++
  ".Lmbeb_slot:\n" ++
  "  li t0, 16; beq s3, t0, .Lmbeb_value; slli t0, s3, 5; slli t1, s3, 3; add t0, t0, t1; add t0, s0, t0; ld t1, 0(t0); addi t0, t0, 8; beqz t1, .Lmbeb_empty; li t2, 32; beq t1, t2, .Lmbeb_hash; mv t3, t0\n" ++
  ".Lmbeb_inline_copy:\n  beqz t1, .Lmbeb_slot_next; lbu t4, 0(t3); sb t4, 0(s5); addi t3, t3, 1; addi s5, s5, 1; addi t1, t1, -1; j .Lmbeb_inline_copy\n" ++
  ".Lmbeb_empty:\n  li t0, 128; sb t0, 0(s5); addi s5, s5, 1; j .Lmbeb_slot_next\n" ++
  ".Lmbeb_hash:\n  li t2, 160; sb t2, 0(s5); addi s5, s5, 1; li t1, 32; mv t3, t0; j .Lmbeb_inline_copy\n" ++
  ".Lmbeb_slot_next:\n  addi s3, s3, 1; j .Lmbeb_slot\n" ++
  ".Lmbeb_value:\n  li t0, 128; sb t0, 0(s5); addi s5, s5, 1; sub t0, s5, s1; sd t0, 0(s2); li a0, 0; j .Lmbeb_ret\n" ++
  ".Lmbeb_fail:\n  li a0, 1\n" ++
  ".Lmbeb_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 80; ret\n"

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

/-- Open one non-empty raw child reference into a descendant frontier frame.
    Inline children are already RLP items in the parent frame and hashes are
    resolved only in the immutable witness. This is intentionally separate
    from the root opener: a zero-length reference denotes a missing child and
    must be handled by the insertion case rather than accidentally treated as
    an RLP node.

    ABI: `a0 = raw child bytes`; `a1 = raw child length`; `a2 = witness`;
    `a3 = witness length`; `a4 = frame`; returns 0/1. -/
def mptBoundedOpenChildFrameFunction : String :=
  "  .globl mpt_bounded_open_child_frame\n" ++
  "mpt_bounded_open_child_frame:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; sd zero, " ++ toString bsrMptFrameNodePtrOffset ++ "(s4); sd zero, " ++ toString bsrMptFrameNodeLenOffset ++ "(s4); sd zero, " ++ toString bsrMptFrameNodeKindOffset ++ "(s4); beqz s1, .Lmboc_fail; li t0, 32; bgtu s1, t0, .Lmboc_fail; bne s1, t0, .Lmboc_inline\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s0; addi a3, sp, 48; addi a4, sp, 56; jal ra, mpt_bounded_resolve_witness; bnez a0, .Lmboc_fail; ld t0, 48(sp); sd t0, " ++ toString bsrMptFrameNodePtrOffset ++ "(s4); ld t0, 56(sp); sd t0, " ++ toString bsrMptFrameNodeLenOffset ++ "(s4); j .Lmboc_classify\n" ++
  ".Lmboc_inline:\n" ++
  "  sd s0, " ++ toString bsrMptFrameNodePtrOffset ++ "(s4); sd s1, " ++ toString bsrMptFrameNodeLenOffset ++ "(s4)\n" ++
  ".Lmboc_classify:\n" ++
  "  ld a0, " ++ toString bsrMptFrameNodePtrOffset ++ "(s4); ld a1, " ++ toString bsrMptFrameNodeLenOffset ++ "(s4); addi a2, sp, 64; jal ra, mpt_bounded_classify_node; bnez a0, .Lmboc_fail; ld t0, 64(sp); sd t0, " ++ toString bsrMptFrameNodeKindOffset ++ "(s4); bnez t0, .Lmboc_ok; ld a0, " ++ toString bsrMptFrameNodePtrOffset ++ "(s4); ld a1, " ++ toString bsrMptFrameNodeLenOffset ++ "(s4); mv a2, s4; jal ra, mpt_bounded_capture_branch_refs; bnez a0, .Lmboc_fail\n" ++
  ".Lmboc_ok:\n  li a0, 0; j .Lmboc_ret\n" ++
  ".Lmboc_fail:\n  li a0, 1\n" ++
  ".Lmboc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); addi sp, sp, 72; ret\n"

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

/-- Build one final bounded-trie leaf from the current remaining state-key
    suffix into a caller-owned 1KiB node buffer, then derive its raw parent
    reference without appending to NodeDb. A descendant leaf must encode only
    the suffix below its ancestor branch/extension, never the original
    64-nibble key. The selected root wrapper supplies the leaf-value bound. -/
def mptBoundedEncodeLeafRefFunction : String :=
  "  .globl mpt_bounded_encode_leaf_ref\n" ++
  "mpt_bounded_encode_leaf_ref:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6; mv s7, a7; sd zero, 0(s5); sd zero, 0(s7); li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu s1, t0, .Lmbelr_fail; la t0, bsr_builder_value_max; ld t0, 0(t0); bgtu s3, t0, .Lmbelr_fail\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4; mv a5, s5; jal ra, mpt_leaf_node_encode_from_nibbles; bnez a0, .Lmbelr_fail\n" ++
  "  mv a0, s4; ld a1, 0(s5); mv a2, s6; mv a3, s7; jal ra, mpt_bounded_node_ref; bnez a0, .Lmbelr_fail; li a0, 0; j .Lmbelr_ret\n" ++
  ".Lmbelr_fail:\n  li a0, 1\n" ++
  ".Lmbelr_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 80; ret\n"

/-- Decode an extension compact path only after proving it fits the caller's
    remaining state-key depth.  Unlike `mpt_extension_extract`, this routine
    cannot write an attacker-derived number of nibbles to a fixed frame.
    ABI: `a0,a1=node`; `a2=remaining`; `a3,a4=path_out,path_len_out`;
    `a5,a6=child_ptr_out,child_len_out`. -/
def mptBoundedDecodeExtensionFunction : String :=
  "  .globl mpt_bounded_decode_extension\n" ++
  "mpt_bounded_decode_extension:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6; sd zero, 0(s4); sd zero, 0(s5); sd zero, 0(s6); mv a0, s0; mv a1, s1; addi a2, sp, 72; jal ra, rlp_list_count_items; bnez a0, .Lmbde_fail; ld t0, 72(sp); li t1, 2; bne t0, t1, .Lmbde_fail\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; addi a3, sp, 56; addi a4, sp, 64; jal ra, rlp_list_nth_item; bnez a0, .Lmbde_fail; ld t0, 64(sp); beqz t0, .Lmbde_fail; ld t1, 56(sp); add t1, s0, t1; lbu t2, 0(t1); srli t3, t2, 4; li t4, 2; bgeu t3, t4, .Lmbde_fail; andi t4, t3, 1; addi t0, t0, -1; slli t0, t0, 1; beqz t4, .Lmbde_even; addi t0, t0, 1; j .Lmbde_len\n" ++
  ".Lmbde_even:\n  andi t5, t2, 15; bnez t5, .Lmbde_fail\n" ++
  ".Lmbde_len:\n  beqz t0, .Lmbde_fail; bgtu t0, s2, .Lmbde_fail; sd t0, 0(s4); addi t1, t1, 1; mv t5, s3; beqz t4, .Lmbde_pairs; andi t2, t2, 15; sb t2, 0(t5); addi t5, t5, 1\n" ++
  ".Lmbde_pairs:\n  ld t2, 64(sp); addi t2, t2, -1\n" ++
  ".Lmbde_pair_loop:\n  beqz t2, .Lmbde_child; lbu t3, 0(t1); srli t4, t3, 4; andi t3, t3, 15; sb t4, 0(t5); sb t3, 1(t5); addi t1, t1, 1; addi t5, t5, 2; addi t2, t2, -1; j .Lmbde_pair_loop\n" ++
  ".Lmbde_child:\n  mv a0, s0; mv a1, s1; li a2, 1; addi a3, sp, 56; addi a4, sp, 64; jal ra, rlp_list_nth_item; bnez a0, .Lmbde_fail; ld t0, 64(sp); li t1, 32; bgtu t0, t1, .Lmbde_fail; ld t1, 56(sp); add t1, s0, t1; sd t1, 0(s5); sd t0, 0(s6); li a0, 0; j .Lmbde_ret\n" ++
  ".Lmbde_fail:\n  li a0, 1\n" ++
  ".Lmbde_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 80; ret\n"

/-- Decode a bounded-trie leaf without using the legacy unbounded compact-path
    extractor. The leaf path is first proved to fit the remaining key depth;
    only then are nibbles written to the caller frame. Its value is returned
    as an in-node slice and bounded by the root wrapper's witness-leaf limit.
    That is deliberately independent of the constructed-value bound: storage
    writes are uint256, whereas an unchanged hash-authenticated witness leaf
    is retained verbatim.

    ABI: `a0,a1=node`; `a2=remaining`; `a3,a4=path_out,path_len_out`;
    `a5,a6=value_ptr_out,value_len_out`. Returns 0/1. -/
def mptBoundedDecodeLeafFunction : String :=
  "  .globl mpt_bounded_decode_leaf\n" ++
  "mpt_bounded_decode_leaf:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6; sd zero, 0(s4); sd zero, 0(s5); sd zero, 0(s6); mv a0, s0; mv a1, s1; addi a2, sp, 72; jal ra, rlp_list_count_items; bnez a0, .Lmbdl_fail; ld t0, 72(sp); li t1, 2; bne t0, t1, .Lmbdl_fail\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; addi a3, sp, 56; addi a4, sp, 64; jal ra, rlp_list_nth_item; bnez a0, .Lmbdl_fail; ld t0, 64(sp); beqz t0, .Lmbdl_fail; ld t1, 56(sp); add t1, s0, t1; lbu t2, 0(t1); srli t3, t2, 4; li t4, 2; bltu t3, t4, .Lmbdl_fail; li t4, 4; bgeu t3, t4, .Lmbdl_fail; andi t4, t3, 1; addi t0, t0, -1; slli t0, t0, 1; beqz t4, .Lmbdl_even; addi t0, t0, 1; j .Lmbdl_len\n" ++
  ".Lmbdl_even:\n  andi t5, t2, 15; bnez t5, .Lmbdl_fail\n" ++
  ".Lmbdl_len:\n  bgtu t0, s2, .Lmbdl_fail; sd t0, 0(s4); addi t1, t1, 1; mv t5, s3; beqz t4, .Lmbdl_pairs; andi t2, t2, 15; sb t2, 0(t5); addi t5, t5, 1\n" ++
  ".Lmbdl_pairs:\n  ld t2, 64(sp); addi t2, t2, -1\n" ++
  ".Lmbdl_pair_loop:\n  beqz t2, .Lmbdl_value; lbu t3, 0(t1); srli t4, t3, 4; andi t3, t3, 15; sb t4, 0(t5); sb t3, 1(t5); addi t1, t1, 1; addi t5, t5, 2; addi t2, t2, -1; j .Lmbdl_pair_loop\n" ++
  ".Lmbdl_value:\n  mv a0, s0; mv a1, s1; li a2, 1; addi a3, sp, 56; addi a4, sp, 64; jal ra, rlp_list_nth_item; bnez a0, .Lmbdl_fail; ld t0, 64(sp); la t1, bsr_builder_witness_value_max; ld t1, 0(t1); bgtu t0, t1, .Lmbdl_fail; ld t1, 56(sp); add t1, s0, t1; sd t1, 0(s5); sd t0, 0(s6); li a0, 0; j .Lmbdl_ret\n" ++
  ".Lmbdl_fail:\n  li a0, 1\n" ++
  ".Lmbdl_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 80; ret\n"

/-- Populate a non-branch frontier frame's bounded compact-path payload.
    Extensions use the payload's second item as a raw child reference; leaves
    use it as the account value slice. Both forms fit the shared tail layout,
    and the caller dispatches on the retained node kind before interpreting
    those two words. -/
def mptBoundedDecodeFramePayloadFunction : String :=
  "  .globl mpt_bounded_decode_frame_payload\n" ++
  "mpt_bounded_decode_frame_payload:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; ld s2, " ++ toString bsrMptFrameNodeKindOffset ++ "(s0); li t0, 1; beq s2, t0, .Lmbdfp_extension; li t0, 2; beq s2, t0, .Lmbdfp_leaf; j .Lmbdfp_fail\n" ++
  ".Lmbdfp_extension:\n" ++
  "  ld a0, " ++ toString bsrMptFrameNodePtrOffset ++ "(s0); ld a1, " ++ toString bsrMptFrameNodeLenOffset ++ "(s0); mv a2, s1; addi a3, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; addi a4, s0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "; addi a5, s0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "; addi a6, s0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "; jal ra, mpt_bounded_decode_extension; bnez a0, .Lmbdfp_fail; li a0, 0; j .Lmbdfp_ret\n" ++
  ".Lmbdfp_leaf:\n" ++
  "  ld a0, " ++ toString bsrMptFrameNodePtrOffset ++ "(s0); ld a1, " ++ toString bsrMptFrameNodeLenOffset ++ "(s0); mv a2, s1; addi a3, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; addi a4, s0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "; addi a5, s0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "; addi a6, s0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "; jal ra, mpt_bounded_decode_leaf; bnez a0, .Lmbdfp_fail; li a0, 0; j .Lmbdfp_ret\n" ++
  ".Lmbdfp_fail:\n  li a0, 1\n" ++
  ".Lmbdfp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 48; ret\n"

/-- Compare one final descriptor key with a decoded compact-path frame at a
    specific state-key depth. `0` means the entire frame path matches, `1`
    means a legitimate divergence (the caller must split rather than reject),
    and `2` means malformed descriptor/frame bounds. -/
def mptBoundedFramePathMatchFunction : String :=
  "  .globl mpt_bounded_frame_path_match\n" ++
  "mpt_bounded_frame_path_match:\n" ++
  "  ld t0, 8(a0); li t1, " ++ toString bsrMptKeyNibbles ++ "; bne t0, t1, .Lmbfpm_bad; ld t0, 0(a0); ld t1, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(a2); li t2, " ++ toString bsrMptKeyNibbles ++ "; bgtu t1, t2, .Lmbfpm_bad; add t2, a1, t1; li t3, " ++ toString bsrMptKeyNibbles ++ "; bgtu t2, t3, .Lmbfpm_bad; add t0, t0, a1; addi t2, a2, " ++ toString bsrMptFrameExtensionPathOffset ++ "\n" ++
  ".Lmbfpm_loop:\n" ++
  "  beqz t1, .Lmbfpm_match; lbu t3, 0(t0); lbu t4, 0(t2); bne t3, t4, .Lmbfpm_mismatch; addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lmbfpm_loop\n" ++
  ".Lmbfpm_match:\n  li a0, 0; ret\n" ++
  ".Lmbfpm_mismatch:\n  li a0, 1; ret\n" ++
  ".Lmbfpm_bad:\n  li a0, 2; ret\n"

/-- Return the common prefix of a decoded old compact path and a non-empty
    sorted descriptor interval.  Comparing the interval extrema is sufficient:
    lexicographic ordering makes every interior key share that prefix too.
    The helper bounds every key/path read by the fixed 64-nibble state-key
    domain, so the grouped leaf/extension splitters never need an
    attacker-sized comparison buffer.

    ABI: `a0=descriptors`, `a1=start`, `a2=end`, `a3=depth`,
    `a4=old_path`, `a5=old_path_len`, `a6=out_common_len`.
    Returns 0/1. -/
def mptBoundedIntervalOldPrefixFunction : String :=
  "  .globl mpt_bounded_interval_old_prefix\n" ++
  "mpt_bounded_interval_old_prefix:\n" ++
  "  sd zero, 0(a6); bgeu a1, a2, .Lmbiop_fail; li t0, " ++ toString bsrMaxStateChanges ++ "; bgtu a2, t0, .Lmbiop_fail; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu a3, t0, .Lmbiop_fail; sub t1, t0, a3; bgtu a5, t1, .Lmbiop_fail; slli t2, a1, 5; slli t3, a1, 3; add t2, t2, t3; add t2, a0, t2; ld t2, 0(t2); addi t3, a2, -1; slli t4, t3, 5; slli t5, t3, 3; add t4, t4, t5; add t4, a0, t4; ld t4, 0(t4); li t5, 0\n" ++
  ".Lmbiop_loop:\n  beq t5, a5, .Lmbiop_ok; add t0, t2, a3; add t0, t0, t5; lbu t1, 0(t0); add t0, t4, a3; add t0, t0, t5; lbu t3, 0(t0); bne t1, t3, .Lmbiop_ok; add t0, a4, t5; lbu t0, 0(t0); bne t1, t0, .Lmbiop_ok; addi t5, t5, 1; j .Lmbiop_loop\n" ++
  ".Lmbiop_ok:\n  sd t5, 0(a6); li a0, 0; ret\n" ++
  ".Lmbiop_fail:\n  li a0, 1; ret\n"

/-- Split an existing leaf against a grouped insertion interval.  The old
    suffix remains a leaf, while the normalized interval is partitioned into
    its bounded radix slots and each new slot is delegated to the fixed-frame
    missing-subtree builder; no raw access list or variable bucket is
    introduced.

    ABI: `a0=leaf_frame`, `a1=descriptors`, `a2=start`, `a3=end`,
    `a4=consumed_depth`, `a5,a6=witness`. Returns 0/1. -/
def mptBoundedSplitLeafGroupFunction : String :=
  "  .globl mpt_bounded_split_leaf_group\n" ++
  "mpt_bounded_split_leaf_group:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; sd a5, 72(sp); sd a6, 80(sp); bgeu s2, s3, .Lmbslg_fail; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu s4, t0, .Lmbslg_fail; sub t0, t0, s4; beqz t0, .Lmbslg_fail; mv a0, s0; mv a1, t0; jal ra, mpt_bounded_decode_frame_payload; bnez a0, .Lmbslg_fail; ld t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); li t1, " ++ toString bsrMptKeyNibbles ++ "; sub t1, t1, s4; bne t0, t1, .Lmbslg_fail; mv a0, s1; mv a1, s2; mv a2, s3; mv a3, s4; addi a4, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; mv a5, t0; addi a6, sp, 120; jal ra, mpt_bounded_interval_old_prefix; bnez a0, .Lmbslg_fail; ld s5, 120(sp); ld t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); bgeu s5, t0, .Lmbslg_fail\n" ++
  "  addi t1, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add t1, t1, s5; lbu s7, 0(t1); li t0, " ++ toString bsrMptRadixFanout ++ "; bgeu s7, t0, .Lmbslg_fail; li t0, 0\n" ++
  ".Lmbslg_clear:\n  li t1, 16; beq t0, t1, .Lmbslg_old; slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; add t1, s0, t1; sd zero, 0(t1); addi t0, t0, 1; j .Lmbslg_clear\n" ++
  ".Lmbslg_old:\n  addi a0, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add a0, a0, s5; addi a0, a0, 1; li t0, " ++ toString bsrMptKeyNibbles ++ "; sub a1, t0, s4; sub a1, a1, s5; addi a1, a1, -1; ld a2, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); ld a3, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); la a4, bsr_builder_node; addi a5, sp, 112; la a6, bsr_builder_result_ref; la a7, bsr_builder_result_len; jal ra, mpt_bounded_encode_leaf_ref; bnez a0, .Lmbslg_fail; slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, s0, t0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n" ++
  ".Lmbslg_copy_old:\n  beqz t2, .Lmbslg_new; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbslg_copy_old\n" ++
  ".Lmbslg_new:\n  add a3, s4, s5; mv a0, s1; mv a1, s2; mv a2, s3; mv a4, s0; jal ra, mpt_bounded_partition_frame; bnez a0, .Lmbslg_fail; slli t0, s7, 4; addi t1, s0, " ++ toString bsrMptFrameRangeTableOffset ++ "; add t1, t1, t0; ld t2, 0(t1); ld t3, 8(t1); beq t2, t3, .Lmbslg_slots; add t0, s4, s5; addi t0, t0, 1; li t1, " ++ toString bsrMptKeyNibbles ++ "; bgeu t0, t1, .Lmbslg_fail; li t1, " ++ toString bsrMptBuilderFrameBytes ++ "; mul t0, t0, t1; la t1, bsr_builder_frames; add t0, t0, t1; la t1, bsr_builder_node; sd t1, " ++ toString bsrMptFrameNodePtrOffset ++ "(t0); ld t1, 112(sp); sd t1, " ++ toString bsrMptFrameNodeLenOffset ++ "(t0); li t1, 2; sd t1, " ++ toString bsrMptFrameNodeKindOffset ++ "(t0); mv a0, t0; mv a1, s1; mv a2, t2; mv a3, t3; add a4, s4, s5; addi a4, a4, 1; ld a5, 72(sp); ld a6, 80(sp); jal ra, mpt_bounded_rebuild_subtree; beqz a0, .Lmbslg_same_store; li t0, 2; bne a0, t0, .Lmbslg_fail; slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, t0, s0; sd zero, 0(t0); j .Lmbslg_slots\n  .Lmbslg_same_store:\n  slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, t0, s0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n  .Lmbslg_same_copy:\n  beqz t2, .Lmbslg_slots; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbslg_same_copy\n  .Lmbslg_slots:\n  li s6, 0\n" ++
  ".Lmbslg_slot:\n  li t0, 16; beq s6, t0, .Lmbslg_branch; slli t0, s6, 4; addi t1, s0, " ++ toString bsrMptFrameRangeTableOffset ++ "; add t1, t1, t0; ld t2, 0(t1); ld t3, 8(t1); beq t2, t3, .Lmbslg_next; beq s6, s7, .Lmbslg_next; mv a0, s1; mv a1, t2; mv a2, t3; addi a3, s4, 1; add a3, a3, s5; jal ra, mpt_bounded_build_missing_subtree; bnez a0, .Lmbslg_fail; slli t0, s6, 5; slli t1, s6, 3; add t0, t0, t1; add t0, t0, s0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n" ++
  ".Lmbslg_copy_new:\n  beqz t2, .Lmbslg_next; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbslg_copy_new\n" ++
  ".Lmbslg_next:\n  addi s6, s6, 1; j .Lmbslg_slot\n" ++
  ".Lmbslg_branch:\n  mv a0, s0; la a1, bsr_builder_node; addi a2, sp, 112; jal ra, mpt_bounded_encode_branch; bnez a0, .Lmbslg_fail; la a0, bsr_builder_node; ld a1, 112(sp); la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_node_ref; bnez a0, .Lmbslg_fail; beqz s5, .Lmbslg_ok; sd s5, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); la t0, bsr_builder_result_ref; sd t0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); la t0, bsr_builder_result_len; ld t0, 0(t0); sd t0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); mv a0, s0; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; bnez a0, .Lmbslg_fail\n" ++
  ".Lmbslg_ok:\n  li a0, 0; j .Lmbslg_ret\n" ++
  ".Lmbslg_fail:\n  li a0, 1\n" ++
  ".Lmbslg_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 128; ret\n"

/-- Split an existing state-account leaf for one insertion whose key diverges
    below the already-consumed prefix.  The old and new suffix leaves are
    reduced to raw references immediately and retained in the current frame's
    two branch slots; the shared leaf prefix is then restored as one extension.
    This uses only the current depth frame plus the shared 1KiB node scratch.

    ABI: `a0 = leaf frame`; `a1 = insertion descriptor`; `a2 = consumed
    depth`.  Returns 0 after placing the raw result in
    `bsr_builder_result_{ref,len}`, or 1 for a malformed/non-insertion split. -/
def mptBoundedSplitLeafFunction : String :=
  "  .globl mpt_bounded_split_leaf\n" ++
  "mpt_bounded_split_leaf:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; ld t0, 32(s1); li t1, 1; bne t0, t1, .Lmbsl_fail; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu s2, t0, .Lmbsl_fail; sub s3, t0, s2; beqz s3, .Lmbsl_fail; mv a0, s0; mv a1, s3; jal ra, mpt_bounded_decode_frame_payload; bnez a0, .Lmbsl_fail; ld t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); bne t0, s3, .Lmbsl_fail; li s6, 0\n" ++
  ".Lmbsl_match:\n" ++
  "  beq s6, s3, .Lmbsl_fail; ld t0, 0(s1); add t0, t0, s2; add t0, t0, s6; lbu t1, 0(t0); addi t0, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add t0, t0, s6; lbu t2, 0(t0); bne t1, t2, .Lmbsl_diverge; addi s6, s6, 1; j .Lmbsl_match\n" ++
  ".Lmbsl_diverge:\n" ++
  "  mv s5, t1; mv s4, t2; li s7, 0\n" ++
  ".Lmbsl_clear:\n" ++
  "  li t0, 16; beq s7, t0, .Lmbsl_old_leaf; slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, s0, t0; sd zero, 0(t0); addi s7, s7, 1; j .Lmbsl_clear\n" ++
  ".Lmbsl_old_leaf:\n" ++
  "  addi a0, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add a0, a0, s6; addi a0, a0, 1; sub a1, s3, s6; addi a1, a1, -1; ld a2, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); ld a3, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); la a4, bsr_builder_node; addi a5, sp, 120; la a6, bsr_builder_result_ref; la a7, bsr_builder_result_len; jal ra, mpt_bounded_encode_leaf_ref; bnez a0, .Lmbsl_fail\n" ++
  "  slli t0, s4, 5; slli t1, s4, 3; add t0, t0, t1; add t0, s0, t0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n" ++
  ".Lmbsl_copy_old:\n" ++
  "  beqz t2, .Lmbsl_new_leaf; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbsl_copy_old\n" ++
  ".Lmbsl_new_leaf:\n" ++
  "  ld a0, 0(s1); add a0, a0, s2; add a0, a0, s6; addi a0, a0, 1; sub a1, s3, s6; addi a1, a1, -1; ld a2, 16(s1); ld a3, 24(s1); la a4, bsr_builder_node; addi a5, sp, 120; la a6, bsr_builder_result_ref; la a7, bsr_builder_result_len; jal ra, mpt_bounded_encode_leaf_ref; bnez a0, .Lmbsl_fail\n" ++
  "  slli t0, s5, 5; slli t1, s5, 3; add t0, t0, t1; add t0, s0, t0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n" ++
  ".Lmbsl_copy_new:\n" ++
  "  beqz t2, .Lmbsl_branch; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbsl_copy_new\n" ++
  ".Lmbsl_branch:\n" ++
  "  mv a0, s0; la a1, bsr_builder_node; addi a2, sp, 120; jal ra, mpt_bounded_encode_branch; bnez a0, .Lmbsl_fail; la a0, bsr_builder_node; ld a1, 120(sp); la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_node_ref; bnez a0, .Lmbsl_fail; beqz s6, .Lmbsl_ok\n" ++
  "  sd s6, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); la t0, bsr_builder_result_ref; sd t0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); la t0, bsr_builder_result_len; ld t0, 0(t0); sd t0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); mv a0, s0; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; bnez a0, .Lmbsl_fail\n" ++
  ".Lmbsl_ok:\n  li a0, 0; j .Lmbsl_ret\n" ++
  ".Lmbsl_fail:\n  li a0, 1\n" ++
  ".Lmbsl_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 128; ret\n"

/-- Split an existing extension for one insertion that diverges within the
    extension path.  The old suffix keeps its original raw child reference;
    the new suffix is a leaf.  Both are placed in a bounded branch frame and
    the common extension prefix is restored from the descriptor key.

    ABI: `a0 = extension frame`; `a1 = insertion descriptor`; `a2 = consumed
    depth`. Returns 0 after placing the raw result in
    `bsr_builder_result_{ref,len}`, or 1 for malformed/non-insertion input. -/
def mptBoundedSplitExtensionFunction : String :=
  "  .globl mpt_bounded_split_extension\n" ++
  "mpt_bounded_split_extension:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; ld t0, 32(s1); li t1, 1; bne t0, t1, .Lmbse_fail; ld t0, 8(s1); li t1, " ++ toString bsrMptKeyNibbles ++ "; bne t0, t1, .Lmbse_fail; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu s2, t0, .Lmbse_fail; sub t0, t0, s2; mv a0, s0; mv a1, t0; jal ra, mpt_bounded_decode_frame_payload; bnez a0, .Lmbse_fail; ld s3, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); beqz s3, .Lmbse_fail; sd zero, 120(sp); ld t0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); sd t0, 72(sp); ld t0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); sd t0, 80(sp); li s6, 0\n" ++
  ".Lmbse_match:\n" ++
  "  beq s6, s3, .Lmbse_fail; ld t0, 0(s1); add t0, t0, s2; add t0, t0, s6; lbu t1, 0(t0); addi t0, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add t0, t0, s6; lbu t2, 0(t0); bne t1, t2, .Lmbse_diverge; addi s6, s6, 1; j .Lmbse_match\n" ++
  ".Lmbse_diverge:\n" ++
  "  mv s5, t1; mv s4, t2; sub s7, s3, s6; addi s7, s7, -1; li t0, 0\n" ++
  ".Lmbse_clear:\n" ++
  "  li t1, 16; beq t0, t1, .Lmbse_old; slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; add t1, s0, t1; sd zero, 0(t1); addi t0, t0, 1; j .Lmbse_clear\n" ++
  ".Lmbse_old:\n" ++
  "  beqz s7, .Lmbse_old_direct; addi t0, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add t1, t0, s6; addi t1, t1, 1; mv t2, t0; mv t3, s7\n" ++
  ".Lmbse_suffix_copy:\n" ++
  "  beqz t3, .Lmbse_suffix_ready; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lmbse_suffix_copy\n" ++
  ".Lmbse_suffix_ready:\n" ++
  "  sd s7, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); ld t0, 72(sp); sd t0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); ld t0, 80(sp); sd t0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); mv a0, s0; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; bnez a0, .Lmbse_fail; j .Lmbse_old_store\n" ++
  ".Lmbse_old_direct:\n" ++
  "  la t0, bsr_builder_result_len; ld t1, 72(sp); ld t2, 80(sp); sd t2, 0(t0); la t0, bsr_builder_result_ref\n" ++
  ".Lmbse_old_direct_copy:\n" ++
  "  beqz t2, .Lmbse_old_store; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbse_old_direct_copy\n" ++
  ".Lmbse_old_store:\n" ++
  "  slli t0, s4, 5; slli t1, s4, 3; add t0, t0, t1; add t0, s0, t0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n" ++
  ".Lmbse_copy_old:\n" ++
  "  beqz t2, .Lmbse_new; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbse_copy_old\n" ++
  ".Lmbse_new:\n" ++
  "  li t0, " ++ toString bsrMptKeyNibbles ++ "; sub t0, t0, s2; sub a1, t0, s6; addi a1, a1, -1; ld a0, 0(s1); add a0, a0, s2; add a0, a0, s6; addi a0, a0, 1; ld a2, 16(s1); ld a3, 24(s1); la a4, bsr_builder_node; addi a5, sp, 120; la a6, bsr_builder_result_ref; la a7, bsr_builder_result_len; jal ra, mpt_bounded_encode_leaf_ref; bnez a0, .Lmbse_fail\n" ++
  "  slli t0, s5, 5; slli t1, s5, 3; add t0, t0, t1; add t0, s0, t0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n" ++
  ".Lmbse_copy_new:\n" ++
  "  beqz t2, .Lmbse_branch; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbse_copy_new\n" ++
  ".Lmbse_branch:\n" ++
  "  mv a0, s0; la a1, bsr_builder_node; addi a2, sp, 120; jal ra, mpt_bounded_encode_branch; bnez a0, .Lmbse_fail; la a0, bsr_builder_node; ld a1, 120(sp); la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_node_ref; bnez a0, .Lmbse_fail; beqz s6, .Lmbse_ok\n" ++
  "  ld t0, 0(s1); add t0, t0, s2; addi t1, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; mv t2, s6\n" ++
  ".Lmbse_prefix_copy:\n" ++
  "  beqz t2, .Lmbse_prefix_ready; lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lmbse_prefix_copy\n" ++
  ".Lmbse_prefix_ready:\n" ++
  "  sd s6, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); la t0, bsr_builder_result_ref; sd t0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); la t0, bsr_builder_result_len; ld t0, 0(t0); sd t0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); mv a0, s0; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; bnez a0, .Lmbse_fail\n" ++
  ".Lmbse_ok:\n  li a0, 0; j .Lmbse_ret\n" ++
  ".Lmbse_fail:\n  li a0, 1\n" ++
  ".Lmbse_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 128; ret\n"

/-- Grouped analogue of `mpt_bounded_split_extension`.  It partitions the
    normalized insertion interval at the first non-old divergence, combines
    the retained old extension suffix with one bounded missing subtree per
    populated radix slot, and encodes the canonical branch. -/
def mptBoundedSplitExtensionGroupFunction : String :=
  "  .globl mpt_bounded_split_extension_group\n" ++
  "mpt_bounded_split_extension_group:\n" ++
  "  addi sp, sp, -128\n  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0,a0; mv s1,a1; mv s2,a2; mv s3,a3; mv s4,a4; bgeu s2,s3,.Lmbseg_fail; li t0," ++ toString bsrMptKeyNibbles ++ "; bgtu s4,t0,.Lmbseg_fail; sub t0,t0,s4; mv a0,s0; mv a1,t0; jal ra,mpt_bounded_decode_frame_payload; bnez a0,.Lmbseg_fail; ld t0," ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); beqz t0,.Lmbseg_fail; sd t0,104(sp); ld t1," ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); sd t1,72(sp); ld t1," ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); sd t1,80(sp); mv a0,s1; mv a1,s2; mv a2,s3; mv a3,s4; addi a4,s0," ++ toString bsrMptFrameExtensionPathOffset ++ "; mv a5,t0; addi a6,sp,120; jal ra,mpt_bounded_interval_old_prefix; bnez a0,.Lmbseg_fail; ld s5,120(sp); ld t0,104(sp); bgeu s5,t0,.Lmbseg_fail\n" ++
  "  addi t1,s0," ++ toString bsrMptFrameExtensionPathOffset ++ "; add t1,t1,s5; lbu s7,0(t1); li t0,16; bgeu s7,t0,.Lmbseg_fail; li t0,0\n" ++
  ".Lmbseg_clear:\n  li t1,16; beq t0,t1,.Lmbseg_old; slli t1,t0,5; slli t2,t0,3; add t1,t1,t2; add t1,s0,t1; sd zero,0(t1); addi t0,t0,1; j .Lmbseg_clear\n" ++
  ".Lmbseg_old:\n  ld t0,104(sp); sub t0,t0,s5; addi t0,t0,-1; beqz t0,.Lmbseg_direct; addi t1,s0," ++ toString bsrMptFrameExtensionPathOffset ++ "; add t2,t1,s5; addi t2,t2,1; mv t3,t1\n" ++
  ".Lmbseg_suffix:\n  beqz t0,.Lmbseg_suffix_done; lbu t4,0(t2); sb t4,0(t3); addi t2,t2,1; addi t3,t3,1; addi t0,t0,-1; j .Lmbseg_suffix\n" ++
  ".Lmbseg_suffix_done:\n  ld t0,104(sp); sub t0,t0,s5; addi t0,t0,-1; sd t0," ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); ld t1,72(sp); sd t1," ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); ld t1,80(sp); sd t1," ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); mv a0,s0; la a1,bsr_builder_node; la a2,bsr_builder_result_ref; la a3,bsr_builder_result_len; jal ra,mpt_bounded_encode_extension; bnez a0,.Lmbseg_fail; j .Lmbseg_store_old\n" ++
  ".Lmbseg_direct:\n  la t0,bsr_builder_result_len; ld t1,72(sp); ld t2,80(sp); sd t2,0(t0); la t0,bsr_builder_result_ref\n  .Lmbseg_direct_copy:\n  beqz t2,.Lmbseg_store_old; lbu t3,0(t1); sb t3,0(t0); addi t1,t1,1; addi t0,t0,1; addi t2,t2,-1; j .Lmbseg_direct_copy\n" ++
  ".Lmbseg_store_old:\n  slli t0,s7,5; slli t1,s7,3; add t0,t0,t1; add t0,s0,t0; la t1,bsr_builder_result_len; ld t2,0(t1); sd t2,0(t0); addi t0,t0,8; la t1,bsr_builder_result_ref\n  .Lmbseg_copy_old:\n  beqz t2,.Lmbseg_new; lbu t3,0(t1); sb t3,0(t0); addi t1,t1,1; addi t0,t0,1; addi t2,t2,-1; j .Lmbseg_copy_old\n" ++
  ".Lmbseg_new:\n  add a3,s4,s5; mv a0,s1; mv a1,s2; mv a2,s3; mv a4,s0; jal ra,mpt_bounded_partition_frame; bnez a0,.Lmbseg_fail; li s6,0\n  .Lmbseg_slot:\n  li t0,16; beq s6,t0,.Lmbseg_branch; slli t0,s6,4; addi t1,s0," ++ toString bsrMptFrameRangeTableOffset ++ "; add t1,t1,t0; ld t2,0(t1); ld t3,8(t1); beq t2,t3,.Lmbseg_next; beq s6,s7,.Lmbseg_fail; mv a0,s1; mv a1,t2; mv a2,t3; addi a3,s4,1; add a3,a3,s5; jal ra,mpt_bounded_build_missing_subtree; bnez a0,.Lmbseg_fail; slli t0,s6,5; slli t1,s6,3; add t0,t0,t1; add t0,s0,t0; la t1,bsr_builder_result_len; ld t2,0(t1); sd t2,0(t0); addi t0,t0,8; la t1,bsr_builder_result_ref\n  .Lmbseg_copy_new:\n  beqz t2,.Lmbseg_next; lbu t3,0(t1); sb t3,0(t0); addi t1,t1,1; addi t0,t0,1; addi t2,t2,-1; j .Lmbseg_copy_new\n  .Lmbseg_next:\n  addi s6,s6,1; j .Lmbseg_slot\n" ++
  ".Lmbseg_branch:\n  mv a0,s0; la a1,bsr_builder_node; addi a2,sp,112; jal ra,mpt_bounded_encode_branch; bnez a0,.Lmbseg_fail; la a0,bsr_builder_node; ld a1,112(sp); la a2,bsr_builder_result_ref; la a3,bsr_builder_result_len; jal ra,mpt_bounded_node_ref; bnez a0,.Lmbseg_fail; beqz s5,.Lmbseg_ok; slli t0,s2,5; slli t1,s2,3; add t0,t0,t1; add t0,s1,t0; ld t0,0(t0); add t0,t0,s4; addi t1,s0," ++ toString bsrMptFrameExtensionPathOffset ++ "; mv t2,s5\n  .Lmbseg_prefix:\n  beqz t2,.Lmbseg_prefix_done; lbu t3,0(t0); sb t3,0(t1); addi t0,t0,1; addi t1,t1,1; addi t2,t2,-1; j .Lmbseg_prefix\n  .Lmbseg_prefix_done:\n  sd s5," ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); la t0,bsr_builder_result_ref; sd t0," ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); la t0,bsr_builder_result_len; ld t0,0(t0); sd t0," ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); mv a0,s0; la a1,bsr_builder_node; la a2,bsr_builder_result_ref; la a3,bsr_builder_result_len; jal ra,mpt_bounded_encode_extension; bnez a0,.Lmbseg_fail\n" ++
  ".Lmbseg_ok:\n  li a0,0; j .Lmbseg_ret\n  .Lmbseg_fail:\n  li a0,1\n  .Lmbseg_ret:\n  ld ra,0(sp); ld s0,8(sp); ld s1,16(sp); ld s2,24(sp); ld s3,32(sp); ld s4,40(sp); ld s5,48(sp); ld s6,56(sp); ld s7,64(sp); addi sp,sp,128; ret\n"

/-- Collapse a one-child state branch when its survivor is a leaf or extension.
    The branch nibble is prepended to the survivor compact suffix before
    re-encoding; this is the canonical MPT branch-elision rule.

    ABI: `a0=branch frame`, `a1=survivor nibble`, `a2=branch depth`,
    `a3,a4=witness`; returns 0 with the raw result or 1 when the survivor is
    not a leaf/extension (branch-survivor collapse is handled separately). -/
def mptBoundedCollapseBranchLeafFunction : String :=
  "  .globl mpt_bounded_collapse_branch_leaf\n" ++
  "mpt_bounded_collapse_branch_leaf:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgeu s2, t0, .Lmbcbl_fail; li t0, " ++ toString bsrMptRadixFanout ++ "; bgeu s1, t0, .Lmbcbl_fail; slli t0, s1, 5; slli t1, s1, 3; add t0, t0, t1; add t0, s0, t0; ld t1, 0(t0); beqz t1, .Lmbcbl_fail; sd t0, 72(sp); addi a0, t0, 8; mv a1, t1; mv a2, s3; mv a3, s4; addi t0, s2, 1; li t1, " ++ toString bsrMptBuilderFrameBytes ++ "; mul t0, t0, t1; la t1, bsr_builder_frames; add s5, t1, t0; mv a4, s5; jal ra, mpt_bounded_open_child_frame; bnez a0, .Lmbcbl_fail; ld t0, " ++ toString bsrMptFrameNodeKindOffset ++ "(s5); sd t0, 64(sp); beqz t0, .Lmbcbl_branch; li t1, 2; beq t0, t1, .Lmbcbl_kind_ok; li t1, 1; beq t0, t1, .Lmbcbl_kind_ok; j .Lmbcbl_fail\n" ++
  ".Lmbcbl_branch:\n  ld t0, 72(sp); addi t1, t0, 8; ld t2, 0(t0); sd t1, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s5); sd t2, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s5); sb s1, " ++ toString bsrMptFrameExtensionPathOffset ++ "(s5); li t0, 1; sd t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s5); mv a0, s5; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; bnez a0, .Lmbcbl_fail; li a0, 0; j .Lmbcbl_ret\n" ++
  ".Lmbcbl_kind_ok:\n" ++
  "  li t0, " ++ toString bsrMptKeyNibbles ++ "; sub t0, t0, s2; addi a1, t0, -1; mv a0, s5; jal ra, mpt_bounded_decode_frame_payload; bnez a0, .Lmbcbl_fail; ld s6, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s5); li t0, " ++ toString bsrMptKeyNibbles ++ "; sub t0, t0, s2; addi t0, t0, -1; bgtu s6, t0, .Lmbcbl_fail; addi t0, s5, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add t1, t0, s6\n" ++
  ".Lmbcbl_shift:\n" ++
  "  beqz s6, .Lmbcbl_prefix; addi t1, t1, -1; lbu t2, 0(t1); addi t3, t1, 1; sb t2, 0(t3); addi s6, s6, -1; j .Lmbcbl_shift\n" ++
  ".Lmbcbl_prefix:\n" ++
  "  sb s1, 0(t0); ld t1, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s5); addi t1, t1, 1; sd t1, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s5); ld t0, 64(sp); li t2, 2; bne t0, t2, .Lmbcbl_extension; addi a0, s5, " ++ toString bsrMptFrameExtensionPathOffset ++ "; mv a1, t1; ld a2, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s5); ld a3, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s5); la a4, bsr_builder_node; addi a5, sp, 80; la a6, bsr_builder_result_ref; la a7, bsr_builder_result_len; jal ra, mpt_bounded_encode_leaf_ref; bnez a0, .Lmbcbl_fail; li a0, 0; j .Lmbcbl_ret\n" ++
  ".Lmbcbl_extension:\n  mv a0, s5; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; bnez a0, .Lmbcbl_fail; li a0, 0; j .Lmbcbl_ret\n" ++
  ".Lmbcbl_fail:\n  li a0, 1\n" ++
  ".Lmbcbl_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 96; ret\n"

/-- Rebuild one isolated leaf of the bounded frontier.  Exact replacement
    re-encodes the final value; an insertion with a divergent path is split
    into two suffix leaves and an optional shared-prefix extension.  A delete
    deliberately returns `2`: the caller must perform canonical parent
    collapse rather than manufacture an empty leaf.

    ABI: `a0 = leaf frame`; `a1 = descriptor`; `a2 = consumed depth`.
    Returns 0 after placing the raw result in `bsr_builder_result_{ref,len}`;
    2 for exact delete; 1 otherwise. -/
def mptBoundedRebuildExactLeafFunction : String :=
  "  .globl mpt_bounded_rebuild_exact_leaf\n" ++
  "mpt_bounded_rebuild_exact_leaf:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu s2, t0, .Lmbrl_fail; sub s3, t0, s2; mv a0, s0; mv a1, s3; jal ra, mpt_bounded_decode_frame_payload; bnez a0, .Lmbrl_fail; ld t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); bne t0, s3, .Lmbrl_fail; mv a0, s1; mv a1, s2; mv a2, s0; jal ra, mpt_bounded_frame_path_match; beqz a0, .Lmbrl_exact; li t0, 1; beq a0, t0, .Lmbrl_split; j .Lmbrl_fail\n" ++
  ".Lmbrl_split:\n  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, mpt_bounded_split_leaf; j .Lmbrl_ret\n" ++
  ".Lmbrl_exact:\n" ++
  "  ld t0, 32(s1); li t1, 2; beq t0, t1, .Lmbrl_delete; bnez t0, .Lmbrl_fail\n" ++
  "  ld s4, 0(s1); add s4, s4, s2; ld s5, 16(s1); ld t0, 24(s1); la t1, bsr_builder_node; la t2, bsr_builder_result_ref; la t3, bsr_builder_result_len; mv a0, s4; mv a1, s3; mv a2, s5; mv a3, t0; mv a4, t1; addi a5, sp, 56; mv a6, t2; mv a7, t3; jal ra, mpt_bounded_encode_leaf_ref; bnez a0, .Lmbrl_fail; li a0, 0; j .Lmbrl_ret\n" ++
  ".Lmbrl_delete:\n  li a0, 2; j .Lmbrl_ret\n" ++
  ".Lmbrl_fail:\n  li a0, 1\n" ++
  ".Lmbrl_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64; ret\n"

/-- Build a canonical subtree for a missing branch child from a non-empty,
    already-normalized descriptor interval.  A singleton becomes a suffix
    leaf; wider intervals are partitioned into the fixed sixteen slots of the
    frame at their current depth.  One occupied digit is path-compressed into
    an extension and two or more become a branch.  Thus this consumes no
    attacker-sized bucket and never stages more than the gas-derived final
    descriptor bound. -/
def mptBoundedBuildMissingSubtreeFunction : String :=
  "  .globl mpt_bounded_build_missing_subtree\n" ++
  "mpt_bounded_build_missing_subtree:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; li t0, " ++ toString bsrMaxStateChanges ++ "; bgtu s2, t0, .Lmbms_fail; bgeu s1, s2, .Lmbms_fail; li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu s3, t0, .Lmbms_fail; li t0, " ++ toString bsrMptBuilderFrameBytes ++ "; mul t1, s3, t0; la t0, bsr_builder_frames; add s4, t0, t1; li t2, 0\n" ++
  ".Lmbms_clear_frame:\n  li t3, 16; beq t2, t3, .Lmbms_clear_done; slli t3, t2, 5; slli t4, t2, 3; add t3, t3, t4; add t3, s4, t3; sd zero, 0(t3); sd zero, 8(t3); sd zero, 16(t3); sd zero, 24(t3); sd zero, 32(t3); addi t2, t2, 1; j .Lmbms_clear_frame\n" ++
  ".Lmbms_clear_done:\n  addi t0, s1, 1; bne t0, s2, .Lmbms_many\n" ++
  ".Lmbms_one:\n  slli t0, s1, 5; slli t1, s1, 3; add t0, t0, t1; add t0, s0, t0; ld t1, 32(t0); li t2, 1; bne t1, t2, .Lmbms_fail; ld a0, 0(t0); add a0, a0, s3; li t1, " ++ toString bsrMptKeyNibbles ++ "; sub a1, t1, s3; ld a2, 16(t0); ld a3, 24(t0); la a4, bsr_builder_node; addi a5, sp, 72; la a6, bsr_builder_result_ref; la a7, bsr_builder_result_len; jal ra, mpt_bounded_encode_leaf_ref; bnez a0, .Lmbms_fail; li a0, 0; j .Lmbms_ret\n" ++
  ".Lmbms_many:\n  li t0, " ++ toString bsrMptKeyNibbles ++ "; bgeu s3, t0, .Lmbms_fail; mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4; jal ra, mpt_bounded_partition_frame; bnez a0, .Lmbms_fail; li s5, 0; li s6, 0; li s7, 0\n" ++
  ".Lmbms_child:\n  li t0, 16; beq s5, t0, .Lmbms_finish; slli t0, s5, 4; addi t1, s4, " ++ toString bsrMptFrameRangeTableOffset ++ "; add t1, t1, t0; ld t2, 0(t1); ld t3, 8(t1); beq t2, t3, .Lmbms_next; sd t2, 72(sp); sd t3, 80(sp); addi a0, s0, 0; mv a1, t2; mv a2, t3; addi a3, s3, 1; jal ra, mpt_bounded_build_missing_subtree; bnez a0, .Lmbms_ret; slli t0, s5, 5; slli t1, s5, 3; add t0, t0, t1; add t0, s4, t0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref\n" ++
  ".Lmbms_copy_ref:\n  beqz t2, .Lmbms_after_child; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbms_copy_ref\n" ++
  ".Lmbms_after_child:\n  addi s6, s6, 1; mv s7, s5\n" ++
  ".Lmbms_next:\n  addi s5, s5, 1; j .Lmbms_child\n" ++
  ".Lmbms_finish:\n  li t0, 2; bgeu s6, t0, .Lmbms_branch; li t0, 1; bne s6, t0, .Lmbms_fail; slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, s4, t0; addi t1, t0, 8; ld t2, 0(t0); sd t1, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s4); sd t2, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s4); sb s7, " ++ toString bsrMptFrameExtensionPathOffset ++ "(s4); li t0, 1; sd t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s4); mv a0, s4; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; j .Lmbms_ret\n" ++
  ".Lmbms_branch:\n  mv a0, s4; la a1, bsr_builder_node; addi a2, sp, 72; jal ra, mpt_bounded_encode_branch; bnez a0, .Lmbms_fail; la a0, bsr_builder_node; ld a1, 72(sp); la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_node_ref; j .Lmbms_ret\n" ++
  ".Lmbms_fail:\n  li a0, 1\n" ++
  ".Lmbms_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 96; ret\n"

/-- Depth-first bounded dispatcher for the already-supported exact-replacement
    subset. It is deliberately a real recursive frontier walk, not a NodeDb
    shim: branch children are opened only from their frame raw refs/witness,
    and every completed child is copied to its parent before the shared result
    slot is reused. Existing extension prefixes are preserved through the same
    continuation; a one-descriptor insertion into an existing branch's empty
    child is materialized as its bounded suffix leaf. Extension/leaf splits
    and deletion collapse remain explicit conservative exits until their
    canonical cases land. -/
def mptBoundedRebuildSubtreeFunction : String :=
  "  .globl mpt_bounded_rebuild_subtree\n" ++
  "  .type mpt_bounded_rebuild_subtree, @function\n" ++
  "mpt_bounded_rebuild_subtree:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6; ld t0, " ++ toString bsrMptFrameNodeKindOffset ++ "(s0); beqz t0, .Lmbrs_branch; li t1, 1; beq t0, t1, .Lmbrs_extension; li t1, 2; beq t0, t1, .Lmbrs_leaf; j .Lmbrs_fail\n" ++
  ".Lmbrs_leaf:\n  addi t0, s2, 1; bne t0, s3, .Lmbrs_leaf_group; mv a0, s0; slli t0, s2, 5; slli t1, s2, 3; add t0, t0, t1; add a1, s1, t0; mv a2, s4; jal ra, mpt_bounded_rebuild_exact_leaf; j .Lmbrs_ret\n" ++
  ".Lmbrs_leaf_group:\n  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4; mv a5, s5; mv a6, s6; jal ra, mpt_bounded_split_leaf_group; j .Lmbrs_ret\n" ++
  ".Lmbrs_extension:\n  li t0, " ++ toString bsrMptKeyNibbles ++ "; bgtu s4, t0, .Lmbrs_fail; sub a1, t0, s4; mv a0, s0; jal ra, mpt_bounded_decode_frame_payload; bnez a0, .Lmbrs_fail; sd s2, 80(sp)\n" ++
  ".Lmbrs_ext_match:\n  ld t0, 80(sp); beq t0, s3, .Lmbrs_ext_descend; slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; add a0, s1, t1; mv a1, s4; mv a2, s0; jal ra, mpt_bounded_frame_path_match; beqz a0, .Lmbrs_ext_next; li t1, 1; bne a0, t1, .Lmbrs_fail; addi t1, s2, 1; bne t1, s3, .Lmbrs_ext_group; slli t1, s2, 5; slli t2, s2, 3; add t1, t1, t2; add a1, s1, t1; mv a0, s0; mv a2, s4; jal ra, mpt_bounded_split_extension; j .Lmbrs_ret\n" ++
  ".Lmbrs_ext_group:\n  mv a0,s0; mv a1,s1; mv a2,s2; mv a3,s3; mv a4,s4; jal ra,mpt_bounded_split_extension_group; j .Lmbrs_ret\n" ++
  ".Lmbrs_ext_next:\n  ld t0, 80(sp); addi t0, t0, 1; sd t0, 80(sp); j .Lmbrs_ext_match\n" ++
  ".Lmbrs_ext_descend:\n  ld t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); add s7, s4, t0; li t1, " ++ toString bsrMptKeyNibbles ++ "; bgeu s7, t1, .Lmbrs_fail; li t1, " ++ toString bsrMptBuilderFrameBytes ++ "; mul t2, s7, t1; la t1, bsr_builder_frames; add t2, t1, t2; sd t2, 72(sp); ld a0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); ld a1, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); mv a2, s5; mv a3, s6; mv a4, t2; jal ra, mpt_bounded_open_child_frame; bnez a0, .Lmbrs_fail\n" ++
  "  ld a0, 72(sp); mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s7; mv a5, s5; mv a6, s6; jal ra, mpt_bounded_rebuild_subtree; bnez a0, .Lmbrs_ret; la a0, bsr_builder_node; jal ra, rlp_item_size; beqz a0, .Lmbrs_fail; li t0, " ++ toString bsrMptNodeMaxBytes ++ "; bgtu a0, t0, .Lmbrs_fail; ld t1, 72(sp); la t0, bsr_builder_node; sd t0, " ++ toString bsrMptFrameNodePtrOffset ++ "(t1); sd a0, " ++ toString bsrMptFrameNodeLenOffset ++ "(t1); la a0, bsr_builder_node; ld a1, " ++ toString bsrMptFrameNodeLenOffset ++ "(t1); addi a2, sp, 80; jal ra, mpt_bounded_classify_node; bnez a0, .Lmbrs_fail; ld t1, 72(sp); ld t0, 80(sp); sd t0, " ++ toString bsrMptFrameNodeKindOffset ++ "(t1); li t1, 1; bne t0, t1, .Lmbrs_ext_wrap\n" ++
  "  .globl mpt_bounded_extension_merge_probe\n  .type mpt_bounded_extension_merge_probe, @function\nmpt_bounded_extension_merge_probe:\n.Lmbrs_ext_merge:\n  ld t0, 72(sp); li t1, " ++ toString bsrMptKeyNibbles ++ "; sub a1, t1, s7; mv a0, t0; jal ra, mpt_bounded_decode_frame_payload; bnez a0, .Lmbrs_fail; ld t0, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); ld t1, 72(sp); ld t2, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(t1); add t3, t0, t2; li t4, " ++ toString bsrMptKeyNibbles ++ "; sub t4, t4, s4; bgtu t3, t4, .Lmbrs_fail; addi t4, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; add t4, t4, t0; addi t5, t1, " ++ toString bsrMptFrameExtensionPathOffset ++ "\n" ++
  ".Lmbrs_ext_copy_path:\n  beqz t2, .Lmbrs_ext_child; lbu t6, 0(t5); sb t6, 0(t4); addi t5, t5, 1; addi t4, t4, 1; addi t2, t2, -1; j .Lmbrs_ext_copy_path\n" ++
  ".Lmbrs_ext_child:\n  ld t1, 72(sp); ld t2, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(t1); sd t2, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); ld t2, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(t1); sd t2, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); sd t3, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); j .Lmbrs_ext_encode\n  .size mpt_bounded_extension_merge_probe, .Lmbrs_ext_wrap - mpt_bounded_extension_merge_probe\n" ++
  ".Lmbrs_ext_wrap:\n  la t0, bsr_builder_result_ref; sd t0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); la t0, bsr_builder_result_len; ld t0, 0(t0); sd t0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0)\n" ++
  ".Lmbrs_ext_encode:\n  mv a0, s0; la a1, bsr_builder_node; la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_encode_extension; j .Lmbrs_ret\n" ++
  ".Lmbrs_branch:\n  mv a0, s1; mv a1, s2; mv a2, s3; mv a3, s4; mv a4, s0; jal ra, mpt_bounded_partition_frame; bnez a0, .Lmbrs_fail; li s7, 0; j .Lmbrs_child\n" ++
  ".Lmbrs_child:\n  li t0, 16; beq s7, t0, .Lmbrs_encode; slli t0, s7, 4; addi t1, s0, " ++ toString bsrMptFrameRangeTableOffset ++ "; add t1, t1, t0; ld t2, 0(t1); ld t3, 8(t1); beq t2, t3, .Lmbrs_next\n" ++
  "  sd t2, 80(sp); sd t3, 88(sp); slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, s0, t0; ld t4, 0(t0); beqz t4, .Lmbrs_missing; addi t5, t0, 8; addi t6, s4, 1; li a0, " ++ toString bsrMptBuilderFrameBytes ++ "; mul t6, t6, a0; la a0, bsr_builder_frames; add a4, a0, t6; sd a4, 72(sp); mv a0, t5; mv a1, t4; mv a2, s5; mv a3, s6; jal ra, mpt_bounded_open_child_frame; bnez a0, .Lmbrs_fail\n" ++
  "  ld a0, 72(sp); mv a1, s1; ld a2, 80(sp); ld a3, 88(sp); addi a4, s4, 1; mv a5, s5; mv a6, s6; jal ra, mpt_bounded_rebuild_subtree; beqz a0, .Lmbrs_child_done; li t0, 2; bne a0, t0, .Lmbrs_ret; slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, s0, t0; sd zero, 0(t0); j .Lmbrs_next\n" ++
  ".Lmbrs_child_done:\n  slli t0, s7, 5; slli t1, s7, 3; add t0, t0, t1; add t0, s0, t0; la t1, bsr_builder_result_len; ld t2, 0(t1); sd t2, 0(t0); addi t0, t0, 8; la t1, bsr_builder_result_ref; j .Lmbrs_copy_ref\n" ++
  ".Lmbrs_missing:\n  mv a0, s1; ld a1, 80(sp); ld a2, 88(sp); addi a3, s4, 1; jal ra, mpt_bounded_build_missing_subtree; bnez a0, .Lmbrs_ret; j .Lmbrs_child_done\n" ++
  ".Lmbrs_copy_ref:\n  beqz t2, .Lmbrs_next; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbrs_copy_ref\n" ++
  ".Lmbrs_next:\n  addi s7, s7, 1; j .Lmbrs_child\n" ++
  ".Lmbrs_encode:\n  li t0, 0; li t1, 0\n" ++
  ".Lmbrs_count:\n  li t2, 16; beq t1, t2, .Lmbrs_count_done; slli t2, t1, 5; slli t3, t1, 3; add t2, t2, t3; add t2, s0, t2; ld t2, 0(t2); beqz t2, .Lmbrs_count_next; sd t1, 80(sp); addi t0, t0, 1\n" ++
  ".Lmbrs_count_next:\n  addi t1, t1, 1; j .Lmbrs_count\n" ++
  ".Lmbrs_count_done:\n  li t1, 2; bgeu t0, t1, .Lmbrs_keep_branch; beqz t0, .Lmbrs_deleted; ld a1, 80(sp); mv a0, s0; mv a2, s4; mv a3, s5; mv a4, s6; jal ra, mpt_bounded_collapse_branch_leaf; j .Lmbrs_ret\n" ++
  ".Lmbrs_keep_branch:\n  la a1, bsr_builder_node; addi a2, sp, 72; mv a0, s0; jal ra, mpt_bounded_encode_branch; bnez a0, .Lmbrs_fail; la a0, bsr_builder_node; ld a1, 72(sp); la a2, bsr_builder_result_ref; la a3, bsr_builder_result_len; jal ra, mpt_bounded_node_ref; j .Lmbrs_ret\n" ++
  ".Lmbrs_deleted:\n  li a0, 2; j .Lmbrs_ret\n" ++
  ".Lmbrs_fail:\n  li a0, 1\n" ++
  ".Lmbrs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 96; ret\n" ++
  "  .size mpt_bounded_rebuild_subtree, . - mpt_bounded_rebuild_subtree\n"

/-- Re-encode one bounded extension frame. The frame stores a *raw* child
    reference, whereas `mpt_extension_node_encode` expects an RLP item: a
    32-byte hash therefore receives its canonical `0xa0` string prefix in a
    fixed stack slot, while an inline child is embedded verbatim. The decoded
    path was already bounded by `mpt_bounded_decode_extension`, so this helper
    can neither re-materialize an attacker-sized compact path nor allocate a
    node per depth.

    ABI: `a0 = frame`; `a1 = node_out[1024]`; `a2 = raw_ref_out[32]`;
    `a3 = raw_ref_len_out`; returns 0/1. -/
def mptBoundedEncodeExtensionFunction : String :=
  "  .globl mpt_bounded_encode_extension\n" ++
  "mpt_bounded_encode_extension:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; sd zero, 0(s3); ld s4, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s0); beqz s4, .Lmbee_fail; li t0, " ++ toString bsrMptFrameExtensionPathBytes ++ "; bgtu s4, t0, .Lmbee_fail; ld s5, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s0); ld s6, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s0); li t0, 32; bgtu s6, t0, .Lmbee_fail; beqz s6, .Lmbee_fail\n" ++
  "  li t0, 32; bne s6, t0, .Lmbee_inline\n" ++
  "  li t0, 160; sb t0, 72(sp); addi t0, sp, 73; mv t1, s5; li t2, 32\n" ++
  ".Lmbee_hash_copy:\n" ++
  "  beqz t2, .Lmbee_hash_ready; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbee_hash_copy\n" ++
  ".Lmbee_hash_ready:\n" ++
  "  addi t0, sp, 72; li t1, 33; j .Lmbee_encode\n" ++
  ".Lmbee_inline:\n" ++
  "  mv t0, s5; mv t1, s6\n" ++
  ".Lmbee_encode:\n" ++
  "  addi a0, s0, " ++ toString bsrMptFrameExtensionPathOffset ++ "; mv a1, s4; mv a2, t0; mv a3, t1; mv a4, s1; addi a5, sp, 64; jal ra, mpt_extension_node_encode; bnez a0, .Lmbee_fail\n" ++
  "  mv a0, s1; ld a1, 64(sp); mv a2, s2; mv a3, s3; jal ra, mpt_bounded_node_ref; bnez a0, .Lmbee_fail; li a0, 0; j .Lmbee_ret\n" ++
  ".Lmbee_fail:\n  li a0, 1\n" ++
  ".Lmbee_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 112; ret\n"

/-- Bounded shared-root body for the supported exact-replacement subset.
    The input descriptors have already been normalized to final, distinct
    committed values.  It intentionally remains disconnected from the live
    verdict until insert/delete/canonical-collapse cases have comparable KATs.

    ABI: `a0 = old_root[32]`; `a1 = witness section`; `a2 = witness length`;
    `a3 = descriptors`; `a4 = descriptor count`; `a5 = out_root[32]`.
    Returns `0`/`1`. -/
def mptBoundedStateRootFunction : String :=
  "  .globl mpt_bounded_state_root\n" ++
  "mpt_bounded_state_root:\n" ++
  "  la t0, bsr_builder_value_max; li t1, " ++ toString bsrEncodedAccountBytes ++ "; sd t1, 0(t0); la t0, bsr_builder_witness_value_max; sd t1, 0(t0); j .Lmbsr_body\n" ++
  "  .globl mpt_bounded_storage_root\n" ++
  "mpt_bounded_storage_root:\n" ++
  "  la t0, bsr_builder_value_max; li t1, " ++ toString bsrEncodedStorageValueBytes ++ "; sd t1, 0(t0); la t0, bsr_builder_witness_value_max; li t1, " ++ toString bsrMptNodeMaxBytes ++ "; sd t1, 0(t0)\n" ++
  ".Lmbsr_body:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; beqz s4, .Lmbsr_copy_old; mv a0, s3; mv a1, s4; jal ra, mpt_bounded_prepare_changes; bnez a0, .Lmbsr_fail\n" ++
  "  # EMPTY_TRIE_ROOT = keccak256(rlp(b'')) has no witness node to open.  Hash its one-byte RLP directly, then build the normalized insertion interval as a missing subtree.\n" ++
  "  addi t0, sp, 72; li t1, 128; sb t1, 0(t0); mv a0, t0; li a1, 1; la a2, bsr_builder_node; jal ra, zkvm_keccak256; li t0, 0; la t1, bsr_builder_node\n" ++
  ".Lmbsr_empty_cmp:\n  li t2, 32; beq t0, t2, .Lmbsr_empty_match; add t3, s0, t0; lbu t4, 0(t3); add t3, t1, t0; lbu t5, 0(t3); bne t4, t5, .Lmbsr_open; addi t0, t0, 1; j .Lmbsr_empty_cmp\n" ++
  "  # On an empty trie, final deletes are no-ops. Compact them in place and\n" ++
  "  # turn final mode-0/1 values into inserts before constructing the missing tree.\n" ++
  ".Lmbsr_empty_match:\n  li t0, 0; li t1, 0\n" ++
  ".Lmbsr_empty_filter:\n  beq t0, s4, .Lmbsr_empty_filtered; slli t2, t0, 5; slli t3, t0, 3; add t2, t2, t3; add t2, s3, t2; ld t3, 32(t2); li t4, 2; beq t3, t4, .Lmbsr_empty_skip; li t4, 1; bgtu t3, t4, .Lmbsr_fail; slli t4, t1, 5; slli t5, t1, 3; add t4, t4, t5; add t4, s3, t4; ld t5, 0(t2); sd t5, 0(t4); ld t5, 8(t2); sd t5, 8(t4); ld t5, 16(t2); sd t5, 16(t4); ld t5, 24(t2); sd t5, 24(t4); li t5, 1; sd t5, 32(t4); addi t1, t1, 1\n" ++
  ".Lmbsr_empty_skip:\n  addi t0, t0, 1; j .Lmbsr_empty_filter\n" ++
  ".Lmbsr_empty_filtered:\n  mv s4, t1; beqz s4, .Lmbsr_copy_old; mv a0, s3; li a1, 0; mv a2, s4; li a3, 0; jal ra, mpt_bounded_build_missing_subtree; bnez a0, .Lmbsr_fail; j .Lmbsr_result\n" ++
  ".Lmbsr_open:\n  mv a0, s0; mv a1, s1; mv a2, s2; la a3, bsr_builder_frames; jal ra, mpt_bounded_open_root_frame; bnez a0, .Lmbsr_fail\n" ++
  "  la a0, bsr_builder_frames; mv a1, s3; li a2, 0; mv a3, s4; li a4, 0; mv a5, s1; mv a6, s2; jal ra, mpt_bounded_rebuild_subtree; beqz a0, .Lmbsr_result; li t0, 2; bne a0, t0, .Lmbsr_fail; la t0, bsr_builder_frames; ld t0, " ++ toString bsrMptFrameNodeKindOffset ++ "(t0); li t1, 2; bne t0, t1, .Lmbsr_fail; li t0, 128; sb t0, 72(sp); addi a0, sp, 72; li a1, 1; mv a2, s5; jal ra, zkvm_keccak256; li a0, 0; j .Lmbsr_ret\n" ++
  ".Lmbsr_result:\n" ++
  "  la t0, bsr_builder_result_len; ld t1, 0(t0); beqz t1, .Lmbsr_fail; li t2, 32; bne t1, t2, .Lmbsr_hash_root; la t0, bsr_builder_result_ref; mv t1, s5; li t2, 32; j .Lmbsr_copy\n" ++
  ".Lmbsr_hash_root:\n  la a0, bsr_builder_result_ref; la t0, bsr_builder_result_len; ld a1, 0(t0); mv a2, s5; jal ra, zkvm_keccak256; li a0, 0; j .Lmbsr_ret\n" ++
  ".Lmbsr_copy_old:\n  mv t0, s0; mv t1, s5; li t2, 32\n" ++
  ".Lmbsr_copy:\n  beqz t2, .Lmbsr_copy_ok; lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lmbsr_copy\n" ++
  ".Lmbsr_copy_ok:\n  li a0, 0; j .Lmbsr_ret\n" ++
  ".Lmbsr_fail:\n  li a0, 1\n" ++
  ".Lmbsr_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 80; ret\n"

/-- The linked sd13v front end.  Keeping this aggregation explicit prevents a
    future caller from accidentally using the sorter without the final-distinct
    boundary. -/
def mptBoundedBuilderFrontEndFunction : String :=
  mptBoundedSortChangesFunction ++ "\n" ++ mptBoundedPrepareChangesFunction ++ "\n" ++
    mptBoundedCaptureBranchRefsFunction ++ "\n" ++ mptBoundedResolveWitnessFunction ++ "\n" ++
    mptBoundedClassifyNodeFunction ++ "\n" ++ mptBoundedOpenRootFrameFunction ++ "\n" ++
    mptBoundedOpenChildFrameFunction ++ "\n" ++
    mptBoundedNodeRefFunction ++ "\n" ++ mptBoundedEncodeBranchFunction ++ "\n" ++
    mptBoundedEncodeLeafRefFunction ++ "\n" ++ mptBoundedDecodeExtensionFunction ++ "\n" ++
    mptBoundedDecodeLeafFunction ++ "\n" ++ mptBoundedDecodeFramePayloadFunction ++ "\n" ++
    mptBoundedFramePathMatchFunction ++ "\n" ++ mptBoundedIntervalOldPrefixFunction ++ "\n" ++
    mptBoundedSplitLeafGroupFunction ++ "\n" ++ mptBoundedSplitLeafFunction ++ "\n" ++
    mptBoundedSplitExtensionFunction ++ "\n" ++ mptBoundedSplitExtensionGroupFunction ++ "\n" ++
    mptBoundedCollapseBranchLeafFunction ++ "\n" ++
    mptBoundedRebuildExactLeafFunction ++ "\n" ++
    mptBoundedBuildMissingSubtreeFunction ++ "\n" ++
    mptBoundedRebuildSubtreeFunction ++ "\n" ++
    mptBoundedEncodeExtensionFunction ++ "\n" ++ mptBoundedStateRootFunction ++ "\n" ++
    mptBoundedPartitionFrameFunction

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
  "bsr_builder_value_max:\n  .zero 8\n" ++
  "bsr_builder_witness_value_max:\n  .zero 8\n" ++
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

/-- Probe the descendant opener through the hashed-child path. The leaf RLP is
    held only in the witness, so a successful result demonstrates that this
    helper did not consult NodeDb and did not confuse a raw 32-byte hash with
    an inline RLP item. -/
def ziskMptBoundedOpenChildFramePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000; ld s1, 8(s0); addi a0, s0, 16; li a1, 32; addi a2, s0, 48; mv a3, s1; la a4, mboc_probe_frame; jal ra, mpt_bounded_open_child_frame; mv s2, a0\n" ++
  "  li t0, 0xa0010000; sd s2, 0(t0); bnez s2, .Lmbocp_done; la t1, mboc_probe_frame; ld t2, " ++ toString bsrMptFrameNodeLenOffset ++ "(t1); sd t2, 8(t0); ld t2, " ++ toString bsrMptFrameNodeKindOffset ++ "(t1); sd t2, 16(t0); ld t2, " ++ toString bsrMptFrameNodePtrOffset ++ "(t1); addi t3, s0, 48; sub t2, t2, t3; sd t2, 24(t0)\n"

def ziskMptBoundedOpenChildFrameDataSection : String :=
  ".section .bss\n.balign 8\nmboc_probe_frame:\n  .zero " ++ toString bsrMptBuilderFrameBytes ++ "\n" ++
  ziskWitnessLookupByHashDataSection

def ziskMptBoundedOpenChildFrameProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedOpenChildFramePrologue ++ "\n" ++
    zkvmKeccak256Function ++ "\n" ++ witnessLookupByHashFunction ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++ rlpListCountItemsFunction ++ "\n" ++
    mptBoundedResolveWitnessFunction ++ "\n" ++ mptBoundedCaptureBranchRefsFunction ++ "\n" ++
    mptBoundedClassifyNodeFunction ++ "\n" ++ mptBoundedOpenChildFrameFunction ++ "\n.Lmbocp_done:"
  dataAsm := ziskMptBoundedOpenChildFrameDataSection
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

/-- Probe the bounded raw-reference producer on both sides of the MPT inline
    threshold. Input is `u64 node_len` followed by node bytes; output is
    `{status, raw_ref_len, raw_ref[32]}`. -/
def ziskMptBoundedNodeRefPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld a1, 8(t0); addi a0, t0, 16; li a2, 0xa0010010; li a3, 0xa0010008; jal ra, mpt_bounded_node_ref; li t0, 0xa0010000; sd a0, 0(t0); j .Lmbnrp_done"

def ziskMptBoundedNodeRefDataSection : String :=
  ".section .data\n.balign 8\nzk3_state:\n  .zero 200"

def ziskMptBoundedNodeRefProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedNodeRefPrologue ++ "\n" ++
    zkvmKeccak256Function ++ "\n" ++ mptBoundedNodeRefFunction ++ "\n.Lmbnrp_done:"
  dataAsm := ziskMptBoundedNodeRefDataSection
}

/-- Canonical branch reconstruction probe: its fixed frame contains empty,
    inline-empty-list, and hashed `00..1f` references, followed by empty
    children. -/
def ziskMptBoundedEncodeBranchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, mbeb_frame; li t1, 1; sd t1, 40(t0); li t1, 192; sb t1, 48(t0); li t1, 32; sd t1, 80(t0); addi t2, t0, 88; li t3, 0\n" ++
  ".Lmbebp_hash:\n  li t4, 32; beq t3, t4, .Lmbebp_call; sb t3, 0(t2); addi t2, t2, 1; addi t3, t3, 1; j .Lmbebp_hash\n" ++
  ".Lmbebp_call:\n  la a0, mbeb_frame; li a1, 0xa0010010; li a2, 0xa0010008; jal ra, mpt_bounded_encode_branch; li t0, 0xa0010000; sd a0, 0(t0); j .Lmbebp_done"

def ziskMptBoundedEncodeBranchDataSection : String :=
  ".section .bss\n.balign 8\nmbeb_frame:\n  .zero " ++ toString bsrMptBuilderFrameBytes

def ziskMptBoundedEncodeBranchProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedEncodeBranchPrologue ++ "\n" ++
    rlpEncodeListPrefixFunction ++ "\n" ++ mptBoundedEncodeBranchFunction ++ "\n.Lmbebp_done:"
  dataAsm := ziskMptBoundedEncodeBranchDataSection
}

def ziskMptBoundedEncodeLeafRefPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld a1, 8(t0); la a0, mbelr_path; la a2, mbelr_path; li a3, 0; la a4, mbelr_node; la a5, mbelr_node_len; la a6, mbelr_ref; la a7, mbelr_ref_len; jal ra, mpt_bounded_encode_leaf_ref; mv s0, a0; li t0, 0xa0010000; sd s0, 0(t0); bnez s0, .Lmbelrp_done; la t1, mbelr_node_len; ld t2, 0(t1); sd t2, 8(t0); la t1, mbelr_ref_len; ld t2, 0(t1); sd t2, 16(t0); la t1, mbelr_node_len; ld t2, 0(t1); la t1, mbelr_node; addi t0, t0, 24\n" ++
  ".Lmbelrp_node:\n  beqz t2, .Lmbelrp_ref_start; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbelrp_node\n" ++
  ".Lmbelrp_ref_start:\n  la t1, mbelr_ref; li t2, 32\n" ++
  ".Lmbelrp_ref:\n  beqz t2, .Lmbelrp_done; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbelrp_ref"

def ziskMptBoundedEncodeLeafRefDataSection : String :=
  ".section .bss\n.balign 8\nmbelr_path:\n  .zero 64\nmbelr_node:\n  .zero 1024\nmbelr_node_len:\n  .zero 8\nmbelr_ref:\n  .zero 32\nmbelr_ref_len:\n  .zero 8\n" ++
    ziskMptLeafNodeEncodeFromNibblesDataSection ++ "\n.section .data\n.balign 8\nbsr_builder_value_max:\n  .dword " ++ toString bsrEncodedAccountBytes ++ "\nbsr_builder_witness_value_max:\n  .dword " ++ toString bsrEncodedAccountBytes ++ "\nzk3_state:\n  .zero 200"

def ziskMptBoundedEncodeLeafRefProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedEncodeLeafRefPrologue ++ "\n" ++ hpEncodeNibblesFunction ++ "\n" ++
    rlpEncodeBytesFunction ++ "\n" ++ rlpEncodeListPrefixFunction ++ "\n" ++
    mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++ zkvmKeccak256Function ++ "\n" ++
    mptBoundedNodeRefFunction ++ "\n" ++ mptBoundedEncodeLeafRefFunction ++ "\n.Lmbelrp_done:"
  dataAsm := ziskMptBoundedEncodeLeafRefDataSection
}

def ziskMptBoundedDecodeExtensionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld a1, 8(t0); addi a0, t0, 16; li a2, 64; li a3, 0xa0010020; li a4, 0xa0010008; li a5, 0xa0010010; li a6, 0xa0010018; jal ra, mpt_bounded_decode_extension; li t0, 0xa0010000; sd a0, 0(t0); bnez a0, .Lmbdep_done; li t0, 0xa0010010; ld t1, 0(t0); li t2, 0x40000010; sub t1, t1, t2; sd t1, 0(t0); j .Lmbdep_done"

def ziskMptBoundedDecodeExtensionProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedDecodeExtensionPrologue ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++ rlpListCountItemsFunction ++ "\n" ++
    mptBoundedDecodeExtensionFunction ++ "\n.Lmbdep_done:"
  dataAsm := ""
}

def ziskMptBoundedDecodeLeafPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld a1, 8(t0); addi a0, t0, 16; li a2, 64; li a3, 0xa0010020; li a4, 0xa0010008; li a5, 0xa0010010; li a6, 0xa0010018; jal ra, mpt_bounded_decode_leaf; li t0, 0xa0010000; sd a0, 0(t0); bnez a0, .Lmbdlp_done; li t0, 0xa0010010; ld t1, 0(t0); li t2, 0x40000010; sub t1, t1, t2; sd t1, 0(t0); j .Lmbdlp_done"

def ziskMptBoundedDecodeLeafProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedDecodeLeafPrologue ++ "\n" ++
    rlpListNthItemFunction ++ "\n" ++ rlpListCountItemsFunction ++ "\n" ++
    mptBoundedDecodeLeafFunction ++ "\n.Lmbdlp_done:"
  dataAsm := ".section .data\n.balign 8\nbsr_builder_witness_value_max:\n  .dword " ++ toString bsrMptNodeMaxBytes
}

/-- Exercise extension rebuilding with a raw 32-byte child hash. This is the
    non-inline case that must add the RLP string prefix before the generic
    extension encoder sees the child reference. -/
def ziskMptBoundedEncodeExtensionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, mbee_frame; li t1, 3; sd t1, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(t0); li t1, 1; sb t1, " ++ toString bsrMptFrameExtensionPathOffset ++ "(t0); li t1, 2; sb t1, " ++ toString (bsrMptFrameExtensionPathOffset + 1) ++ "(t0); li t1, 3; sb t1, " ++ toString (bsrMptFrameExtensionPathOffset + 2) ++ "(t0); la t1, mbee_child; sd t1, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(t0); li t1, 32; sd t1, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(t0)\n" ++
  "  la t1, mbee_child; li t2, 0\n" ++
  ".Lmbeep_fill:\n" ++
  "  li t3, 32; beq t2, t3, .Lmbeep_call; sb t2, 0(t1); addi t1, t1, 1; addi t2, t2, 1; j .Lmbeep_fill\n" ++
  ".Lmbeep_call:\n" ++
  "  la a0, mbee_frame; la a1, mbee_node; la a2, mbee_ref; la a3, mbee_ref_len; jal ra, mpt_bounded_encode_extension; mv s0, a0; li t0, 0xa0010000; sd s0, 0(t0); bnez s0, .Lmbeep_done; # node length is fixed by this KAT's known encoding\n" ++
  "  li t2, 37; sd t2, 8(t0); la t1, mbee_ref_len; ld t2, 0(t1); sd t2, 16(t0); la t1, mbee_node; addi t0, t0, 24; li t2, 37\n" ++
  ".Lmbeep_copy_node:\n" ++
  "  beqz t2, .Lmbeep_copy_ref_start; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbeep_copy_node\n" ++
  ".Lmbeep_copy_ref_start:\n" ++
  "  la t1, mbee_ref; li t2, 32\n" ++
  ".Lmbeep_copy_ref:\n" ++
  "  beqz t2, .Lmbeep_done; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbeep_copy_ref\n"

def ziskMptBoundedEncodeExtensionDataSection : String :=
  ".section .bss\n.balign 8\nmbee_frame:\n  .zero " ++ toString bsrMptBuilderFrameBytes ++
  "\nmbee_child:\n  .zero 32\nmbee_node:\n  .zero 1024\nmbee_ref:\n  .zero 32\nmbee_ref_len:\n  .zero 8\n" ++
  ziskMptExtensionNodeEncodeDataSection ++ "\n" ++ ziskMptBoundedNodeRefDataSection

def ziskMptBoundedEncodeExtensionProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedEncodeExtensionPrologue ++ "\n" ++
    hpEncodeNibblesFunction ++ "\n" ++ rlpEncodeBytesFunction ++ "\n" ++
    rlpEncodeListPrefixFunction ++ "\n" ++ mptExtensionNodeEncodeFunction ++ "\n" ++
    zkvmKeccak256Function ++ "\n" ++ mptBoundedNodeRefFunction ++ "\n" ++
    mptBoundedEncodeExtensionFunction ++ "\n.Lmbeep_done:"
  dataAsm := ziskMptBoundedEncodeExtensionDataSection
}

/-- End-to-end probe for the currently supported exact-leaf replacement path.
    Input is `witness_len:u64`, old root, 64-nibble key, value length/value,
    descriptor mode, then one SSZ witness-state section. -/
def ziskMptBoundedStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld s0, 8(t0); addi s1, t0, 16; addi s2, t0, 48; ld s3, 112(t0); addi s4, t0, 120; ld s5, 128(t0); addi s6, t0, 136\n" ++
  "  la t1, mbsr_desc; sd s2, 0(t1); li t2, 64; sd t2, 8(t1); sd s4, 16(t1); sd s3, 24(t1); sd s5, 32(t1)\n" ++
  "  mv a0, s1; mv a1, s6; mv a2, s0; la a3, mbsr_desc; li a4, 1; la a5, mbsr_out; jal ra, mpt_bounded_state_root; mv s6, a0\n" ++
  "  li t0, 0xa0010000; sd s6, 0(t0); bnez s6, .Lmbsrp_done; la t1, mbsr_out; addi t0, t0, 8; li t2, 32\n" ++
  ".Lmbsrp_copy:\n  beqz t2, .Lmbsrp_done; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbsrp_copy\n"

def ziskMptBoundedStateRootDataSection : String :=
  ".section .bss\n.balign 8\nmbsr_desc:\n  .zero 40\nmbsr_out:\n  .zero 32\n" ++
  "bsr_sort_ranges:\n  .zero " ++ toString (bsrMptSortRangeStackCapacity * bsrMptSortRangeFrameBytes) ++ "\n" ++
  "bsr_builder_frames:\n  .zero " ++ toString (bsrMptBuilderFrameCapacity * bsrMptBuilderFrameBytes) ++ "\n" ++
  "bsr_builder_node:\n  .zero " ++ toString bsrMptBuilderNodeScratchBytes ++ "\n" ++
  "bsr_builder_result_ref:\n  .zero " ++ toString bsrMptFrameChildRefBytes ++ "\nbsr_builder_result_len:\n  .zero 8\nbsr_builder_value_max:\n  .zero 8\nbsr_builder_witness_value_max:\n  .zero 8\n" ++
  ziskWitnessLookupByHashDataSection ++ "\n" ++ ziskMptLeafNodeEncodeFromNibblesDataSection ++ "\n" ++
  ziskMptExtensionNodeEncodeDataSection

def ziskMptBoundedStateRootProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedStateRootPrologue ++ "\n" ++
    hpEncodeNibblesFunction ++ "\n" ++ rlpEncodeBytesFunction ++ "\n" ++ rlpItemSizeFunction ++ "\n" ++
    rlpEncodeListPrefixFunction ++ "\n" ++ mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
    mptExtensionNodeEncodeFunction ++ "\n" ++ zkvmKeccak256Function ++ "\n" ++
    witnessLookupByHashFunction ++ "\n" ++ rlpListNthItemFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++ mptBoundedBuilderFrontEndFunction ++ "\n.Lmbsrp_done:"
  dataAsm := ziskMptBoundedStateRootDataSection
}

/-- Storage-root variant of the bounded-root probe. It reserves a fixed
    40-byte input value field so its KAT can exercise the 33-byte full-uint256
    RLP encoding; it otherwise selects the storage wrapper, whose decoded
    witness leaves retain the node-sized bound. -/
def ziskMptBoundedStorageRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld s0, 8(t0); addi s1, t0, 16; addi s2, t0, 48; ld s3, 112(t0); addi s4, t0, 120; ld s5, 160(t0); addi s6, t0, 168\n" ++
  "  la t1, mbsr_desc; sd s2, 0(t1); li t2, 64; sd t2, 8(t1); sd s4, 16(t1); sd s3, 24(t1); sd s5, 32(t1)\n" ++
  "  mv a0, s1; mv a1, s6; mv a2, s0; la a3, mbsr_desc; li a4, 1; la a5, mbsr_out; jal ra, mpt_bounded_storage_root; mv s6, a0\n" ++
  "  li t0, 0xa0010000; sd s6, 0(t0); bnez s6, .Lmbstrp_done; la t1, mbsr_out; addi t0, t0, 8; li t2, 32\n" ++
  ".Lmbstrp_copy:\n  beqz t2, .Lmbstrp_done; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbstrp_copy\n"

def ziskMptBoundedStorageRootProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedStorageRootPrologue ++ "\n" ++
    hpEncodeNibblesFunction ++ "\n" ++ rlpEncodeBytesFunction ++ "\n" ++ rlpItemSizeFunction ++ "\n" ++
    rlpEncodeListPrefixFunction ++ "\n" ++ mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
    mptExtensionNodeEncodeFunction ++ "\n" ++ zkvmKeccak256Function ++ "\n" ++
    witnessLookupByHashFunction ++ "\n" ++ rlpListNthItemFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++ mptBoundedBuilderFrontEndFunction ++ "\n.Lmbstrp_done:"
  dataAsm := ziskMptBoundedStateRootDataSection
}

/-- Two-descriptor bounded-root probe. Descriptor modes are explicit so the
    KATs cover grouped insertions and an existing-leaf update sharing its radix
    slot with a new insertion. -/
def ziskMptBoundedMissingGroupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld s0, 8(t0); addi s1, t0, 16; addi s2, t0, 48; addi s3, t0, 112; addi s4, t0, 120; addi s5, t0, 184; ld t3, 192(t0); ld t4, 200(t0); addi s6, t0, 208\n" ++
  "  la t1, mbsmg_desc; sd s2, 0(t1); li t2, 64; sd t2, 8(t1); sd s3, 16(t1); li t2, 1; sd t2, 24(t1); sd t3, 32(t1); addi t1, t1, 40; sd s4, 0(t1); li t2, 64; sd t2, 8(t1); sd s5, 16(t1); li t2, 1; sd t2, 24(t1); sd t4, 32(t1)\n" ++
  "  mv a0, s1; mv a1, s6; mv a2, s0; la a3, mbsmg_desc; li a4, 2; la a5, mbsmg_out; jal ra, mpt_bounded_state_root; mv s6, a0\n" ++
  "  li t0, 0xa0010000; sd s6, 0(t0); bnez s6, .Lmbsmg_done; la t1, mbsmg_out; addi t0, t0, 8; li t2, 32\n" ++
  ".Lmbsmg_copy:\n  beqz t2, .Lmbsmg_done; lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lmbsmg_copy\n"

def ziskMptBoundedMissingGroupDataSection : String :=
  ".section .bss\n.balign 8\nmbsmg_desc:\n  .zero 80\nmbsmg_out:\n  .zero 32\n" ++
  "bsr_sort_ranges:\n  .zero " ++ toString (bsrMptSortRangeStackCapacity * bsrMptSortRangeFrameBytes) ++ "\n" ++
  "bsr_builder_frames:\n  .zero " ++ toString (bsrMptBuilderFrameCapacity * bsrMptBuilderFrameBytes) ++ "\n" ++
  "bsr_builder_node:\n  .zero " ++ toString bsrMptBuilderNodeScratchBytes ++ "\n" ++
  "bsr_builder_result_ref:\n  .zero " ++ toString bsrMptFrameChildRefBytes ++ "\nbsr_builder_result_len:\n  .zero 8\nbsr_builder_value_max:\n  .zero 8\nbsr_builder_witness_value_max:\n  .zero 8\n" ++
  ziskWitnessLookupByHashDataSection ++ "\n" ++ ziskMptLeafNodeEncodeFromNibblesDataSection ++ "\n" ++
  ziskMptExtensionNodeEncodeDataSection

def ziskMptBoundedMissingGroupProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptBoundedMissingGroupPrologue ++ "\n" ++
    hpEncodeNibblesFunction ++ "\n" ++ rlpEncodeBytesFunction ++ "\n" ++ rlpItemSizeFunction ++ "\n" ++
    rlpEncodeListPrefixFunction ++ "\n" ++ mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
    mptExtensionNodeEncodeFunction ++ "\n" ++ zkvmKeccak256Function ++ "\n" ++
    witnessLookupByHashFunction ++ "\n" ++ rlpListNthItemFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++ mptBoundedBuilderFrontEndFunction ++ "\n.Lmbsmg_done:"
  dataAsm := ziskMptBoundedMissingGroupDataSection
}

end EvmAsm.Codegen
