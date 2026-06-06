/-
  EvmAsm.Codegen.Programs.MptWitnessLookup

  Witness lookup helpers used by MPT and state/code proof programs.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.MptWitnessIndex

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## witness_lookup_by_hash -- PR-K19 (linear-scan flavour)

    Find the entry in an SSZ list section whose keccak256 digest
    matches a caller-supplied target hash. Returns the matched
    entry's (offset, length) within the section, or status=1 on
    miss.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.state /
                    witness.codes shape)
      a1 (input)  : section_len (0 ⇒ guaranteed miss)
      a2 (input)  : 32-byte target hash ptr
      a3 (input)  : u64 out ptr (matched entry's byte offset
                    within the section; meaningful only on hit)
      a4 (input)  : u64 out ptr (matched entry's byte length;
                    meaningful only on hit)
      ra (input)  : return
      a0 (output) : 0 on hit, 1 on miss

    Walks every element computing `keccak256(element_bytes)`
    until either a match is found or the list is exhausted.

    The linear fallback is deliberately capped at the default 64 KiB
    witness-section budget. Large stateless-verdict runs build a sorted
    NodeDb index once via `witness_index_build`; when the `(section_ptr,len)`
    matches that index this routine uses binary search instead of rescanning.
    The index is deterministic and sorted by the full 32-byte hash, not an
    attacker-shaped hash bucket chain. -/
def witnessLookupByHashFunction : String :=
  "witness_lookup_by_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # target_hash ptr\n" ++
  "  mv s3, a3                  # out_offset ptr\n" ++
  "  mv s4, a4                  # out_length ptr\n" ++
  "  la t0, widx_enabled\n" ++
  "  ld t0, 0(t0)\n" ++
  "  beqz t0, .Lwlh_linear\n" ++
  "  la t0, widx_section_ptr\n" ++
  "  ld t0, 0(t0)\n" ++
  "  bne s0, t0, .Lwlh_linear\n" ++
  "  la t0, widx_section_len\n" ++
  "  ld t0, 0(t0)\n" ++
  "  bne s1, t0, .Lwlh_linear\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  jal ra, witness_lookup_by_hash_indexed\n" ++
  "  j .Lwlh_ret\n" ++
  ".Lwlh_linear:\n" ++
  "  beqz s1, .Lwlh_miss        # empty section ⇒ miss\n" ++
  "  li t0, 65536               # linear-scan budget: default BSR witness cap\n" ++
  "  bgtu s1, t0, .Lwlh_miss    # larger witnesses need the indexed NodeDb path\n" ++
  "  lwu t0, 0(s0)              # first inner offset = 4 * N\n" ++
  "  srli s5, t0, 2             # s5 = N\n" ++
  "  li s6, 0                   # s6 = i\n" ++
  ".Lwlh_loop:\n" ++
  "  beq s6, s5, .Lwlh_miss\n" ++
  "  # Compute element i bounds.\n" ++
  "  slli t0, s6, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lwlh_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwlh_have_end\n" ++
  ".Lwlh_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lwlh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, wlh_scratch_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Compare scratch_hash vs target_hash.\n" ++
  "  la t0, wlh_scratch_hash\n" ++
  "  mv t1, s2\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwlh_no_match\n" ++
  "  # Match. Recompute (offset, length) from i (clobbered above).\n" ++
  "  slli t0, s6, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  sd t2, 0(s3)               # *out_offset = inner_off_i\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lwlh_last_len\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  sub t4, t4, t2             # length = inner_off_{i+1} - inner_off_i\n" ++
  "  j .Lwlh_store_len\n" ++
  ".Lwlh_last_len:\n" ++
  "  sub t4, s1, t2             # length = section_len - inner_off_i\n" ++
  ".Lwlh_store_len:\n" ++
  "  sd t4, 0(s4)\n" ++
  "  li a0, 0                   # hit\n" ++
  "  j .Lwlh_ret\n" ++
  ".Lwlh_no_match:\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lwlh_loop\n" ++
  ".Lwlh_miss:\n" ++
  "  li a0, 1                   # miss\n" ++
  ".Lwlh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  witnessIndexFunctions

/-- `zisk_witness_lookup_by_hash`: probe BuildUnit. Reads
    (section_len, target_hash, section_bytes) from host input,
    writes (status, offset, length) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..40 : target_hash (32 bytes)
      bytes 40..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64; 0 hit, 1 miss)
      bytes  8..16 : matched entry offset within section (u64)
      bytes 16..24 : matched entry length (u64) -/
def ziskWitnessLookupByHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a2, a5, 16             # target_hash ptr\n" ++
  "  addi a0, a5, 48             # section ptr\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  # Pre-zero offset/length so a miss surfaces as zeros.\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lwlh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwlh_pdone:"

def ziskWitnessLookupByHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessLookupByHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessLookupByHashPrologue
  dataAsm     := ziskWitnessLookupByHashDataSection
}

/-- `zisk_witness_lookup_by_hash_indexed`: same probe contract as
    `zisk_witness_lookup_by_hash`, but first builds the sorted witness index and
    then resolves the hash through the indexed path. OUTPUT+24 records the
    index-build status (0 = built, 1 = malformed/cap exceeded). -/
def ziskWitnessLookupByHashIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld s0, 8(a5)                # section_len\n" ++
  "  addi s1, a5, 16             # target_hash ptr\n" ++
  "  addi s2, a5, 48             # section ptr\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, witness_index_build\n" ++
  "  li t0, 0xa0010018\n" ++
  "  sd a0, 0(t0)                # index-build status at OUTPUT + 24\n" ++
  "  bnez a0, .Lwlhi_done\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # lookup status at OUTPUT + 0\n" ++
  ".Lwlhi_done:\n" ++
  "  j .Lwlhi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwlhi_pdone:"

def ziskWitnessLookupByHashIndexedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessLookupByHashIndexedPrologue
  dataAsm     := ziskWitnessLookupByHashDataSection
}

end EvmAsm.Codegen
