/-
  EvmAsm.Codegen.Programs.WitnessHeadersAllChainLinksValidate

  Batched full-chain validation over witness.headers.
  Iterates parent_idx = 0..N-2, verifies each consecutive
  chain link (keccak(headers[i]) == headers[i+1].parent_hash),
  and returns (valid_count, invalid_count) summing to N-1.

  Per-link version of #7276 expanded to a full-section walk.
  Lets the caller validate an entire witness.headers chain
  in one host round-trip.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_all_chain_links_validate

    Given a witness.headers SSZ list section, iterate every
    consecutive pair (headers[i], headers[i+1]) for
    i = 0..N-2 and check
      keccak(headers[i]) == headers[i+1].parent_hash.

    Returns the per-pair tallies:
      * valid_count   = pairs where the link verifies
      * invalid_count = pairs where the comparison failed
                        OR the child header's parent_hash
                        couldn't be RLP-extracted (parse fail
                        or wrong size).

    Invariant: valid_count + invalid_count = max(N - 1, 0).

    Distinct from #7276 which validates ONE link by index;
    this one walks the entire chain at once.

    Use cases:
      * Full-chain consistency audit: confirm the entire
        witness.headers run is internally linked before
        using any of its state_roots downstream.
      * Witness sanity: detect SSZ-encoded witnesses where
        the chain is broken or partially garbled before
        spending compute on state-trie walks.
      * Producer compliance: relayer ships an alleged chain
        of headers; this primitive surfaces how many links
        survive validation.

    Calling convention (4 args):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : u64 valid_count out ptr
      a3 (input)  : u64 invalid_count out ptr
      ra (input)  : return

      a0 (output) : 0 (always; per-link parse failures
                    counted into invalid_count, not
                    propagated)
-/
def witnessHeadersAllChainLinksValidateFunction : String :=
  "witness_headers_all_chain_links_validate:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # valid_count out\n" ++
  "  mv s3, a3                  # invalid_count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  sd zero, 0(s3)\n" ++
  "  beqz s1, .Lwhal_done       # empty section -> 0 / 0\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  li t1, 1\n" ++
  "  bleu s4, t1, .Lwhal_done   # N <= 1 -> 0 / 0\n" ++
  "  li s5, 0                   # s5 = i (parent index)\n" ++
  ".Lwhal_loop:\n" ++
  "  addi s6, s5, 1             # s6 = i + 1\n" ++
  "  beq s6, s4, .Lwhal_done\n" ++
  "  # Compute parent (i) bounds.\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s7, s0, t2             # parent start\n" ++
  "  slli t3, s6, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # parent end = child start\n" ++
  "  sub s8, t4, s7             # parent len\n" ++
  "  mv s9, t4                  # child start\n" ++
  "  # Compute child (i+1) bounds.\n" ++
  "  addi t5, s6, 1\n" ++
  "  beq t5, s4, .Lwhal_use_end\n" ++
  "  slli t5, t5, 2\n" ++
  "  add t5, s0, t5\n" ++
  "  lwu t0, 0(t5)\n" ++
  "  add t0, s0, t0\n" ++
  "  j .Lwhal_have_end\n" ++
  ".Lwhal_use_end:\n" ++
  "  add t0, s0, s1\n" ++
  ".Lwhal_have_end:\n" ++
  "  sub s10, t0, s9            # child len\n" ++
  "  # Extract child.parent_hash.\n" ++
  "  mv a0, s9\n" ++
  "  mv a1, s10\n" ++
  "  la a2, whal_child_ph\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  bnez a0, .Lwhal_count_invalid\n" ++
  "  # keccak(parent_rlp).\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, whal_parent_keccak\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, whal_child_ph\n" ++
  "  la t1, whal_parent_keccak\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwhal_count_invalid\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwhal_count_invalid\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwhal_count_invalid\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwhal_count_invalid\n" ++
  "  # Valid.\n" ++
  "  ld t4, 0(s2)\n" ++
  "  addi t4, t4, 1\n" ++
  "  sd t4, 0(s2)\n" ++
  "  j .Lwhal_step\n" ++
  ".Lwhal_count_invalid:\n" ++
  "  ld t4, 0(s3)\n" ++
  "  addi t4, t4, 1\n" ++
  "  sd t4, 0(s3)\n" ++
  ".Lwhal_step:\n" ++
  "  mv s5, s6\n" ++
  "  j .Lwhal_loop\n" ++
  ".Lwhal_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_witness_headers_all_chain_links_validate`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..   : witness.headers section bytes
    Output layout (24 bytes):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : valid_count
      bytes 16..24 : invalid_count -/
def ziskWitnessHeadersAllChainLinksValidatePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # witness.headers ptr\n" ++
  "  li a2, 0xa0010008           # valid_count out\n" ++
  "  li a3, 0xa0010010           # invalid_count out\n" ++
  "  jal ra, witness_headers_all_chain_links_validate\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhal_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  witnessHeadersAllChainLinksValidateFunction ++ "\n" ++
  ".Lwhal_pdone:"

def ziskWitnessHeadersAllChainLinksValidateDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "whal_child_ph:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "whal_parent_keccak:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
