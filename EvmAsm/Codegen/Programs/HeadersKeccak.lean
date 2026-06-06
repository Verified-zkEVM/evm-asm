/-
  EvmAsm.Codegen.Programs.HeadersKeccak

  SSZ-list-of-headers Keccak walk + parent-hash linkage utilities
  carved out of `EvmAsm.Codegen.Programs` per the file-size hard
  cap. Hosts:

    K15  headers_keccak_chain     (walk + per-element keccak)
    K16  headers_keccak_array     (write each digest)
    K17  headers_parent_hash      (RLP-walk to parent_hash field)
    K18  headers_validate_chain   (parent_hash chain check)
    K94  header_validate_parent_hash
    K96  header_chain_walk_step

  All six iterate over a contiguous header-bytes section and call
  `zkvm_keccak256` (from `HashBridge.lean`) plus the
  `headers_parent_hash` RLP-walk; no other inter-cluster deps.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## headers_keccak_chain -- PR-K15 walk an SSZ list section,
    keccak each element, return the last digest + count.

    Walks the SSZ inner-offset table to derive per-element
    bounds (same parsing shape as the SSZ list-merkleize work),
    then calls `zkvm_keccak256(el_i_start, el_i_len, out_ptr)`
    for each element. The output buffer is overwritten on every
    iteration; after the loop, it holds the LAST element's
    digest. Returns the element count `N` in `a0`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (read-only)
      a1 (input)  : section_len (0 ⇒ empty list)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *a2 : keccak256(element[N-1]) if N > 0, else 0.

    No per-element scratch; works for any N. -/
def headersKeccakChainFunction : String :=
  "headers_keccak_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = output ptr\n" ++
  "  beqz s1, .Lhkc_n0          # empty section ⇒ N = 0\n" ++
  "  lwu t0, 0(s0)              # offset_0 = 4 * N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhkc_loop:\n" ++
  "  beq s4, s3, .Lhkc_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhkc_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhkc_have_end\n" ++
  ".Lhkc_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhkc_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s2                  # output (overwritten each iter)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhkc_loop\n" ++
  ".Lhkc_n0:\n" ++
  "  sd zero,  0(s2)\n" ++
  "  sd zero,  8(s2)\n" ++
  "  sd zero, 16(s2)\n" ++
  "  sd zero, 24(s2)\n" ++
  "  li s3, 0                   # N = 0\n" ++
  ".Lhkc_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_chain`: probe BuildUnit that reads an
    SSZ list section from host input and writes the count + last
    digest to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : N (u64 LE)
      bytes  8..40 : keccak256(element[N-1]) or 0 if N=0 -/
def ziskHeadersKeccakChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # last_hash output (OUTPUT + 8)\n" ++
  "  jal ra, headers_keccak_chain\n" ++
  "  li t0, 0xa0010000           # write N at OUTPUT + 0\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhkc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakChainFunction ++ "\n" ++
  ".Lhkc_pdone:"

def ziskHeadersKeccakChainDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakChainPrologue
  dataAsm     := ziskHeadersKeccakChainDataSection
}

/-! ## headers_keccak_array -- PR-K16 walk SSZ list section,
    keccak each element, store every digest in caller table.

    Sibling of `headers_keccak_chain` (PR-K15): same SSZ-list
    parsing loop, but each iteration writes the digest to
    `table[i]` instead of overwriting the same slot. Returns the
    element count `N`.

    Calling convention:
      a0 (input)  : section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : table base ptr (must hold N*32 bytes)
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *(table + 32*i) = keccak256(element[i])
        for each i in 0..N. -/
def headersKeccakArrayFunction : String :=
  "headers_keccak_array:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = table base\n" ++
  "  beqz s1, .Lhka_n0\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhka_loop:\n" ++
  "  beq s4, s3, .Lhka_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhka_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhka_have_end\n" ++
  ".Lhka_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhka_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  slli t0, s4, 5             # 32*i\n" ++
  "  add a2, s2, t0             # a2 = &table[i]\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhka_loop\n" ++
  ".Lhka_n0:\n" ++
  "  li s3, 0\n" ++
  ".Lhka_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_array`: probe BuildUnit that reads an
    SSZ list section from host input and writes (count, table)
    to OUTPUT, capped at N ≤ 7 to fit ziskemu's 256-byte output
    channel.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8     : N (u64 LE)
      bytes  8..8+32*N : N digests of 32 bytes each -/
def ziskHeadersKeccakArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # table at OUTPUT + 8\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write N at OUTPUT + 0\n" ++
  "  j .Lhka_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  ".Lhka_pdone:"

def ziskHeadersKeccakArrayDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakArrayPrologue
  dataAsm     := ziskHeadersKeccakArrayDataSection
}

/-! ## headers_parent_hash -- PR-K17 RLP-walk to extract the
    first 32-byte field of an RLP-encoded Ethereum header
    (`parent_hash`).

    Skips the outer list prefix (0xc0..0xc0+55 short form, 0xf8
    1-byte-length, or 0xf9 2-byte-length forms), expects a
    0xa0 Bytes32 string prefix, then copies the 32 raw bytes
    to the caller's output.

    Calling convention:
      a0 (input)  : RLP-encoded header ptr (read-only)
      a1 (input)  : header byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 on success; 32 bytes at *a2 = parent_hash
        1 on RLP parse failure

    Pure register arithmetic; no scratch memory, no callee-saved
    registers used. Leaf-callable. -/
def headersParentHashFunction : String :=
  "headers_parent_hash:\n" ++
  "  # a0 = header ptr, a1 = header_len, a2 = out ptr\n" ++
  "  lbu t0, 0(a0)                # first byte\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lhph_fail      # not an RLP list (< 0xc0)\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lhph_short     # 0xc0..0xf7 → short list, 1-byte prefix\n" ++
  "  # long list: t0 in [0xf8..0xff].\n" ++
  "  # length_of_length = t0 - 0xf7. Outer prefix = 1 + length_of_length bytes.\n" ++
  "  li t1, 0xf7\n" ++
  "  sub t2, t0, t1               # length_of_length\n" ++
  "  li t3, 2                     # cap: support 0xf8 (LoL=1), 0xf9 (LoL=2)\n" ++
  "  bltu t3, t2, .Lhph_fail      # LoL > 2 → unsupported\n" ++
  "  addi t2, t2, 1               # prefix bytes = LoL + 1\n" ++
  "  add a0, a0, t2               # skip prefix\n" ++
  "  sub a1, a1, t2\n" ++
  "  j .Lhph_after_prefix\n" ++
  ".Lhph_short:\n" ++
  "  addi a0, a0, 1               # skip 1-byte prefix\n" ++
  "  addi a1, a1, -1\n" ++
  ".Lhph_after_prefix:\n" ++
  "  # Expect 0xa0 Bytes32 prefix.\n" ++
  "  li t0, 33\n" ++
  "  bltu a1, t0, .Lhph_fail      # not enough bytes for 0xa0 + 32\n" ++
  "  lbu t1, 0(a0)\n" ++
  "  li t2, 0xa0\n" ++
  "  bne t1, t2, .Lhph_fail       # not a Bytes32 string\n" ++
  "  # Copy 32 bytes from a0+1 to a2.\n" ++
  "  ld t0,  1(a0); sd t0,  0(a2)\n" ++
  "  ld t0,  9(a0); sd t0,  8(a2)\n" ++
  "  ld t0, 17(a0); sd t0, 16(a2)\n" ++
  "  ld t0, 25(a0); sd t0, 24(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lhph_fail:\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_headers_parent_hash`: probe BuildUnit that reads an
    RLP-encoded header from host input and writes
    `(status, parent_hash)` to OUTPUT.
    Input layout:
      bytes  0.. 8 : header_len (u64)
      bytes  8..   : RLP-encoded header bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 = ok, 1 = parse fail)
      bytes  8..40 : parent_hash (32 bytes; meaningful only on
                     status=0; on failure, contains zeros) -/
def ziskHeadersParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # parent_hash output (OUTPUT + 8)\n" ++
  "  # Pre-zero output[8..40] so a parse failure surfaces as zeros.\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write status at OUTPUT + 0\n" ++
  "  j .Lhph_pdone\n" ++
  headersParentHashFunction ++ "\n" ++
  ".Lhph_pdone:"

def ziskHeadersParentHashDataSection : String :=
  ".section .data\n" ++
  "hph_scratch:\n" ++
  "  .zero 8"

def ziskHeadersParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersParentHashPrologue
  dataAsm     := ziskHeadersParentHashDataSection
}

/-! ## header_validate_parent_hash -- PR-K94

    Per-header parent-hash continuity check from `validate_header`
    in `forks/amsterdam/fork.py`:

      block_parent_hash = keccak256(rlp.encode(parent_header))
      if header.parent_hash != block_parent_hash:
          raise InvalidBlock

    The single-pair check that anchors a block to its parent. Used
    by `validate_header` directly; the multi-header walk in
    `validate_headers(headers, parent_header)` consists of K18-style
    pairwise iterations of exactly this primitive (K18 already
    handles the iteration via the SSZ digest table, but expects a
    pre-computed digest array; K94 is the standalone form that
    callers without that pipeline can use).

    Composes:
      - PR-K17 `headers_parent_hash`  — extract this header's
                                        parent_hash field (RLP[0])
      - PR-K3  `zkvm_keccak256`       — Keccak-f[1600] sponge

    Calling convention:
      a0 (input)  : this_header_rlp ptr
      a1 (input)  : this_header_rlp byte length
      a2 (input)  : parent_header_rlp ptr
      a3 (input)  : parent_header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : match — parent_hash field == keccak256(parent_rlp)
        1 : RLP parse failure of this_header (field 0 not 32 B)
        2 : mismatch — both decode/hash succeeded, values differ

    Uses 64 bytes of `.data` scratch (`hvph_claimed` 32 B +
    `hvph_computed` 32 B). -/
def headerValidateParentHashFunction : String :=
  "header_validate_parent_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # parent_rlp ptr (stash)\n" ++
  "  mv s1, a3                   # parent_rlp_len (stash)\n" ++
  "  # Step 1: extract this header's parent_hash (field 0).\n" ++
  "  la a2, hvph_claimed\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  beqz a0, .Lhvph_hash\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvph_ret\n" ++
  ".Lhvph_hash:\n" ++
  "  # Step 2: keccak256(parent_rlp) → hvph_computed.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, hvph_computed\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # zkvm_keccak256 always returns 0 (ZKVM_EOK).\n" ++
  "  # Step 3: byte-by-byte compare (32 bytes via 4 × dword).\n" ++
  "  la t0, hvph_claimed\n" ++
  "  la t1, hvph_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lhvph_diff\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvph_ret\n" ++
  ".Lhvph_diff:\n" ++
  "  li a0, 2\n" ++
  ".Lhvph_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_validate_parent_hash`: probe BuildUnit. Reads
    (this_len, parent_len, this_bytes ‖ parent_bytes) from host
    input, writes 8-byte status to OUTPUT.
    Input layout:
      bytes  0.. 8 : this_header_len
      bytes  8..16 : parent_header_len
      bytes 16..   : this_header_rlp ‖ parent_header_rlp -/
def ziskHeaderValidateParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # this_header_len\n" ++
  "  ld a3, 16(a4)               # parent_header_len\n" ++
  "  addi a0, a4, 24             # this_header_ptr\n" ++
  "  add a2, a0, a1              # parent_header_ptr\n" ++
  "  jal ra, header_validate_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhvph_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  ".Lhvph_pdone:"

def ziskHeaderValidateParentHashDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "hvph_claimed:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hvph_computed:\n" ++
  "  .zero 32"

def ziskHeaderValidateParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateParentHashPrologue
  dataAsm     := ziskHeaderValidateParentHashDataSection
}

/-! ## header_chain_walk_step -- PR-K96

    Per-step primitive for chain validation: given the previous
    block's hash and a candidate child header's RLP, verify
    `child.parent_hash == previous_hash` and compute
    `keccak256(child_rlp)` as the new running hash.

    A caller iterating over N headers does N calls; at the end
    `*new_hash` holds the latest block's hash, and any mid-chain
    mismatch returns status 2.

    PR-K18 `headers_validate_chain` already implements the chain
    walk on top of a pre-computed SSZ digest table; K96 is the
    standalone per-step that works without that pipeline (raw
    RLP-encoded headers in, no precomputed digest array required).

    Composes:
      - PR-K17 `headers_parent_hash` — extract child's parent_hash
      - PR-K3  `zkvm_keccak256`      — compute child's hash

    Calling convention:
      a0 (input)  : prev_hash ptr (32 B, caller-supplied)
      a1 (input)  : child_header_rlp ptr
      a2 (input)  : child_header_rlp byte length
      a3 (input)  : 32-byte out ptr (receives child's hash on
                    success, zeros on failure)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : child header parse failed (field 0 not 32 B)
        2 : mismatch — child.parent_hash != prev_hash

    Uses 32 bytes of `.data` scratch (`hcws_claimed`). -/
def headerChainWalkStepFunction : String :=
  "header_chain_walk_step:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # prev_hash ptr\n" ++
  "  mv s1, a1                   # child_rlp ptr\n" ++
  "  mv s2, a2                   # child_len\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  # Step 1: extract child's parent_hash → hcws_claimed.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  la a2, hcws_claimed\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  beqz a0, .Lhcws_compare\n" ++
  "  li a0, 1\n" ++
  "  j .Lhcws_zero_out\n" ++
  ".Lhcws_compare:\n" ++
  "  # Compare prev_hash (s0) to claimed (hcws_claimed) byte-by-byte.\n" ++
  "  la t0, hcws_claimed\n" ++
  "  ld t1,  0(s0); ld t2,  0(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1,  8(s0); ld t2,  8(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1, 16(s0); ld t2, 16(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1, 24(s0); ld t2, 24(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  # Match — compute child hash → *out.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcws_ret\n" ++
  ".Lhcws_diff:\n" ++
  "  li a0, 2\n" ++
  ".Lhcws_zero_out:\n" ++
  "  # Zero the output on any failure.\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  ".Lhcws_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_header_chain_walk_step`: probe BuildUnit. Reads
    (child_len, prev_hash[32], child_rlp) from host input, writes
    (status, child_hash[32]) to OUTPUT.
    Input layout:
      bytes  0.. 8 : child_header_len
      bytes  8..40 : prev_hash (32 B)
      bytes 40..   : child_header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : child block hash on success, zero otherwise -/
def ziskHeaderChainWalkStepPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a2, 8(a4)                # child_header_len\n" ++
  "  addi a0, a4, 16             # prev_hash ptr\n" ++
  "  addi a1, a4, 48             # child_rlp ptr\n" ++
  "  li a3, 0xa0010008           # child_hash output (OUTPUT + 8)\n" ++
  "  jal ra, header_chain_walk_step\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhcws_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerChainWalkStepFunction ++ "\n" ++
  ".Lhcws_pdone:"

def ziskHeaderChainWalkStepDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "hcws_claimed:\n" ++
  "  .zero 32"

def ziskHeaderChainWalkStepProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderChainWalkStepPrologue
  dataAsm     := ziskHeaderChainWalkStepDataSection
}

/-! ## K99 / K126 / K127 address-derivation cluster — moved to `Programs/Address.lean` (file-size hard cap). -/
/-! ## K100 mpt_account_path_nibbles — moved to `Programs/Mpt.lean` (file-size hard cap). -/


/-! ## headers_validate_chain -- PR-K18 parent_hash chain check

    Composes PR-K16 `headers_keccak_array` (build per-header
    digest table) with PR-K17 `headers_parent_hash` (RLP-extract
    each header's first 32-byte field) to verify the
    `validate_headers` invariant:

        header[i].parent_hash == keccak256(header[i-1])
            for every i in 1..N

    matches the Python check in
    `execution-specs/.../stateless.py::validate_headers`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.headers)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : 8-byte output ptr (receives N as u64 LE)
      ra (input)  : return
      a0 (output) : 0 on success (chain valid) or N ≤ 1
                    1 on mismatch / RLP-decode failure

    Walks the list using the same SSZ inner-offset table as
    PR-K15/K16. Caps at N ≤ 256 (matches `MAX_WITNESS_HEADERS`).

    Uses two `.data` scratch buffers:
      vh_keccak_table          : 256 × 32 = 8 KB
      vh_extracted_parent_hash : 32 B
-/
def headersValidateChainFunction : String :=
  "headers_validate_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = N out ptr\n" ++
  "  # Match execution-specs validate_headers: witness headers are capped at\n" ++
  "  # 256. Enforce this before filling the fixed 256-entry keccak table.\n" ++
  "  beqz s1, .Lvh_count_ok\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli t0, t0, 2             # first inner offset = 4*N\n" ++
  "  li t1, 256\n" ++
  "  bgtu t0, t1, .Lvh_fail\n" ++
  ".Lvh_count_ok:\n" ++
  "  # Step 1: keccak each header into vh_keccak_table.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vh_keccak_table\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  mv s3, a0                  # s3 = N\n" ++
  "  sd s3, 0(s2)               # *N_out = N\n" ++
  "  # If N ≤ 1, no chain links to check → ok.\n" ++
  "  li t0, 2\n" ++
  "  bltu s3, t0, .Lvh_ok\n" ++
  "  # Loop i = 1..N.\n" ++
  "  li s4, 1\n" ++
  ".Lvh_loop:\n" ++
  "  beq s4, s3, .Lvh_ok\n" ++
  "  # Find element i bounds from inner-offset table.\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lvh_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lvh_have_end\n" ++
  ".Lvh_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lvh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, vh_extracted_parent_hash\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  bnez a0, .Lvh_fail         # RLP parse failed\n" ++
  "  # Compare extracted parent_hash against vh_keccak_table[i-1].\n" ++
  "  la t0, vh_keccak_table\n" ++
  "  addi t1, s4, -1\n" ++
  "  slli t1, t1, 5             # (i-1) * 32\n" ++
  "  add t0, t0, t1             # &table[i-1]\n" ++
  "  la t1, vh_extracted_parent_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvh_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvh_fail\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lvh_loop\n" ++
  ".Lvh_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lvh_ret\n" ++
  ".Lvh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lvh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_validate_chain`: probe BuildUnit that reads an
    SSZ list of RLP-encoded headers from host input and writes
    (status, N) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 ok / 1 mismatch)
      bytes  8..16 : N (u64 LE; element count) -/
def ziskHeadersValidateChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # N out ptr (OUTPUT + 8)\n" ++
  "  jal ra, headers_validate_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lvh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  ".Lvh_pdone:"

def ziskHeadersValidateChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192                 # 256 × 32-byte digests\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32"

def ziskHeadersValidateChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersValidateChainPrologue
  dataAsm     := ziskHeadersValidateChainDataSection
}


end EvmAsm.Codegen
