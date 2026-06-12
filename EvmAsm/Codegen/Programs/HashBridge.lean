/-
  EvmAsm.Codegen.Programs.HashBridge

  Standalone Lean strings for the two host-hash bridge stubs:
  - `zkvm_sha256` — Merkle-Damgård wrapper around ziskemu's SHA-256
                    permutation accelerator
  - `zkvm_keccak256` — sponge wrapper around the Keccak-f[1600]
                    permutation accelerator

  Both are pure-text shims used by every higher-level BuildUnit
  that wants to inline a hash routine. Lifted out of
  `EvmAsm.Codegen.Programs` so SSZ/MPT/state-trie consumers can
  import them without pulling the whole registry hub.
-/

namespace EvmAsm.Codegen

def zkvmSha256Function : String :=
  "zkvm_sha256:\n" ++
  "  # save callee-saved regs (s0..s5)\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd s0, 0(sp)\n" ++
  "  sd s1, 8(sp)\n" ++
  "  sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp)\n" ++
  "  sd s4, 32(sp)\n" ++
  "  sd s5, 40(sp)\n" ++
  "  # s0 = state ptr; s1 = data ptr; s2 = remaining len;\n" ++
  "  # s3 = output ptr (= caller's a2); s4 = bit-length;\n" ++
  "  # s5 = sha256_input buffer base.\n" ++
  "  la s0, sha256_w_state\n" ++
  "  mv s1, a0\n" ++
  "  mv s2, a1\n" ++
  "  mv s3, a2\n" ++
  "  slli s4, a1, 3\n" ++
  "  la s5, sha256_w_input\n" ++
  "  # initialise state from IV (LE-u32 packed, 4 × u64)\n" ++
  "  la t0, sha256_w_iv\n" ++
  "  ld t1, 0(t0);  sd t1, 0(s0)\n" ++
  "  ld t1, 8(t0);  sd t1, 8(s0)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s0)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s0)\n" ++
  "  # absorb full 64-byte blocks\n" ++
  ".Lzkv_sha_loop:\n" ++
  "  li t0, 64\n" ++
  "  blt s2, t0, .Lzkv_sha_final\n" ++
  "  ld t0, 0(s1);  sd t0, 0(s5)\n" ++
  "  ld t0, 8(s1);  sd t0, 8(s5)\n" ++
  "  ld t0, 16(s1); sd t0, 16(s5)\n" ++
  "  ld t0, 24(s1); sd t0, 24(s5)\n" ++
  "  ld t0, 32(s1); sd t0, 32(s5)\n" ++
  "  ld t0, 40(s1); sd t0, 40(s5)\n" ++
  "  ld t0, 48(s1); sd t0, 48(s5)\n" ++
  "  ld t0, 56(s1); sd t0, 56(s5)\n" ++
  "  la a0, sha256_w_params\n" ++
  "  .4byte 0x80552073           # csrs 0x805, a0\n" ++
  "  addi s1, s1, 64\n" ++
  "  addi s2, s2, -64\n" ++
  "  j .Lzkv_sha_loop\n" ++
  ".Lzkv_sha_final:\n" ++
  "  # zero the input buffer\n" ++
  "  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)\n" ++
  "  # byte-copy remaining s2 bytes from s1 to s5\n" ++
  "  mv t0, s5\n" ++
  "  mv t1, s1\n" ++
  "  mv t2, s2\n" ++
  ".Lzkv_sha_bcopy:\n" ++
  "  beqz t2, .Lzkv_sha_pad\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb  t3, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lzkv_sha_bcopy\n" ++
  ".Lzkv_sha_pad:\n" ++
  "  # write 0x80 at offset s2 in input buffer\n" ++
  "  add t0, s5, s2\n" ++
  "  li  t1, 0x80\n" ++
  "  sb  t1, 0(t0)\n" ++
  "  # if remainder < 56: single final block; else two-block path\n" ++
  "  li  t0, 56\n" ++
  "  blt s2, t0, .Lzkv_sha_writelen\n" ++
  "  # two-block: compress this block (data + 0x80, no length yet)\n" ++
  "  la  a0, sha256_w_params\n" ++
  "  .4byte 0x80552073\n" ++
  "  # zero input buffer for the second (length-only) block\n" ++
  "  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)\n" ++
  ".Lzkv_sha_writelen:\n" ++
  "  # 8-byte BE bit-length at offset 56..64 of input buffer\n" ++
  "  addi t0, s5, 56\n" ++
  "  srli t1, s4, 56; sb t1, 0(t0)\n" ++
  "  srli t1, s4, 48; sb t1, 1(t0)\n" ++
  "  srli t1, s4, 40; sb t1, 2(t0)\n" ++
  "  srli t1, s4, 32; sb t1, 3(t0)\n" ++
  "  srli t1, s4, 24; sb t1, 4(t0)\n" ++
  "  srli t1, s4, 16; sb t1, 5(t0)\n" ++
  "  srli t1, s4,  8; sb t1, 6(t0)\n" ++
  "  sb   s4, 7(t0)\n" ++
  "  # compress final block\n" ++
  "  la  a0, sha256_w_params\n" ++
  "  .4byte 0x80552073\n" ++
  "  # squeeze: byte-swap each u32 of state into output\n" ++
  "  # output[i] = state[i ^ 3]   (reverses bytes within each 4-byte group)\n" ++
  "  li  t0, 0\n" ++
  ".Lzkv_sha_squeeze:\n" ++
  "  li  t1, 32\n" ++
  "  beq t0, t1, .Lzkv_sha_return\n" ++
  "  xori t2, t0, 3\n" ++
  "  add t3, s0, t2\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  add t5, s3, t0\n" ++
  "  sb  t4, 0(t5)\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lzkv_sha_squeeze\n" ++
  ".Lzkv_sha_return:\n" ++
  "  li  a0, 0\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def zkvmKeccak256Function : String :=
  "zkvm_keccak256:\n" ++
  "  # save s0/s1/s2/s4 (callee-saved per RV64 ABI)\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp)\n" ++
  "  sd s1, 8(sp)\n" ++
  "  sd s2, 16(sp)\n" ++
  "  sd s4, 24(sp)\n" ++
  "  # stash args (a0/a1/a2 get clobbered during the absorb loop)\n" ++
  "  mv s4, a0                # data ptr\n" ++
  "  mv s1, a1                # remaining length\n" ++
  "  mv s2, a2                # output ptr\n" ++
  "  la s0, zk3_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lzk3_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lzk3_zero\n" ++
  "  # absorb full blocks (rate = 136 bytes)\n" ++
  ".Lzk3_full:\n" ++
  "  li t4, 136\n" ++
  "  blt s1, t4, .Lzk3_final\n" ++
  "  mv t3, s0\n" ++
  "  mv t5, s4\n" ++
  "  li t6, 17\n" ++
  ".Lzk3_xor:\n" ++
  "  ld t0, 0(t5)\n" ++
  "  ld t1, 0(t3)\n" ++
  "  xor t1, t1, t0\n" ++
  "  sd t1, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t5, t5, 8\n" ++
  "  addi t6, t6, -1\n" ++
  "  bnez t6, .Lzk3_xor\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  addi s4, s4, 136\n" ++
  "  addi s1, s1, -136\n" ++
  "  j .Lzk3_full\n" ++
  ".Lzk3_final:\n" ++
  "  mv t3, s0\n" ++
  "  mv t5, s4\n" ++
  "  beqz s1, .Lzk3_pad\n" ++
  ".Lzk3_bxor:\n" ++
  "  lbu t0, 0(t5)\n" ++
  "  lbu t1, 0(t3)\n" ++
  "  xor t0, t0, t1\n" ++
  "  sb t0, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t5, t5, 1\n" ++
  "  addi s1, s1, -1\n" ++
  "  bnez s1, .Lzk3_bxor\n" ++
  ".Lzk3_pad:\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  xori t0, t0, 0x01\n" ++
  "  sb t0, 0(t3)\n" ++
  "  addi t3, s0, 135\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  xori t0, t0, 0x80\n" ++
  "  sb t0, 0(t3)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # squeeze 32 bytes to s2 (= output ptr)\n" ++
  "  ld t0, 0(s0);  sd t0, 0(s2)\n" ++
  "  ld t0, 8(s0);  sd t0, 8(s2)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s2)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s2)\n" ++
  "  # return ZKVM_EOK\n" ++
  "  li a0, 0\n" ++
  "  ld s0, 0(sp)\n" ++
  "  ld s1, 8(sp)\n" ++
  "  ld s2, 16(sp)\n" ++
  "  ld s4, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zkvm_keccak256_segments`: streaming keccak256 over the CONCATENATION of a list
    of (ptr,len) byte segments, without materializing the concatenation in one
    buffer. Same sponge as `zkvm_keccak256` (reuses `zk3_state` + the keccak-f
    permutation `.4byte 0x80052073`), but absorbs segment-by-segment, carrying the
    136-byte rate-block fill across segment boundaries in a register. This lets a
    caller hash `small_prefix || BIG_in_place_slice || small_suffix` (e.g. a tx
    signing RLP whose calldata is megabytes) by passing the big slice as one
    segment pointing straight into its source region -- O(1) extra memory, no copy,
    no input mutation, no fixed-buffer cap. Identical digest to the one-shot.

    Calling convention:
      a0 (input) : segments array ptr -- N×16 bytes, each = (u64 ptr, u64 len)
      a1 (input) : N (segment count; segments of len 0 are skipped)
      a2 (input) : 32-byte output hash ptr
      a0 (output): 0 (ZKVM_EOK)
    Byte-wise absorb (correctness-first); the keccak-f permutation dominates and
    is accelerated, so the per-byte XOR is cheap relative to the recovery. -/
def zkvmKeccak256SegmentsFunction : String :=
  "zkvm_keccak256_segments:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                # &segments[0]\n" ++
  "  mv s1, a1                # remaining segment count\n" ++
  "  mv s2, a2                # output ptr\n" ++
  "  la s3, zk3_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t0, s3; li t1, 25\n" ++
  ".Lkss_zero:\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lkss_zero\n" ++
  "  li s4, 0                 # rate-block fill (0..135), carried across segments\n" ++
  ".Lkss_seg:\n" ++
  "  beqz s1, .Lkss_pad\n" ++
  "  ld s5, 0(s0)             # segment ptr\n" ++
  "  ld s6, 8(s0)             # segment len\n" ++
  "  addi s0, s0, 16\n" ++
  "  addi s1, s1, -1\n" ++
  ".Lkss_byte:\n" ++
  "  beqz s6, .Lkss_seg\n" ++
  "  lbu t0, 0(s5)            # message byte\n" ++
  "  add t1, s3, s4           # &state[fill]\n" ++
  "  lbu t2, 0(t1); xor t2, t2, t0; sb t2, 0(t1)\n" ++
  "  addi s5, s5, 1; addi s6, s6, -1; addi s4, s4, 1\n" ++
  "  li t0, 136; bne s4, t0, .Lkss_byte\n" ++
  "  mv a0, s3\n" ++
  "  .4byte 0x80052073        # keccak-f on full rate block\n" ++
  "  li s4, 0\n" ++
  "  j .Lkss_byte\n" ++
  ".Lkss_pad:\n" ++
  "  add t1, s3, s4\n" ++
  "  lbu t2, 0(t1); xori t2, t2, 0x01; sb t2, 0(t1)   # pad start bit\n" ++
  "  addi t1, s3, 135\n" ++
  "  lbu t2, 0(t1); xori t2, t2, 0x80; sb t2, 0(t1)   # pad end bit\n" ++
  "  mv a0, s3\n" ++
  "  .4byte 0x80052073\n" ++
  "  ld t0, 0(s3);  sd t0, 0(s2)\n" ++
  "  ld t0, 8(s3);  sd t0, 8(s2)\n" ++
  "  ld t0, 16(s3); sd t0, 16(s2)\n" ++
  "  ld t0, 24(s3); sd t0, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

end EvmAsm.Codegen
