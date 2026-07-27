/-
  EvmAsm.Codegen.Programs.KeccakIncremental

  Resumable keccak256: `keccak_init` / `keccak_absorb` / `keccak_final`.

  ## Why these exist

  Every keccak entry point in the tree is ONE-SHOT. `zkvm_keccak256` hashes one
  buffer; `zkvm_keccak256_segments` hashes the concatenation of a (ptr,len) array
  without materialising it — but both zero the sponge on entry, so neither can be
  resumed across calls. A caller that must hash a byte string it is *generating*
  therefore has to materialise the whole string first, or describe it as a segment
  array, and both cost memory proportional to the output.

  These three entry points remove that constraint: the caller absorbs whatever it
  has produced so far, as often as it likes, and finalises once. Memory cost is the
  208-byte context, independent of the length hashed.

  ## General infrastructure, not a BAL detail

  Nothing here knows about block access lists, RLP, or any traversal. The first
  consumer is #10680's BAL rebuild, but incremental hashing is the kind of thing
  that recurs, so the API is deliberately shaped for any producer of bytes.

  ## The context is CALLER-SUPPLIED, and that is the important design decision

  `zk3_state` is a single global, and there are **16 call sites** of the one-shot
  routines in the emitted guest. Had these wrappers shared that global, any
  intervening one-shot call — a nested hash somewhere inside the caller's walk —
  would zero the sponge and silently corrupt an open incremental hash. The
  corruption would not fault; it would produce a clean, wrong digest.

  So the context is a caller-supplied pointer: 200 bytes of sponge state plus an
  8-byte rate-block fill offset. That makes these wrappers independent of the
  one-shot routines and of each other, so an interleaved or nested hash of any kind
  is harmless, and two incremental hashes can be open at once.

  **The one-shot routines are not modified, refactored, or reimplemented.** They
  keep `zk3_state` and their own control flow. This module only adds entry points.

  ## Conventions taken from the existing in-tree sponge

  Not re-derived — mirrored from `MptIndexedTrieRoot`'s `.Lmislh_absorb`, which is
  working streaming code:

  * rate is **136** bytes (keccak-256), state is 200 bytes (25 × u64);
  * absorb is byte-wise XOR into `state[fill]`, permuting whenever `fill` reaches
    136 and resetting `fill` to 0;
  * the permutation is the custom instruction `.4byte 0x80052073` with the **state
    pointer in `a0`**;
  * padding is `state[fill] ^= 0x01` then `state[135] ^= 0x80`, then one
    permutation — pre-NIST keccak padding, not SHA-3's `0x06`;
  * the digest is the first 4 u64 of the state.

  Byte-wise absorb rather than word-wise, matching the existing code: the
  accelerated permutation dominates, so the per-byte XOR is not the cost.

  ## Correctness criterion

  Agreement with the existing one-shot on the same input — `keccak_init`, one
  `keccak_absorb` over the whole buffer, `keccak_final` must equal
  `zkvm_keccak256` of that buffer, and a split into several `keccak_absorb` calls
  must give the same digest as one. That is congruence against already-trusted
  code rather than a fresh correctness argument, and it needs no assumption about
  collisions: the claim is that two computations agree, not that two digests
  agreeing implies anything about their inputs.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

/-- Keccak-256 rate in bytes: 1088 bits. -/
def keccakRateBytes : Nat := 136
/-- Sponge state: 25 × u64. -/
def keccakStateBytes : Nat := 200
/-- Context = state ++ fill offset. The fill offset must persist across calls,
    which is exactly what the one-shot routines keep in a register and discard. -/
def keccakCtxBytes : Nat := keccakStateBytes + 8
/-- Offset of the rate-block fill counter within the context. -/
def keccakCtxFillOff : Nat := keccakStateBytes

/-! ## `keccak_init`

    a0 = ctx pointer (`keccakCtxBytes` bytes, 8-byte aligned).
    Zeroes the sponge and the fill offset. No result register.

    The caller owns the context's storage; this does not allocate. -/
def keccakInitFunction : String :=
  "  .globl keccak_init\n" ++
  "keccak_init:\n" ++
  "  mv t0, a0; li t1, 26\n" ++            -- 25 state dwords + the fill dword
  ".Lkci_zero:\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lkci_zero\n" ++
  "  ret\n"

/-! ## `keccak_absorb`

    a0 = ctx, a1 = byte pointer, a2 = length. No result register.

    Absorbs `len` bytes, permuting on each completed 136-byte rate block and
    carrying a partial block in the context. A zero length is a no-op, so a caller
    need not special-case empty fields.

    Callee-saved registers are preserved; `a0`-`a2` and `t0`-`t4` are clobbered.
    The permutation needs the state pointer in `a0`, so the live pointer and
    remaining length are stacked around it — the one place this cannot simply use
    temporaries. -/
def keccakAbsorbFunction : String :=
  "  .globl keccak_absorb\n" ++
  "keccak_absorb:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++                       -- s0 = ctx (survives the permutation)
  ".Lkca_loop:\n" ++
  "  beqz a2, .Lkca_done\n" ++
  s!"  ld t4, {keccakCtxFillOff}(s0)\n" ++  -- t4 = fill
  "  lbu t0, 0(a1)\n" ++                   -- next input byte
  "  add t1, s0, t4; lbu t2, 0(t1); xor t2, t2, t0; sb t2, 0(t1)\n" ++
  "  addi a1, a1, 1; addi a2, a2, -1; addi t4, t4, 1\n" ++
  s!"  sd t4, {keccakCtxFillOff}(s0)\n" ++
  s!"  li t3, {keccakRateBytes}; bne t4, t3, .Lkca_loop\n" ++
  -- Rate block complete: permute, then reset the fill offset.
  "  sd a1, 16(sp); sd a2, 24(sp)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  ld a1, 16(sp); ld a2, 24(sp)\n" ++
  s!"  sd zero, {keccakCtxFillOff}(s0)\n" ++
  "  j .Lkca_loop\n" ++
  ".Lkca_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 32\n" ++
  "  ret\n"

/-! ## `keccak_final`

    a0 = ctx, a1 = 32-byte output pointer. No result register.

    Applies pre-NIST keccak padding (`0x01` at the fill offset, `0x80` at the last
    rate byte), permutes once, and writes the first 32 bytes of state.

    The context is left in its post-permutation state; it is NOT re-initialised.
    A caller reusing a context must call `keccak_init` again — this does not do it
    implicitly, because an implicit reset makes a double-final silently return the
    digest of the empty string instead of faulting. -/
def keccakFinalFunction : String :=
  "  .globl keccak_final\n" ++
  "keccak_final:\n" ++
  s!"  ld t4, {keccakCtxFillOff}(a0)\n" ++
  "  add t0, a0, t4; lbu t1, 0(t0); xori t1, t1, 0x01; sb t1, 0(t0)\n" ++
  s!"  addi t0, a0, {keccakRateBytes - 1}; lbu t1, 0(t0); xori t1, t1, 0x80; sb t1, 0(t0)\n" ++
  "  mv t2, a1\n" ++                       -- save the output pointer past the permutation
  "  .4byte 0x80052073\n" ++
  "  ld t0, 0(a0);  sd t0, 0(t2)\n" ++
  "  ld t0, 8(a0);  sd t0, 8(t2)\n" ++
  "  ld t0, 16(a0); sd t0, 16(t2)\n" ++
  "  ld t0, 24(a0); sd t0, 24(t2)\n" ++
  "  ret\n"

/-! ## `keccak_incremental_selftest`

    The correctness criterion, as a routine rather than as prose: hash the SAME
    bytes with the one-shot and with init/absorb/final, and compare the digests.

    a0 = byte pointer, a1 = length, returns a0 = 0 if the two digests agree,
    1 if they differ. a2 = scratch (>= 64 bytes for the two digests, 8-aligned),
    a3 = keccak context (>= `keccakCtxBytes`, 8-aligned) -- both caller-supplied,
    so the self-test allocates nothing either.

    The incremental side deliberately splits the input into THREE UNEVEN CHUNKS
    (len/3 each, remainder in the last), because the interesting failure is the
    permutation that fires mid-absorb when a rate block completes. A single-chunk
    split, or chunks that happen to align to 136, would exercise the same path as
    the one-shot and agree vacuously -- so the caller should pass a length over
    136 for the comparison to mean anything, and over 272 to cross two boundaries.

    This is congruence against already-trusted code, not a fresh correctness
    argument: the claim is that two computations of the same function agree. No
    assumption about collisions is involved, because nothing is inferred FROM the
    digests matching -- they are two outputs of the same intended function, and a
    mismatch localises a defect in the new code. -/
def keccakIncrementalSelftestFunction : String :=
  "  .globl keccak_incremental_selftest\n" ++
  "keccak_incremental_selftest:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++      -- ptr, len, scratch, ctx
  -- One-shot digest into scratch+0.
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  -- Incremental digest into scratch+32, in three uneven chunks.
  "  mv a0, s3; jal ra, keccak_init\n" ++
  "  li t0, 3; divu s4, s1, t0\n" ++                       -- s4 = len/3
  "  mv a0, s3; mv a1, s0; mv a2, s4; jal ra, keccak_absorb\n" ++
  "  add t0, s0, s4\n" ++
  "  mv a0, s3; mv a1, t0; mv a2, s4; jal ra, keccak_absorb\n" ++
  "  slli t0, s4, 1; add t1, s0, t0\n" ++                  -- tail pointer
  "  slli t0, s4, 1; sub t2, s1, t0\n" ++                  -- tail length = len - 2*(len/3)
  "  mv a0, s3; mv a1, t1; mv a2, t2; jal ra, keccak_absorb\n" ++
  "  mv a0, s3; addi a1, s2, 32; jal ra, keccak_final\n" ++
  -- Compare the two 32-byte digests.
  "  li t3, 4\n" ++
  "  mv t4, s2; addi t5, s2, 32\n" ++
  ".Lkcs_cmp:\n" ++
  "  ld t0, 0(t4); ld t1, 0(t5); bne t0, t1, .Lkcs_differ\n" ++
  "  addi t4, t4, 8; addi t5, t5, 8; addi t3, t3, -1; bnez t3, .Lkcs_cmp\n" ++
  "  li a0, 0; j .Lkcs_ret\n" ++
  ".Lkcs_differ:\n" ++
  "  li a0, 1\n" ++
  ".Lkcs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-- All three entry points, in emission order. -/
def keccakIncrementalFunctions : String :=
  keccakInitFunction ++
  keccakAbsorbFunction ++
  keccakFinalFunction ++
  keccakIncrementalSelftestFunction

/-! ## Anti-drift guards on the emitted text

    Not a correctness argument: correctness is agreement with the one-shot on the
    same input, which is a runtime comparison. These only stop a later edit from
    quietly changing a constant or dropping a step.

    Fully qualified, one per line — a `#guard` in the wrong namespace auto-binds
    its identifiers as implicits and passes vacuously, and one wrapping to a second
    line silently covers only the first. -/

#guard keccakRateBytes == 136
#guard keccakStateBytes == 200
#guard keccakCtxBytes == 208
#guard keccakCtxFillOff == 200

-- All three entry points emitted.
#guard (keccakIncrementalFunctions.splitOn "keccak_init:").length == 2
#guard (keccakIncrementalFunctions.splitOn "keccak_absorb:").length == 2
#guard (keccakIncrementalFunctions.splitOn "keccak_final:").length == 2
#guard (keccakIncrementalFunctions.splitOn "keccak_incremental_selftest:").length == 2

-- The self-test must split into THREE absorb calls. One call would exercise the
-- same path as the one-shot and agree vacuously.
#guard (keccakIncrementalSelftestFunction.splitOn "jal ra, keccak_absorb").length == 4
-- ...and it must actually call the one-shot as the oracle.
#guard (keccakIncrementalSelftestFunction.splitOn "jal ra, zkvm_keccak256").length == 2

-- `init` must clear 26 dwords: 25 state + the fill counter. Clearing 25 would
-- leave a stale fill offset, so a reused context would resume mid-block and
-- produce a clean wrong digest rather than failing.
#guard (keccakInitFunction.splitOn "li t1, 26").length == 2

-- The permutation must appear exactly once in absorb and once in final. A missing
-- one produces a digest over an unpermuted state -- well-formed and wrong.
#guard (keccakAbsorbFunction.splitOn "0x80052073").length == 2
#guard (keccakFinalFunction.splitOn "0x80052073").length == 2

-- Pre-NIST keccak padding, NOT SHA-3's 0x06. Both produce a digest; only one
-- matches the one-shot.
#guard (keccakFinalFunction.splitOn "xori t1, t1, 0x01").length == 2
#guard (keccakFinalFunction.splitOn "xori t1, t1, 0x80").length == 2

-- The fill offset must be PERSISTED (not just read) inside the absorb loop, or a
-- second absorb call would restart at offset 0 and overwrite the partial block.
#guard (keccakAbsorbFunction.splitOn s!"sd t4, {keccakCtxFillOff}(s0)").length == 2
-- ...and reset to zero after each permutation.
#guard (keccakAbsorbFunction.splitOn s!"sd zero, {keccakCtxFillOff}(s0)").length == 2

-- `final` must NOT re-initialise the context: an implicit reset turns a double
-- final into the digest of the empty string instead of an observable error.
#guard (keccakFinalFunction.splitOn "li t1, 26").length == 1

end EvmAsm.Codegen
