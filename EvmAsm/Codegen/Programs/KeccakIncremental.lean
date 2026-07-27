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

def keccakSelftestLengths : List Nat := [0, 1, 134, 135, 136, 137, 271, 272, 273]
/-- Non-rate-aligned prefix sizes; `0` means a single chunk. -/
def keccakSelftestPrefixes : List Nat := [0, 1, 67, 135]


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

/-- The matrix tables live in `.bss` and are FILLED AT RUNTIME by the self-test.

    They were briefly `.data` with `.dword` initialisers, which grew `.data` by 104
    bytes and broke address-pinned `decide` proofs in `Bn254FieldMulModSAsm` and
    `Bn254FieldMulModPSAsmStage` — those carry concrete guest-linked `laHi`/`laLo`
    immediates for `.data` symbols, so shifting `.data` invalidates them. `.text`
    and `.bss` growth does not have that effect, which is why the three earlier
    PRs in this stack regenerated cleanly and this one did not.

    Zero-initialised storage plus runtime fill avoids the whole class. -/
def keccakIncrementalDataSection : String :=
  "kcs_lengths:\n  .zero " ++ toString (keccakSelftestLengths.length * 8) ++ "\n" ++
  "kcs_prefixes:\n  .zero " ++ toString (keccakSelftestPrefixes.length * 8) ++ "\n"

/-- Fill the matrix tables. Emitted into the self-test prologue rather than kept as
    initialised data, for the `.data`-shift reason above. -/
def keccakSelftestFillAsm : String :=
  "  la t0, kcs_lengths\n" ++
  String.join (keccakSelftestLengths.zipIdx.map (fun (n, i) =>
    s!"  li t1, {n}; sd t1, {i * 8}(t0)\n")) ++
  "  la t0, kcs_prefixes\n" ++
  String.join (keccakSelftestPrefixes.zipIdx.map (fun (n, i) =>
    s!"  li t1, {n}; sd t1, {i * 8}(t0)\n"))

/-! ## `keccak_incremental_selftest` -- the CONTRACT, as an executable matrix

    General-purpose code gets called by people who were not present when it was
    written and who will not re-derive its boundary behaviour. So the cases this
    establishes are written down here, and checked by a routine, rather than left
    to a reader to assume.

    ## Why a matrix and not one comparison

    A single absorb over the whole buffer takes the same path as the one-shot and
    agrees VACUOUSLY -- it exercises no boundary at all. The failures worth catching
    live at two independent axes:

    * **total length mod the 136-byte rate** -- the padding branch differs when the
      final block is empty (`0`), nearly full (`134`, `135`) or exactly full;
    * **where the caller splits** -- a chunk boundary that does not coincide with a
      rate boundary forces the partial-block carry in the context, which is the one
      piece of state the one-shot keeps in a register and discards.

    This session supplies the motivating evidence for the first axis: a hand-rolled
    keccak used earlier was validated on the empty string, `abc` and `testing`, all
    single-block, and was still wrong at `len mod 136 == 135` -- the case where the
    `0x01` pad lands on the last byte and collides with the `0x80`. Three passing
    vectors said nothing about it.

    ## What the matrix covers

    Lengths (9): `0, 1, 134, 135, 136, 137, 271, 272, 273`, giving
    `len mod 136 ∈ {0, 1, 134, 135}` and both sides of one and two rate boundaries.

    Split shapes (4) per length: a single chunk, then a prefix of `1`, `67` and
    `135` bytes with the remainder as a second chunk, each clamped to the length.
    None of `1`, `67`, `135` is a multiple of `136`, so the first chunk is never
    rate-aligned and the carry path is always exercised.

    36 comparisons in total. `len == 0` is included deliberately: absorbing nothing
    then finalising must equal the one-shot of an empty buffer, which is the case a
    caller most easily reaches by accident.

    ## ABI

      a0 = source bytes (must be readable for at least 273 bytes)
      a1 = scratch, >= 64 bytes, 8-aligned (two digests)
      a2 = keccak context, >= `keccakCtxBytes`, 8-aligned
      a0 (out) = 0 if every case agrees, else `1 + lengthIndex*4 + shapeIndex`

    A nonzero return LOCALISES the first disagreement rather than reporting a
    boolean, because "incremental keccak is wrong somewhere" is not actionable.

    This is congruence against already-trusted code, not a fresh correctness
    argument: nothing is inferred FROM digests matching, so no collision assumption
    is involved. Two computations of one intended function are compared, and a
    mismatch localises a defect in the new code. -/
def keccakIncrementalSelftestFunction : String :=
  "  .globl keccak_incremental_selftest\n" ++
  "keccak_incremental_selftest:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++          -- src, scratch, ctx
  keccakSelftestFillAsm ++
  "  li s3, 0\n" ++                                 -- s3 = length index
  ".Lkcs_len_loop:\n" ++
  s!"  li t0, {keccakSelftestLengths.length}; bgeu s3, t0, .Lkcs_pass\n" ++
  "  la t0, kcs_lengths; slli t1, s3, 3; add t0, t0, t1; ld s4, 0(t0)\n" ++   -- s4 = len
  -- Oracle: the one-shot over the same bytes, digest into scratch+0.
  "  mv a0, s0; mv a1, s4; mv a2, s1; jal ra, zkvm_keccak256\n" ++
  "  li s5, 0\n" ++                                 -- s5 = shape index
  ".Lkcs_shape_loop:\n" ++
  s!"  li t0, {keccakSelftestPrefixes.length}; bgeu s5, t0, .Lkcs_len_next\n" ++
  "  la t0, kcs_prefixes; slli t1, s5, 3; add t0, t0, t1; ld s6, 0(t0)\n" ++  -- s6 = prefix
  -- Clamp the prefix to the length; prefix 0 means one chunk of the whole length.
  "  bgeu s4, s6, .Lkcs_prefix_ok\n  mv s6, s4\n" ++
  ".Lkcs_prefix_ok:\n" ++
  "  mv a0, s2; jal ra, keccak_init\n" ++
  "  beqz s6, .Lkcs_single\n" ++
  -- Two chunks: [0, prefix) then [prefix, len).
  "  mv a0, s2; mv a1, s0; mv a2, s6; jal ra, keccak_absorb\n" ++
  "  add s7, s0, s6; sub s8, s4, s6\n" ++
  "  mv a0, s2; mv a1, s7; mv a2, s8; jal ra, keccak_absorb\n" ++
  "  j .Lkcs_finish\n" ++
  ".Lkcs_single:\n" ++
  "  mv a0, s2; mv a1, s0; mv a2, s4; jal ra, keccak_absorb\n" ++
  ".Lkcs_finish:\n" ++
  "  mv a0, s2; addi a1, s1, 32; jal ra, keccak_final\n" ++
  -- Compare the two digests.
  "  li t3, 4; mv t4, s1; addi t5, s1, 32\n" ++
  ".Lkcs_cmp:\n" ++
  "  ld t0, 0(t4); ld t1, 0(t5); bne t0, t1, .Lkcs_differ\n" ++
  "  addi t4, t4, 8; addi t5, t5, 8; addi t3, t3, -1; bnez t3, .Lkcs_cmp\n" ++
  "  addi s5, s5, 1; j .Lkcs_shape_loop\n" ++
  ".Lkcs_len_next:\n" ++
  "  addi s3, s3, 1; j .Lkcs_len_loop\n" ++
  ".Lkcs_differ:\n" ++
  -- Localise: 1 + lengthIndex*4 + shapeIndex.
  "  slli t0, s3, 2; add t0, t0, s5; addi a0, t0, 1; j .Lkcs_ret\n" ++
  ".Lkcs_pass:\n" ++
  "  li a0, 0\n" ++
  ".Lkcs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 96\n" ++
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

-- CONTRACT GUARDS on the matrix. These pin the cases the self-test claims to
-- cover, so a later edit cannot quietly shrink the matrix while the routine still
-- returns 0 -- which would look exactly like passing.
--
-- Axis 1, length mod the rate. 135 is the case that broke a hand-rolled keccak
-- earlier in this session: the 0x01 pad lands on the last byte and collides with
-- the 0x80. Three single-block vectors had passed.
#guard 135 ∈ keccakSelftestLengths
#guard 134 ∈ keccakSelftestLengths
#guard 136 ∈ keccakSelftestLengths
#guard 0 ∈ keccakSelftestLengths
#guard 1 ∈ keccakSelftestLengths
-- Both sides of TWO rate boundaries, so a carry that survives one block but not
-- two cannot hide.
#guard 272 ∈ keccakSelftestLengths
#guard 273 ∈ keccakSelftestLengths
-- The residues actually reached.
#guard (keccakSelftestLengths.map (· % keccakRateBytes)).eraseDups.length == 4

-- Axis 2, split points. NONE of the nonzero prefixes may be rate-aligned, or the
-- first chunk would end on a block boundary and the partial-block carry -- the one
-- piece of state the one-shot does not keep -- would never be exercised.
#guard keccakSelftestPrefixes.all (fun p => p == 0 || p % keccakRateBytes != 0)
-- A single-chunk shape must be present (index 0) AND must not be the only one: it
-- takes the one-shot's own path and agrees vacuously.
#guard keccakSelftestPrefixes.head? == some 0
#guard keccakSelftestPrefixes.length >= 3

-- The oracle must be the existing one-shot, not a second incremental computation.
#guard (keccakIncrementalSelftestFunction.splitOn "jal ra, zkvm_keccak256").length == 2
-- Both the two-chunk and single-chunk paths must absorb.
#guard (keccakIncrementalSelftestFunction.splitOn "jal ra, keccak_absorb").length == 4
-- The failure return must LOCALISE rather than be a boolean.
#guard (keccakIncrementalSelftestFunction.splitOn "slli t0, s3, 2").length == 2

-- The emitted tables must be present and must have one .dword per list entry.
-- NOT matched by value: `.dword 135` occurs in BOTH tables (135 is a length AND a
-- prefix), so a value guard on it counts two hits and fails against correct code --
-- the same substring collision that bit the account_writes data-section guard. The
-- values are already pinned above against the Lean lists, which is the right place.
#guard (keccakIncrementalDataSection.splitOn "kcs_lengths:").length == 2
#guard (keccakIncrementalDataSection.splitOn "kcs_prefixes:").length == 2
-- The section switch MUST be balanced. Dropping the restore would move every
-- later symbol from .bss into .data, which does not fail to assemble -- it just
-- makes zero-initialised arenas occupy image bytes.
-- The tables must be ZERO-INITIALISED (.bss), not .dword literals: initialised
-- data grows `.data` and shifts address-pinned proofs in unrelated modules.
#guard (keccakIncrementalDataSection.splitOn ".dword").length == 1
#guard (keccakIncrementalDataSection.splitOn ".zero").length == 3
-- ...so the fill must store every entry, or a table row silently stays 0 and the
-- matrix tests length 0 several times instead of the case it claims.
#guard (keccakSelftestFillAsm.splitOn "sd t1,").length
         == keccakSelftestLengths.length + keccakSelftestPrefixes.length + 1


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
