/-
  EvmAsm.Codegen.Probes.HashProbes

  Hash-bridge probe BuildUnits (K1..K4 + K15 + S2 + S3) carved
  out of `EvmAsm.Codegen.Programs` per the file-size hard cap.
  Hosts:

    K1   zisk_keccak_probe
    K2   zisk_keccak256_empty
    K2a  zisk_keccak256_abc
    K15  zisk_sha256_probe_le
    S2   zkvm_sha256
    S3   zisk_sha256_from_input
    K3   zisk_zkvm_keccak256
    K4   zisk_keccak256_from_input

  These are the standalone probe ELFs exercising the keccak and
  sha256 hash bridges; the function strings themselves live in
  `Programs/HashBridge.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## stateless_guest — PR2 SSZ-output stub

    See the definition of `statelessGuestUnit` below
    (after `zkvmKeccak256Function`, which the epilogue inlines). -/

/-! ## zisk_keccak_probe — PR-K1 ziskemu Keccak-f[1600] intrinsic probe

    Emits a raw-asm probe that triggers ziskemu's built-in
    Keccak-f[1600] accelerator (`_opcode_keccak` in
    `~/.zisk/zisk/emulator-asm/src/emu.c:507`). The accelerator is
    invoked by writing the state pointer into a non-standard CSR at
    address 0x800 -- which is the syscall ID the Zisk compiler
    expects, per `ziskos/entrypoint/src/syscalls/keccakf.rs` (uses
    `csrs 0x800, <reg>` via the `ziskos_syscall!` macro).

    GNU-as `csrs csr, rs1` expands to `csrrs x0, csr, rs1`. The
    32-bit encoding for `csrs 0x800, a0`:

      csr(0x800)    rs1(x10=01010)  f3(010)  rd(x0)    op(0x73)
      [31..20]      [19..15]        [14..12] [11..7]   [6..0]
      = 0x80052073

    We emit this as a raw `.4byte` directive rather than the
    `csrs` mnemonic so the existing
    `riscv64-unknown-elf-as -march=rv64imac` toolchain string
    works without enabling the `Zicsr` extension. The 32-bit value
    is what `as -march=rv64imac_zicsr` produces for the same
    mnemonic; pinning it here is the whole point of PR-K1.

    Probe sequence:
      la a0, zisk_keccak_state    # state pointer
      .4byte 0x80052073           # csrs 0x800, a0 -> _opcode_keccak
      <copy 200 bytes to OUTPUT_ADDR>
      <halt>

    Verified Program body is a single NOP -- everything observable
    happens in raw asm, so the verified semantics carry no claim
    about the probe yet. PR-K2 wires this through verified Instrs
    once the CSR instruction is added to `Rv64.Instr`. -/

/-- Asm prologue: probe the keccak intrinsic and stream the
    post-permutation 200-byte state to ziskemu's public-output
    region. Hard-codes `OUTPUT_ADDR = 0xa0010000` (mirrors the
    constant above). -/
def ziskKeccakProbePrologue : String :=
  "  la a0, zisk_keccak_state\n" ++
  "  .4byte 0x80052073           # csrs 0x800, a0\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 25\n" ++
  ".Lzkp_copy_loop:\n" ++
  "  ld t2, 0(a0)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi a0, a0, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lzkp_copy_loop"

/-- `.data` section: 200 zero bytes labeled `zisk_keccak_state`.
    Lands in ziskemu RAM (0xa0000000..0xc0000000) via the standard
    `-Tdata=0xa0000000` link flag from `Codegen/Driver.lean`. -/
def ziskKeccakProbeDataSection : String :=
  ".section .data\n" ++
  "zisk_keccak_state:\n" ++
  "  .zero 200"

def ziskKeccakProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskKeccakProbePrologue
  dataAsm     := ziskKeccakProbeDataSection
}

/-! ## zisk_keccak256_empty — PR-K2 keccak256 sponge over empty input

    First wrapper around PR-K1's intrinsic: the keccak256 sponge
    construction applied to a zero-byte message. Concretely:

      1. Zero the 200-byte state buffer.
      2. Pad: set byte 0 = 0x01, byte 135 = 0x80
         (Ethereum Keccak padding; rate = 1088 bits = 136 bytes).
      3. Trigger `_opcode_keccak` (csrs 0x800, a0).
      4. Copy the first 32 bytes of state to OUTPUT_ADDR -- those
         are the 256-bit hash digest.

    Expected output (32 bytes):
      c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Matches the canonical keccak256("") hash and the value produced
    by `eth_utils.keccak(b"")` / `Cryptodome.Hash.keccak.new(...).digest()`.
    This is the simplest possible exercise of the full sponge wrapper:
    no input blocks to absorb, just the final padded block. Future
    PRs extend this to one-block ("abc") and multi-block inputs. -/

/-- Asm prologue: zero state, apply Ethereum Keccak padding for the
    empty-message case, call the keccak-f intrinsic, copy the 32-byte
    digest to OUTPUT_ADDR. -/
def ziskKeccak256EmptyPrologue : String :=
  "  la s0, k256e_state\n" ++
  "  # zero state (25 × u64)\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256e_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256e_zero\n" ++
  "  # apply Ethereum Keccak padding to empty message\n" ++
  "  li t0, 0x01\n" ++
  "  sb t0, 0(s0)              # state[0] = 0x01\n" ++
  "  li t0, 0x80\n" ++
  "  sb t0, 135(s0)            # state[135] = 0x80\n" ++
  "  # call keccak-f via PR-K1 intrinsic (csrs 0x800, a0)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # copy first 32 bytes of state to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000         # OUTPUT_ADDR\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256EmptyDataSection : String :=
  ".section .data\n" ++
  "k256e_state:\n" ++
  "  .zero 200"


/-! ## zisk_keccak256_abc — PR-K2a single-block input

    Same sponge skeleton as PR-K2 but with the 3-byte input "abc"
    (RFC test vector) XORed into state positions 0..3 before the
    padding bytes (`0x01` at byte 3, `0x80` at byte 135). Single
    absorb block, single keccak-f call, then squeeze.

    Expected:
      keccak256(b"abc") =
        4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

    Demonstrates the single-block absorb path (input ≤ rate). The
    multi-block path lands in a follow-up. -/
def ziskKeccak256AbcPrologue : String :=
  "  la s0, k256a_state\n" ++
  "  # zero state\n" ++
  "  mv t3, s0\n" ++
  "  li t4, 25\n" ++
  ".Lk256a_zero:\n" ++
  "  sd zero, 0(t3)\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lk256a_zero\n" ++
  "  # input \"abc\" at state[0..3]\n" ++
  "  li t0, 0x61; sb t0, 0(s0)\n" ++
  "  li t0, 0x62; sb t0, 1(s0)\n" ++
  "  li t0, 0x63; sb t0, 2(s0)\n" ++
  "  # Ethereum Keccak padding (length 3 < rate 136)\n" ++
  "  li t0, 0x01; sb t0, 3(s0)\n" ++
  "  li t0, 0x80; sb t0, 135(s0)\n" ++
  "  # call keccak-f\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  # squeeze 32 bytes to OUTPUT_ADDR\n" ++
  "  li t0, 0xa0010000\n" ++
  "  ld t1, 0(s0);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(s0);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(s0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(s0); sd t1, 24(t0)"

def ziskKeccak256AbcDataSection : String :=
  ".section .data\n" ++
  "k256a_state:\n" ++
  "  .zero 200"


/-! ## zisk_sha256_probe_le — PR-K15 SHA-256 intrinsic probe (LE-u32 layout)

    Earlier PR-S1 v1 (`task #17`) tried the SHA-256 intrinsic at
    CSR `0x805` with the 0.15.0-documented BE-per-u64 packing
    (state[0] = (h0 BE-u32 << 32) | h1 BE-u32, stored LE as a
    single u64). Output didn't match `sha256(b"")`.

    Hypothesis: the installed ziskemu (0.18.0) uses a different
    state packing -- specifically LE-u32 within u64 (state bytes
    are u32 BE in spec, stored as LE u32s -- so the 64-bit memory
    layout is `LE(h0) || LE(h1)` = bytes `67 e6 09 6a 85 ae 67 bb`
    for the first u64). As a u64 value this is
    `0xbb67ae856a09e667`.

    Probe re-runs the empty-message compression with this
    alternative layout. If it matches `sha256(b"")`, the 0.18.0
    intrinsic layout is pinned; if not, document further.

    Expected on success (SHA-256("") in LE-u32 packed memory):
      67 e6 09 6a 85 ae 67 bb 72 f3 6e 3c 3a f5 4f a5
      7f 52 0e 51 8c 68 05 9b ab d9 83 1f 19 cd e0 5b
    Then post-compression state should be SHA-256("")'s words
    packed the same way:
      sha256(empty) = e3 b0 c4 42 98 fc 1c 14 9a fb f4 c8 99 6f
                      b9 24 27 ae 41 e4 64 9b 93 4c a4 95 99 1b
                      78 52 b8 55
    As LE-u32 within u64 (per-byte memory order):
      42 c4 b0 e3 14 1c fc 98 c8 f4 fb 9a 24 b9 6f 99
      e4 41 ae 27 4c 93 9b 64 1b 99 95 a4 55 b8 52 78
-/
def ziskSha256ProbeLePrologue : String :=
  "  la a0, sha256_le_params\n" ++
  "  .4byte 0x80552073           # csrs 0x805, a0\n" ++
  "  # copy 32-byte post-compression state to OUTPUT_ADDR\n" ++
  "  la t0, sha256_le_state\n" ++
  "  li t1, 0xa0010000\n" ++
  "  ld t2, 0(t0);  sd t2, 0(t1)\n" ++
  "  ld t2, 8(t0);  sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)"

def ziskSha256ProbeLeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_le_state:\n" ++
  "  # state[0..4] = LE-u32-pack (each u32 stored LE in memory)\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_le_input:\n" ++
  "  # input[0] = LE-u32-pack of message u32[0..2]\n" ++
  "  # padded empty: u32[0] = 0x80 (LE bytes [80 00 00 00]) || u32[1] = 0\n" ++
  "  .quad 0x80\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0\n" ++
  "  .quad 0                     # u32[15] = length BE bits = 0\n" ++
  ".balign 8\n" ++
  "sha256_le_params:\n" ++
  "  .quad sha256_le_state\n" ++
  "  .quad sha256_le_input"


/-! ## zkvm_sha256 — PR-S2 Merkle-Damgård wrapper

    Parameterised SHA-256 callable matching the zkvm-standards C
    signature:

        zkvm_status zkvm_sha256(const uint8_t* data, size_t len,
                                zkvm_sha256_hash* output);

    Sister to PR-K3's `zkvm_keccak256`. Composes the LE-u32
    intrinsic pinned in PR-S1 (#5286) with the FIPS 180-4
    Merkle-Damgård wrapper:

      1. Initialise state to the SHA-256 IV (LE-u32 packing).
      2. For each full 64-byte input block: copy into the
         intrinsic's `sha256_input` buffer, `csrs 0x805, a0` to
         compress.
      3. Final block: copy <64 remainder bytes, append 0x80,
         append 8-byte big-endian bit-length at offset 56..64.
         If remainder >= 56, use two blocks (current + a fresh
         length-only block).
      4. Squeeze: byte-swap each u32 of the LE-packed state to
         produce canonical SHA-256 wire bytes
         (`e3b0c442 98fc1c14 ...` byte order). The byte-swap uses
         the `xori 3` index trick (within each 4-byte group,
         byte j maps to byte (3 ^ j)).

    Calling convention (RV64 ABI, mirrors `zkvm_keccak256`):
      a0 = data ptr; a1 = len; a2 = output ptr;
      ra = return; returns a0 = ZKVM_EOK = 0. -/


def ziskZkvmSha256Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # call 1: sha256(empty)\n" ++
  "  la a0, zsha_empty\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 2: sha256(\"abc\")\n" ++
  "  la a0, zsha_abc\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # call 3: sha256(0xaa × 200)\n" ++
  "  la a0, zsha_aa\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzkv_sha_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzkv_sha_done:"

def ziskZkvmSha256DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667    # LE(h0) || LE(h1)\n" ++
  "  .quad 0xa54ff53a3c6ef372    # LE(h2) || LE(h3)\n" ++
  "  .quad 0x9b05688c510e527f    # LE(h4) || LE(h5)\n" ++
  "  .quad 0x5be0cd191f83d9ab    # LE(h6) || LE(h7)\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  "zsha_empty:\n" ++
  "  .byte 0\n" ++
  "zsha_abc:\n" ++
  "  .ascii \"abc\"\n" ++
  "zsha_aa:\n" ++
  "  .fill 200, 1, 0xaa"


/-! ## zisk_sha256_from_input — PR-S3 host-supplied input

    Mirror of PR-K4 `zisk_keccak256_from_input` for SHA-256:
    hash whatever's at `INPUT_ADDR + 16` (length given at
    `INPUT_ADDR + 8` per ziskemu's input-region layout) and
    write the 32-byte digest to `OUTPUT_ADDR + 0..32`.

    Uses PR-S2's `zkvm_sha256` (the Merkle-Damgård wrapper)
    inlined per-BuildUnit. Test exercises arbitrary input
    lengths via the Python harness (`--shape header` for an
    RLP-encoded amsterdam Header ~658 bytes, `--shape long`
    for 1024 bytes of 0x55). -/
def ziskSha256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  j .Lzks_done\n" ++
  zkvmSha256Function ++ "\n" ++
  ".Lzks_done:"

def ziskSha256FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input"


/-! ## zisk_zkvm_keccak256 — PR-K3 parameterised wrapper

    Refactors the three hardcoded sponge probes (PR-K2 empty,
    PR-K2a "abc", PR-K2b multi-block) into a single jal-callable
    function matching the zkvm-standards C signature:

        zkvm_status zkvm_keccak256(const uint8_t* data, size_t len,
                                   zkvm_keccak256_hash* output);

    Calling convention (RV64 ABI):
      a0 = data ptr
      a1 = len
      a2 = output ptr (32 bytes will be written)
      ra = return address
      returns: a0 = 0 on success (ZKVM_EOK = 0)

    Internally clobbers t0..t6, a0..a2. Saves s0/s1/s2/s4 on the
    stack and restores them before returning. Caller is
    responsible for sp pointing at usable RAM.

    The build unit's test driver initialises sp, then makes three
    calls (empty / "abc" / 200×0xaa) writing the three 32-byte
    digests to OUTPUT[0..96]. After the third call, jumps past
    the function definition and falls through to halt.

    Expected OUTPUT[0..96]:
      0..32  : keccak256(b"")               = c5d2460186f7233c...
      32..64 : keccak256(b"abc")            = 4e03657aea45a94f...
      64..96 : keccak256(b"\xaa" * 200)     = ebad1a3694934 0cb... -/

/-- Test driver: initialises sp, calls `zkvm_keccak256` three times
    with the empty / abc / 200×0xaa inputs, then jumps over the
    function definition so we fall through to halt. -/
def ziskZkvmKeccak256Prologue : String :=
  "  # set up a usable stack pointer in RAM\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # call 1: keccak256(empty)\n" ++
  "  la a0, zk3_empty_marker\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 2: keccak256(\"abc\")\n" ++
  "  la a0, zk3_abc_input\n" ++
  "  li a1, 3\n" ++
  "  li a2, 0xa0010020\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # call 3: keccak256(0xaa × 200)\n" ++
  "  la a0, zk3_aa_input\n" ++
  "  li a1, 200\n" ++
  "  li a2, 0xa0010040\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # skip over the function definition, fall through to halt\n" ++
  "  j .Lzk3_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk3_done:"

def ziskZkvmKeccak256DataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "zk3_empty_marker:\n" ++
  "  .byte 0\n" ++
  "zk3_abc_input:\n" ++
  "  .ascii \"abc\"\n" ++
  "zk3_aa_input:\n" ++
  "  .fill 200, 1, 0xaa"


/-! ## zisk_keccak256_from_input — PR-K4 host-supplied input

    First real-shape consumer of the parameterised
    `zkvm_keccak256` from PR-K3: hash an arbitrary byte buffer
    that the host streamed in via `ziskemu -i <file>`. ziskemu
    places file bytes 0..8 (the u64 LE length prefix) at
    `INPUT_ADDR + 8..16` and file bytes 8.. (the data) at
    `INPUT_ADDR + 16..`. The probe reads the length, points at
    the data, calls `zkvm_keccak256`, writes the 32-byte digest
    at OUTPUT_ADDR.

    Designed to test header-shaped inputs (typical Ethereum
    header RLP is ~530-540 bytes), but accepts any byte stream.
    The Python harness (`scripts/keccak256-gen-input.py`)
    SSZ/RLP-encodes a real Header dataclass and emits the
    ziskemu-formatted input file. The test script runs ziskemu,
    diffs the OUTPUT digest against the Python-computed
    reference hash. -/
def ziskKeccak256FromInputPrologue : String :=
  "  # set up stack\n" ++
  "  li sp, 0xa0050000\n" ++
  "  # read length and data ptr from ziskemu input region\n" ++
  "  li a3, 0x40000000           # INPUT_ADDR\n" ++
  "  ld a1, 8(a3)                # a1 = length (u64 LE at INPUT_ADDR + 8)\n" ++
  "  addi a0, a3, 16             # a0 = data ptr (INPUT_ADDR + 16)\n" ++
  "  li a2, 0xa0010000           # a2 = OUTPUT_ADDR\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  j .Lzk4_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  ".Lzk4_done:"

/-- `.data` for the from-input probe: 200-byte state buffer used
    by `zkvm_keccak256`. Input data lives in the
    `INPUT_ADDR` region (host-supplied via `ziskemu -i`), not in
    `.data`. -/
def ziskKeccak256FromInputDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"



end EvmAsm.Codegen
