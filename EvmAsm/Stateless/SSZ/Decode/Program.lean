/-
  EvmAsm.Stateless.SSZ.Decode.Program

  Minimal SSZ decoder slice (PR3): read `chain_config.chain_id` from a
  host-supplied `SszStatelessInput` blob on `INPUT_ADDR`.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`class SszStatelessInput(Container)`,
   `class SszChainConfig(Container)`).

  ## SSZ wire layout of `SszStatelessInput`

  Container fixed-header section (20 bytes):

  | Offset | Size | Field                              | Wire form     |
  |--------|------|------------------------------------|---------------|
  |  0..4  |    4 | `new_payload_request` offset       | uint32 LE     |
  |  4..8  |    4 | `witness` offset                   | uint32 LE     |
  |  8..16 |    8 | `chain_config.chain_id` (inline)   | uint64 LE     |
  | 16..20 |    4 | `public_keys` offset               | uint32 LE     |

  The variable-size body follows the header. PR3 only reads
  `chain_id`; the offsets / variable body are ignored for now.

  ## ziskemu input-buffer layout

  Per `EvmAsm/Codegen/Programs.lean`:

      INPUT_ADDR +  0..8   : ziskemu metadata (zero)
      INPUT_ADDR +  8..16  : LE u64 length of the SSZ blob
      INPUT_ADDR + 16..    : SSZ-encoded SszStatelessInput

  So `chain_id` lives at `INPUT_ADDR + 16 + 8 = INPUT_ADDR + 24`. The
  base address is 8-byte aligned (`INPUT_ADDR = 0x40000000`), and
  `24 mod 8 = 0`, so an `LD` at offset 24 satisfies
  `isValidDwordAccess`.

  ## Memory layout (preconditions)
  - `INPUT_BASE = 0x40000000` (matches `EvmAsm.Codegen.INPUT_ADDR`).
  - `[INPUT_BASE + 16, INPUT_BASE + 16 + N)` is host-supplied SSZ
    data; PR5 reads bytes 0..4 (offset_1), 16..20 (offset_3), and
    inside the witness section at byte 8..12 (offset_headers).
  - The input zone (`INPUT_MEM_START..INPUT_MEM_END`, see #5164)
    admits all of these.
  - All reads are 4-byte aligned: the SSZ blob starts at the
    8-byte-aligned `INPUT_BASE + 16`, every nested container's
    fixed header begins on a 4-byte boundary in our fixtures, and
    the offsets we read all target 4-byte-aligned positions.

  ## Side effects
  - `read_chain_id` loads `chain_id` (u64 LE) into `x10`; clobbers
    `x11`.
  - `decode_validation_bit` chases offset_1 (outer SSZ →
    witness_addr), the witness section's third inner u32
    (witness_addr → headers_addr), and offset_3 (outer SSZ →
    public_keys_addr = headers_end_addr). It then writes `1` into
    `x11` iff `headers_end_addr - headers_addr == 0`, i.e. the
    `witness.headers` SSZ list section is empty. The helper also
    **leaves** `headers_addr` in `x17` and
    `headers_byte_length` in `x14`, so the PR6
    `decode_header_count` follow-up can reuse both without
    redoing the offset walk. Clobbers `x12..x15`, `x17`.
  - `decode_header_count` (PR6) reads the first u32 of the
    `witness.headers` list (= `4 * header_count` for a non-empty
    list, or out-of-bounds memory for an empty list -- which we
    avoid via a BEQ guard), divides by 4, and leaves
    `header_count` in `x16`. Sets `x16 = 0` when the headers list
    is empty. Clobbers `x16`.

  ## PR5/PR6 framing

  PR4 set the bool from whether the **whole** `SszExecutionWitness`
  body was empty (length 12). PR5 narrows this: the bool reflects
  whether `witness.headers` specifically is empty, regardless of
  what's in `state` or `codes`. PR6 adds `header_count` as a
  diagnostic u64 written past the 41-byte SSZ result -- the encoder
  surfaces it at `OUTPUT_ADDR + 48`. This is the first guest-side
  observable derived from the **content** of the headers list,
  not just its length.

  Future PRs replace the validation bool with the real STF verdict
  and iterate over headers via the same `headers_addr` / count.

  ## Frame
  - `read_chain_id`: 2 instructions (1 LI + 1 LD).
  - `decode_validation_bit`: 10 instructions.
  - `decode_header_count`: 4 instructions
    (1 ADDI + 1 BEQ guard + 1 LWU + 1 SRLI).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.SSZ.Decode

open EvmAsm.Rv64

/-- ziskemu private-input region base. Mirrors
    `EvmAsm.Codegen.Programs.INPUT_ADDR`. -/
def INPUT_BASE : Word := 0x40000000

/-- ziskemu's 16-byte preamble at `INPUT_ADDR`: 8 bytes of zero
    metadata + 8 bytes of u64 length prefix. The host-supplied
    payload starts at `INPUT_BASE + INPUT_DATA_OFFSET`. -/
def INPUT_DATA_OFFSET : BitVec 12 := 16

/-- Schema-prefixed input: 2 bytes of schema-ID
    (`STATELESS_INPUT_SCHEMA_ID = 0x1501` at tests-zkevm@v0.6.0:
    fork index `0x15` || revision `0x01`, big-endian) before the
    SSZ-encoded `SszStatelessInput`. The SSZ container therefore
    starts at `INPUT_BASE + INPUT_DATA_OFFSET + SCHEMA_ID_SIZE =
    0x40000012`. -/
def SCHEMA_ID_SIZE : BitVec 12 := 2

/-- SSZ outer offset table: `SszStatelessInput` has 4 variable-size
    fields (`new_payload_request`, `witness`, `chain_config`,
    `public_keys`). Each offset is u32 LE. -/
def OUTER_NPR_OFFSET_SSZ        : BitVec 12 := 0
def OUTER_WITNESS_OFFSET_SSZ    : BitVec 12 := 4
def OUTER_CHAIN_CONFIG_OFFSET_SSZ : BitVec 12 := 8
def OUTER_PUBLIC_KEYS_OFFSET_SSZ : BitVec 12 := 12

/-- Byte offset within an `SszExecutionWitness` section of its
    third u32 (`offset_2` = `headers` offset). The witness's fixed
    header is three u32s: `state`, `codes`, `headers`. -/
def WITNESS_HEADERS_INNER_OFFSET : BitVec 12 := 8

/-- Read `chain_config.chain_id` from `INPUT_BASE` into `x10`.

    NEW-schema flow: skip 16 bytes of ziskemu preamble + 2 bytes
    of schema-ID, then walk `SszStatelessInput`'s outer offset
    table to find `chain_config`'s relative offset, then load the
    `chain_id` u64 LE at the start of the chain_config section.

    Postcondition: `x10` holds the host-supplied `chain_id` as a u64.
    Clobbers `x11`, `x12`, `x13`. -/
def read_chain_id : Program :=
  LI .x11 INPUT_BASE ;;
  ADDI .x12 .x11 (INPUT_DATA_OFFSET + SCHEMA_ID_SIZE) ;;
  LWU .x13 .x12 OUTER_CHAIN_CONFIG_OFFSET_SSZ ;;
  ADD .x13 .x12 .x13 ;;
  LD .x10 .x13 0

/-- Walk the SSZ outer offset table + witness inner offsets to
    locate the `witness.headers` section. Leaves three registers
    set up for the validator-pipeline epilogue:

      x14 = headers_section_length (in bytes)
      x21 = headers_addr (start of the headers list in memory)
      x17 = SSZ_BASE (preserved for the encoder's bounded
            byte-copy, which reads outer.offsets[3] there).

    Also sets `x11 = 0` (the legacy validation-bit stub; the
    pipeline downstream may overwrite OUTPUT[32] independently if
    a validator chooses to set the success flag).

    The witness section starts at `SSZ_BASE + outer.offsets[1]`
    and ends at `SSZ_BASE + outer.offsets[2]` (= chain_config
    start). Its first 12 bytes are the inner u32 offsets for the
    `state`, `codes`, `headers` lists; the third (`+8`) is
    `headers_offset_in_witness`. Headers section length is
    therefore `witness_length - headers_offset_in_witness`. For
    empty witness (all 3 lists empty) the headers section is
    empty (length 0).

    Clobbers `x11`, `x14`, `x15`, `x17`, `x21`, `x22`, `x23`. -/
def decode_validation_bit : Program :=
  -- #12057: all outer/inner u32 offsets via LBU pack (SSZ base 0x40000012 unaligned).
  [ .ADDI .x11 .x0 (0 : BitVec 12),
    .LI .x15 INPUT_BASE,
    .ADDI .x17 .x15 (INPUT_DATA_OFFSET + SCHEMA_ID_SIZE),
    -- x22 = witness_addr = SSZ_BASE + outer.offsets[1]
    .LBU .x22 .x17 (4 : BitVec 12),
    .LBU .x5 .x17 (5 : BitVec 12), .SLLI .x5 .x5 (8 : BitVec 6), .OR .x22 .x22 .x5,
    .LBU .x5 .x17 (6 : BitVec 12), .SLLI .x5 .x5 (16 : BitVec 6), .OR .x22 .x22 .x5,
    .LBU .x5 .x17 (7 : BitVec 12), .SLLI .x5 .x5 (24 : BitVec 6), .OR .x22 .x22 .x5,
    .ADD .x22 .x17 .x22,
    -- x23 = witness_end
    .LBU .x23 .x17 (8 : BitVec 12),
    .LBU .x5 .x17 (9 : BitVec 12), .SLLI .x5 .x5 (8 : BitVec 6), .OR .x23 .x23 .x5,
    .LBU .x5 .x17 (10 : BitVec 12), .SLLI .x5 .x5 (16 : BitVec 6), .OR .x23 .x23 .x5,
    .LBU .x5 .x17 (11 : BitVec 12), .SLLI .x5 .x5 (24 : BitVec 6), .OR .x23 .x23 .x5,
    .ADD .x23 .x17 .x23,
    .SUB .x14 .x23 .x22,
    -- x21 = headers_offset_in_witness
    .LBU .x21 .x22 (8 : BitVec 12),
    .LBU .x5 .x22 (9 : BitVec 12), .SLLI .x5 .x5 (8 : BitVec 6), .OR .x21 .x21 .x5,
    .LBU .x5 .x22 (10 : BitVec 12), .SLLI .x5 .x5 (16 : BitVec 6), .OR .x21 .x21 .x5,
    .LBU .x5 .x22 (11 : BitVec 12), .SLLI .x5 .x5 (24 : BitVec 6), .OR .x21 .x21 .x5,
    .SUB .x14 .x14 .x21,
    .ADD .x21 .x22 .x21 ]

def decode_header_count : Program :=
  -- #12057: first inner u32 via LBU pack (headers_addr may be unaligned).
  -- BEQ empty skips 12 insn (pack+srli+jal) = 48 bytes to ADDI x16,0.
  [ .BEQ .x14 .x0 (48 : BitVec 13),
    .LBU .x16 .x21 (0 : BitVec 12),
    .LBU .x5 .x21 (1 : BitVec 12), .SLLI .x5 .x5 (8 : BitVec 6), .OR .x16 .x16 .x5,
    .LBU .x5 .x21 (2 : BitVec 12), .SLLI .x5 .x5 (16 : BitVec 6), .OR .x16 .x16 .x5,
    .LBU .x5 .x21 (3 : BitVec 12), .SLLI .x5 .x5 (24 : BitVec 6), .OR .x16 .x16 .x5,
    .SRLI .x16 .x16 (2 : BitVec 6),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x16 .x0 (0 : BitVec 12) ]

/-- Byte offset of `offset_active_fork` (u32 LE) within
    `SszChainConfig`. `SszChainConfig` is the variable-size
    Container `(chain_id: uint64, active_fork: SszForkConfig)`,
    so its fixed-header area is 8 + 4 = 12 bytes:

        bytes [0..8)  : chain_id
        bytes [8..12) : offset_active_fork

    v0.6.0: `SszForkConfig` = `{activation}` — the `fork` field is
    gone (fork identity travels in the schema id), so the reader
    below is RETIRED from the pipeline (kept only as the unverified
    ancestor of `ActiveForkSAsm.lean`'s proof patterns). -/
def CHAIN_CONFIG_ACTIVE_FORK_OFFSET_INNER : BitVec 12 := 8

/-- (Retired at v0.6.0 — reads a field that no longer exists.)
    Read `chain_config.active_fork.fork` (u64 LE) from `INPUT_BASE`
    into `x12`.

    Precondition (left by `read_chain_id`):
      x13 = chain_config_addr (start of the SszChainConfig section
            in memory)

    Postcondition: `x12` holds the host-supplied `fork` index as a u64.
    Clobbers `x12`, `x14`. -/
def read_active_fork : Program :=
  LWU .x14 .x13 CHAIN_CONFIG_ACTIVE_FORK_OFFSET_INNER ;;
  ADD .x14 .x13 .x14 ;;
  LD .x12 .x14 0

end EvmAsm.Stateless.SSZ.Decode
