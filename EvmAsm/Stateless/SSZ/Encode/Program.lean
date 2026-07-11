/-
  EvmAsm.Stateless.SSZ.Encode.Program

  Serializer for `SszStatelessValidationResult` -- the variable-size
  SSZ Container at `tests-zkevm@v0.6.0` (`40f956fab`), where
  `SszForkConfig` lost its `fork` and `blob_schedule` fields.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`class SszStatelessValidationResult(Container)`,
   `class SszChainConfig(Container)`,
   `class SszForkConfig(Container)`).

  ## SSZ wire layout (61 bytes for empty activation; 69 for the
     common timestamp-only fixture shape)

  Outer container `SszStatelessValidationResult`:
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  |  0..32  |   32 | `new_payload_request_root`  | `Bytes32`        |
  |     32  |    1 | `successful_validation`     | `boolean`        |
  | 33..37  |    4 | offset of `chain_config`    | u32 LE = 37      |
  | 37..    |      | `chain_config` SSZ          | nested container |

  Inside `SszChainConfig` (bytes 37..):
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  | 37..45  |    8 | `chain_id`                  | `uint64`         |
  | 45..49  |    4 | offset of `active_fork`     | u32 LE = 12      |
  | 49..    |      | `active_fork` SSZ           | nested container |

  Inside `SszForkConfig` (bytes 49..):
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  | 49..53  |    4 | offset of `activation`      | u32 LE = 4       |
  | 53..    |      | `activation` SSZ            | nested container |

  Inside `SszForkActivation` (bytes 53..61 for the empty shape):
  | Offset  | Size | Field                       | Type             |
  |---------|------|-----------------------------|------------------|
  | 53..57  |    4 | offset of `block_number`    | u32 LE           |
  | 57..61  |    4 | offset of `timestamp`       | u32 LE           |
  | 61..    |  0.. | optional bodies             | `SszList[u64,1]` |

  The activation section (fork_config bytes past its 4-byte offset
  table) is byte-copied verbatim from the INPUT chain_config -- the
  output chain-config is a pure echo, and the input's `SszForkConfig`
  has the same one-entry offset table, so `chain_config[12..len)`
  maps 1:1 onto `OUTPUT[49..49+len-12)`.

  ## Caller contract

  Caller places both SSZ fields in registers:

      x10 : chain_id              (u64 at output bytes 37..45)
      x11 : successful_validation (low byte at output byte 32)

  The encoder must only see `0` or `1` in `x11`'s low byte; the
  decoder's `decode_validation_bit` guarantees that. (The v0.5.0
  `x12 = active_fork.fork` input is gone with the field.)

  Bytes 0..32 are zeroed here as a stub; the `stateless_guest`
  caller's epilogue overwrites them with `hash_tree_root(witness)`.

  ## Memory layout

  - **Preconditions**:
    - `OUTPUT_BASE = 0xa0010000` is ziskemu's public-output region
      (mirrors `EvmAsm.Codegen.OUTPUT_ADDR`).
    - `[OUTPUT_BASE, OUTPUT_BASE + 73)` lies inside the RAM zone
      (`RAM_MEM_START..RAM_MEM_END`) and is accepted by
      `isValidMemAddr` per issue #5164.
    - `x10` holds the u64 `chain_id` to encode.
  - **Postconditions**: 73 bytes at `OUTPUT_BASE` carry the SSZ
    encoding of `SszStatelessValidationResult(root = 0,
    successful_validation = x11&1, chain_config = SszChainConfig(
    chain_id = x10, active_fork = SszForkConfig(fork = 0,
    activation = SszForkActivation(empty, empty),
    blob_schedule = empty)))`.
  - **Clobbers**: `x5` (constant scratch), `x6` (base pointer),
    `x7` (packed word work).
  - **Exit**: falls through to the caller's halt stub.

  ## Alignment

  Every store is u64-aligned (offsets 0, 8, 16, 24, 32, 40, 48, 56,
  64) or a single byte (offset 72). No unaligned word/double store
  -- consistent with the verified RV64 subset already used by the
  rest of `EvmAsm/Stateless/`.

  ## Packed-u64 layout (constants at byte positions inside each store)

  - byte 32 (SD): `[b, 0x25, 0, 0, 0, c[0], c[1], c[2]]`
  - byte 40 (SD): `[c[3], c[4], c[5], c[6], c[7], 0x0c, 0, 0]`
  - byte 48 (SD): all zero (offset_active_fork high + fork low 7)
  - byte 56 (SD): `[0, 0x10, 0, 0, 0, 0x18, 0, 0]`
  - byte 64 (SD): `[0, 0x08, 0, 0, 0, 0x08, 0, 0]`
  - byte 72 (SB): zero (high byte of offset_ts = 8)

  ## Frame

  21 instructions: 1 LI base + 4 SD (zero hash) + (3 + 1 OR + 1 SD)
  bytes32 + (2 + 1 OR + 1 SD) bytes40 + 1 SD (zero) bytes48 + 2
  bytes56 + 2 bytes64 + 1 SB byte72.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.SSZ.Encode

open EvmAsm.Rv64

/-- Output region base address. Duplicated from
    `EvmAsm.Codegen.Programs.OUTPUT_ADDR` so `EvmAsm/Stateless/` stays
    free of the codegen umbrella. -/
def OUTPUT_BASE : Word := 0xa0010000

/-- Parameterized serializer Program.

    Caller contract:
      - `x10` holds the u64 `chain_id` to encode.
      - `x11` holds `successful_validation` (low byte = 0 or 1).

    The body writes the SSZ encoding of `SszStatelessValidationResult`
    (61 bytes for an empty activation; the activation section is echoed
    verbatim from the input) at `OUTPUT_BASE`, and falls through to the
    caller's halt stub. -/
def serialize_stateless_output : Program :=
  LI .x6 OUTPUT_BASE ;;
  -- bytes [0..32) hash zero-stub (epilogue overwrites)
  SD .x6 .x0 0  ;;
  SD .x6 .x0 8  ;;
  SD .x6 .x0 16 ;;
  SD .x6 .x0 24 ;;
  -- bytes [32..40): bool || offset_chain_config=37 || chain_id_lo3
  SLLI .x7 .x10 40 ;;
  LI .x5 0x2500 ;;
  OR' .x7 .x7 .x5 ;;
  OR' .x7 .x7 .x11 ;;
  SD .x6 .x7 32 ;;
  -- bytes [40..48): chain_id_hi5 || offset_active_fork=12 (lo3)
  SRLI .x7 .x10 24 ;;
  LI .x5 0xc0000000000 ;;
  OR' .x7 .x7 .x5 ;;
  SD .x6 .x7 40 ;;
  -- byte 48: high byte of offset_active_fork (= 0). v0.6.0: the fork
  -- u64 that used to follow is gone; the fork_config section (its
  -- 4-byte activation offset + the activation) is echoed from the
  -- input below, starting at OUTPUT[49].
  SB .x6 .x0 48 ;;
  -- Bounded byte-copy from chain_config[12..len) to OUTPUT[49..37+len)
  -- (the whole `SszForkConfig` section, echoed verbatim: the input's
  -- fork_config has the same one-entry offset table the output needs).
  -- `len = chain_config_length` is derived from the outer SSZ offset
  -- table: outer.offsets[3] - outer.offsets[2]. We equivalently compute
  -- `chain_config_end_addr = SSZ_BASE + outer.offsets[3]` and stop when
  -- the source pointer reaches it.
  --
  -- The previous unrolled implementation (PRs #6793 / #6802 /
  -- #6807 / #6811) read chain_config[24..76) UNCONDITIONALLY and
  -- relied on ziskemu's per-fixture mem slack. Cross-product
  -- fixtures with witness content + active_fork content could
  -- panic ziskemu with "section not found" when chain_config_end
  -- landed at or past mem_end; the [[ziskemu-input-slack]] memory
  -- note documents this. The bounded loop eliminates that
  -- constraint entirely.
  --
  -- Range covers: offset_activation (chain_config[12..16)) and the
  -- activation container (offsets + optional bodies,
  -- chain_config[16..len)).
  --
  -- Register usage: x18=chain_config_end_addr, x19=src cursor,
  -- x20=dst cursor, x7=byte temp. x13=chain_config_addr and
  -- x17=SSZ_BASE are preserved from the decoder.
  LWU .x18 .x17 12 ;;             -- offsets[3] (= chain_config_end_offset)
  ADD .x18 .x17 .x18 ;;           -- chain_config_end_addr
  ADDI .x19 .x13 12 ;;            -- src = chain_config + 12
  ADDI .x20 .x6 49 ;;             -- dst = output + 49
  -- Loop: BGEU exit forward 24 bytes (skip 6 instructions: BGEU
  -- itself + the 5 body instructions). Otherwise: LBU + SB + bump
  -- cursors + JAL back 20 bytes to the BGEU.
  BGEU .x19 .x18 24 ;;
  LBU .x7 .x19 0 ;;
  SB .x20 .x7 0 ;;
  ADDI .x19 .x19 1 ;;
  ADDI .x20 .x20 1 ;;
  JAL .x0 (-20 : BitVec 21)
  -- Old unrolled byte-copy (chain_config[28..76) -> OUTPUT[65..113))
  -- and the standalone byte 64 zero-fill removed; the loop above
  -- subsumes both.
  /-
  -- bytes [65..81): byte-copy active_fork[16..32) from input.
  -- active_fork[16..24) = activation header (offset_block_number,
  --   offset_timestamp); same shape regardless of emptiness:
  --     empty:                  [8, 0, 0, 0, 8, 0, 0, 0]
  --     block_number=[N]:       [8, 0, 0, 0, 16, 0, 0, 0]
  -- active_fork[24..32) = block_number value (8 bytes) IF
  --   activation.block_number is non-empty; otherwise PAST the
  --   active_fork section (ziskemu zero-fills past file content).
  -- For empty activation, output[73..81) is past spec.len() (= 73)
  -- and the test framework only compares the first spec.len()
  -- bytes, so garbage there doesn't matter.
  -- byte 64 left at zero (the high byte of offset_blob_schedule,
  -- written by the SD at offset 56 -- this works because
  -- offset_blob_schedule is always <= 64 fits in one byte).
  LBU .x7 .x13 28 ;; SB .x6 .x7 65 ;;
  LBU .x7 .x13 29 ;; SB .x6 .x7 66 ;;
  LBU .x7 .x13 30 ;; SB .x6 .x7 67 ;;
  LBU .x7 .x13 31 ;; SB .x6 .x7 68 ;;
  LBU .x7 .x13 32 ;; SB .x6 .x7 69 ;;
  LBU .x7 .x13 33 ;; SB .x6 .x7 70 ;;
  LBU .x7 .x13 34 ;; SB .x6 .x7 71 ;;
  LBU .x7 .x13 35 ;; SB .x6 .x7 72 ;;
  LBU .x7 .x13 36 ;; SB .x6 .x7 73 ;;
  LBU .x7 .x13 37 ;; SB .x6 .x7 74 ;;
  LBU .x7 .x13 38 ;; SB .x6 .x7 75 ;;
  LBU .x7 .x13 39 ;; SB .x6 .x7 76 ;;
  LBU .x7 .x13 40 ;; SB .x6 .x7 77 ;;
  LBU .x7 .x13 41 ;; SB .x6 .x7 78 ;;
  LBU .x7 .x13 42 ;; SB .x6 .x7 79 ;;
  LBU .x7 .x13 43 ;; SB .x6 .x7 80 ;;
  -- bytes [81..89): byte-copy active_fork[32..40) from input.
  -- This range is the timestamp value slot when both
  -- block_number and timestamp are non-empty (then
  -- activation_body_len = 24, occupying active_fork[16..40)).
  -- For any other activation shape, these bytes lie past the
  -- actual active_fork section and ziskemu zero-fills them; the
  -- test framework only compares the first spec.len() bytes.
  LBU .x7 .x13 44 ;; SB .x6 .x7 81 ;;
  LBU .x7 .x13 45 ;; SB .x6 .x7 82 ;;
  LBU .x7 .x13 46 ;; SB .x6 .x7 83 ;;
  LBU .x7 .x13 47 ;; SB .x6 .x7 84 ;;
  LBU .x7 .x13 48 ;; SB .x6 .x7 85 ;;
  LBU .x7 .x13 49 ;; SB .x6 .x7 86 ;;
  LBU .x7 .x13 50 ;; SB .x6 .x7 87 ;;
  LBU .x7 .x13 51 ;; SB .x6 .x7 88 ;;
  -- bytes [89..97): byte-copy active_fork[40..48) from input.
  -- When `blob_schedule = [entry]` (one SszBlobSchedule of 3 u64s
  -- = 24 bytes) and activation is empty, the active_fork layout
  -- places the third u64 (`base_fee_update_fraction`) at
  -- active_fork[40..48). For other shapes (already covered by
  -- prior cases) this range lies past the active_fork section
  -- and ziskemu zero-fills it; the test framework only compares
  -- the first spec.len() bytes.
  LBU .x7 .x13 52 ;; SB .x6 .x7 89 ;;
  LBU .x7 .x13 53 ;; SB .x6 .x7 90 ;;
  LBU .x7 .x13 54 ;; SB .x6 .x7 91 ;;
  LBU .x7 .x13 55 ;; SB .x6 .x7 92 ;;
  LBU .x7 .x13 56 ;; SB .x6 .x7 93 ;;
  LBU .x7 .x13 57 ;; SB .x6 .x7 94 ;;
  LBU .x7 .x13 58 ;; SB .x6 .x7 95 ;;
  LBU .x7 .x13 59 ;; SB .x6 .x7 96 ;;
  -- bytes [97..113): byte-copy active_fork[48..64) from input.
  -- Covers the blob_schedule entry when activation is non-empty
  -- (then activation pushes blob_schedule forward by 8/16 bytes,
  -- so the entry's bytes land at active_fork[48..72) -- the
  -- first 16 bytes of which fall in this range). The MAX
  -- active_fork = 64 bytes (16 fc-header + 24 activation + 24
  -- blob_schedule) so OUTPUT[97..113) is the tail of spec
  -- output. For smaller active_fork shapes, the range is past
  -- the actual section; ziskemu zero-fills and the test
  -- framework ignores bytes past len(spec).
  LBU .x7 .x13 60 ;; SB .x6 .x7 97 ;;
  LBU .x7 .x13 61 ;; SB .x6 .x7 98 ;;
  LBU .x7 .x13 62 ;; SB .x6 .x7 99 ;;
  LBU .x7 .x13 63 ;; SB .x6 .x7 100 ;;
  LBU .x7 .x13 64 ;; SB .x6 .x7 101 ;;
  LBU .x7 .x13 65 ;; SB .x6 .x7 102 ;;
  LBU .x7 .x13 66 ;; SB .x6 .x7 103 ;;
  LBU .x7 .x13 67 ;; SB .x6 .x7 104 ;;
  LBU .x7 .x13 68 ;; SB .x6 .x7 105 ;;
  LBU .x7 .x13 69 ;; SB .x6 .x7 106 ;;
  LBU .x7 .x13 70 ;; SB .x6 .x7 107 ;;
  LBU .x7 .x13 71 ;; SB .x6 .x7 108 ;;
  LBU .x7 .x13 72 ;; SB .x6 .x7 109 ;;
  LBU .x7 .x13 73 ;; SB .x6 .x7 110 ;;
  LBU .x7 .x13 74 ;; SB .x6 .x7 111 ;;
  LBU .x7 .x13 75 ;; SB .x6 .x7 112
  -/

end EvmAsm.Stateless.SSZ.Encode
