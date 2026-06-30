/-
  EvmAsm.Codegen.Programs.TxDecode

  EIP-typed-tx decoders + dispatcher carved out of
  `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap.
  Hosts:

    K41  tx_eip1559_decode   (12-field EIP-1559)
    K42  tx_eip2930_decode   (11-field EIP-2930)
    K44  tx_eip7702_decode   (13-field EIP-7702)
    K45  tx_eip4844_decode   (14-field EIP-4844)
    K87  tx_decode_dispatch  (legacy + typed)

  Each decoder splits the appropriate RLP shape into per-field
  offset / length pairs in a caller-supplied output table, using
  the cursor-advancing walker pair (`EvmAsm.Codegen.Programs.
  RlpWalk`) for a single left-to-right pass over the fields.
  K87 inspects the typed-tx prefix byte and dispatches to the
  matching specific decoder (legacy / 1559 / 2930 / 4844 /
  7702). Composes the RlpWalk walker + K36 (tx_legacy_decode) +
  K40 (tx_type_dispatch) which remain in `Programs/Tx.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxDecode1559
import EvmAsm.Codegen.Programs.TxDecode7702
import EvmAsm.Codegen.Programs.TxDecode4844
import EvmAsm.Codegen.Programs.TxDecode2930

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## tx_decode_dispatch -- PR-K87 unified tx decoder

    Dispatch on a tx envelope's type byte and route to the
    appropriate inner decoder. Mirrors Python's
    `decode_transaction`:

      byte 0 ≥ 0xc0     → legacy        → tx_legacy_decode    (K36)
      byte 0 == 0x01    → EIP-2930      → tx_eip2930_decode   (K42)
      byte 0 == 0x02    → EIP-1559      → tx_eip1559_decode   (K41)
      byte 0 == 0x03    → EIP-4844      → tx_eip4844_decode   (K45)
      byte 0 == 0x04    → EIP-7702      → tx_eip7702_decode   (K44)
      else              → status = type-unrecognized

    The decoded struct's size depends on the tx type:
      type 0 (legacy)   : 196 B
      type 1 (EIP-2930) : 216 B
      type 2 (EIP-1559) : 248 B
      type 3 (EIP-4844) : 248 B
      type 4 (EIP-7702) : 240 B

    Status encoding packs both the tx_type and sub-status:

      status = (tx_type << 8) | sub_status

      sub_status 0  : success
      sub_status 1  : type unrecognized (used with tx_type=0)
      sub_status 2  : sub-decoder returned non-zero

    Caller responsibilities:
      - Pre-zero the 248-byte struct_out buffer.
      - After success, infer struct_size from `tx_type` extracted
        as `(status >> 8) & 0xff`.

    Composes PR-K40 + each of K36, K41, K42, K44, K45.

    Calling convention:
      a0 (input)  : envelope ptr
      a1 (input)  : envelope_len
      a2 (input)  : struct_out ptr (must be ≥ 248 bytes, pre-zeroed)
      ra (input)  : return
      a0 (output) : packed status (see encoding above).

    Uses `.data` scratch for its own `tdd_type` / `tdd_inner_off`
    (via `tx_type_dispatch`) and for `tcbg_blob_fee_be` (written
    by `tx_eip4844_decode`); the five decoders themselves hold
    their (cursor, end) pair in callee-saved registers and need
    no per-decoder `.data` scratch. -/
def txDecodeDispatchFunction : String :=
  "tx_decode_dispatch:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # envelope ptr\n" ++
  "  mv s1, a1                   # envelope_len\n" ++
  "  mv s2, a2                   # struct_out ptr\n" ++
  "  # tx_type_dispatch(envelope, len, type_out=tdd_type, inner_offset_out=tdd_inner_off)\n" ++
  "  la a2, tdd_type\n" ++
  "  la a3, tdd_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltdd_unrec\n" ++
  "  la t0, tdd_type; ld t1, 0(t0)\n" ++
  "  la t0, tdd_inner_off; ld t2, 0(t0)\n" ++
  "  add t3, s0, t2              # inner_ptr\n" ++
  "  sub t4, s1, t2              # inner_len\n" ++
  "  # Dispatch on tx_type (t1)\n" ++
  "  beqz t1, .Ltdd_legacy\n" ++
  "  li t5, 1\n" ++
  "  beq t1, t5, .Ltdd_2930\n" ++
  "  li t5, 2\n" ++
  "  beq t1, t5, .Ltdd_1559\n" ++
  "  li t5, 3\n" ++
  "  beq t1, t5, .Ltdd_4844\n" ++
  "  li t5, 4\n" ++
  "  beq t1, t5, .Ltdd_7702\n" ++
  "  j .Ltdd_unrec\n" ++
  ".Ltdd_legacy:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  jal ra, tx_legacy_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_legacy\n" ++
  "  li a0, 0\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_2930:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip2930_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_2930\n" ++
  "  li a0, 0x0100\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_1559:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip1559_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_1559\n" ++
  "  li a0, 0x0200\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_4844:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_4844\n" ++
  "  li a0, 0x0300\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_7702:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip7702_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_7702\n" ++
  "  li a0, 0x0400\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_unrec:\n" ++
  "  li a0, 0x0001\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_legacy:\n" ++
  "  li a0, 0x0002\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_2930:\n" ++
  "  li a0, 0x0102\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_1559:\n" ++
  "  li a0, 0x0202\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_4844:\n" ++
  "  li a0, 0x0302\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_7702:\n" ++
  "  li a0, 0x0402\n" ++
  ".Ltdd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_decode_dispatch`: probe BuildUnit. Reads (env_len,
    env_bytes) from host input; pre-zeros 248-byte struct slot
    at OUTPUT+8; calls helper; writes (packed status, struct)
    to OUTPUT (256 bytes total). -/
def ziskTxDecodeDispatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # env_len\n" ++
  "  addi a0, a3, 16             # env ptr\n" ++
  "  li a2, 0xa0010008           # struct slot at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 dwords).\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Ltdd_zout:\n" ++
  "  beqz t1, .Ltdd_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltdd_zout\n" ++
  ".Ltdd_zout_done:\n" ++
  "  jal ra, tx_decode_dispatch\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # packed status\n" ++
  "  j .Ltdd_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txLegacyDecodeFunction ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  txEip1559DecodeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  txEip7702DecodeFunction ++ "\n" ++
  txDecodeDispatchFunction ++ "\n" ++
  ".Ltdd_pdone:"

/-- The five decoders all use the cursor-advancing walker and hold
    (cursor, end) in callee-saved registers, so the only `.data`
    cells the dispatcher's combined image needs are: its own
    `tdd_type` / `tdd_inner_off` scratch (for `tx_type_dispatch`),
    and `tcbg_blob_fee_be` -- the full BE u256 of
    `max_fee_per_blob_gas` that `tx_eip4844_decode` persists and
    downstream consumers (`BlockVerdict` / EIP-8037 gate) read
    back. Declaring `tcbg_blob_fee_be` here makes the standalone
    dispatcher probe linkable (previously it relied on the symbol
    being defined only in unrelated probe data sections). -/
def ziskTxDecodeDispatchDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tcbg_blob_fee_be:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "tdd_type:\n" ++
  "  .zero 8\n" ++
  "tdd_inner_off:\n" ++
  "  .zero 8"

def ziskTxDecodeDispatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxDecodeDispatchPrologue
  dataAsm     := ziskTxDecodeDispatchDataSection
}


end EvmAsm.Codegen
