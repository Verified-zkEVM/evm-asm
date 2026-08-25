/-
  EvmAsm.Codegen.Programs.ExtractDepositData

  `extract_deposit_data` (bead 8uld3.1, EIP-6110) — strip the Solidity ABI framing
  from a DepositEvent log payload and return the concatenated raw fields:
  pubkey(48) || withdrawal_credentials(32) || amount(8) || signature(96) || index(8)
  = 192 bytes, the per-deposit body the consensus layer consumes.

  Mirrors execution-specs amsterdam requests.py:extract_deposit_data. Every
  well-formed DepositEvent payload is exactly 576 bytes with a FIXED ABI layout:
    head: 5 x 32-byte big-endian offsets = 160, 256, 320, 384, 512
    each field: 32-byte big-endian size (= 48,32,8,96,8) then the data, 32-padded
  Any deviation => InvalidBlock (a misbehaving deposit contract), so this returns a
  nonzero status rather than silently accepting unexpected data.

  Self-contained (no external callees). The full parse_deposit_requests (scan the
  block receipts for deposit-contract logs and concatenate extract_deposit_data over
  each) composes this once receipts are materialized from execution — that scan is
  the execution-gated remainder of 8uld3.1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.EddBe32EqSAsm
import EvmAsm.Codegen.Programs.EddMemcpySAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## extract_deposit_data
    a0 = DepositEvent data ptr   a1 = data byte length   a2 = 192-byte out ptr
    a0 (output) = 0 ok / 1 malformed (bad length / offset / size). -/
-- Drift guard (build-time evaluation): the exact rendering of the verified
-- `edd_memcpy` program.  The assemble+cmp byte-identity check against the
-- previous hand-written text was run against THIS string; if the emitter or
-- the program changes, this pin fails and the check must be rerun.
#guard emitProgram EddMemcpySAsm.eddMemcpy_prog ==
  "  beq x12, x0, .+28\n  lbu x5, 0(x10)\n  sb x5, 0(x11)\n"
    ++ "  addi x10, x10, 1\n  addi x11, x11, 1\n  addi x12, x12, -1\n"
    ++ "  jal x0, .-24\n  jalr x0, 0(x1)"

-- Drift guard (build-time evaluation): the exact rendering of the verified
-- `edd_be32_eq` program.  The assemble+cmp byte-identity check against the
-- previous hand-written text was run against THIS string; if the emitter or
-- the program changes, this pin fails and the check must be rerun.
#guard emitProgram EddBe32EqSAsm.eddBe32Eq_prog ==
  "  li x5, 0\n  li x6, 28\n  beq x5, x6, .+24\n  add x7, x10, x5\n"
    ++ "  lbu x28, 0(x7)\n  bne x28, x0, .+64\n  addi x5, x5, 1\n"
    ++ "  jal x0, .-24\n  lbu x6, 28(x10)\n  slli x6, x6, 24\n"
    ++ "  lbu x7, 29(x10)\n  slli x7, x7, 16\n  or x6, x6, x7\n"
    ++ "  lbu x7, 30(x10)\n  slli x7, x7, 8\n  or x6, x6, x7\n"
    ++ "  lbu x7, 31(x10)\n  or x6, x6, x7\n  bne x6, x11, .+12\n"
    ++ "  li x10, 1\n  jalr x0, 0(x1)\n  li x10, 0\n  jalr x0, 0(x1)"

def extractDepositDataFunction : String :=
  "extract_deposit_data:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # data ptr\n" ++
  "  mv s1, a2                   # out ptr\n" ++
  "  li t0, 576; bne a1, t0, .Ledd_fail        # DEPOSIT_EVENT_LENGTH\n" ++
  "  # 5 ABI offsets must be the canonical 160,256,320,384,512 (big-endian u256)\n" ++
  "  mv a0, s0;        li a1, 160; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 32;  li a1, 256; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 64;  li a1, 320; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 96;  li a1, 384; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 128; li a1, 512; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  # 5 field sizes must be 48,32,8,96,8 (at their offsets)\n" ++
  "  addi a0, s0, 160; li a1, 48; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 256; li a1, 32; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 320; li a1, 8;  jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 384; li a1, 96; jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  addi a0, s0, 512; li a1, 8;  jal ra, edd_be32_eq; beqz a0, .Ledd_fail\n" ++
  "  # extract fields (offset+32 skips each size word) into the 192-byte out\n" ++
  "  addi a0, s0, 192; mv a1, s1;        li a2, 48; jal ra, edd_memcpy   # pubkey  -> out[0]\n" ++
  "  addi a0, s0, 288; addi a1, s1, 48;  li a2, 32; jal ra, edd_memcpy   # wc      -> out[48]\n" ++
  "  addi a0, s0, 352; addi a1, s1, 80;  li a2, 8;  jal ra, edd_memcpy   # amount  -> out[80]\n" ++
  "  addi a0, s0, 416; addi a1, s1, 88;  li a2, 96; jal ra, edd_memcpy   # sig     -> out[88]\n" ++
  "  addi a0, s0, 544; addi a1, s1, 184; li a2, 8;  jal ra, edd_memcpy   # index   -> out[184]\n" ++
  "  li a0, 0; j .Ledd_ret\n" ++
  ".Ledd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ledd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n" ++
  -- a0=ptr to 32-byte BE field, a1=K (<2^32); a0=1 if value==K else 0.
  -- Emitted from the verified DCode program (`EddBe32EqSAsm.eddDeriv`,
  -- spec `eddBe32Eq_retSpec`); byte-identity with the previous
  -- hand-written text checked by assemble+cmp, the rendering pinned below.
  "edd_be32_eq:\n" ++
  emitProgram EddBe32EqSAsm.eddBe32Eq_prog ++ "\n" ++
  -- a0=src, a1=dst, a2=len (leaf, byte-wise).  Emitted from the verified
  -- DCode program (`EddMemcpySAsm.mcDeriv`, spec `eddMemcpy_retSpec`);
  -- byte-identity with the previous hand-written text checked by
  -- assemble+cmp, the rendering pinned below.
  "edd_memcpy:\n" ++
  emitProgram EddMemcpySAsm.eddMemcpy_prog

/-- `zisk_extract_deposit_data`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8..16 : data length (so the check can exercise the length guard)
      bytes 16..  : the DepositEvent data payload
    Output: bytes 0..8 = status; bytes 8..200 = the 192-byte unframed deposit. -/
def ziskExtractDepositDataPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # data len\n" ++
  "  addi a0, a5, 16             # data ptr\n" ++
  "  li a2, 0xa0010008           # 192-byte out (OUTPUT + 8)\n" ++
  "  jal ra, extract_deposit_data\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ledd_pdone\n" ++
  extractDepositDataFunction ++ "\n" ++
  ".Ledd_pdone:"


end EvmAsm.Codegen
