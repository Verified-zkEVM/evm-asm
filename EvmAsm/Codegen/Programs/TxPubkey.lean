/-
  EvmAsm.Codegen.Programs.TxPubkey

  Transaction public-key verification substrate. This slice routes one
  transaction to the right signature extractor and signing-hash builder; the
  following slice uses the produced material for secp256k1 recovery.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.Secp256k1Curve
import EvmAsm.Codegen.Programs.Secp256k1Recover

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## tx_pubkey_signature_material

    Build the canonical signature material needed to verify an Amsterdam
    `stateless_input.public_keys[i]` entry against the i-th transaction.
    Mirrors execution-specs Amsterdam `recover_transaction_public_key` up to,
    but not including, the secp256k1 recovery call:

      (r, s, recovery_id, signing_hash) =
        _signature_recovery_parameters(chain_id, tx)

    Calling convention:
      a0 (input)  : encoded transaction ptr
      a1 (input)  : encoded transaction byte length
      a2 (input)  : execution chain_id (u64)
      a3 (input)  : output ptr
      ra (input)  : return
      a0 (output) : status

    Output layout at `a3`:
      +0   tx type (0 legacy, 1 EIP-2930, 2 EIP-1559, 3 EIP-4844, 4 EIP-7702)
      +8   recovery id / y_parity (0 or 1)
      +16  r, 32-byte BE
      +48  s, 32-byte BE
      +80  signing hash, 32 bytes
      +112 inner offset
      +120 legacy is_eip155 flag

    Status:
      0 success
      1 tx type dispatch failed
      2 inner offset exceeds tx length
      10 signature extraction failed
      20 signing hash failed
      30 bad legacy v / chain-id mismatch
      31 bad typed y_parity
      40 r is zero
      41 s is zero
      42 r >= SECP256K1N
      43 s > SECP256K1N / 2
-/
def txPubkeySignatureMaterialFunction : String :=
  "tx_pubkey_signature_material:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # chain_id\n" ++
  "  mv s3, a3                   # output ptr\n" ++
  "  sd zero,   0(s3); sd zero,   8(s3); sd zero,  16(s3); sd zero,  24(s3)\n" ++
  "  sd zero,  32(s3); sd zero,  40(s3); sd zero,  48(s3); sd zero,  56(s3)\n" ++
  "  sd zero,  64(s3); sd zero,  72(s3); sd zero,  80(s3); sd zero,  88(s3)\n" ++
  "  sd zero,  96(s3); sd zero, 104(s3); sd zero, 112(s3); sd zero, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tps_type; la a3, tps_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltps_type_fail\n" ++
  "  la t0, tps_type; ld s4, 0(t0); sd s4, 0(s3)\n" ++
  "  la t0, tps_inner_off; ld s5, 0(t0); sd s5, 112(s3)\n" ++
  "  bltu s1, s5, .Ltps_inner_oob\n" ++
  "  add s6, s0, s5              # inner ptr\n" ++
  "  sub s7, s1, s5              # inner len\n" ++
  "  beqz s4, .Ltps_legacy\n" ++
  "  li t0, 1; beq s4, t0, .Ltps_t1\n" ++
  "  li t0, 2; beq s4, t0, .Ltps_t2\n" ++
  "  li t0, 3; beq s4, t0, .Ltps_t3\n" ++
  "  li t0, 4; beq s4, t0, .Ltps_t4\n" ++
  "  j .Ltps_type_fail\n" ++
  ".Ltps_legacy:\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tps_v; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_legacy_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  la t0, tps_v; ld t1, 0(t0)\n" ++
  "  li t2, 27; beq t1, t2, .Ltps_legacy_v27\n" ++
  "  li t2, 28; beq t1, t2, .Ltps_legacy_v28\n" ++
  "  slli t2, s2, 1\n" ++
  "  li t3, 35; add t3, t3, t2\n" ++
  "  beq t1, t3, .Ltps_legacy_eip155_y0\n" ++
  "  addi t3, t3, 1\n" ++
  "  beq t1, t3, .Ltps_legacy_eip155_y1\n" ++
  "  j .Ltps_bad_v\n" ++
  ".Ltps_legacy_v27:\n" ++
  "  sd zero, 8(s3); sd zero, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6; li a3, 0; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_legacy_v28:\n" ++
  "  li t0, 1; sd t0, 8(s3); sd zero, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6; li a3, 0; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_legacy_eip155_y0:\n" ++
  "  sd zero, 8(s3); li t0, 1; sd t0, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s3, 80\n" ++
  "  jal ra, tx_signing_hash_legacy_eip155\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_legacy_eip155_y1:\n" ++
  "  li t0, 1; sd t0, 8(s3); sd t0, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s3, 80\n" ++
  "  jal ra, tx_signing_hash_legacy_eip155\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_t1:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip2930_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 8; li a3, 1; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_t2:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip1559_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 9; li a3, 2; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_t3:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip4844_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 11; li a3, 3; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_t4:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip7702_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 10; li a3, 4; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_validate_y:\n" ++
  "  ld t0, 8(s3)\n" ++
  "  li t1, 1\n" ++
  "  bgtu t0, t1, .Ltps_bad_y\n" ++
  ".Ltps_validate_scalars:\n" ++
  "  addi a0, s3, 16; jal ra, u256_is_zero\n" ++
  "  bnez a0, .Ltps_r_zero\n" ++
  "  addi a0, s3, 48; jal ra, u256_is_zero\n" ++
  "  bnez a0, .Ltps_s_zero\n" ++
  "  addi a0, s3, 16; la a1, tps_secp256k1_n; la a2, tps_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, tps_cmp; ld t1, 0(t0)\n" ++
  "  beqz t1, .Ltps_r_order\n" ++
  "  la a0, tps_secp256k1_half_n; addi a1, s3, 48; la a2, tps_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, tps_cmp; ld t1, 0(t0)\n" ++
  "  bnez t1, .Ltps_s_high\n" ++
  "  li a0, 0\n" ++
  "  j .Ltps_ret\n" ++
  ".Ltps_type_fail:\n" ++
  "  li a0, 1; j .Ltps_ret\n" ++
  ".Ltps_inner_oob:\n" ++
  "  li a0, 2; j .Ltps_ret\n" ++
  ".Ltps_sig_fail:\n" ++
  "  li a0, 10; j .Ltps_ret\n" ++
  ".Ltps_hash_fail:\n" ++
  "  li a0, 20; j .Ltps_ret\n" ++
  ".Ltps_bad_v:\n" ++
  "  li a0, 30; j .Ltps_ret\n" ++
  ".Ltps_bad_y:\n" ++
  "  li a0, 31; j .Ltps_ret\n" ++
  ".Ltps_r_zero:\n" ++
  "  li a0, 40; j .Ltps_ret\n" ++
  ".Ltps_s_zero:\n" ++
  "  li a0, 41; j .Ltps_ret\n" ++
  ".Ltps_r_order:\n" ++
  "  li a0, 42; j .Ltps_ret\n" ++
  ".Ltps_s_high:\n" ++
  "  li a0, 43\n" ++
  ".Ltps_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"


/-! ## tx_pubkey_ecrecover_stage_material

    Stage `tx_pubkey_signature_material` output into the byte layout consumed by
    `zkvm_secp256k1_ecrecover(msg, sig, recid, output)`.

    Calling convention:
      a0 (input)  : material ptr from `tx_pubkey_signature_material`
      a1 (input)  : output/staging ptr
      ra (input)  : return
      a0 (output) : status

    Staging output at `a1`:
      +0    32-byte message hash
      +32   64-byte signature (`r || s`)
      +96   recid as u64 word (low byte consumed by backend)
      +104  reserved 64-byte recovered-pubkey buffer, pre-zeroed

    Status:
      0 success
      1 recid outside {0, 1}

    Scalar and signing-hash validity are owned by `tx_pubkey_signature_material`;
    this helper is deliberately just the ABI staging layer for the later recovery
    and compare slices. -/
def txPubkeyEcrecoverStageMaterial_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x18 (16 : BitVec 12),
    .SD .x2 .x19 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .LD .x18 .x8 (8 : BitVec 12),
    .LI .x5 (1 : Word),
    .BLTU .x5 .x18 (112 : BitVec 13),
    .ADDI .x5 .x8 (80 : BitVec 12),
    .MV .x6 .x9,
    .LI .x7 (4 : Word),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .ADDI .x5 .x8 (16 : BitVec 12),
    .ADDI .x6 .x9 (32 : BitVec 12),
    .LI .x7 (8 : Word),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .SD .x9 .x18 (96 : BitVec 12),
    .ADDI .x6 .x9 (104 : BitVec 12),
    .LI .x7 (8 : Word),
    .SD .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x18 .x2 (16 : BitVec 12),
    .LD .x19 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def txPubkeyEcrecoverStageMaterialFunction : String :=
  "tx_pubkey_ecrecover_stage_material:\n" ++ emitProgram txPubkeyEcrecoverStageMaterial_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `txPubkeyEcrecoverStageMaterial_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem txPubkeyEcrecoverStageMaterialFunction_eq_prog :
    txPubkeyEcrecoverStageMaterialFunction = "tx_pubkey_ecrecover_stage_material:\n" ++ emitProgram txPubkeyEcrecoverStageMaterial_prog := rfl

#guard txPubkeyEcrecoverStageMaterialFunction.startsWith "tx_pubkey_ecrecover_stage_material:\n"
#guard txPubkeyEcrecoverStageMaterial_prog.length = 44
/-! ## tx_pubkey_recover_raw

    Callable recovered-key helper surface. Mirrors execution-specs Amsterdam
    `recover_transaction_public_key`: build the signature material, stage it into
    the `zkvm_secp256k1_ecrecover(msg, sig, recid, output)` ABI, then run software
    secp256k1 recovery to produce the 64-byte public key. The safe-fail
    accelerator wrapper is deliberately NOT used, and no stateless `public_keys`
    comparison happens here.

    Recovery math (standard ECDSA, matching execution-specs `secp256k1_recover`):
      e      = msg_hash mod n
      r_inv  = r^{-1} mod n
      u1     = (-e * r_inv) mod n
      u2     = ( s * r_inv) mod n
      R      = curve point decompressed from r and the recovery id
      Q      = u1 * G + u2 * R
    and Q's affine x||y is the recovered public key. Composes the
    `Secp256k1Field` mod-n scalar helpers (reduce/mul/inv), the `Secp256k1Recover`
    R-decompression, and the `Secp256k1Curve` scalar-mul / point-add primitives.

    PERFORMANCE: the field multiplies and affine point operations are backed
    by the ziskemu accelerators (`Arith256Mod` / `Secp256k1Add` /
    `Secp256k1Dbl`, see `Secp256k1Field` / `Secp256k1Curve`), so one full
    recovery is ~2e6 ziskemu steps -- comfortably inside the stateless guest's
    ~1e9 step budget (the earlier all-software stack was ~1e11 steps).

    Calling convention:
      a0 (input)  : encoded transaction ptr
      a1 (input)  : encoded transaction byte length
      a2 (input)  : execution chain_id (u64)
      a3 (input)  : recovered-pubkey output ptr (64 bytes, BE x || y)
      a4 (input)  : scratch ptr (>= 304 bytes, 8-byte aligned)
      ra (input)  : return
      a0 (output) : status

    Scratch layout at `a4`:
      +0    material status side slot (u64; meaningful when status == 10)
      +8    signature material block (128 bytes; `tx_pubkey_signature_material`
            output: type/recid/r/s/hash/inner_off/is_eip155)
      +136  staged ecrecover ABI block (168 bytes; msg hash 32 @+0 || sig r 32
            @+32 || sig s 32 @+64 || recid word 8 @+96 || reserved pubkey 64)

    Status:
      0  success: recovered public key written to the output buffer
      10 signature material failed (material status stored at scratch +0)
      20 ecrecover ABI staging failed
      60 secp256k1 recovery failed (R is off-curve / out of range, or the
         recovered point is the identity)

    On any nonzero status the recovered-pubkey output buffer is zeroed so callers
    never observe stale or partial coordinates from a failed run. -/
def txPubkeyRecoverRawFunction : String :=
  "tx_pubkey_recover_raw:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # chain_id\n" ++
  "  mv s3, a3                   # recovered pubkey out\n" ++
  "  mv s4, a4                   # scratch ptr\n" ++
  "  # build signature material into scratch+8\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s4, 8\n" ++
  "  jal ra, tx_pubkey_signature_material\n" ++
  "  sd a0, 0(s4)                # record material status in side slot\n" ++
  "  beqz a0, .Ltprr_material_ok\n" ++
  "  li a0, 10\n" ++
  "  j .Ltprr_ret\n" ++
  ".Ltprr_material_ok:\n" ++
  "  # stage material into ecrecover ABI at scratch+136\n" ++
  "  addi a0, s4, 8; addi a1, s4, 136\n" ++
  "  jal ra, tx_pubkey_ecrecover_stage_material\n" ++
  "  beqz a0, .Ltprr_stage_ok\n" ++
  "  li a0, 20\n" ++
  "  j .Ltprr_ret\n" ++
  ".Ltprr_stage_ok:\n" ++
  "  # --- secp256k1 public-key recovery over the staged ABI block ---\n" ++
  "  # (extracted as secp256k1_recover_pubkey_staged so the ECRECOVER\n" ++
  "  #  precompile can reuse it; .62.2.5)\n" ++
  "  addi a0, s4, 136            # staged ABI block ptr\n" ++
  "  mv a1, s3                   # recovered pubkey out\n" ++
  "  jal ra, secp256k1_recover_pubkey_staged\n" ++
  "  beqz a0, .Ltprr_ok\n" ++
  "  li a0, 60\n" ++
  "  j .Ltprr_ret\n" ++
  ".Ltprr_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Ltprr_ret\n" ++
  ".Ltprr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## secp256k1_recover_pubkey_staged (.62.2.5)

    ECDSA public-key recovery over a staged ABI block — the shared kernel
    behind transaction-sender recovery (`tx_pubkey_recover_raw`) and the
    ECRECOVER (0x01) precompile backend. Same math and accelerator backing as
    documented on `tx_pubkey_recover_raw` above (~2e6 ziskemu steps).

    Calling convention:
      a0 (input)  : staged ABI block ptr: msg hash 32 @+0 || r 32 @+32 ||
                    s 32 @+64 || recid word (u64, 0/1) @+96. All BE 32-byte
                    scalars; the caller has already validated r, s in (0, n).
      a1 (input)  : recovered-pubkey output ptr (64 bytes, BE x || y)
      ra (input)  : return
      a0 (output) : 0 success; 60 recovery failed (R off-curve / out of range,
                    r non-invertible, or the recovered point is the identity).
                    On failure the 64-byte output is zeroed.

    Uses the `tpr_*` static scratch (recovery is not re-entrant). -/
def secp256k1RecoverPubkeyStagedFunction : String :=
  "secp256k1_recover_pubkey_staged:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s3,  8(sp); sd s4, 16(sp)\n" ++
  "  mv s4, a0                   # ABI block ptr (hash @+0, r @+32, s @+64, recid @+96)\n" ++
  "  mv s3, a1                   # recovered pubkey out\n" ++
  "  # 1. Decompress R = (x, y) from r and the recovery id.\n" ++
  "  addi a0, s4, 32             # r ptr (ABI+32)\n" ++
  "  ld a1, 96(s4)               # recid word (ABI+96); 0 or 1\n" ++
  "  la a2, tpr_R\n" ++
  "  jal ra, secp256k1_recover_r\n" ++
  "  bnez a0, .Ltprr_recover_fail\n" ++
  "  # 2. e = msg_hash mod n. The hash is < 2^256 < 2n, so one conditional\n" ++
  "  #    subtraction of n is sufficient.\n" ++
  "  mv a0, s4                   # msg hash ptr (ABI+0)\n" ++
  "  la a1, tpr_e\n" ++
  "  jal ra, secf_reduce_once_n\n" ++
  "  # 3. r_inv = r^{-1} mod n.\n" ++
  "  addi a0, s4, 32             # r ptr\n" ++
  "  la a1, tpr_rinv\n" ++
  "  jal ra, secf_inv_mod_n\n" ++
  "  bnez a0, .Ltprr_recover_fail   # r == 0 (defensive; callers reject it)\n" ++
  "  # 4. neg_e = (n - e) mod n, i.e. (-e) mod n (0 when e == 0).\n" ++
  "  la a0, tpr_e\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  bnez a0, .Ltprr_neg_e_zero\n" ++
  "  la a0, secf_n_be\n" ++
  "  la a1, tpr_e\n" ++
  "  la a2, tpr_nege\n" ++
  "  jal ra, u256_sub_be          # nege = n - e (0 < e < n)\n" ++
  "  j .Ltprr_have_nege\n" ++
  ".Ltprr_neg_e_zero:\n" ++
  "  la a0, tpr_nege\n" ++
  "  jal ra, secf_zero32\n" ++
  ".Ltprr_have_nege:\n" ++
  "  # 5. u1 = (-e) * r_inv mod n ; u2 = s * r_inv mod n.\n" ++
  "  la a0, tpr_nege\n" ++
  "  la a1, tpr_rinv\n" ++
  "  la a2, tpr_u1\n" ++
  "  jal ra, secf_mul_mod_n\n" ++
  "  addi a0, s4, 64             # s ptr (ABI+64)\n" ++
  "  la a1, tpr_rinv\n" ++
  "  la a2, tpr_u2\n" ++
  "  jal ra, secf_mul_mod_n\n" ++
  "  # 6. Q = u1*G + u2*R.\n" ++
  "  la a0, tpr_u1\n" ++
  "  la a1, secp256k1_generator\n" ++
  "  la a2, tpr_p1\n" ++
  "  jal ra, secp256k1_scalar_mul\n" ++
  "  la a0, tpr_u2\n" ++
  "  la a1, tpr_R\n" ++
  "  la a2, tpr_p2\n" ++
  "  jal ra, secp256k1_scalar_mul\n" ++
  "  la a0, tpr_p1\n" ++
  "  la a1, tpr_p2\n" ++
  "  mv a2, s3                   # recovered pubkey out (x || y)\n" ++
  "  jal ra, secp256k1_point_add\n" ++
  "  bnez a0, .Ltprr_recover_fail   # identity result => invalid recovery\n" ++
  "  j .Ltprr_staged_ok\n" ++
  ".Ltprr_recover_fail:\n" ++
  "  # zero the 64-byte output so callers never see partial coordinates\n" ++
  "  mv t1, s3\n" ++
  "  li t2, 8\n" ++
  ".Ltprr_zero_out:\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltprr_zero_out\n" ++
  "  li a0, 60\n" ++
  "  j .Ltprr_staged_ret\n" ++
  ".Ltprr_staged_ok:\n" ++
  "  li a0, 0\n" ++
  ".Ltprr_staged_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s3,  8(sp); ld s4, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- Static scratch buffers for `tx_pubkey_recover_raw`'s recovery math (the
    decompressed R point, the reduced hash and its negation, `r^{-1}`, the two
    scalars, and the two scalar-mul outputs). Recovery is never re-entrant, so a
    single static region is safe and mirrors the other secp256k1 helpers. Must be
    emitted (once) alongside `secp256k1CurveDataSection` /
    `secp256k1RecoverDataSection` in any build unit that links
    `txPubkeyRecoverRawFunction`. -/
def txPubkeyRecoverRawDataSection : String :=
  ".balign 8\n" ++
  "tpr_R:\n  .zero 64\n" ++
  "tpr_e:\n  .zero 32\n" ++
  "tpr_nege:\n  .zero 32\n" ++
  "tpr_rinv:\n  .zero 32\n" ++
  "tpr_u1:\n  .zero 32\n" ++
  "tpr_u2:\n  .zero 32\n" ++
  "tpr_p1:\n  .zero 64\n" ++
  "tpr_p2:\n  .zero 64\n"

/-! ## tx_pubkey_public_key_matches

    Final `public_keys` comparison helper. Mirrors execution-specs Amsterdam
    `transactions.recover_sender_from_public_key`: the supplied stateless
    `public_keys[i]` entry must equal `recover_transaction_public_key(chain_id,
    tx)`. The supplied key is a 65-byte SEC1 uncompressed point (`0x04 || x || y`);
    this helper checks the `0x04` prefix, recovers the canonical key from the
    transaction signature via `tx_pubkey_recover_raw`, and byte-compares the
    supplied 64 coordinate bytes against the recovered `x || y`.

    The prefix is checked BEFORE recovery: a non-`0x04` key can never match a
    valid recovered point, and the early-out keeps the bad-prefix path free of
    the recovery math (~2e6 ziskemu steps), so it can be probed fast.

    Calling convention:
      a0 (input)  : encoded transaction ptr
      a1 (input)  : encoded transaction byte length
      a2 (input)  : execution chain_id (u64)
      a3 (input)  : supplied public key ptr (65 bytes, 0x04 || BE x || BE y)
      a4 (input)  : recovered-pubkey scratch ptr (64 bytes, written by recover_raw)
      a5 (input)  : recover scratch ptr (>= 304 bytes, 8-byte aligned)
      ra (input)  : return
      a0 (output) : status

    Status:
      0   match: prefix ok, recovery ok, supplied coords == recovered x||y
      1   mismatch: prefix 0x04 and recovery ok, but coordinates differ
      2   bad prefix: supplied[0] != 0x04
      10  signature material failed (from tx_pubkey_recover_raw)
      20  ecrecover ABI staging failed (from tx_pubkey_recover_raw)
      60  secp256k1 recovery failed (from tx_pubkey_recover_raw)

    The 0/1/2 comparison statuses are disjoint from the 10/20/60 recovery
    statuses, so a caller can distinguish all four failure classes. -/
def txPubkeyPublicKeyMatchesFunction : String :=
  "tx_pubkey_public_key_matches:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # chain_id\n" ++
  "  mv s3, a3                   # supplied public_key (0x04 || x || y)\n" ++
  "  mv s4, a4                   # recovered pubkey out (64 bytes)\n" ++
  "  mv s5, a5                   # recover scratch (>= 304 bytes)\n" ++
  "  # 1. SEC1 uncompressed prefix must be 0x04 (cheap; before recovery).\n" ++
  "  lbu t0, 0(s3)\n" ++
  "  li t1, 4\n" ++
  "  bne t0, t1, .Ltpm_bad_prefix\n" ++
  "  # 2. Recover the canonical public key from the transaction signature.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s4; mv a4, s5\n" ++
  "  jal ra, tx_pubkey_recover_raw\n" ++
  "  bnez a0, .Ltpm_ret          # propagate material/stage/recovery failure\n" ++
  "  # 3. Byte-compare supplied[1..65] against recovered x||y (64 bytes).\n" ++
  "  addi t0, s3, 1              # supplied coordinate bytes\n" ++
  "  mv t1, s4                   # recovered coordinate bytes\n" ++
  "  li t2, 64\n" ++
  ".Ltpm_cmp:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1)\n" ++
  "  bne t3, t4, .Ltpm_mismatch\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltpm_cmp\n" ++
  "  li a0, 0\n" ++
  "  j .Ltpm_ret\n" ++
  ".Ltpm_mismatch:\n" ++
  "  li a0, 1\n" ++
  "  j .Ltpm_ret\n" ++
  ".Ltpm_bad_prefix:\n" ++
  "  li a0, 2\n" ++
  ".Ltpm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_tx_pubkey_ecrecover_stage_material`: probe BuildUnit.
    Reads the same input as `zisk_tx_pubkey_signature_material`, first builds
    material at OUTPUT+8, then stages accelerator ABI bytes at OUTPUT+136.

    Output layout:
      +0    material status
      +8    128-byte material block
      +136  stage status
      +144  staged message hash
      +176  staged signature r||s
      +240  staged recid word
      +248  reserved pubkey buffer -/
def ziskTxPubkeyEcrecoverStageMaterialPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx ptr\n" ++
  "  li a3, 0xa0010008           # material out\n" ++
  "  jal ra, tx_pubkey_signature_material\n" ++
  "  li s0, 0xa0010000\n" ++
  "  sd a0, 0(s0)                # material status\n" ++
  "  bnez a0, .Ltpes_probe_done\n" ++
  "  addi a0, s0, 8              # material ptr\n" ++
  "  addi a1, s0, 144            # staged ABI ptr\n" ++
  "  jal ra, tx_pubkey_ecrecover_stage_material\n" ++
  "  sd a0, 136(s0)              # stage status\n" ++
  "  j .Ltpes_probe_done\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  ".Ltpes_probe_done:"

/-- `zisk_tx_pubkey_signature_material`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tx byte length
      bytes  8..16 : execution chain_id
      bytes 16..   : encoded transaction

    Output layout:
      bytes  0.. 8 : status
      bytes  8..   : `tx_pubkey_signature_material` output layout. -/
def ziskTxPubkeySignatureMaterialPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx ptr\n" ++
  "  li a3, 0xa0010008           # material out\n" ++
  "  jal ra, tx_pubkey_signature_material\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltps_pdone\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  ".Ltps_pdone:"

def ziskTxPubkeySignatureMaterialDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "tps_type:\n  .zero 8\n" ++
  "tps_inner_off:\n  .zero 8\n" ++
  "tps_v:\n  .zero 8\n" ++
  "tps_cmp:\n  .zero 8\n" ++
  "tps_secp256k1_n:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "tps_secp256k1_half_n:\n" ++
  "  .byte 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d\n" ++
  "  .byte 0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0\n" ++
  "tlxs_offset:\n  .zero 8\n" ++
  "tlxs_length:\n  .zero 8\n" ++
  "txes_offset:\n  .zero 8\n" ++
  "txes_length:\n  .zero 8\n" ++
  "t29es_offset:\n  .zero 8\n" ++
  "t29es_length:\n  .zero 8\n" ++
  "t44es_offset:\n  .zero 8\n" ++
  "t44es_length:\n  .zero 8\n" ++
  "t77es_offset:\n  .zero 8\n" ++
  "t77es_length:\n  .zero 8\n" ++
  "tsh_buf:\n  .zero 131072\n" ++
  "tsh_trunc_len:\n  .zero 8\n" ++
  "rltn_offset_lo:\n  .zero 8\n" ++
  "rltn_length_lo:\n  .zero 8\n" ++
  "rltn_offset_hi:\n  .zero 8\n" ++
  "rltn_length_hi:\n  .zero 8\n" ++
  "rltn_prefix_len:\n  .zero 8\n" ++
  "t155_buf:\n  .zero 131072\n" ++
  "t155_offset_lo:\n  .zero 8\n" ++
  "t155_length_lo:\n  .zero 8\n" ++
  "t155_offset_hi:\n  .zero 8\n" ++
  "t155_length_hi:\n  .zero 8\n" ++
  "t155_chain_be:\n  .zero 8\n" ++
  "t155_chain_enc:\n  .zero 9\n" ++
  ".balign 8\n" ++
  "t155_prefix_len:\n  .zero 8"

def ziskTxPubkeyEcrecoverStageMaterialProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPubkeyEcrecoverStageMaterialPrologue
  dataAsm     := ziskTxPubkeySignatureMaterialDataSection
}

def ziskTxPubkeySignatureMaterialProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPubkeySignatureMaterialPrologue
  dataAsm     := ziskTxPubkeySignatureMaterialDataSection
}

/-- `zisk_tx_pubkey_recover_raw_status`: probe BuildUnit.

    Drives `tx_pubkey_recover_raw` over one transaction and exposes both the
    helper status and the material-failure side slot, so a script can assert a
    valid tx reaches status 50 (material+stage succeeded, recovery backend not
    implemented) while a malformed/high-s tx surfaces the material failure
    class (status 10 with the material status preserved).

    Input layout (same as `zisk_tx_pubkey_signature_material`):
      bytes  0.. 8 : tx byte length
      bytes  8..16 : execution chain_id
      bytes 16..   : encoded transaction

    Output layout:
      +0  helper status (10 material fail, 20 stage fail, 50 backend stub)
      +8  material status side slot (meaningful when helper status == 10) -/
def ziskTxPubkeyRecoverRawStatusPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx ptr\n" ++
  "  la a3, tprr_pubkey_out      # recovered pubkey out (64 bytes)\n" ++
  "  la a4, tprr_scratch         # scratch (>= 304 bytes)\n" ++
  "  jal ra, tx_pubkey_recover_raw\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # helper status\n" ++
  "  la t1, tprr_scratch\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)                # material status side slot\n" ++
  "  # copy the 64-byte recovered pubkey (x||y) to output+16 for assertions\n" ++
  "  la t1, tprr_pubkey_out\n" ++
  "  addi t0, t0, 16\n" ++
  "  li t2, 8\n" ++
  ".Ltprrs_copy_pub:\n" ++
  "  ld t3, 0(t1); sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8; addi t0, t0, 8; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltprrs_copy_pub\n" ++
  "  j .Ltprrs_pdone\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  -- secp256k1 recovery stack (curve common already provides u256_lt_be/_add_be/
  -- _sub_be, so the standalone u256_lt_be above is dropped to avoid a duplicate
  -- label).
  secp256k1CurveCommonFunctions ++ "\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  txPubkeyRecoverRawFunction ++ "\n" ++
  secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
  ".Ltprrs_pdone:"

def ziskTxPubkeyRecoverRawStatusDataSection : String :=
  ziskTxPubkeySignatureMaterialDataSection ++ "\n" ++
  secp256k1CurveDataSection ++ "\n" ++
  secp256k1RecoverDataSection ++ "\n" ++
  txPubkeyRecoverRawDataSection ++ "\n" ++
  "tprr_pubkey_out:\n  .zero 64\n" ++
  "tprr_scratch:\n  .zero 312"

def ziskTxPubkeyRecoverRawStatusProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPubkeyRecoverRawStatusPrologue
  dataAsm     := ziskTxPubkeyRecoverRawStatusDataSection
}

/-- `zisk_tx_pubkey_public_key_matches_status`: probe BuildUnit.

    Drives `tx_pubkey_public_key_matches` over one transaction and a supplied
    SEC1 public key. The cheap cases (bad prefix; signature-material failure)
    are decided before the recovery, so they run in a small step budget; the
    match/mismatch cases run a full accelerator-backed recovery (~2e6 steps,
    gated behind the check script's `RECOVER_RAW_FULL=1` switch).

    Input layout:
      bytes  0.. 8 : tx byte length
      bytes  8..16 : execution chain_id
      bytes 16..81 : supplied public key (65 bytes, 0x04 || x || y)
      bytes 88..   : encoded transaction (8-byte aligned)

    Output layout:
      +0  match status (0 match, 1 mismatch, 2 bad prefix, 10/20/60 recovery)
      +8  reserved (zero)
      +16 recovered public key (64 bytes, BE x||y; zeroed on recovery failure) -/
def ziskTxPubkeyPublicKeyMatchesStatusPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000           # input base (ziskemu writes an 8-byte length\n" ++
  "                              # header at +0, so user byte k is at t6+8+k)\n" ++
  "  ld a1, 8(t6)                # tx_len      (user +0)\n" ++
  "  ld a2, 16(t6)               # chain_id    (user +8)\n" ++
  "  addi a3, t6, 24             # supplied public key ptr (65 bytes; user +16)\n" ++
  "  addi a0, t6, 96             # tx ptr       (user +88)\n" ++
  "  la a4, tpm_pubkey_out       # recovered pubkey out (64 bytes)\n" ++
  "  la a5, tpm_scratch          # recover scratch (>= 304 bytes)\n" ++
  "  jal ra, tx_pubkey_public_key_matches\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # match status\n" ++
  "  sd zero, 8(t0)              # reserved\n" ++
  "  # copy the 64-byte recovered pubkey (x||y) to output+16 for assertions\n" ++
  "  la t1, tpm_pubkey_out\n" ++
  "  addi t0, t0, 16\n" ++
  "  li t2, 8\n" ++
  ".Ltpms_copy_pub:\n" ++
  "  ld t3, 0(t1); sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8; addi t0, t0, 8; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltpms_copy_pub\n" ++
  "  j .Ltpms_pdone\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  -- secp256k1 recovery stack (curve common already provides u256_lt_be/_add_be/
  -- _sub_be, so no standalone u256_lt_be is linked here to avoid a duplicate
  -- label).
  secp256k1CurveCommonFunctions ++ "\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  txPubkeyRecoverRawFunction ++ "\n" ++
  secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
  txPubkeyPublicKeyMatchesFunction ++ "\n" ++
  ".Ltpms_pdone:"

def ziskTxPubkeyPublicKeyMatchesStatusDataSection : String :=
  ziskTxPubkeySignatureMaterialDataSection ++ "\n" ++
  secp256k1CurveDataSection ++ "\n" ++
  secp256k1RecoverDataSection ++ "\n" ++
  txPubkeyRecoverRawDataSection ++ "\n" ++
  "tpm_pubkey_out:\n  .zero 64\n" ++
  "tpm_scratch:\n  .zero 312"

def ziskTxPubkeyPublicKeyMatchesStatusProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPubkeyPublicKeyMatchesStatusPrologue
  dataAsm     := ziskTxPubkeyPublicKeyMatchesStatusDataSection
}

end EvmAsm.Codegen
