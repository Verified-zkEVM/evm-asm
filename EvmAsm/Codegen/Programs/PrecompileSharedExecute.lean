/-
  EvmAsm.Codegen.Programs.PrecompileSharedExecute

  Route-neutral precompile execution core (#11163 item 2).

  Descriptor I/O only (`precompile_shared_ctx` + selector/cost/status from
  `precompile_shared_select_price`). Writes `evm_precompile_frame` returndata.
  Does **not** charge gas, copy to CALL OUT windows, or branch on depth.
  Spec shape: pin e5a8caf1b `src/ethereum/amsterdam/vm/interpreter.py:398-401`
  (`PRE_COMPILED_CONTRACTS[code_address](evm)` after `move_ether`).

  ABI: `jal`/`ret`; a0 = 0 success (including soft-empty returndata);
  a0 ≠ 0 hard fail (exceptional halt / InvalidParameter / kernel EFAIL).
  Callers own charge policy and OUT/exit framing.
-/

import EvmAsm.Codegen.Programs.Modexp
import EvmAsm.Codegen.Programs.PrecompileRuntime

namespace EvmAsm.Codegen

private def pseLoadCtx (ptrReg sizeReg : String) : String :=
  "  la t0, precompile_shared_ctx\n" ++
  "  ld " ++ ptrReg ++ ", 8(t0)\n" ++
  "  ld " ++ sizeReg ++ ", 16(t0)\n"

/-- EIP-2537 G1 compact 96 → padded 128-byte returndata at frame+16. -/
private def pseBlsG1PadRetdataAsm (tag : String) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  "  li x22, 16\n" ++
  ".L" ++ tag ++ "_blsg1_pad1:\n" ++
  "  sb x0, 0(x18); addi x18, x18, 1; addi x22, x22, -1; bnez x22, .L" ++ tag ++ "_blsg1_pad1\n" ++
  precompileFrameAddi "x19" precompileFrameBls12G1OutputOff ++
  "  li x22, 48\n" ++
  ".L" ++ tag ++ "_blsg1_cx:\n" ++
  "  lbu x16, 0(x19); sb x16, 0(x18); addi x19, x19, 1; addi x18, x18, 1; addi x22, x22, -1; bnez x22, .L" ++ tag ++ "_blsg1_cx\n" ++
  "  li x22, 16\n" ++
  ".L" ++ tag ++ "_blsg1_pad2:\n" ++
  "  sb x0, 0(x18); addi x18, x18, 1; addi x22, x22, -1; bnez x22, .L" ++ tag ++ "_blsg1_pad2\n" ++
  "  li x22, 48\n" ++
  ".L" ++ tag ++ "_blsg1_cy:\n" ++
  "  lbu x16, 0(x19); sb x16, 0(x18); addi x19, x19, 1; addi x18, x18, 1; addi x22, x22, -1; bnez x22, .L" ++ tag ++ "_blsg1_cy\n" ++
  "  li x16, 1; sd x16, 0(x15); li x16, 128; sd x16, 8(x15)\n"

/-- EIP-2537 G2 compact 192 → padded 256-byte returndata at frame+16. -/
private def pseBlsG2PadRetdataAsm (tag : String) (compactOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  precompileFrameAddi "x19" compactOff ++
  "  li x23, 4\n" ++
  ".L" ++ tag ++ "_blsg2_comp:\n" ++
  "  li x22, 16\n" ++
  ".L" ++ tag ++ "_blsg2_pad:\n" ++
  "  sb x0, 0(x18); addi x18, x18, 1; addi x22, x22, -1; bnez x22, .L" ++ tag ++ "_blsg2_pad\n" ++
  "  li x22, 48\n" ++
  ".L" ++ tag ++ "_blsg2_cx:\n" ++
  "  lbu x16, 0(x19); sb x16, 0(x18); addi x19, x19, 1; addi x18, x18, 1; addi x22, x22, -1; bnez x22, .L" ++ tag ++ "_blsg2_cx\n" ++
  "  addi x23, x23, -1; bnez x23, .L" ++ tag ++ "_blsg2_comp\n" ++
  "  li x16, 1; sd x16, 0(x15); li x16, 256; sd x16, 8(x15)\n"

/-- KZG FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS constant returndata (64 bytes). -/
private def pseKzgPointEvalRetdataAsm : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  "  li x22, 30\n" ++
  ".Lpse_kzg_field_zero:\n" ++
  "  beqz x22, .Lpse_kzg_field_tail\n" ++
  "  sb x0, 0(x18); addi x18, x18, 1; addi x22, x22, -1; j .Lpse_kzg_field_zero\n" ++
  ".Lpse_kzg_field_tail:\n" ++
  "  li x16, 0x10; sb x16, 0(x18); sb x0, 1(x18); addi x18, x18, 2\n" ++
  "  li x16, 0x73; sb x16, 0(x18)\n" ++
  "  li x16, 0xed; sb x16, 1(x18)\n" ++
  "  li x16, 0xa7; sb x16, 2(x18)\n" ++
  "  li x16, 0x53; sb x16, 3(x18)\n" ++
  "  li x16, 0x29; sb x16, 4(x18)\n" ++
  "  li x16, 0x9d; sb x16, 5(x18)\n" ++
  "  li x16, 0x7d; sb x16, 6(x18)\n" ++
  "  li x16, 0x48; sb x16, 7(x18)\n" ++
  "  li x16, 0x33; sb x16, 8(x18)\n" ++
  "  li x16, 0x39; sb x16, 9(x18)\n" ++
  "  li x16, 0xd8; sb x16, 10(x18)\n" ++
  "  li x16, 0x08; sb x16, 11(x18)\n" ++
  "  li x16, 0x09; sb x16, 12(x18)\n" ++
  "  li x16, 0xa1; sb x16, 13(x18)\n" ++
  "  li x16, 0xd8; sb x16, 14(x18)\n" ++
  "  li x16, 0x05; sb x16, 15(x18)\n" ++
  "  li x16, 0x53; sb x16, 16(x18)\n" ++
  "  li x16, 0xbd; sb x16, 17(x18)\n" ++
  "  li x16, 0xa4; sb x16, 18(x18)\n" ++
  "  li x16, 0x02; sb x16, 19(x18)\n" ++
  "  li x16, 0xff; sb x16, 20(x18)\n" ++
  "  li x16, 0xfe; sb x16, 21(x18)\n" ++
  "  li x16, 0x5b; sb x16, 22(x18)\n" ++
  "  li x16, 0xfe; sb x16, 23(x18)\n" ++
  "  li x16, 0xff; sb x16, 24(x18); sb x16, 25(x18); sb x16, 26(x18); sb x16, 27(x18)\n" ++
  "  sb x0, 28(x18); sb x0, 29(x18); sb x0, 30(x18)\n" ++
  "  li x16, 0x01; sb x16, 31(x18)\n" ++
  "  li x16, 1; sd x16, 0(x15); li x16, 64; sd x16, 8(x15)\n"

/-- Linked execution core. Selector already in `precompile_shared_selector`. -/
def precompileSharedExecuteFunction : String :=
  "precompile_shared_execute:\n" ++
  -- Save ra + callee-saved: internal `jal` to zkvm_* overwrites ra; arms also
  -- clobber s2-s8 (x18-x24). Without this, `.Lpse_ok: ret` loops to the
  -- post-jal site (sha256/ripemd/bn254/bls hang = step-cap).
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  sd s9, 80(sp)\n" ++
  "  sd s10, 88(sp)\n" ++
  "  sd s11, 96(sp)\n" ++
  "  la t0, precompile_shared_selector\n" ++
  "  ld x14, 0(t0)\n" ++
  "  beqz x14, .Lpse_fail\n" ++
  -- Soft-empty leaves x15 = evm_precompile_frame. Keep it as the frame base
  -- through dispatch: branch scratch is x16 only (precompileFrameAddi uses x15).
  precompileFrameSoftEmptyAsm ++
  "  li x16, 4\n" ++
  "  bgeu x16, x14, .Lpse_legacy\n" ++
  precompileSelectorBranchesAsm "x14" "x16" false
    [ ("5", ".Lpse_modexp")
    , ("0x06", ".Lpse_bn254_add")
    , ("0x07", ".Lpse_bn254_mul")
    , ("0x08", ".Lpse_bn254_pairing")
    , ("0x09", ".Lpse_blake2f")
    , ("0x0a", ".Lpse_kzg")
    , ("0x0b", ".Lpse_bls_g1add")
    , ("0x0c", ".Lpse_bls_g1msm")
    , ("0x0d", ".Lpse_bls_g2add")
    , ("0x0e", ".Lpse_bls_g2msm")
    , ("0x0f", ".Lpse_bls_pairing")
    , ("0x10", ".Lpse_bls_map_g1")
    , ("0x11", ".Lpse_bls_map_g2")
    , ("0x100", ".Lpse_p256") ] ++
  "  j .Lpse_fail\n" ++
  -- Selectors 1-4: ecrecover / sha256 / ripemd160 / identity
  ".Lpse_legacy:\n" ++
  "  li x16, 1\n" ++
  "  beq x14, x16, .Lpse_ecrecover\n" ++
  "  li x16, 2\n" ++
  "  beq x14, x16, .Lpse_sha256\n" ++
  "  li x16, 3\n" ++
  "  beq x14, x16, .Lpse_ripemd\n" ++
  "  li x16, 4\n" ++
  "  bne x14, x16, .Lpse_fail\n" ++
  -- IDENTITY: returndata = full input (clamped to frame cap)
  ".Lpse_identity:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "x18" "x17" ++
  "  sd x17, 8(x15)\n" ++
  "  mv x22, x18\n" ++
  "  addi x23, x15, 16\n" ++
  "  mv x24, x17\n" ++
  "  li x16, " ++ toString precompileFrameReturndataCapBytes ++ "\n" ++
  "  bgeu x16, x24, .Lpse_id_len_ok\n" ++
  "  mv x24, x16\n" ++
  ".Lpse_id_len_ok:\n" ++
  "  beqz x24, .Lpse_ok\n" ++
  ".Lpse_id_copy:\n" ++
  "  lbu x16, 0(x22); sb x16, 0(x23)\n" ++
  "  addi x22, x22, 1; addi x23, x23, 1; addi x24, x24, -1\n" ++
  "  bnez x24, .Lpse_id_copy\n" ++
  "  j .Lpse_ok\n" ++
  -- SHA256
  ".Lpse_sha256:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  li x16, 32; sd x16, 8(x15)\n" ++
  pseLoadCtx "a0" "a1" ++
  "  addi a2, x15, 16\n" ++
  "  jal x1, zkvm_sha256\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  "  j .Lpse_ok\n" ++
  -- RIPEMD160 (kernel left-pads to 32)
  ".Lpse_ripemd:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  li x16, 32; sd x16, 8(x15)\n" ++
  pseLoadCtx "a0" "a1" ++
  "  addi a2, x15, 16\n" ++
  "  jal x1, zkvm_ripemd160\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  "  j .Lpse_ok\n" ++
  -- ECRECOVER: soft-empty on bad v/r/s/sig; address on success
  ".Lpse_ecrecover:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "x18" "x17" ++
  stageEcrecoverInputFromAsm "x18" "x17" ++
  ecrecoverVGateAsm ".Lpse_soft_ok" ++
  ecrecoverNonzeroRSGateAsm ".Lpse_soft_ok" ++
  ecrecoverScalarOrderGateAsm ".Lpse_soft_ok" ++
  ecrecoverRecoverToFrameAsm ".Lpse_soft_ok" ++
  "  j .Lpse_ok\n" ++
  -- MODEXP: charge-free absolute body (select_price already validated lengths)
  ".Lpse_modexp:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  modexpSharedExecuteAsm ++
  -- BN254 ADD
  ".Lpse_bn254_add:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "x24" "x17" ++
  stagePrecompileInputWindowFromAsm "pse_bn254_add_p1" "x24" "x17"
    precompileFrameBls12G1Input0Off 0 64 ++
  stagePrecompileInputWindowFromAsm "pse_bn254_add_p2" "x24" "x17"
    precompileFrameBls12G1Input1Off 64 64 ++
  precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
  precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  "  jal x1, zkvm_bn254_g1_add\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  precompileFrameSetRetdataFromOffAsm "pse_bn254_add" precompileFrameBls12G1OutputOff 64 ++
  "  j .Lpse_ok\n" ++
  -- BN254 MUL
  ".Lpse_bn254_mul:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "x24" "x17" ++
  stagePrecompileInputWindowFromAsm "pse_bn254_mul_pt" "x24" "x17"
    precompileFrameBls12G1Input0Off 0 64 ++
  stagePrecompileInputWindowFromAsm "pse_bn254_mul_sc" "x24" "x17"
    precompileFrameBls12G1Input1Off 64 32 ++
  precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
  precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  "  jal x1, zkvm_bn254_g1_mul\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  precompileFrameSetRetdataFromOffAsm "pse_bn254_mul" precompileFrameBls12G1OutputOff 64 ++
  "  j .Lpse_ok\n" ++
  -- BN254 pairing
  ".Lpse_bn254_pairing:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x18" ++
  "  li x16, 192\n" ++
  "  remu x17, x18, x16\n" ++
  "  bnez x17, .Lpse_fail\n" ++
  "  divu a1, x18, x16\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  "  jal x1, zkvm_bn254_pairing\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  precompileFrameSetBoolFromOffAsm precompileFrameBls12G1OutputOff ++
  "  j .Lpse_ok\n" ++
  -- BLAKE2F
  ".Lpse_blake2f:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "x24" "x16" ++
  "  li x17, 213\n" ++
  "  bne x16, x17, .Lpse_fail\n" ++
  stagePrecompileInputWindowFromAsm "pse_blake2f" "x24" "x16"
    precompileFrameBls12G2InputOff 0 213 ++
  precompileFrameAddi "x18" precompileFrameBls12G2InputOff ++
  "  lbu x16, 0(x18); slli x16, x16, 24\n" ++
  "  lbu x17, 1(x18); slli x17, x17, 16; or x16, x16, x17\n" ++
  "  lbu x17, 2(x18); slli x17, x17, 8; or x16, x16, x17\n" ++
  "  lbu x17, 3(x18); or x16, x16, x17\n" ++
  "  lbu x17, 212(x18)\n" ++
  "  li x22, 1\n" ++
  "  bltu x22, x17, .Lpse_fail\n" ++
  "  mv a0, x16\n" ++
  precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 4) ++
  precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 68) ++
  precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 196) ++
  "  mv a4, x17\n" ++
  "  jal x1, zkvm_blake2f\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  precompileFrameSetRetdataFromOffAsm "pse_blake2f" (precompileFrameBls12G2InputOff + 4) 64 ++
  "  j .Lpse_ok\n" ++
  -- KZG point evaluation
  ".Lpse_kzg:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "x24" "x16" ++
  "  li x17, 192\n" ++
  "  bne x16, x17, .Lpse_fail\n" ++
  stagePrecompileInputWindowFromAsm "pse_kzg" "x24" "x16"
    precompileFrameBls12G2InputOff 0 192 ++
  kzgVersionedHashGateAsm ".Lpse_fail" ++
  "  la x15, evm_precompile_frame\n" ++
  "  sb x0, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
  precompileFrameAddi "a0" (precompileFrameBls12G2InputOff + 96) ++
  precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 32) ++
  precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 64) ++
  precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 144) ++
  precompileFrameAddi "a4" precompileFrameBls12G2OutputOff ++
  "  jal x1, zkvm_kzg_point_eval\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  lbu x16, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
  "  beqz x16, .Lpse_fail\n" ++
  pseKzgPointEvalRetdataAsm ++
  "  j .Lpse_ok\n" ++
  -- P256VERIFY: wrong length / invalid sig = soft empty; EFAIL = hard fail
  ".Lpse_p256:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "x24" "x16" ++
  "  li x17, 160\n" ++
  "  bne x16, x17, .Lpse_soft_ok\n" ++
  stagePrecompileInputWindowFromAsm "pse_p256" "x24" "x16"
    precompileFrameBls12G2InputOff 0 160 ++
  "  la x15, evm_precompile_frame\n" ++
  "  sb x0, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
  precompileFrameAddi "a0" precompileFrameBls12G2InputOff ++
  precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 32) ++
  precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 96) ++
  precompileFrameAddi "a3" precompileFrameBls12G2OutputOff ++
  "  jal x1, zkvm_secp256r1_verify\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  lbu x16, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
  "  beqz x16, .Lpse_soft_ok\n" ++
  precompileFrameSetBoolFromOffAsm precompileFrameBls12G2OutputOff ++
  "  j .Lpse_ok\n" ++
  -- BLS G1 ADD
  ".Lpse_bls_g1add:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x17" ++
  "  li x16, 256\n" ++
  "  bne x17, x16, .Lpse_fail\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
  "  jal x1, zkvm_bls12_g1_add\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  pseBlsG1PadRetdataAsm "pse_g1add" ++
  "  j .Lpse_ok\n" ++
  -- BLS G1 MSM
  ".Lpse_bls_g1msm:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x18" ++
  "  beqz x18, .Lpse_fail\n" ++
  "  li x16, 160\n" ++
  "  remu x17, x18, x16\n" ++
  "  bnez x17, .Lpse_fail\n" ++
  "  divu a1, x18, x16\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  "  jal x1, zkvm_bls12_g1_msm\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  pseBlsG1PadRetdataAsm "pse_g1msm" ++
  "  j .Lpse_ok\n" ++
  -- BLS G2 ADD
  ".Lpse_bls_g2add:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x17" ++
  "  li x16, 512\n" ++
  "  bne x17, x16, .Lpse_fail\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G2AddOutputOff ++
  "  jal x1, zkvm_bls12_g2_add\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  pseBlsG2PadRetdataAsm "pse_g2add" precompileFrameBls12G2AddOutputOff ++
  "  j .Lpse_ok\n" ++
  -- BLS G2 MSM
  ".Lpse_bls_g2msm:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x18" ++
  "  beqz x18, .Lpse_fail\n" ++
  "  li x16, 288\n" ++
  "  remu x17, x18, x16\n" ++
  "  bnez x17, .Lpse_fail\n" ++
  "  divu a1, x18, x16\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G2OutputOff ++
  "  jal x1, zkvm_bls12_g2_msm\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  pseBlsG2PadRetdataAsm "pse_g2msm" precompileFrameBls12G2OutputOff ++
  "  j .Lpse_ok\n" ++
  -- BLS pairing
  ".Lpse_bls_pairing:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x18" ++
  "  beqz x18, .Lpse_fail\n" ++
  "  li x16, 384\n" ++
  "  remu x17, x18, x16\n" ++
  "  bnez x17, .Lpse_fail\n" ++
  "  divu a1, x18, x16\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  "  jal x1, zkvm_bls12_pairing\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  precompileFrameSetBoolFromOffAsm precompileFrameBls12G1OutputOff ++
  "  j .Lpse_ok\n" ++
  -- BLS map Fp → G1
  ".Lpse_bls_map_g1:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x17" ++
  "  li x16, 64\n" ++
  "  bne x17, x16, .Lpse_fail\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
  "  jal x1, zkvm_bls12_map_fp_to_g1\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  pseBlsG1PadRetdataAsm "pse_map_g1" ++
  "  j .Lpse_ok\n" ++
  -- BLS map Fp2 → G2
  ".Lpse_bls_map_g2:\n" ++
  "  la x15, evm_precompile_frame\n" ++
  pseLoadCtx "a0" "x17" ++
  "  li x16, 128\n" ++
  "  bne x17, x16, .Lpse_fail\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G2OutputOff ++
  "  jal x1, zkvm_bls12_map_fp2_to_g2\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  pseBlsG2PadRetdataAsm "pse_map_g2" precompileFrameBls12G2OutputOff ++
  "  j .Lpse_ok\n" ++
  ".Lpse_soft_ok:\n" ++
  precompileFrameSoftEmptyAsm ++
  ".Lpse_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lpse_epilogue\n" ++
  ".Lpse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpse_epilogue:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  ld s9, 80(sp)\n" ++
  "  ld s10, 88(sp)\n" ++
  "  ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n"

end EvmAsm.Codegen
