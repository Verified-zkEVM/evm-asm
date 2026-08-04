/-
  EvmAsm.Codegen.Programs.PrecompileRuntime

  Shared precompile helper builders reused by Noop.lean's child-frame
  handler (`childFrameHandlers`) across multiple precompile entries:
  ECRECOVER fixed-gas and input staging, and general precompile-frame
  window copy helpers added for BN254 / BLS12 / KZG backends.

  Extracted from Noop.lean to keep that file under the 1500-line guard.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def precompileFrameAddi (dst : String) (off : Nat) : String :=
  "  addi " ++ dst ++ ", x15, " ++ toString off ++ "\n"

/-- Classify a canonical 20-byte big-endian address as an Osaka precompile
    number. The selector is independent of the caller's stack, memory, gas,
    and continuation conventions: callers supply the address bytes and retain
    ownership of the branch targets. A zero result means that the address is
    not a supported precompile. -/
def precompileAddressClassifyAsm
    (tag addressReg resultReg indexReg byteReg : String) : String :=
  "  li " ++ resultReg ++ ", 0\n" ++
  "  li " ++ indexReg ++ ", 0\n" ++
  ".L" ++ tag ++ "_precompile_high_zero:\n" ++
  "  li " ++ byteReg ++ ", 18\n" ++
  "  beq " ++ indexReg ++ ", " ++ byteReg ++ ", .L" ++ tag ++ "_precompile_low\n" ++
  "  add " ++ byteReg ++ ", " ++ addressReg ++ ", " ++ indexReg ++ "; lbu " ++ byteReg ++ ", 0(" ++ byteReg ++ ")\n" ++
  "  bnez " ++ byteReg ++ ", .L" ++ tag ++ "_precompile_done\n" ++
  "  addi " ++ indexReg ++ ", " ++ indexReg ++ ", 1; j .L" ++ tag ++ "_precompile_high_zero\n" ++
  ".L" ++ tag ++ "_precompile_low:\n" ++
  "  lbu " ++ resultReg ++ ", 18(" ++ addressReg ++ "); slli " ++ resultReg ++ ", " ++ resultReg ++ ", 8\n" ++
  "  lbu " ++ byteReg ++ ", 19(" ++ addressReg ++ "); or " ++ resultReg ++ ", " ++ resultReg ++ ", " ++ byteReg ++ "\n" ++
  "  li " ++ byteReg ++ ", 1; bltu " ++ resultReg ++ ", " ++ byteReg ++ ", .L" ++ tag ++ "_precompile_none\n" ++
  "  li " ++ byteReg ++ ", 0x11; bgeu " ++ byteReg ++ ", " ++ resultReg ++ ", .L" ++ tag ++ "_precompile_done\n" ++
  "  li " ++ byteReg ++ ", 0x100; beq " ++ resultReg ++ ", " ++ byteReg ++ ", .L" ++ tag ++ "_precompile_done\n" ++
  ".L" ++ tag ++ "_precompile_none:\n" ++
  "  li " ++ resultReg ++ ", 0\n" ++
  ".L" ++ tag ++ "_precompile_done:\n"

/-- Emit the selector-to-handler branch table shared by root and child
    precompile dispatchers.  Classification owns the numeric selector; this
    helper only emits caller-owned targets, so output, success, continuation,
    and gas-allotment policy remain at each call site. -/
def precompileSelectorBranchesAsm
    (selectorReg scratchReg : String) (inline : Bool) : List (String × String) → String
  | [] => ""
  | (selector, target) :: rest =>
      (if inline then
        "  li " ++ scratchReg ++ ", " ++ selector ++ "; beq " ++
          selectorReg ++ ", " ++ scratchReg ++ ", " ++ target ++ "\n"
       else
        "  li " ++ scratchReg ++ ", " ++ selector ++ "\n" ++
          "  beq " ++ selectorReg ++ ", " ++ scratchReg ++ ", " ++ target ++ "\n") ++
      precompileSelectorBranchesAsm selectorReg scratchReg inline rest

/-- Call a precompile validity kernel and branch on its status. The optional
    post-call text is for caller-local ABI restoration (the child path saves
    its dispatch registers around LP64 kernels); it deliberately does not
    encode output, success, continuation, or gas-allotment policy. -/
def precompileKernelCallAsm
    (linkReg kernel statusReg failLabel afterCall callPrefix : String) : String :=
  callPrefix ++ "jal " ++ linkReg ++ ", " ++ kernel ++ "\n" ++
  afterCall ++
  "  bnez " ++ statusReg ++ ", " ++ failLabel ++ "\n"

private def precompileGasRemainingOff : Nat := 568

def chargePrecompileGasAsm (costReg remainingReg : String) : String :=
  "  ld " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  bltu " ++ remainingReg ++ ", " ++ costReg ++ ", .exit_outofgas\n" ++
  "  sub " ++ remainingReg ++ ", " ++ remainingReg ++ ", " ++ costReg ++ "\n" ++
  "  sd " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n"

/-- Materialize a fixed precompile gas formula.  The caller retains the
    distinct child-allotment or top-level-settlement policy. -/
def precompileFixedGasCostAsm (cost : Nat) (costReg : String) : String :=
  "  li " ++ costReg ++ ", " ++ toString cost ++ "\n"

def chargePrecompileGasConstAsm (cost : Nat)
    (costReg remainingReg : String) : String :=
  precompileFixedGasCostAsm cost costReg ++
  chargePrecompileGasAsm costReg remainingReg

/-- Compute the common `base + perWord * ceil(size / 32)` precompile cost.
    Charging remains with the caller: child messages apply the result to their
    EIP-150 allotment, while the top-level transaction route records it for
    transaction settlement. -/
def precompileWordGasCostAsm
    (overflowLabel : String) (baseGas perWordGas : Nat)
    (sizeReg costReg scratchReg : String) : String :=
  "  li " ++ scratchReg ++ ", 31\n" ++
  "  add " ++ costReg ++ ", " ++ sizeReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bltu " ++ costReg ++ ", " ++ sizeReg ++ ", " ++ overflowLabel ++ "\n" ++
  "  srli " ++ costReg ++ ", " ++ costReg ++ ", 5\n" ++
  "  li " ++ scratchReg ++ ", " ++ toString perWordGas ++ "\n" ++
  "  mul " ++ costReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  "  li " ++ scratchReg ++ ", " ++ toString baseGas ++ "\n" ++
  "  add " ++ costReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n"

/-- Compute `base + perUnit * floor(size / unit)` and reject machine-word
    overflow.  Input-shape validation and charging remain caller concerns. -/
def precompilePerUnitGasCostAsm
    (overflowLabel : String) (unit baseGas perUnit : Nat)
    (sizeReg costReg quotientReg scratchReg : String) : String :=
  "  li " ++ scratchReg ++ ", " ++ toString unit ++ "\n" ++
  "  divu " ++ quotientReg ++ ", " ++ sizeReg ++ ", " ++ scratchReg ++ "\n" ++
  "  li " ++ scratchReg ++ ", " ++ toString perUnit ++ "\n" ++
  "  mulhu " ++ costReg ++ ", " ++ quotientReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bnez " ++ costReg ++ ", " ++ overflowLabel ++ "\n" ++
  "  mul " ++ costReg ++ ", " ++ quotientReg ++ ", " ++ scratchReg ++ "\n" ++
  "  li " ++ scratchReg ++ ", " ++ toString baseGas ++ "\n" ++
  "  add " ++ costReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bltu " ++ costReg ++ ", " ++ scratchReg ++ ", " ++ overflowLabel ++ "\n"

def chargePrecompileGasWithAllotmentAsm
    (tag costReg remainingReg : String) : String :=
  "  jal x1, bn254_call_allotment\n" ++
  "  bltu x22, " ++ costReg ++ ", .L" ++ tag ++ "_bn254_fail_burn\n" ++
  "  ld " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  sub " ++ remainingReg ++ ", " ++ remainingReg ++ ", " ++ costReg ++ "\n" ++
  "  sd " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n"

/-- MODEXP has already parsed the input size and three length fields when it
    charges gas. The shared allotment helper clobbers x17/x22/x23, so this
    variant preserves those parsed values on the successful path. If the child
    allotment is too small, the failure stub exits immediately and the saved
    temporaries do not need restoring. -/
def chargePrecompileGasWithAllotmentPreservingModexpAsm
    (tag costReg remainingReg : String) : String :=
  "  mv x6, x17
  mv x7, x22
  mv x28, x23
  jal x1, bn254_call_allotment
" ++
  "  bltu x22, " ++ costReg ++ ", .L" ++ tag ++ "_bn254_fail_burn\n" ++
  "  ld " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  sub " ++ remainingReg ++ ", " ++ remainingReg ++ ", " ++ costReg ++ "\n" ++
  "  sd " ++ remainingReg ++ ", " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  mv x17, x6\n" ++
  "  mv x22, x7\n" ++
  "  mv x23, x28\n"

def chargePrecompileGasConstWithAllotmentAsm (tag : String) (cost : Nat)
    (costReg remainingReg : String) : String :=
  "  li " ++ costReg ++ ", " ++ toString cost ++ "\n" ++
  chargePrecompileGasWithAllotmentAsm tag costReg remainingReg

def stageEcrecoverInputAsm
    (inOffsetOff inSizeOff : Nat) : String :=
  "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x18, x13, x18\n" ++
  precompileFrameAddi "x19" precompileFrameEcrecoverInputOff ++
  "  mv x22, x17
  li x23, 128
  bgeu x23, x22, 30f
  mv x22, x23
" ++
  "30:\n" ++
  "  mv x24, x22\n" ++
  "  beqz x24, 32f\n" ++
  "31:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x24, x24, -1
  bnez x24, 31b
" ++
  "32:\n" ++
  "  sub x24, x23, x22\n" ++
  "  beqz x24, 34f\n" ++
  "33:\n" ++
  "  sb x0, 0(x19)
  addi x19, x19, 1
  addi x24, x24, -1
  bnez x24, 33b
" ++
  "34:\n"

/-- Soft-success target defaults to the child CALL success tail (`7b`).
    Route-neutral cores pass a local empty-frame success label instead. -/
def ecrecoverVGateAsm (softOk := "7b") : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 32) ++
  "  li x19, 31\n" ++
  "40:\n" ++
  "  beqz x19, 41f
  lbu x16, 0(x18)
  bnez x16, 43f
  addi x18, x18, 1
  addi x19, x19, -1
  j 40b
" ++
  "41:\n" ++
  "  lbu x16, 0(x18)
  li x19, 27
  beq x16, x19, 42f
  li x19, 28
  beq x16, x19, 42f
" ++
  "43:\n" ++
  "  j " ++ softOk ++ "\n" ++
  "42:\n"

def ecrecoverNonzeroRSGateAsm (softOk := "7b") : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 64) ++
  "  ld x16, 0(x18)
  ld x17, 8(x18)
  or x16, x16, x17
  ld x17, 16(x18)
  or x16, x16, x17
  ld x17, 24(x18)
  or x16, x16, x17
  beqz x16, " ++ softOk ++ "
" ++
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 96) ++
  "  ld x16, 0(x18)
  ld x17, 8(x18)
  or x16, x16, x17
  ld x17, 16(x18)
  or x16, x16, x17
  ld x17, 24(x18)
  or x16, x16, x17
  beqz x16, " ++ softOk ++ "
"

private def secp256k1OrderBytes : List Nat :=
  [ 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe
  , 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b
  , 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41
  ]

private def ecrecoverScalarBelowOrderCompareAsm
    (bytes : List Nat) (idx belowLabel : Nat) (softOk : String) : String :=
  match bytes with
  | [] => ""
  | byte :: rest =>
      "  lbu x16, " ++ toString idx ++ "(x18)\n" ++
      "  li x17, " ++ toString byte ++ "\n" ++
      "  bltu x17, x16, " ++ softOk ++ "\n" ++
      "  bltu x16, x17, " ++ toString belowLabel ++ "f\n" ++
      ecrecoverScalarBelowOrderCompareAsm rest (idx + 1) belowLabel softOk

private def ecrecoverScalarBelowOrderGateAsm
    (wordOff : Nat) (belowLabel : Nat) (softOk : String) : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + wordOff) ++
  ecrecoverScalarBelowOrderCompareAsm secp256k1OrderBytes 0 belowLabel softOk ++
  "  j " ++ softOk ++ "\n" ++
  toString belowLabel ++ ":\n"

def ecrecoverScalarOrderGateAsm (softOk := "7b") : String :=
  ecrecoverScalarBelowOrderGateAsm 64 44 softOk ++
  ecrecoverScalarBelowOrderGateAsm 96 45 softOk

/-- Recover pubkey → left-padded address in `evm_precompile_frame` returndata.
    Soft failures (no backend / bad sig / hash fail) leave empty returndata and
    jump to `softOk`. Does **not** copy to caller memory — wrappers own OUT.
    Reached via `ecrecover_backend_ptr` (optional secp link). -/
def ecrecoverRecoverToFrameAsm (softOk := "7b") : String :=
  "  la x18, ecrecover_backend_ptr\n" ++
  "  ld x18, 0(x18)\n" ++
  "  beqz x18, " ++ softOk ++ "\n" ++
  precompileFrameAddi "x19" precompileFrameEcrecoverInputOff ++
  "  la x22, ecr_abi
  ld x16, 0(x19);  sd x16, 0(x22)
  ld x16, 8(x19);  sd x16, 8(x22)
  ld x16, 16(x19); sd x16, 16(x22)
  ld x16, 24(x19); sd x16, 24(x22)
  ld x16, 64(x19); sd x16, 32(x22)
  ld x16, 72(x19); sd x16, 40(x22)
  ld x16, 80(x19); sd x16, 48(x22)
  ld x16, 88(x19); sd x16, 56(x22)
  ld x16, 96(x19);  sd x16, 64(x22)
  ld x16, 104(x19); sd x16, 72(x22)
  ld x16, 112(x19); sd x16, 80(x22)
  ld x16, 120(x19); sd x16, 88(x22)
" ++
  "  lbu x16, 63(x19)\n" ++
  "  addi x16, x16, -27\n" ++
  "  sd x16, 96(x22)\n" ++
  "  mv s9, x13
  mv s10, x10
  mv s11, x12
  la a0, ecr_abi
  la a1, ecr_pubkey
" ++
  "  jalr x1, x18, 0\n" ++
  "  mv x16, a0
  mv x13, s9
  mv x10, s10
  mv x12, s11
" ++
  "  bnez x16, " ++ softOk ++ "\n" ++
  "  mv s9, x13
  mv s10, x10
  mv s11, x12
  la a0, ecr_pubkey
  li a1, 64
  la a2, ecr_hash
  jal x1, zkvm_keccak256
" ++
  "  mv x16, a0\n" ++
  "  mv x13, s9\n" ++
  "  mv x10, s10\n" ++
  "  mv x12, s11\n" ++
  "  bnez x16, " ++ softOk ++ "\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 16(x15)\n" ++
  "  sd x0, 24(x15)\n" ++
  "  la x18, ecr_hash\n" ++
  "  addi x18, x18, 12\n" ++
  "  addi x19, x15, 28\n" ++
  "  li x22, 20\n" ++
  "46:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x22, x22, -1
  bnez x22, 46b
  li x16, 32
" ++
  "  sd x16, 8(x15)\n"

/-- Child CALL path: recover to frame then copy min(32, out_size) to caller. -/
def ecrecoverRecoverAndOutputAsm (outOffsetOff outSizeOff : Nat) : String :=
  ecrecoverRecoverToFrameAsm "7b" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  li x23, 32\n" ++
  "  bgeu x22, x23, 47f\n" ++
  "  mv x23, x22\n" ++
  "47:\n" ++
  "  beqz x23, 7b\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  "48:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x23, x23, -1
  bnez x23, 48b
  j 7b
"

/-- Stage ECRECOVER input from an absolute calldata pointer/length (descriptor). -/
def stageEcrecoverInputFromAsm (inputReg sizeReg : String) : String :=
  "  mv x17, " ++ sizeReg ++ "\n" ++
  "  mv x18, " ++ inputReg ++ "\n" ++
  precompileFrameAddi "x19" precompileFrameEcrecoverInputOff ++
  "  mv x22, x17
  li x23, 128
  bgeu x23, x22, 30f
  mv x22, x23
" ++
  "30:\n" ++
  "  mv x24, x22\n" ++
  "  beqz x24, 32f\n" ++
  "31:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x24, x24, -1
  bnez x24, 31b
" ++
  "32:\n" ++
  "  sub x24, x23, x22\n" ++
  "  beqz x24, 34f\n" ++
  "33:\n" ++
  "  sb x0, 0(x19)
  addi x19, x19, 1
  addi x24, x24, -1
  bnez x24, 33b
" ++
  "34:\n"

/-- Copy `evm_precompile_frame` returndata (`+8` len, `+16` data) into the
    CALL-family OUT window. Frame and caller memory never alias, so forward
    copy is always safe (identity no longer needs memmove). -/
def precompileCopyFrameReturndataToOutAsm
    (tag : String) (outOffsetOff outSizeOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  ld x22, 8(x15)\n" ++
  "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  bgeu x23, x22, .L" ++ tag ++ "_frame_out_len_ok\n" ++
  "  mv x22, x23\n" ++
  ".L" ++ tag ++ "_frame_out_len_ok:\n" ++
  "  beqz x22, .L" ++ tag ++ "_frame_out_done\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  ".L" ++ tag ++ "_frame_out_copy:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x22, x22, -1
  bnez x22, .L" ++ tag ++ "_frame_out_copy
" ++
  ".L" ++ tag ++ "_frame_out_done:\n"

/-- Write a fixed-length result already at `resultFrameOff` into returndata. -/
def precompileFrameSetRetdataFromOffAsm (tag : String) (resultFrameOff len : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  precompileFrameAddi "x19" resultFrameOff ++
  "  li x22, " ++ toString len ++ "\n" ++
  ".L" ++ tag ++ "_frame_set_ret_copy:\n" ++
  "  beqz x22, .L" ++ tag ++ "_frame_set_ret_done\n" ++
  "  lbu x16, 0(x19)
  sb x16, 0(x18)
  addi x19, x19, 1
  addi x18, x18, 1
  addi x22, x22, -1
  j .L" ++ tag ++ "_frame_set_ret_copy\n" ++
  ".L" ++ tag ++ "_frame_set_ret_done:\n" ++
  "  li x16, 1
  sd x16, 0(x15)
  li x16, " ++ toString len ++ "
  sd x16, 8(x15)
"

/-- Materialize a 32-byte boolean word from a single status byte at `resultFrameOff`. -/
def precompileFrameSetBoolFromOffAsm (resultFrameOff : Nat) : String :=
  "  la x15, evm_precompile_frame
  sd x0, 16(x15)
  sd x0, 24(x15)
  sd x0, 32(x15)
  sd x0, 40(x15)
" ++
  "  lbu x16, " ++ toString resultFrameOff ++ "(x15)\n" ++
  "  sb x16, 47(x15)
  li x16, 1
  sd x16, 0(x15)
  li x16, 32
  sd x16, 8(x15)
"

/-- Empty successful precompile frame (status=1, len=0). -/
def precompileFrameSoftEmptyAsm : String :=
  "  la x15, evm_precompile_frame
  li x16, 1
  sd x16, 0(x15)
  sd x0, 8(x15)
"

/-- BN254 (0x06/0x07) charge-and-gate. `x16` must already hold the
    EIP-1108 constant cost. Computes the EIP-150 child allotment
    A = min(gas word, 63/64 * remaining) via `bn254_call_allotment`
    (kernel suite, `Bn254Curve.lean`); if A < cost the child runs out of
    gas — burn A and surface a failed call (`.L<tag>_bn254_fail_burn`,
    emitted by `bn254FailureStubAsm`). Otherwise charge the cost against
    568(x20) and park the unspent allotment A - cost in `bn254_allot_rest`
    so an invalid-input kernel status can burn the rest (execution-specs
    raises OutOfGasError for malformed ecAdd/ecMul input, which consumes
    everything forwarded to the child). Clobbers x17/x22/x23/x24/x1. -/
def bn254ChargeGateAsm (tag : String) : String :=
  "  jal x1, bn254_call_allotment\n" ++
  "  bltu x22, x16, .L" ++ tag ++ "_bn254_fail_burn\n" ++
  "  ld x17, " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  sub x17, x17, x16\n" ++
  "  sd x17, " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  sub x22, x22, x16\n" ++
  "  la x17, bn254_allot_rest\n" ++
  "  sd x22, 0(x17)\n"

/-- Precompile failed-call tail (shared by BN254 and MODEXP hard-fail paths).
    `.L<tag>_bn254_kfail` is the kernel-invalid-input target: it reloads
    the parked allotment remainder and falls into `.L<tag>_bn254_fail_burn`,
    which burns x22 gas, then pushes 0 (failed call, empty returndata) and
    resumes the dispatch loop. Only reachable via branches. -/
def failedPrecompileCallNewAccountStateGasAsm (tag : String) : String :=
  if tag != "call_target" then "" else
    -- execution-specs charges NEW_ACCOUNT before entering the child. On a
    -- precompile error, generic_call refunds that recorded provisional charge
    -- exactly once, restoring spill first and then the state-gas reservoir.
    "  la t5, cd_new_account_charged_current
  ld t4, 0(t5)
  beqz t4, .L" ++ tag ++ "_fp_call_nacc_done
  sd x0, 0(t5)
" ++
    "  ld t6, 64(x12)
" ++
    "  ld t5, 72(x12)
  or t6, t6, t5
" ++
    "  ld t5, 80(x12)
  or t6, t6, t5
" ++
    "  ld t5, 88(x12)
  or t6, t6, t5
" ++
    "  beqz t6, .L" ++ tag ++ "_fp_call_nacc_done
" ++
    "  la t0, evm_state_gas_used
  ld t1, 0(t0)
  li t2, 183600
" ++
    "  bltu t1, t2, .L" ++ tag ++ "_fp_call_nacc_done
" ++
    "  li t2, 183600
" ++
    "  la t0, evm_state_gas_spilled
  ld t1, 0(t0)
  li t3, 0
" ++
    "  beqz t1, .L" ++ tag ++ "_fp_call_nacc_no_spill
" ++
    "  mv t3, t1
  bleu t1, t2, .L" ++ tag ++ "_fp_call_nacc_spill_le
  mv t3, t2
" ++
    ".L" ++ tag ++ "_fp_call_nacc_spill_le:
" ++
    "  sub t1, t1, t3
  sd t1, 0(t0)
  ld t4, 568(x20)
  add t4, t4, t3
  sd t4, 568(x20)
  sub t2, t2, t3
" ++
    ".L" ++ tag ++ "_fp_call_nacc_no_spill:
" ++
    "  beqz t2, .L" ++ tag ++ "_fp_call_nacc_used
" ++
    "  la t0, evm_state_gas_left
  ld t1, 0(t0)
  add t1, t1, t2
  sd t1, 0(t0)
" ++
    ".L" ++ tag ++ "_fp_call_nacc_used:
" ++
    "  la t0, evm_state_gas_used
  ld t1, 0(t0)
  li t2, 183600
" ++
    "  bltu t1, t2, .L" ++ tag ++ "_fp_call_nacc_done
" ++
    "  sub t1, t1, t2
  sd t1, 0(t0)
" ++
    ".L" ++ tag ++ "_fp_call_nacc_done:
"

def bn254FailureStubAsm (tag : String) (netPopBytes : Nat) : String :=
  -- Entry for failures detected BEFORE the charge gate parked the
  -- allotment (for example, a pairing gas-formula overflow or MODEXP
  -- capped-length/backend failure): compute A fresh and burn it.
  ".L" ++ tag ++ "_bn254_fail_allot:\n" ++
  "  jal x1, bn254_call_allotment\n" ++
  "  j .L" ++ tag ++ "_bn254_fail_burn\n" ++
  ".L" ++ tag ++ "_bn254_kfail:\n" ++
  "  la x17, bn254_allot_rest\n" ++
  "  ld x22, 0(x17)\n" ++
  ".L" ++ tag ++ "_bn254_fail_burn:\n" ++
  "  ld x17, " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  "  sub x17, x17, x22\n" ++
  "  sd x17, " ++ toString precompileGasRemainingOff ++ "(x20)\n" ++
  failedPrecompileCallNewAccountStateGasAsm tag ++
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
  "  sd x0, 0(x12)
  sd x0, 8(x12)
  sd x0, 16(x12)
  sd x0, 24(x12)
  addi x10, x10, 1
" ++
  dispatchContinueRet ++ "\n"

def chargePrecompileWordGasAsm
    (baseGas perWordGas : Nat) (sizeReg costReg scratchReg : String) : String :=
  precompileWordGasCostAsm ".exit_outofgas" baseGas perWordGas sizeReg costReg scratchReg ++
  chargePrecompileGasAsm costReg scratchReg

def chargePrecompileWordGasWithAllotmentAsm
    (tag : String) (baseGas perWordGas : Nat) (sizeReg costReg scratchReg : String) : String :=
  precompileWordGasCostAsm ".exit_outofgas" baseGas perWordGas sizeReg costReg scratchReg ++
  chargePrecompileGasWithAllotmentAsm tag costReg scratchReg

def stagePrecompileInputWindowFromAsm
    (tag inputReg sizeReg : String) (frameOff sourceOff byteLen : Nat) : String :=
  -- Zero-fill the fixed accelerator window, then copy the available suffix of
  -- input bytes. This mirrors execution-specs `buffer_read` padding and lets
  -- the top-level and child precompile routes share the validator input shape.
  "  mv x24, " ++ inputReg ++ "\n" ++
  precompileFrameAddi "x18" frameOff ++
  "  li x19, " ++ toString byteLen ++ "\n" ++
  ".L" ++ tag ++ "_zero:\n" ++
  "  beqz x19, .L" ++ tag ++ "_zero_done\n" ++
  "  sb x0, 0(x18)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, -1\n" ++
  "  j .L" ++ tag ++ "_zero\n" ++
  ".L" ++ tag ++ "_zero_done:\n" ++
  "  li x19, " ++ toString sourceOff ++ "\n" ++
  "  bgeu x19, " ++ sizeReg ++ ", .L" ++ tag ++ "_done\n" ++
  "  sub x18, " ++ sizeReg ++ ", x19\n" ++
  "  li x22, " ++ toString byteLen ++ "\n" ++
  "  bgeu x22, x18, .L" ++ tag ++ "_copy_len_ok\n" ++
  "  mv x18, x22\n" ++
  ".L" ++ tag ++ "_copy_len_ok:\n" ++
  "  li x22, " ++ toString sourceOff ++ "\n" ++
  "  add x19, x24, x22\n" ++
  precompileFrameAddi "x24" frameOff ++
  ".L" ++ tag ++ "_copy:\n" ++
  "  beqz x18, .L" ++ tag ++ "_done\n" ++
  "  lbu x23, 0(x19)
  sb x23, 0(x24)
  addi x19, x19, 1
  addi x24, x24, 1
  addi x18, x18, -1
" ++
  "  j .L" ++ tag ++ "_copy\n" ++
  ".L" ++ tag ++ "_done:\n"

def stagePrecompileInputWindowAsm
    (tag : String) (inOffsetOff inSizeOff frameOff sourceOff byteLen : Nat) : String :=
  "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  ld x19, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x19, x19, x13\n" ++
  stagePrecompileInputWindowFromAsm tag "x19" "x17" frameOff sourceOff byteLen

def precompileSuccess64FromFrameAsm
    (tag : String) (outOffsetOff outSizeOff resultFrameOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  precompileFrameAddi "x19" resultFrameOff ++
  "  li x22, 64\n" ++
  ".L" ++ tag ++ "_retcopy:\n" ++
  "  beqz x22, .L" ++ tag ++ "_retcopy_done\n" ++
  "  lbu x16, 0(x19)
  sb x16, 0(x18)
  addi x19, x19, 1
  addi x18, x18, 1
  addi x22, x22, -1
" ++
  "  j .L" ++ tag ++ "_retcopy\n" ++
  ".L" ++ tag ++ "_retcopy_done:\n" ++
  "  li x16, 1
  sd x16, 0(x15)
  li x16, 64
  sd x16, 8(x15)
" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  li x23, 64\n" ++
  "  bgeu x22, x23, .L" ++ tag ++ "_out_len_ok\n" ++
  "  mv x23, x22\n" ++
  ".L" ++ tag ++ "_out_len_ok:\n" ++
  "  beqz x23, 7b\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  ".L" ++ tag ++ "_outcopy:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x23, x23, -1
" ++
  "  bnez x23, .L" ++ tag ++ "_outcopy\n" ++
  "  j 7b\n"

/-- EIP-2537 MSM discounted cost computed into x16 (pair count left in
    x17) WITHOUT charging — for entries on the EIP-150 child-allotment
    gas model (`bn254ChargeGateAsm` consumes x16 next). Mirrors
    `chargeBls12G1MsmGasAsm`'s math, but the multiplication overflow
    guards route to `failureLabel` rather than `.exit_outofgas`.

    ABI: input byte length is x18; discounted cost is returned in x16;
    x17/x22/x23 are clobbered. -/
def bls12MsmCostAsm (failureLabel : String)
    (pairBytes basePerPair maxDiscount : Nat) (tableLabel : String) : String :=
  "  li x22, " ++ toString pairBytes ++ "\n" ++
  "  divu x17, x18, x22\n" ++
  "  li x16, " ++ toString basePerPair ++ "\n" ++
  "  mul x16, x17, x16\n" ++
  "  li x22, " ++ toString basePerPair ++ "\n" ++
  "  divu x23, x16, x22\n" ++
  "  bne x23, x17, " ++ failureLabel ++ "\n" ++
  "  li x22, 128
  bltu x22, x17, 44f
  addi x23, x17, -1
  slli x23, x23, 3
" ++
  "  la x22, " ++ tableLabel ++ "\n" ++
  "  add x23, x22, x23\n" ++
  "  ld x23, 0(x23)\n" ++
  "  j 45f\n" ++
  "44:\n" ++
  "  li x23, " ++ toString maxDiscount ++ "\n" ++
  "45:\n" ++
  "  mul x16, x16, x23\n" ++
  "  divu x22, x16, x23\n" ++
  "  li x23, " ++ toString basePerPair ++ "\n" ++
  "  mul x23, x17, x23\n" ++
  "  bne x22, x23, " ++ failureLabel ++ "\n" ++
  "  li x23, 1000\n" ++
  "  divu x16, x16, x23\n"

def precompileSharedLoadCostAsm (costReg : String) : String :=
  "  la t0, precompile_shared_cost\n  ld " ++ costReg ++ ", 0(t0)\n"

def precompileSharedStatusFailAsm (failLabel : String) : String :=
  "  la t0, precompile_shared_status\n  ld t0, 0(t0)\n  bnez t0, " ++ failLabel ++ "\n"

private def precompileSharedWordCostKernelAsm (baseGas perWordGas : Nat) : String :=
  "  la t0, precompile_shared_ctx\n  ld t5, 16(t0)\n" ++
  "  li t4, 31\n  add t6, t5, t4\n  bltu t6, t5, .Lprecompile_shared_shape_fail\n" ++
  "  srli t6, t6, 5\n  li t4, " ++ toString perWordGas ++ "\n" ++
  "  mulhu t5, t6, t4\n  bnez t5, .Lprecompile_shared_shape_fail\n" ++
  "  mul t5, t6, t4\n  li t4, " ++ toString baseGas ++ "\n  add t5, t5, t4\n" ++
  "  bltu t5, t4, .Lprecompile_shared_shape_fail\n  j .Lprecompile_shared_store_cost\n"

private def precompileSharedPerUnitCostKernelAsm
    (unit baseGas perUnitGas : Nat) : String :=
  "  la t0, precompile_shared_ctx\n  ld t5, 16(t0)\n" ++
  "  li t4, " ++ toString unit ++ "\n  divu t6, t5, t4\n" ++
  "  li t4, " ++ toString perUnitGas ++ "\n  mulhu t5, t6, t4\n  bnez t5, .Lprecompile_shared_shape_fail\n" ++
  "  mul t5, t6, t4\n  li t4, " ++ toString baseGas ++ "\n  add t5, t5, t4\n" ++
  "  bltu t5, t4, .Lprecompile_shared_shape_fail\n" ++
  "  j .Lprecompile_shared_store_cost\n"

private def precompileSharedMsmCostKernelAsm
    (pairBytes basePerPair maxDiscount : Nat) (tableLabel : String) : String :=
  "  la t0, precompile_shared_ctx\n  ld t5, 16(t0)\n  beqz t5, .Lprecompile_shared_shape_fail\n" ++
  "  li t4, " ++ toString pairBytes ++ "\n  remu t3, t5, t4\n  bnez t3, .Lprecompile_shared_shape_fail\n" ++
  "  divu t6, t5, t4\n  li t4, " ++ toString basePerPair ++ "\n  mulhu t3, t6, t4\n  bnez t3, .Lprecompile_shared_shape_fail\n  mul t5, t6, t4\n" ++
  "  li t4, 128\n  bltu t4, t6, .Lprecompile_shared_msm_max_" ++ toString pairBytes ++ "\n" ++
  "  addi t3, t6, -1\n  slli t3, t3, 3\n  la t4, " ++ tableLabel ++ "\n  add t3, t4, t3\n  ld t3, 0(t3)\n  j .Lprecompile_shared_msm_discount_" ++ toString pairBytes ++ "\n" ++
  " .Lprecompile_shared_msm_max_" ++ toString pairBytes ++ ":\n  li t3, " ++ toString maxDiscount ++ "\n" ++
  " .Lprecompile_shared_msm_discount_" ++ toString pairBytes ++ ":\n" ++
  "  mulhu t4, t5, t3\n  bnez t4, .Lprecompile_shared_shape_fail\n  mul t5, t5, t3\n  li t4, 1000\n  divu t5, t5, t4\n  j .Lprecompile_shared_store_cost\n"

private def precompileSharedModexpReadLengthAsm (fieldOff : Nat) (dstReg : String) : String :=
  "  li " ++ dstReg ++ ", 0\n  li t2, 0\n" ++
  " .Lprecompile_shared_modexp_len_" ++ toString fieldOff ++ ":\n" ++
  "  li t6, 32\n  beq t2, t6, .Lprecompile_shared_modexp_len_done_" ++ toString fieldOff ++ "\n" ++
  "  addi t6, t2, " ++ toString fieldOff ++ "\n  bgeu t6, a1, .Lprecompile_shared_modexp_len_missing_" ++ toString fieldOff ++ "\n" ++
  "  add t6, t0, t6\n  lbu t6, 0(t6)\n  j .Lprecompile_shared_modexp_len_have_" ++ toString fieldOff ++ "\n" ++
  " .Lprecompile_shared_modexp_len_missing_" ++ toString fieldOff ++ ":\n  li t6, 0\n" ++
  " .Lprecompile_shared_modexp_len_have_" ++ toString fieldOff ++ ":\n" ++
  "  li a0, 30\n  bltu t2, a0, .Lprecompile_shared_modexp_len_high_" ++ toString fieldOff ++ "\n" ++
  "  slli " ++ dstReg ++ ", " ++ dstReg ++ ", 8\n  or " ++ dstReg ++ ", " ++ dstReg ++ ", t6\n  j .Lprecompile_shared_modexp_len_next_" ++ toString fieldOff ++ "\n" ++
  " .Lprecompile_shared_modexp_len_high_" ++ toString fieldOff ++ ":\n" ++
  "  bnez t6, .Lprecompile_shared_shape_fail\n" ++
  " .Lprecompile_shared_modexp_len_next_" ++ toString fieldOff ++ ":\n  addi t2, t2, 1\n  j .Lprecompile_shared_modexp_len_" ++ toString fieldOff ++ "\n" ++
  " .Lprecompile_shared_modexp_len_done_" ++ toString fieldOff ++ ":\n" ++
  "  li t6, 1024\n  bltu t6, " ++ dstReg ++ ", .Lprecompile_shared_shape_fail\n"

private def precompileSharedModexpCostAsm : String :=
  "  la t0, precompile_shared_ctx\n  ld t1, 8(t0)\n  ld a1, 16(t0)\n  mv t0, t1\n" ++
  precompileSharedModexpReadLengthAsm 0 "t3" ++
  precompileSharedModexpReadLengthAsm 32 "t4" ++
  precompileSharedModexpReadLengthAsm 64 "t5" ++
  -- Preserve baseLen before t3 becomes the max-length/bit-length scratch;
  -- exponent bytes begin after the base payload.
  "  mv a2, t3\n  mv t6, t3\n  bgeu t6, t5, .Lprecompile_shared_modexp_max_done\n  mv t6, t5\n" ++
  " .Lprecompile_shared_modexp_max_done:\n" ++
  "  mv t3, t6\n  li t6, 16\n  li a0, 32\n  bgeu a0, t3, .Lprecompile_shared_modexp_complex_done\n" ++
  "  addi t3, t3, 7\n  srli t3, t3, 3\n  mul t6, t3, t3\n  slli t6, t6, 1\n" ++
  " .Lprecompile_shared_modexp_complex_done:\n" ++
  "  mv t5, t4\n  li a0, 32\n  bgeu a0, t5, .Lprecompile_shared_modexp_head_len_done\n  mv t5, a0\n" ++
  " .Lprecompile_shared_modexp_head_len_done:\n  li t2, 0\n  li t3, 0\n" ++
  " .Lprecompile_shared_modexp_head_loop:\n  beq t2, t5, .Lprecompile_shared_modexp_head_done\n" ++
  "  addi a0, t2, 96\n  add a0, a0, a2\n  bgeu a0, a1, .Lprecompile_shared_modexp_head_missing\n  add a0, t0, a0\n  lbu a0, 0(a0)\n  j .Lprecompile_shared_modexp_head_have\n" ++
  " .Lprecompile_shared_modexp_head_missing:\n  li a0, 0\n" ++
  " .Lprecompile_shared_modexp_head_have:\n  bnez a0, .Lprecompile_shared_modexp_head_nonzero\n  addi t2, t2, 1\n  j .Lprecompile_shared_modexp_head_loop\n" ++
  " .Lprecompile_shared_modexp_head_nonzero:\n  sub t3, t5, t2\n  addi t3, t3, -1\n  slli t3, t3, 3\n" ++
  " .Lprecompile_shared_modexp_head_log:\n  li a1, 2\n  bltu a0, a1, .Lprecompile_shared_modexp_head_done\n  srli a0, a0, 1\n  addi t3, t3, 1\n  j .Lprecompile_shared_modexp_head_log\n" ++
  " .Lprecompile_shared_modexp_head_done:\n  li a0, 32\n  bgeu a0, t4, .Lprecompile_shared_modexp_iterations_min\n  addi t5, t4, -32\n  slli t5, t5, 4\n  add t5, t5, t3\n  j .Lprecompile_shared_modexp_iterations_done\n" ++
  " .Lprecompile_shared_modexp_iterations_min:\n  mv t5, t3\n" ++
  " .Lprecompile_shared_modexp_iterations_done:\n  bnez t5, .Lprecompile_shared_modexp_cost_mul\n  li t5, 1\n" ++
  " .Lprecompile_shared_modexp_cost_mul:\n  mul t6, t6, t5\n  li a0, 500\n  bgeu t6, a0, .Lprecompile_shared_modexp_cost_done\n  mv t6, a0\n  .Lprecompile_shared_modexp_cost_done:\n  mv t5, t6\n  j .Lprecompile_shared_store_cost\n"

def precompileSharedSelectPriceFunction : String :=
  "precompile_shared_select_price:\n" ++
  "  la t0, precompile_shared_selector\n  sd zero, 0(t0)\n" ++
  "  la t0, precompile_shared_cost\n  sd zero, 0(t0)\n" ++
  "  la t0, precompile_shared_status\n  sd zero, 0(t0)\n" ++
  "  la t0, precompile_shared_ctx\n  ld t1, 0(t0)\n" ++
  precompileAddressClassifyAsm "shared" "t1" "t2" "t3" "t4" ++
  "  la t0, precompile_shared_selector\n  sd t2, 0(t0)\n" ++
  precompileSelectorBranchesAsm "t2" "t3" true
    [ ("1", ".Lprecompile_shared_fixed_3000")
    , ("2", ".Lprecompile_shared_word_60_12")
    , ("3", ".Lprecompile_shared_word_600_120")
    , ("4", ".Lprecompile_shared_word_15_3")
    , ("5", ".Lprecompile_shared_modexp")
    , ("6", ".Lprecompile_shared_fixed_150")
    , ("7", ".Lprecompile_shared_fixed_6000")
    , ("8", ".Lprecompile_shared_pair_192")
    , ("9", ".Lprecompile_shared_blake")
    , ("10", ".Lprecompile_shared_fixed_50000")
    , ("11", ".Lprecompile_shared_fixed_375")
    , ("12", ".Lprecompile_shared_msm_g1")
    , ("13", ".Lprecompile_shared_fixed_600")
    , ("14", ".Lprecompile_shared_msm_g2")
    , ("15", ".Lprecompile_shared_pair_384")
    , ("16", ".Lprecompile_shared_fixed_5500")
    , ("17", ".Lprecompile_shared_fixed_23800")
    , ("256", ".Lprecompile_shared_fixed_6900") ] ++
  "  j .Lprecompile_shared_return\n" ++
  " .Lprecompile_shared_fixed_3000:\n  li t5, 3000\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_150:\n  li t5, 150\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_6000:\n  li t5, 6000\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_50000:\n  li t5, 50000\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_375:\n  li t5, 375\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_600:\n  li t5, 600\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_5500:\n  li t5, 5500\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_23800:\n  li t5, 23800\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_fixed_6900:\n  li t5, 6900\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_word_60_12:\n" ++
  precompileSharedWordCostKernelAsm 60 12 ++
  " .Lprecompile_shared_word_600_120:\n" ++
  precompileSharedWordCostKernelAsm 600 120 ++
  " .Lprecompile_shared_word_15_3:\n" ++
  precompileSharedWordCostKernelAsm 15 3 ++
  " .Lprecompile_shared_pair_192:\n" ++
  precompileSharedPerUnitCostKernelAsm 192 45000 34000 ++
  " .Lprecompile_shared_pair_384:\n" ++
  precompileSharedPerUnitCostKernelAsm 384 37700 32600 ++
  " .Lprecompile_shared_blake:\n" ++
  "  la t0, precompile_shared_ctx\n  ld t5, 16(t0)\n  li t4, 213\n  bne t5, t4, .Lprecompile_shared_shape_fail\n" ++
  "  ld t0, 8(t0)\n  lbu t5, 0(t0)\n  slli t5, t5, 24\n  lbu t4, 1(t0)\n  slli t4, t4, 16\n  or t5, t5, t4\n  lbu t4, 2(t0)\n  slli t4, t4, 8\n  or t5, t5, t4\n  lbu t4, 3(t0)\n  or t5, t5, t4\n  j .Lprecompile_shared_store_cost\n" ++
  " .Lprecompile_shared_modexp:\n" ++
  precompileSharedModexpCostAsm ++
  " .Lprecompile_shared_msm_g1:\n" ++
  precompileSharedMsmCostKernelAsm 160 12000 519 "bls12_g1_msm_discount_table" ++
  " .Lprecompile_shared_msm_g2:\n" ++
  precompileSharedMsmCostKernelAsm 288 22500 524 "bls12_g2_msm_discount_table" ++
  " .Lprecompile_shared_store_cost:\n" ++
  "  la t0, precompile_shared_cost\n  sd t5, 0(t0)\n  j .Lprecompile_shared_return\n" ++
  " .Lprecompile_shared_shape_fail:\n" ++
  "  la t0, precompile_shared_status\n  li t5, 1\n  sd t5, 0(t0)\n" ++
  " .Lprecompile_shared_return:\n  jalr x0, x1, 0\n"

def chargeBls12G1MsmGasAsm
    (inputLenReg pairCountReg costReg discountReg scratchReg : String) : String :=
  "  li " ++ scratchReg ++ ", 160\n" ++
  "  divu " ++ pairCountReg ++ ", " ++ inputLenReg ++ ", " ++ scratchReg ++ "\n" ++
  "  li " ++ costReg ++ ", 12000\n" ++
  "  mul " ++ costReg ++ ", " ++ pairCountReg ++ ", " ++ costReg ++ "\n" ++
  "  li " ++ scratchReg ++ ", 12000\n" ++
  "  divu " ++ discountReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bne " ++ discountReg ++ ", " ++ pairCountReg ++ ", .exit_outofgas\n" ++
  "  li " ++ scratchReg ++ ", 128\n" ++
  "  bltu " ++ scratchReg ++ ", " ++ pairCountReg ++ ", 40f\n" ++
  "  addi " ++ discountReg ++ ", " ++ pairCountReg ++ ", -1\n" ++
  "  slli " ++ discountReg ++ ", " ++ discountReg ++ ", 3\n" ++
  "  la " ++ scratchReg ++ ", bls12_g1_msm_discount_table\n" ++
  "  add " ++ discountReg ++ ", " ++ scratchReg ++ ", " ++ discountReg ++ "\n" ++
  "  ld " ++ discountReg ++ ", 0(" ++ discountReg ++ ")\n" ++
  "  j 41f\n" ++
  "40:\n" ++
  "  li " ++ discountReg ++ ", 519\n" ++
  "41:\n" ++
  "  mv " ++ scratchReg ++ ", " ++ costReg ++ "\n" ++
  "  mul " ++ costReg ++ ", " ++ costReg ++ ", " ++ discountReg ++ "\n" ++
  "  divu " ++ scratchReg ++ ", " ++ costReg ++ ", " ++ discountReg ++ "\n" ++
  "  li " ++ discountReg ++ ", 12000\n" ++
  "  mul " ++ discountReg ++ ", " ++ pairCountReg ++ ", " ++ discountReg ++ "\n" ++
  "  bne " ++ scratchReg ++ ", " ++ discountReg ++ ", .exit_outofgas\n" ++
  "  li " ++ discountReg ++ ", 1000\n" ++
  "  divu " ++ costReg ++ ", " ++ costReg ++ ", " ++ discountReg ++ "\n" ++
  chargePrecompileGasAsm costReg scratchReg

def chargeBls12G2MsmGasAsm
    (inputLenReg pairCountReg costReg discountReg scratchReg : String) : String :=
  "  li " ++ scratchReg ++ ", 288\n" ++
  "  divu " ++ pairCountReg ++ ", " ++ inputLenReg ++ ", " ++ scratchReg ++ "\n" ++
  "  li " ++ costReg ++ ", 22500\n" ++
  "  mul " ++ costReg ++ ", " ++ pairCountReg ++ ", " ++ costReg ++ "\n" ++
  "  li " ++ scratchReg ++ ", 22500\n" ++
  "  divu " ++ discountReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bne " ++ discountReg ++ ", " ++ pairCountReg ++ ", .exit_outofgas\n" ++
  "  li " ++ scratchReg ++ ", 128\n" ++
  "  bltu " ++ scratchReg ++ ", " ++ pairCountReg ++ ", 42f\n" ++
  "  addi " ++ discountReg ++ ", " ++ pairCountReg ++ ", -1\n" ++
  "  slli " ++ discountReg ++ ", " ++ discountReg ++ ", 3\n" ++
  "  la " ++ scratchReg ++ ", bls12_g2_msm_discount_table\n" ++
  "  add " ++ discountReg ++ ", " ++ scratchReg ++ ", " ++ discountReg ++ "\n" ++
  "  ld " ++ discountReg ++ ", 0(" ++ discountReg ++ ")\n" ++
  "  j 43f\n" ++
  "42:\n" ++
  "  li " ++ discountReg ++ ", 524\n" ++
  "43:\n" ++
  "  mv " ++ scratchReg ++ ", " ++ costReg ++ "\n" ++
  "  mul " ++ costReg ++ ", " ++ costReg ++ ", " ++ discountReg ++ "\n" ++
  "  divu " ++ scratchReg ++ ", " ++ costReg ++ ", " ++ discountReg ++ "\n" ++
  "  li " ++ discountReg ++ ", 22500\n" ++
  "  mul " ++ discountReg ++ ", " ++ pairCountReg ++ ", " ++ discountReg ++ "\n" ++
  "  bne " ++ scratchReg ++ ", " ++ discountReg ++ ", .exit_outofgas\n" ++
  "  li " ++ discountReg ++ ", 1000\n" ++
  "  divu " ++ costReg ++ ", " ++ costReg ++ ", " ++ discountReg ++ "\n" ++
  chargePrecompileGasAsm costReg scratchReg

def chargeBls12PairingGasAsm
    (inputLenReg pairCountReg costReg scratchReg : String) : String :=
  "  li " ++ scratchReg ++ ", 384\n" ++
  "  divu " ++ pairCountReg ++ ", " ++ inputLenReg ++ ", " ++ scratchReg ++ "\n" ++
  "  li " ++ costReg ++ ", 32600\n" ++
  "  mul " ++ costReg ++ ", " ++ pairCountReg ++ ", " ++ costReg ++ "\n" ++
  "  li " ++ scratchReg ++ ", 32600\n" ++
  "  divu " ++ scratchReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bne " ++ scratchReg ++ ", " ++ pairCountReg ++ ", .exit_outofgas\n" ++
  "  li " ++ scratchReg ++ ", 37700\n" ++
  "  add " ++ costReg ++ ", " ++ costReg ++ ", " ++ scratchReg ++ "\n" ++
  "  bltu " ++ costReg ++ ", " ++ scratchReg ++ ", .exit_outofgas\n" ++
  chargePrecompileGasAsm costReg scratchReg

def kzgVersionedHashCompareBytesAsm (failLabel : String) : String :=
  String.intercalate "" <| (List.range 31).map fun i =>
    let idx := i + 1
    "  lbu x16, " ++ toString (precompileFrameBls12G2InputOff + idx) ++ "(x15)\n" ++
    "  lbu x17, " ++ toString (precompileFrameBls12G2OutputOff + idx) ++ "(x15)\n" ++
    "  bne x16, x17, " ++ failLabel ++ "\n"

def kzgVersionedHashGateAsm (failLabel : String) : String :=
  "  mv s10, x10\n" ++
  "  mv s11, x12\n" ++
  precompileFrameAddi "a0" (precompileFrameBls12G2InputOff + 96) ++
  "  li a1, 48\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G2OutputOff ++
  -- kzg_commitment_to_versioned_hash is sha256(commitment), NOT keccak.
  "  jal x1, zkvm_sha256\n" ++
  -- a0 IS x10: stash the wrapper status before restoring the saved
  -- value into x10 (the ecrecover-path landmine, #8721 stack notes).
  "  mv x16, a0\n" ++
  "  mv x10, s10\n" ++
  "  mv x12, s11\n" ++
  "  bnez x16, " ++ failLabel ++ "\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  lbu x16, " ++ toString precompileFrameBls12G2InputOff ++ "(x15)\n" ++
  "  li x17, 1\n" ++
  "  bne x16, x17, " ++ failLabel ++ "\n" ++
  kzgVersionedHashCompareBytesAsm failLabel

def precompileSuccessBoolFromFrameAsm
    (tag : String) (outOffsetOff outSizeOff resultFrameOff : Nat) : String :=
  "  la x15, evm_precompile_frame
  sd x0, 16(x15)
  sd x0, 24(x15)
  sd x0, 32(x15)
  sd x0, 40(x15)
" ++
  "  lbu x16, " ++ toString resultFrameOff ++ "(x15)\n" ++
  "  sb x16, 47(x15)
  li x16, 1
  sd x16, 0(x15)
  li x16, 32
  sd x16, 8(x15)
" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  li x23, 32\n" ++
  "  bgeu x22, x23, .L" ++ tag ++ "_out_len_ok\n" ++
  "  mv x23, x22\n" ++
  ".L" ++ tag ++ "_out_len_ok:\n" ++
  "  beqz x23, 7b\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  ".L" ++ tag ++ "_outcopy:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x23, x23, -1
" ++
  "  bnez x23, .L" ++ tag ++ "_outcopy\n" ++
  "  j 7b\n"


def precompileSuccessKzgPointEvalAsm
    (tag : String) (outOffsetOff outSizeOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  addi x18, x15, 16\n" ++
  "  li x22, 30\n" ++
  ".L" ++ tag ++ "_field_zero:\n" ++
  "  beqz x22, .L" ++ tag ++ "_field_tail\n" ++
  "  sb x0, 0(x18)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j .L" ++ tag ++ "_field_zero\n" ++
  ".L" ++ tag ++ "_field_tail:\n" ++
  "  li x16, 0x10
  sb x16, 0(x18)
  sb x0, 1(x18)
  addi x18, x18, 2
  li x16, 0x73
  sb x16, 0(x18)
  li x16, 0xed
  sb x16, 1(x18)
  li x16, 0xa7
  sb x16, 2(x18)
  li x16, 0x53
  sb x16, 3(x18)
  li x16, 0x29
  sb x16, 4(x18)
  li x16, 0x9d
  sb x16, 5(x18)
  li x16, 0x7d
  sb x16, 6(x18)
  li x16, 0x48
  sb x16, 7(x18)
  li x16, 0x33
  sb x16, 8(x18)
  li x16, 0x39
  sb x16, 9(x18)
  li x16, 0xd8
  sb x16, 10(x18)
  li x16, 0x08
  sb x16, 11(x18)
  li x16, 0x09
  sb x16, 12(x18)
  li x16, 0xa1
  sb x16, 13(x18)
  li x16, 0xd8
  sb x16, 14(x18)
  li x16, 0x05
  sb x16, 15(x18)
  li x16, 0x53
  sb x16, 16(x18)
  li x16, 0xbd
  sb x16, 17(x18)
  li x16, 0xa4
  sb x16, 18(x18)
  li x16, 0x02
  sb x16, 19(x18)
  li x16, 0xff
  sb x16, 20(x18)
  li x16, 0xfe
  sb x16, 21(x18)
  li x16, 0x5b
  sb x16, 22(x18)
  li x16, 0xfe
  sb x16, 23(x18)
  li x16, 0xff
  sb x16, 24(x18)
  sb x16, 25(x18)
  sb x16, 26(x18)
  sb x16, 27(x18)
  sb x0, 28(x18)
  sb x0, 29(x18)
  sb x0, 30(x18)
  li x16, 0x01
  sb x16, 31(x18)
  li x16, 1
  sd x16, 0(x15)
  li x16, 64
  sd x16, 8(x15)
" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  li x23, 64\n" ++
  "  bgeu x22, x23, .L" ++ tag ++ "_out_len_ok\n" ++
  "  mv x23, x22\n" ++
  ".L" ++ tag ++ "_out_len_ok:\n" ++
  "  beqz x23, 7b\n" ++
  "  addi x18, x15, 16\n" ++
  "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x19, x13, x19\n" ++
  ".L" ++ tag ++ "_outcopy:\n" ++
  "  lbu x16, 0(x18)
  sb x16, 0(x19)
  addi x18, x18, 1
  addi x19, x19, 1
  addi x23, x23, -1
" ++
  "  bnez x23, .L" ++ tag ++ "_outcopy\n" ++
  "  j 7b\n"

end EvmAsm.Codegen
