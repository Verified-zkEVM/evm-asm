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
  "  mv x6, x17\n" ++
  "  mv x7, x22\n" ++
  "  mv x28, x23\n" ++
  "  jal x1, bn254_call_allotment\n" ++
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
  "  mv x22, x17\n" ++
  "  li x23, 128\n" ++
  "  bgeu x23, x22, 30f\n" ++
  "  mv x22, x23\n" ++
  "30:\n" ++
  "  mv x24, x22\n" ++
  "  beqz x24, 32f\n" ++
  "31:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  bnez x24, 31b\n" ++
  "32:\n" ++
  "  sub x24, x23, x22\n" ++
  "  beqz x24, 34f\n" ++
  "33:\n" ++
  "  sb x0, 0(x19)\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  bnez x24, 33b\n" ++
  "34:\n"

def ecrecoverVGateAsm : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 32) ++
  "  li x19, 31\n" ++
  "40:\n" ++
  "  beqz x19, 41f\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  bnez x16, 43f\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, -1\n" ++
  "  j 40b\n" ++
  "41:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  li x19, 27\n" ++
  "  beq x16, x19, 42f\n" ++
  "  li x19, 28\n" ++
  "  beq x16, x19, 42f\n" ++
  "43:\n" ++
  "  j 7b\n" ++
  "42:\n"

def ecrecoverNonzeroRSGateAsm : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 64) ++
  "  ld x16, 0(x18)\n" ++
  "  ld x17, 8(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 16(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 24(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  beqz x16, 7b\n" ++
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + 96) ++
  "  ld x16, 0(x18)\n" ++
  "  ld x17, 8(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 16(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  ld x17, 24(x18)\n" ++
  "  or x16, x16, x17\n" ++
  "  beqz x16, 7b\n"

private def secp256k1OrderBytes : List Nat :=
  [ 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  , 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe
  , 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b
  , 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41
  ]

private def ecrecoverScalarBelowOrderCompareAsm
    (bytes : List Nat) (idx belowLabel : Nat) : String :=
  match bytes with
  | [] => ""
  | byte :: rest =>
      "  lbu x16, " ++ toString idx ++ "(x18)\n" ++
      "  li x17, " ++ toString byte ++ "\n" ++
      "  bltu x17, x16, 7b\n" ++
      "  bltu x16, x17, " ++ toString belowLabel ++ "f\n" ++
      ecrecoverScalarBelowOrderCompareAsm rest (idx + 1) belowLabel

private def ecrecoverScalarBelowOrderGateAsm
    (wordOff : Nat) (belowLabel : Nat) : String :=
  precompileFrameAddi "x18" (precompileFrameEcrecoverInputOff + wordOff) ++
  ecrecoverScalarBelowOrderCompareAsm secp256k1OrderBytes 0 belowLabel ++
  "  j 7b\n" ++
  toString belowLabel ++ ":\n"

def ecrecoverScalarOrderGateAsm : String :=
  ecrecoverScalarBelowOrderGateAsm 64 44 ++
  ecrecoverScalarBelowOrderGateAsm 96 45

/-- ECRECOVER (0x01) recovery + output tail (.62.2.5). Runs AFTER the v/r/s
    gates have validated the staged input (hash @+0, v @+32, r @+64, s @+96 at
    `evm_precompile_frame + precompileFrameEcrecoverInputOff`, buffer_read
    padded). Behavior matches execution-specs `ecrecover`: on a valid
    signature the returndata is the 32-byte left-padded keccak address of the
    recovered public key; on recovery failure the call still SUCCEEDS with
    empty returndata (the gates' `j 7b` path).

    The recovery kernel is reached through the `ecrecover_backend_ptr` data
    cell rather than a direct `jal`: the secp256k1 chain is only linked by
    closures that arm the pointer (the stateless guest arms it in
    `dispatch_tx_runtime_code`; the focused ecrecover probe arms it itself).
    Closures that leave it 0 (the standalone dispatch probes) keep the legacy
    success-with-empty-returndata behavior AND keep linking without the
    secp256k1 dependency tree — the same data-driven optionality as
    `callee_seed_count`.

    Register use mirrors the SHA256 path: x13/x10/x12 are saved in s9/s10/s11
    across the LP64 calls (the secp/keccak helpers preserve s-registers);
    label 7 is the handler's success-push tail; numeric labels 46-48 are
    local. -/
def ecrecoverRecoverAndOutputAsm (outOffsetOff outSizeOff : Nat) : String :=
  "  la x18, ecrecover_backend_ptr\n" ++
  "  ld x18, 0(x18)\n" ++
  "  beqz x18, 7b\n" ++
  -- Stage the recovery ABI block (hash/r/s/recid) from the gated input
  -- (hash/v/r/s). Both regions are 8-byte aligned; copy by u64 limbs.
  precompileFrameAddi "x19" precompileFrameEcrecoverInputOff ++
  "  la x22, ecr_abi\n" ++
  "  ld x16, 0(x19);  sd x16, 0(x22)\n" ++
  "  ld x16, 8(x19);  sd x16, 8(x22)\n" ++
  "  ld x16, 16(x19); sd x16, 16(x22)\n" ++
  "  ld x16, 24(x19); sd x16, 24(x22)\n" ++
  "  ld x16, 64(x19); sd x16, 32(x22)\n" ++
  "  ld x16, 72(x19); sd x16, 40(x22)\n" ++
  "  ld x16, 80(x19); sd x16, 48(x22)\n" ++
  "  ld x16, 88(x19); sd x16, 56(x22)\n" ++
  "  ld x16, 96(x19);  sd x16, 64(x22)\n" ++
  "  ld x16, 104(x19); sd x16, 72(x22)\n" ++
  "  ld x16, 112(x19); sd x16, 80(x22)\n" ++
  "  ld x16, 120(x19); sd x16, 88(x22)\n" ++
  "  lbu x16, 63(x19)\n" ++          -- v byte 31 (the v gate proved 27/28)
  "  addi x16, x16, -27\n" ++
  "  sd x16, 96(x22)\n" ++           -- recid word
  "  mv s9, x13\n" ++
  "  mv s10, x10\n" ++
  "  mv s11, x12\n" ++
  "  la a0, ecr_abi\n" ++
  "  la a1, ecr_pubkey\n" ++
  "  jalr x1, x18, 0\n" ++           -- secp256k1_recover_pubkey_staged
  -- a0 IS x10: stash the status before restoring the EVM code pointer
  -- (restoring first would make the bnez read the nonzero code pointer).
  "  mv x16, a0\n" ++
  "  mv x13, s9\n" ++
  "  mv x10, s10\n" ++
  "  mv x12, s11\n" ++
  "  bnez x16, 7b\n" ++              -- invalid signature: empty-returndata success
  "  mv s9, x13\n" ++
  "  mv s10, x10\n" ++
  "  mv s11, x12\n" ++
  "  la a0, ecr_pubkey\n" ++
  "  li a1, 64\n" ++
  "  la a2, ecr_hash\n" ++
  "  jal x1, zkvm_keccak256\n" ++
  "  mv x16, a0\n" ++                -- stash status before the x10 (=a0) restore
  "  mv x13, s9\n" ++
  "  mv x10, s10\n" ++
  "  mv x12, s11\n" ++
  "  bnez x16, 7b\n" ++              -- hash backend failure: stay conservative
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 16(x15)\n" ++            -- returndata[0..12] = 0 (left padding)
  "  sd x0, 24(x15)\n" ++
  "  la x18, ecr_hash\n" ++
  "  addi x18, x18, 12\n" ++         -- address = keccak(pubkey)[12..32]
  "  addi x19, x15, 28\n" ++
  "  li x22, 20\n" ++
  "46:\n" ++
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  bnez x22, 46b\n" ++
  "  li x16, 32\n" ++
  "  sd x16, 8(x15)\n" ++            -- returndata length = 32
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
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x23, x23, -1\n" ++
  "  bnez x23, 48b\n" ++
  "  j 7b\n"

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
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
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
  "  lbu x23, 0(x19)\n" ++
  "  sb x23, 0(x24)\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x24, x24, 1\n" ++
  "  addi x18, x18, -1\n" ++
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
  "  lbu x16, 0(x19)\n" ++
  "  sb x16, 0(x18)\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j .L" ++ tag ++ "_retcopy\n" ++
  ".L" ++ tag ++ "_retcopy_done:\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  li x16, 64\n" ++
  "  sd x16, 8(x15)\n" ++
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
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x23, x23, -1\n" ++
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
  "  li x22, 128\n" ++
  "  bltu x22, x17, 44f\n" ++
  "  addi x23, x17, -1\n" ++
  "  slli x23, x23, 3\n" ++
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
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 16(x15)\n" ++
  "  sd x0, 24(x15)\n" ++
  "  sd x0, 32(x15)\n" ++
  "  sd x0, 40(x15)\n" ++
  "  lbu x16, " ++ toString resultFrameOff ++ "(x15)\n" ++
  "  sb x16, 47(x15)\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  li x16, 32\n" ++
  "  sd x16, 8(x15)\n" ++
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
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x23, x23, -1\n" ++
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
  "  li x16, 0x10\n" ++
  "  sb x16, 0(x18)\n" ++
  "  sb x0, 1(x18)\n" ++
  "  addi x18, x18, 2\n" ++
  "  li x16, 0x73\n" ++
  "  sb x16, 0(x18)\n" ++
  "  li x16, 0xed\n" ++
  "  sb x16, 1(x18)\n" ++
  "  li x16, 0xa7\n" ++
  "  sb x16, 2(x18)\n" ++
  "  li x16, 0x53\n" ++
  "  sb x16, 3(x18)\n" ++
  "  li x16, 0x29\n" ++
  "  sb x16, 4(x18)\n" ++
  "  li x16, 0x9d\n" ++
  "  sb x16, 5(x18)\n" ++
  "  li x16, 0x7d\n" ++
  "  sb x16, 6(x18)\n" ++
  "  li x16, 0x48\n" ++
  "  sb x16, 7(x18)\n" ++
  "  li x16, 0x33\n" ++
  "  sb x16, 8(x18)\n" ++
  "  li x16, 0x39\n" ++
  "  sb x16, 9(x18)\n" ++
  "  li x16, 0xd8\n" ++
  "  sb x16, 10(x18)\n" ++
  "  li x16, 0x08\n" ++
  "  sb x16, 11(x18)\n" ++
  "  li x16, 0x09\n" ++
  "  sb x16, 12(x18)\n" ++
  "  li x16, 0xa1\n" ++
  "  sb x16, 13(x18)\n" ++
  "  li x16, 0xd8\n" ++
  "  sb x16, 14(x18)\n" ++
  "  li x16, 0x05\n" ++
  "  sb x16, 15(x18)\n" ++
  "  li x16, 0x53\n" ++
  "  sb x16, 16(x18)\n" ++
  "  li x16, 0xbd\n" ++
  "  sb x16, 17(x18)\n" ++
  "  li x16, 0xa4\n" ++
  "  sb x16, 18(x18)\n" ++
  "  li x16, 0x02\n" ++
  "  sb x16, 19(x18)\n" ++
  "  li x16, 0xff\n" ++
  "  sb x16, 20(x18)\n" ++
  "  li x16, 0xfe\n" ++
  "  sb x16, 21(x18)\n" ++
  "  li x16, 0x5b\n" ++
  "  sb x16, 22(x18)\n" ++
  "  li x16, 0xfe\n" ++
  "  sb x16, 23(x18)\n" ++
  "  li x16, 0xff\n" ++
  "  sb x16, 24(x18)\n" ++
  "  sb x16, 25(x18)\n" ++
  "  sb x16, 26(x18)\n" ++
  "  sb x16, 27(x18)\n" ++
  "  sb x0, 28(x18)\n" ++
  "  sb x0, 29(x18)\n" ++
  "  sb x0, 30(x18)\n" ++
  "  li x16, 0x01\n" ++
  "  sb x16, 31(x18)\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  li x16, 64\n" ++
  "  sd x16, 8(x15)\n" ++
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
  "  lbu x16, 0(x18)\n" ++
  "  sb x16, 0(x19)\n" ++
  "  addi x18, x18, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x23, x23, -1\n" ++
  "  bnez x23, .L" ++ tag ++ "_outcopy\n" ++
  "  j 7b\n"

end EvmAsm.Codegen
