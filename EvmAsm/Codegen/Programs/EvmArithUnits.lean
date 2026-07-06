/-
  EvmAsm.Codegen.Programs.EvmArithUnits

  Arithmetic operation BuildUnits carved out of `Programs/Evm.lean` to
  satisfy the 1500-line file-size hard cap.  Contains the DIV / MOD /
  SDIV / SMOD baked-data and from-input `BuildUnit` definitions.
-/

import EvmAsm.Codegen.Programs.Evm

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Dividend as four LE limbs. 2^64, exercises the phase-B n=2 cascade
    plus the normalize/loop path (not an early-exit). -/
def evmDivDividend : List UInt64 := [0, 1, 0, 0]

/-- Divisor as four LE limbs. 2. -/
def evmDivDivisor : List UInt64 := [2, 0, 0, 0]

/-- Expected quotient = 2^64 / 2 = 2^63, LE limbs. The actual on-disk
    expected hex is asserted by `scripts/codegen-evm_div-check.sh`; this
    constant is documentation. -/
def evmDivExpectedQuotient : List UInt64 := [0x8000000000000000, 0, 0, 0]

/-- Same `la x12, operands` as ADD — points the EVM stack pointer at
    the dividend, with the divisor packed directly after it. -/
def evmDivPrologue : String :=
  "  la x12, operands"

/-- `.data` section: 256 bytes of zero-filled scratch labeled
    `div_scratch:` *first*, then `operands:` with dividend ++ divisor
    (eight LE dwords). The scratch comes first so that `x12 - 160..-8`
    (the DIV body's scratch range, encoded as unsigned 12-bit offsets
    `3936..4088`) falls inside writable RAM.

    Written as raw asm rather than `emitDataLabel` because the layout
    mixes `.zero` and `.dword`. -/
def evmDivDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmDivDividend ++ evmDivDivisor).map emitDword)

def evmDivUnit : BuildUnit := {
  body        := evmDivPatched ++ evmAddEpilogue
  prologueAsm := evmDivPrologue
  dataAsm     := evmDivDataSection
}

/-! ## evm_div_from_input — M4 prover-supplied DIV operands

    Same wrapping as `evmDivUnit`, but operands arrive at runtime from
    the ziskemu `-i` input region instead of being baked into `.data`.
    Lets one ELF cover many test vectors. Layout is identical to
    `evm_add_from_input` plus the 256 B `div_scratch:` block in front
    of `operands_ram:`. -/

def evm_div_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmDivPatched ++
  evmAddEpilogue

def evmDivFromInputPrologue : String :=
  "  la x12, operands_ram"

/-- `.data` section: 256 B of writable `div_scratch:` *before*
    `operands_ram:` (64 B reserved zero, overwritten at runtime). -/
def evmDivFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmDivFromInputUnit : BuildUnit := {
  body        := evm_div_from_input
  prologueAsm := evmDivFromInputPrologue
  dataAsm     := evmDivFromInputDataSection
}

/-! ## evm_div_v5 — DIV executable using the v5 div128 subroutine -/

def evmDivV5Unit : BuildUnit := {
  body        := evmDivV5Patched ++ evmAddEpilogue
  prologueAsm := evmDivPrologue
  dataAsm     := evmDivDataSection
}

def evm_div_v5_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmDivV5Patched ++
  evmAddEpilogue

def evmDivV5FromInputUnit : BuildUnit := {
  body        := evm_div_v5_from_input
  prologueAsm := evmDivFromInputPrologue
  dataAsm     := evmDivFromInputDataSection
}

/-! ## evm_div_v6 — DIV executable using the n=1 fast-path dispatch

    Same calling convention, prologue, and `.data` scratch layout as the v5
    DIV unit; only the body differs (`evmDivV6Patched`, which dispatches to a
    single-limb fast path for n=1 divisors and falls back to the embedded v5
    Knuth path otherwise). Backed by the `evm_div_v6_stack_spec` proof over
    `divCodeV6`. -/
def evmDivV6Unit : BuildUnit := {
  body        := evmDivV6Patched ++ evmAddEpilogue
  prologueAsm := evmDivPrologue
  dataAsm     := evmDivDataSection
}

def evm_div_v6_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmDivV6Patched ++
  evmAddEpilogue

def evmDivV6FromInputUnit : BuildUnit := {
  body        := evm_div_v6_from_input
  prologueAsm := evmDivFromInputPrologue
  dataAsm     := evmDivFromInputDataSection
}

/-! ## evm_mod — M2 first MOD end-to-end through ziskemu

    Same calling convention and scratch layout as `evm_div`. `evm_mod`
    differs only in the epilogue: `divK_mod_epilogue` copies `u[0..3]`
    (the de-normalized remainder) to `sp+32..64` instead of `q[0..3]`.
    The body structure (NOP "exit PC" at index 267 followed by the
    75-instruction `divK_div128_v4` subroutine) is identical, so the
    same NOP-splice fix applies. Like `evm_div`, `evm_mod` is not yet
    proven correct in Lean — the scripts under `scripts/codegen-evm_mod*`
    provide empirical confirmation by running on ziskemu. -/

/-- Dividend as four LE limbs. 2^64, exercises the phase-B n=1 cascade
    on the divisor (b=3, limb 0 only) plus the loop body. -/
def evmModDividend : List UInt64 := [0, 1, 0, 0]

/-- Divisor as four LE limbs. 3. -/
def evmModDivisor : List UInt64 := [3, 0, 0, 0]

/-- Expected remainder = 2^64 mod 3 = 1 (since 2^64 = 3·6148914691236517205 + 1). -/
def evmModExpectedRemainder : List UInt64 := [1, 0, 0, 0]

def evmModPrologue : String :=
  "  la x12, operands"

def evmModDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmModDividend ++ evmModDivisor).map emitDword)

def evmModUnit : BuildUnit := {
  body        := evmModPatched ++ evmAddEpilogue
  prologueAsm := evmModPrologue
  dataAsm     := evmModDataSection
}

/-! ## evm_mod_from_input — M4 prover-supplied MOD operands

    Same wrapping as `evmModUnit`, but operands arrive at runtime from
    the ziskemu `-i` input region (mirrors `evm_div_from_input`). -/

def evm_mod_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmModPatched ++
  evmAddEpilogue

def evmModFromInputPrologue : String :=
  "  la x12, operands_ram"

def evmModFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmModFromInputUnit : BuildUnit := {
  body        := evm_mod_from_input
  prologueAsm := evmModFromInputPrologue
  dataAsm     := evmModFromInputDataSection
}

/-! ## evm_mod_v5 — MOD executable using the v5 div128 subroutine -/

def evmModV5Unit : BuildUnit := {
  body        := evmModV5Patched ++ evmAddEpilogue
  prologueAsm := evmModPrologue
  dataAsm     := evmModDataSection
}

def evm_mod_v5_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  evmModV5Patched ++
  evmAddEpilogue

def evmModV5FromInputUnit : BuildUnit := {
  body        := evm_mod_v5_from_input
  prologueAsm := evmModFromInputPrologue
  dataAsm     := evmModFromInputDataSection
}

/-! ## evm_sdiv_v4 — signed DIV end-to-end through ziskemu

    `evm_sdiv_v4` uses the SDIV sign-handling wrapper and the corrected v4
    unsigned callable divider. Unlike standalone DIV/MOD, the wrapper returns
    via the caller return address saved in `x18`, so codegen seeds `x1` with a
    raw-asm label immediately after the verified body. -/

def evmSdivV4Dividend : List UInt64 := [0xffffffffffffff9c, 0xffffffffffffffff,
  0xffffffffffffffff, 0xffffffffffffffff]

def evmSdivV4Divisor : List UInt64 := [7, 0, 0, 0]

def evmSdivV4ExpectedQuotient : List UInt64 := [0xfffffffffffffff2,
  0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]

def evmSdivV4Prologue : String :=
  "  la x1, after_sdiv\n" ++
  "  la x12, operands"

def evmSdivV4Epilogue : String :=
  "after_sdiv:\n" ++ emitProgram evmAddEpilogue

def evmSdivV4DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmSdivV4Dividend ++ evmSdivV4Divisor).map emitDword)

def evmSdivV4Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_sdiv_v4
  prologueAsm := evmSdivV4Prologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4DataSection
}

/-! ## evm_sdiv_v4_from_input — prover-supplied signed DIV operands -/

def evm_sdiv_v4_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_sdiv_v4

def evmSdivV4FromInputPrologue : String :=
  "  la x1, after_sdiv\n" ++
  "  la x12, operands_ram"

def evmSdivV4FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmSdivV4FromInputUnit : BuildUnit := {
  body        := evm_sdiv_v4_from_input
  prologueAsm := evmSdivV4FromInputPrologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4FromInputDataSection
}

/-! ## evm_sdiv_v5 — signed DIV executable using the v5 unsigned callable -/

def evmSdivV5Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_sdiv_v5
  prologueAsm := evmSdivV4Prologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4DataSection
}

def evm_sdiv_v5_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_sdiv_v5

def evmSdivV5FromInputUnit : BuildUnit := {
  body        := evm_sdiv_v5_from_input
  prologueAsm := evmSdivV4FromInputPrologue
  epilogueAsm := evmSdivV4Epilogue
  dataAsm     := evmSdivV4FromInputDataSection
}

/-! ## evm_smod_v4 — signed MOD end-to-end through ziskemu -/

def evmSmodV4Dividend : List UInt64 := [0xffffffffffffff9c, 0xffffffffffffffff,
  0xffffffffffffffff, 0xffffffffffffffff]

def evmSmodV4Divisor : List UInt64 := [7, 0, 0, 0]

def evmSmodV4ExpectedRemainder : List UInt64 := [0xfffffffffffffffd,
  0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]

def evmSmodV4Prologue : String :=
  "  la x1, after_smod\n" ++
  "  la x12, operands"

def evmSmodV4Epilogue : String :=
  "after_smod:\n" ++ emitProgram evmAddEpilogue

def evmSmodV4DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands:\n" ++
  String.intercalate "\n"
    ((evmSmodV4Dividend ++ evmSmodV4Divisor).map emitDword)

def evmSmodV4Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_smod
  prologueAsm := evmSmodV4Prologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4DataSection
}

def evmSmodUnit : BuildUnit := evmSmodV4Unit

/-! ## evm_smod_v4_from_input — prover-supplied signed MOD operands -/

def evm_smod_v4_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_smod

def evm_smod_from_input : Program := evm_smod_v4_from_input

def evmSmodV4FromInputPrologue : String :=
  "  la x1, after_smod\n" ++
  "  la x12, operands_ram"

def evmSmodV4FromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "div_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 64"

def evmSmodV4FromInputUnit : BuildUnit := {
  body        := evm_smod_v4_from_input
  prologueAsm := evmSmodV4FromInputPrologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4FromInputDataSection
}

def evmSmodFromInputUnit : BuildUnit := {
  body        := evm_smod_from_input
  prologueAsm := evmSmodV4FromInputPrologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4FromInputDataSection
}

/-! ## evm_smod_v5 — signed MOD executable using the v5 unsigned callable -/

def evmSmodV5Unit : BuildUnit := {
  body        := EvmAsm.Evm64.evm_smod_v5
  prologueAsm := evmSmodV4Prologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4DataSection
}

def evm_smod_v5_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_smod_v5

def evmSmodV5FromInputUnit : BuildUnit := {
  body        := evm_smod_v5_from_input
  prologueAsm := evmSmodV4FromInputPrologue
  epilogueAsm := evmSmodV4Epilogue
  dataAsm     := evmSmodV4FromInputDataSection
}

end EvmAsm.Codegen
