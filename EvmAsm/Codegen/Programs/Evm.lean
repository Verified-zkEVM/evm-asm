/-
  EvmAsm.Codegen.Programs.Evm

  M-series demo programs: smoke target, input echo, the verified-body
  end-to-end paths for ADD / DIV / MOD / SDIV / SMOD, the tiny
  interpreter scaffolding, and the runtime dispatcher.

  Extracted from `EvmAsm.Codegen.Programs` so the registry hub stays
  manageable.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Eq.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SMod.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Swap.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmBasic
import EvmAsm.Codegen.Programs.EvmTinyInterp
import EvmAsm.Codegen.Programs.EvmDivModWrappers
import EvmAsm.Codegen.Programs.EvmStackHandlers
import EvmAsm.Codegen.Programs.EvmSingletonHandlers
import EvmAsm.Codegen.Programs.EvmMemoryHandlers
import EvmAsm.Codegen.Programs.EvmGasHandlers
import EvmAsm.Codegen.Programs.EvmCodeHandlers
import EvmAsm.Codegen.Programs.EvmEnvHandlers
import EvmAsm.Codegen.Programs.EvmSlotnum
import EvmAsm.Codegen.Programs.EvmMcopyGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Clz
import EvmAsm.Codegen.Programs.EvmBalance
import EvmAsm.Codegen.Programs.Noop
import EvmAsm.Codegen.Programs.EvmAccountWitness
import EvmAsm.Codegen.Programs.EvmExtcodecopy
import EvmAsm.Codegen.Programs.Storage
import EvmAsm.Codegen.Programs.EvmRegistry

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tiny_interp_dispatch — M5b runtime fetch/decode/dispatch loop

    Same EVM bytecodes as M5a, but routed through an actual RISC-V
    dispatch loop. The dispatcher scaffolding (loop body, 256-entry
    jump table, `h_invalid` fallback, `.exit_label`) now lives in
    `EvmAsm.Codegen.Dispatch`; this section declares only the opcode
    handler registry.

    **Adding a new opcode = adding one `OpcodeHandlerSpec` entry below.**

    Calling convention (informal):
      x10  EVM code pointer  (preserved across handler calls; each
                              handler with `tail := .advanceAndRet n`
                              advances `x10` by `n` before returning)
      x12  EVM stack pointer (handlers update freely; persistent
                              across the loop)
      x1   return address    (clobbered by `jalr ra, ...`; each
                              `advanceAndRet` handler ends in `ret`)
      x5, x6, x7   scratch   (clobbered by both the dispatcher's
                              fetch/lookup *and* the verified handler
                              bodies; the dispatcher reloads from x10
                              and the table base on every iteration,
                              so no preservation needed)

    Coverage (M6b): 82 opcodes wired —
      - **PUSH0..PUSH32** (33) via `pushHandlers`
      - **DUP1..DUP16** (16) via `dupHandlers`
      - **SWAP1..SWAP16** (16) via `swapHandlers`
      - **17 fixed-shape singletons** via `singletonHandlers`:
        SUB, MUL, SIGNEXTEND, AND, OR, XOR, NOT, LT, GT, SLT, SGT,
        EQ, ISZERO, BYTE, CLZ, SHR, POP — CLZ is currently a bounded
        raw RV64IM handler; the others are parameter-free verified
        `Program`s with the standard `<body>` + `addi x10, x10, 1` +
        `ret` ABI.
      - **STOP** via `stopHandler` (jumps to `.exit_label` instead
        of returning to the dispatcher).

    All other opcode bytes fall to `h_invalid` (emitted automatically
    by `emitDispatcherEpilogue`), which takes the same exit path as
    STOP. -/


/-! ## evm_div — M2 first DIV end-to-end through ziskemu

    NOTE: `evm_div` is not yet proven correct in Lean — the spec
    composition (Phase 2a, see bead `evm-asm-9iqmw`) is still in
    flight. The scripts under `scripts/codegen-evm_div*` provide
    empirical confirmation by running the codegen output on ziskemu.

    `evm_div` shares ADD's `x12`-points-at-operands convention: before,
    `x12 = sp` with dividend `a` at `sp+0..32` and divisor `b` at
    `sp+32..64`; after, the quotient lives at `sp+32..64` and `x12 = sp+32`.
    So `evmAddEpilogue` (which copies `[x12, x12+32)` to `OUTPUT_ADDR`)
    works unchanged for DIV.

    Unlike ADD, `evm_div` also uses scratch at "negative" offsets from
    `x12` — the body encodes them as the unsigned bit pattern of
    12-bit signed negatives (`3936..4088 ≡ -160..-8`). The `.data`
    layout therefore places a 256-byte zero-filled `div_scratch:` block
    *before* the `operands:` label so that `x12 - 160..-8` lands in
    writable RAM.

    `evm_div`'s body lays out main code, then a NOP "exit PC" at index
    267, then the 75-instruction `divK_div128_v4` subroutine. When the
    main path completes (via `divK_div_epilogue`'s JAL +24 to the NOP)
    it falls through into the subroutine instead of halting — and the
    codegen's halt stub, appended after the body, is unreachable. We
    splice the body to replace that NOP with `JAL .x0 +304`, which
    skips over the 75 subroutine instructions (75·4 + 4 = 304 bytes)
    and lands at the start of `evmAddEpilogue`. The in-loop callers of
    the subroutine still use the original `jal x2, +560` offsets, which
    remain correct because we only replaced the NOP, not the
    subroutine's position relative to its callers. -/


end EvmAsm.Codegen
