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

def controlFlowHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_JUMPDEST"
    , opcodes := [0x5b]
    , body    := []
    , tail    := .advanceAndRet 1 }
  , { label := "h_JUMP"
    , opcodes := [0x56]
    , preBody := stackUnderflowGuardAsm 1
    , body    := EvmAsm.Evm64.ControlFlow.evm_jump .x21 .x14 .x17
    , tail    := jumpValidityTail }
  , { label := "h_JUMPI"
    , opcodes := [0x57]
    , preBody := stackUnderflowGuardAsm 2
    , body    := EvmAsm.Evm64.ControlFlow.evm_jumpi .x21 .x14 .x15 .x16 .x17
    , tail    := jumpiValidityTail }
  , { label := "h_PC"
    , opcodes := [0x58]
    , body    := EvmAsm.Evm64.ControlFlow.evm_pc .x21 .x14
    , tail    := .advanceAndRet 1 } ]

/-- M16 hash / precompile-via-syscall opcodes. KECCAK256 (0x20) is the
    first ECALL-bridge opcode wired into the dispatcher.

    The handler does NOT have a verified body (`Instr` has no CSRS
    variant; the Zisk `csrs 0x800, a0` accelerator is encoded as a
    raw `.4byte 0x80052073` inside the `zkvm_keccak256` subroutine).
    Like `stopHandler` and the M15 JUMP/JUMPI handlers, this uses
    `body := []` + `tail := .custom "..."` with the full asm inline.

    **Calling convention.** The handler must navigate the conflict
    between LP64 (a0/a1/a2 = x10/x11/x12) and the dispatcher's
    preserved state (x10 = EVM code ptr, x12 = EVM stack ptr).
    Solution: save `x10` to `s10` and `x12` to `s11` (callee-saved
    in LP64, preserved across the keccak call), set up a0/a1/a2 as
    keccak args, then restore after the call.

    **Stack delta**: pop 2 words (offset + size, 64 B) and push 1
    word (32-byte digest). Net x12 advance = +32 (one word).

    **Tail return mechanism**: `j .dispatch_loop` (NOT `ret`),
    because the `jal x1, zkvm_keccak256` clobbers `x1`. Same fix as
    M9's `signedDivModTail`.

    **Endianness**: the keccak subroutine writes the 32-byte digest
    to `a2` in standard byte order (`digest[0]` first). The
    dispatcher's epilogue (e.g. `evmAddEpilogue`) copies x12+0..x12+31
    verbatim to OUTPUT_ADDR. So `expectedOutHex` in test cases is
    the standard keccak digest hex.

    M17+ will extend `hashHandlers` with LOG0-4 / SLOAD / SSTORE /
    other precompiles via the same ECALL bridge pattern. -/
def hashHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_KECCAK256"
    , opcodes := [0x20]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 keccakRangeGuardAsm ++
                 "  ld x14, 0(x12)\n" ++
                 "  ld x15, 32(x12)\n" ++
                 keccakWordGasAsm "x15" ++
                 updateActiveMemorySizeAsm "keccak" "x14" "x15" "x16" "x17" "x18" "x6" true
    , body    := []
    , tail    := .custom (
        "  mv s10, x10\n" ++           -- save EVM code ptr
        "  ld t0, 0(x12)\n" ++          -- t0 = offset_low (low 64 bits of top word)
        "  ld a1, 32(x12)\n" ++         -- a1 = size_low
        "  addi x12, x12, 32\n" ++      -- net stack delta: pop 2 (64), push 1 (-32) = +32
        "  add a0, x13, t0\n" ++        -- a0 = evm_memory + offset (input ptr)
        "  mv a2, x12\n" ++             -- a2 = result slot (= new EVM stack top)
        "  mv s11, x12\n" ++            -- save EVM stack ptr across the call
        "  jal x1, zkvm_keccak256\n" ++ -- call keccak (clobbers x1, a0, a1, a2)
        "  mv x10, s10\n" ++            -- restore EVM code ptr
        "  mv x12, s11\n" ++            -- restore EVM stack ptr
        "  addi x10, x10, 1\n" ++       -- advance PC by 1
        "  j .dispatch_loop") } ]

/-- Copy `topicCount` stack words into an event-log descriptor.
    Descriptor topics live at entry offsets 32, 64, 96, and 128. -/
def logTopicCopies (topicCount : Nat) : String :=
  String.intercalate "" <|
    (List.range topicCount).map fun i =>
      let stackOff := 64 + i * 32
      let entryOff := 32 + i * 32
      "  ld x21, " ++ toString stackOff ++ "(x12)\n" ++
      "  sd x21, " ++ toString entryOff ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 8) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 8) ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 16) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 16) ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 24) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 24) ++ "(x14)\n"

/-- M26 LOG capture prefix. Appends a bounded 256-byte descriptor:
      +0  topic count (u64)
      +8  memory offset low u64
      +16 memory size low u64
      +24 copied data length (min(size, 32))
      +32..160 four 32-byte topic slots
      +160..192 first up to 32 data bytes
      +192..224 ADDRESS context word
      +224..256 CALLER context word

    The descriptor uses the dispatcher's current stack-word byte order
    (low limb first). A full receipt encoder can canonicalize to the
    Ethereum byte order later. Overflow writes halt_kind = 4 and exits
    via `.exit_no_epilogue` instead of silently dropping the event. -/
def logCapturePreBody (topicCount : Nat) : String :=
  "  ld x15, 472(x20)\n" ++          -- x15 = event log length
  "  li x16, 16\n" ++                -- static cap: 16 descriptors
  "  bgeu x15, x16, 9f\n" ++
  "  la x14, evm_event_logs\n" ++
  "  slli x16, x15, 8\n" ++          -- entry offset = count * 256
  "  add x14, x14, x16\n" ++         -- x14 = descriptor pointer
  -- Zero the full descriptor before filling the fields/topics/data prefix.
  "  mv x16, x14\n" ++
  "  li x17, 32\n" ++
  "1:\n" ++
  "  sd x0, 0(x16)\n" ++
  "  addi x16, x16, 8\n" ++
  "  addi x17, x17, -1\n" ++
  "  bnez x17, 1b\n" ++
  "  li x16, " ++ toString topicCount ++ "\n" ++
  "  sd x16, 0(x14)\n" ++
  "  ld x17, 0(x12)\n" ++            -- memory offset low u64
  "  ld x18, 32(x12)\n" ++           -- memory size low u64
  "  sd x17, 8(x14)\n" ++
  "  sd x18, 16(x14)\n" ++
  logTopicCopies topicCount ++
  -- Capture the local address and caller context from the env block.
  "  ld x21, 0(x20)\n" ++
  "  sd x21, 192(x14)\n" ++
  "  ld x21, 8(x20)\n" ++
  "  sd x21, 200(x14)\n" ++
  "  ld x21, 16(x20)\n" ++
  "  sd x21, 208(x14)\n" ++
  "  ld x21, 24(x20)\n" ++
  "  sd x21, 216(x14)\n" ++
  "  ld x21, 64(x20)\n" ++
  "  sd x21, 224(x14)\n" ++
  "  ld x21, 72(x20)\n" ++
  "  sd x21, 232(x14)\n" ++
  "  ld x21, 80(x20)\n" ++
  "  sd x21, 240(x14)\n" ++
  "  ld x21, 88(x20)\n" ++
  "  sd x21, 248(x14)\n" ++
  "  li x19, 32\n" ++
  "  bgeu x19, x18, 2f\n" ++
  "  mv x18, x19\n" ++
  "2:\n" ++
  "  sd x18, 24(x14)\n" ++
  "  add x22, x13, x17\n" ++         -- source = evm_memory + offset
  "  addi x23, x14, 160\n" ++        -- data-prefix destination
  "3:\n" ++
  "  beqz x18, 4f\n" ++
  "  lbu x24, 0(x22)\n" ++
  "  sb x24, 0(x23)\n" ++
  "  addi x22, x22, 1\n" ++
  "  addi x23, x23, 1\n" ++
  "  addi x18, x18, -1\n" ++
  "  j 3b\n" ++
  "4:\n" ++
  "  addi x15, x15, 1\n" ++
  "  sd x15, 472(x20)\n" ++
  "  j 8f\n" ++
  "9:\n" ++
  "  li x16, 0xa0010000\n" ++
  "  li x17, 4\n" ++                 -- LOG buffer overflow
  "  sd x17, 32(x16)\n" ++
  "  j .exit_no_epilogue\n" ++
  "8:\n"

/-- M26 LOG opcodes (LOG0..LOG4). Each handler captures a bounded
    event descriptor, pops `(2 + n)` EVM words, advances PC by one
    byte, and returns to the dispatcher. -/
def logHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_LOG0", opcodes := [0xa0]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++ logDynamicGasAsm 0 ++ logCapturePreBody 0
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG1", opcodes := [0xa1]
    , preBody := stackUnderflowGuardAsm 3 ++ "\n" ++ logDynamicGasAsm 1 ++ logCapturePreBody 1
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG2", opcodes := [0xa2]
    , preBody := stackUnderflowGuardAsm 4 ++ "\n" ++ logDynamicGasAsm 2 ++ logCapturePreBody 2
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 128)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG3", opcodes := [0xa3]
    , preBody := stackUnderflowGuardAsm 5 ++ "\n" ++ logDynamicGasAsm 3 ++ logCapturePreBody 3
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 160)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG4", opcodes := [0xa4]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n" ++ logDynamicGasAsm 4 ++ logCapturePreBody 4
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 192)
    , tail := .advanceAndRet 1 } ]


-- Runtime account-witness handlers (EXTCODESIZE, EXTCODEHASH) live in
-- `EvmAsm/Codegen/Programs/EvmAccountWitness.lean`.

-- M17 / M22 storage handlers (SLOAD, SSTORE, TLOAD, TSTORE) live in
-- `EvmAsm/Codegen/Programs/Storage.lean` — extracted at M22 (when
-- the inline-asm scan loops pushed this file past the per-file size
-- cap) following the same pattern as `Programs/Noop.lean` (M18).
-- The `storageHandlers` builder is brought into scope by the
-- `import EvmAsm.Codegen.Programs.Storage` near the top of this file.

-- M18 stack-pop / push-zero / halt no-op handlers (haltHandlers,
-- pushZeroHandlers, popPushZeroHandlers, copyNoopHandlers) live in
-- `EvmAsm/Codegen/Programs/Noop.lean` — extracted to respect the
-- file-size guard at the bottom of `Programs.lean`. They're brought
-- into scope here by the `import EvmAsm.Codegen.Programs.Noop`
-- statement near the top of this file.

/-- M8 unsigned division opcodes. Both `evm_div` and `evm_mod` carry
    a 75-instruction `divK_div128_v4` subroutine appended after a
    NOP "exit PC" at body index 267; the `evmDivPatched` /
    `evmModPatched` helpers (above) replace that NOP with `JAL .x0
    (304 : BitVec 21)` so the main path skips the inline subroutine
    and lands at the handler's wrapper tail.

    Both bodies clobber `x10` heavily (Knuth-D quotient accumulator,
    69 references) AND `x9` heavily (loop counter `j`, 94 refs).
    So we can't reuse the standard `x9`-as-save pattern from M6b —
    DIV/MOD save `x10` to **`x14`** instead, with a custom tail that
    restores from `x14`. `x14` is unused by `evm_div` / `evm_mod` (and
    their internal subroutine `divK_div128_v4`), and it's outside the
    dispatcher's preserved set, so clobbering it post-handler is fine.

    Stack-scratch: `evm_div` writes to negative `x12` offsets down to
    `-152` bytes (per `divK_*` scratch layout). The runtime dispatcher's
    EVM stack arena is sized for the protocol 1024-word depth and includes
    guard space around the arena for current stack-relative scratch uses.

    **SDIV / SMOD are deferred to M8.5 / M9.** Their verified bodies
    end with a "saved-ra-ret" pattern (`JALR x0, x18, 0`) that
    bypasses the dispatcher's standard wrapper tail; integrating them
    needs a trampoline-style wrapper (set `x18` to a per-handler
    "restore" stub before the body runs, splice off the body's
    initial save_ra_block). Tracked as the next codegen PR. -/
private def mulmodTail : HandlerTail :=
  .custom <|
    "  mv x10, x23\n" ++
    "  mv x13, x21\n" ++
    "  mv x20, x22\n" ++
    "  addi x10, x10, 1\n" ++
    "  ret"

def mulmodHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_MULMOD"
      opcodes := [0x09]
      preBody := stackUnderflowGuardAsm 3 ++ "\n  mv x23, x10\n  mv x21, x13\n  mv x22, x20"
      body    := EvmAsm.Evm64.evm_mulmod
      tail    := mulmodTail } ]

private def divModTail : HandlerTail :=
  .custom "  mv x10, x14\n  addi x10, x10, 1\n  ret"

def divModHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_DIV"
      opcodes := [0x04]
      preBody := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10"
      body    := evmDivPatched
      tail    := divModTail }
  , { label   := "h_MOD"
      opcodes := [0x06]
      preBody := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10"
      body    := evmModPatched
      tail    := divModTail } ]

/-- Tail for SDIV/SMOD: restore `x10` from `x14`, advance the EVM
    code pointer by 1, then jump directly to `.dispatch_loop`
    rather than `ret`-ing. The standard `ret` (= `jalr x0, x1, 0`)
    won't work for these handlers because the wrapper's inner
    `JAL .x1` into `evm_div_callable_v4` / `evm_mod_callable_v4`
    clobbers `x1` mid-body — `x1` no longer holds the dispatcher's
    continuation by the time control reaches this tail. -/
private def signedDivModTail : HandlerTail :=
  .custom "  mv x10, x14\n  addi x10, x10, 1\n  j .dispatch_loop"

/-- M9 signed division handlers: SDIV (0x05) and SMOD (0x07).

    Different wrapping than M8's DIV/MOD because `evm_sdiv` /
    `evm_smod` end with a "saved-ra-ret" pattern (`JALR x0, x18, 0`
    after the wrapper copies `x1` into `x18` at entry) — this
    bypasses the dispatcher's standard `.advanceAndRet` / `divModTail`
    tail entirely.

    **Trampoline pattern:**
    1. `preBody` saves `x10` to `x14` (same register convention as
       M8 DIV/MOD; `x14` is untouched by both the SDIV/SMOD
       wrappers and the inner `evm_div_callable_v4` /
       `evm_mod_callable_v4`) AND loads `x18` with the address of the
       per-handler `postBodyLabel` stub via `la x18, h_<NAME>_done`.
    2. The verified body is `evmSdivPatched` / `evmSmodPatched`,
       which is the verified `evm_sdiv` / `evm_smod` with the
       leading `ADDI .x18 .x1 0` save_ra_block dropped. Without
       the splice, that instruction would overwrite the `x18` we
       just set up in `preBody`.
    3. When the body's `JALR x0, x18, 0` fires (mid-body, at the
       wrapper's `evm_sdiv_saved_ra_ret_block`), control jumps to
       our `postBodyLabel` stub (one of `h_SDIV_done` /
       `h_SMOD_done`).
    4. `signedDivModTail` restores `x10` from `x14`, advances the
       EVM PC, then `j .dispatch_loop` — bypassing the standard
       `ret` because the inner `JAL` into the divider clobbered
       `x1` (so `ret` would jump to garbage).

    Both canonical signed wrappers now route through the v4 callable
    divider/modulo bodies; the trampoline shape is unchanged by that
    migration because the saved-ra return convention is the same. -/
def signedDivModHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_SDIV"
      opcodes       := [0x05]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10\n  la x18, h_SDIV_done"
      body          := evmSdivPatched
      postBodyLabel := some "h_SDIV_done"
      tail          := signedDivModTail }
  , { label         := "h_SMOD"
      opcodes       := [0x07]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10\n  la x18, h_SMOD_done"
      body          := evmSmodPatched
      postBodyLabel := some "h_SMOD_done"
      tail          := signedDivModTail } ]

/-! ## M10 self-calling opcode — ADDMOD (0x08)

    `evm_addmod` is parametric over a JAL byte offset that targets
    a callable variant of another handler (`evm_mod_callable_v4`).
    The natural composition is `<wrapper>(<offset>) ++ <callable>`
    — the callable is inlined in the same handler subroutine; the
    offset is chosen so the wrapper's JAL lands on the callable's
    first instruction.

    Unlike SDIV/SMOD's M9 trampoline, ADDMOD doesn't have a
    saved-ra-ret pattern. It DOES clobber `x1` (via the inner
    `JAL .x1` into the callable), so the wrapper tail must use
    `j .dispatch_loop` instead of `ret` — reusing M9's
    `signedDivModTail` helper. It also clobbers `x10` via the
    inline mod callable, so `preBody` saves `x10` to `x14`.

    EXP (0x0a) now rides the same self-calling pattern via
    `evmExpComposed` below, using the `_fixed_fixed` body variant.
    The earlier deferral note was that `mul_callable` clobbers `x6`
    (the EXP loop's per-limb counter) — the `_fixed` variant only
    moved the `x19` cursor to a callee-saved register, leaving the
    `x6` counter to be corrupted mid-iteration. `_fixed_fixed`
    (`EvmAsm/Evm64/Exp/Program.lean`) moves the counter to `x22`
    (s6, callee-saved, untouched by `evm_mul`/`cc_ret`), so EXP now
    runs correctly through the dispatcher. (The limb pointer `x16`
    was never the problem — `evm_mul` doesn't touch it.) -/

/-- Runtime ADDMOD handler body for the dispatcher.

    The proof-facing `evm_addmod` skeleton still only reduces the truncated
    low 256-bit sum. The dispatcher needs total EVM behavior now, so this
    raw handler uses assembler labels for the internal calls and handles the
    carry-out path empirically:

      * if `N = 0`, write zero and advance by one stack word;
      * if the ADD carry is zero, reduce the truncated sum with MOD;
      * if the ADD carry is one, compute `m = 2^256 mod N`, reduce the
        truncated sum first, add `m`, then perform the single conditional
        subtract required because both addends are already `< N`.

    The carry helper uses `addmod_runtime_scratch` for the extra callable MOD
    frames so temporary reduction state cannot alias deeper live EVM stack
    words. This wrapper exists only to avoid brittle
    hand-counted JAL offsets in the runtime dispatcher while the verified
    top-level ADDMOD assembly catches up. -/
private def evmAddmodRuntimeTail : HandlerTail :=
  .custom <| String.intercalate "\n" [
    emitProgram EvmAsm.Evm64.evm_addmod_prologue,
    emitProgram EvmAsm.Evm64.evm_addmod_phase1_carry,
    "  ld x6, 32(x12)\n  ld x5, 40(x12)\n  or x6, x6, x5\n  ld x5, 48(x12)\n  or x6, x6, x5\n  ld x5, 56(x12)\n  or x6, x6, x5\n  beq x6, x0, .Laddmod_zero\n  beq x7, x0, .Laddmod_no_carry\n  la x16, addmod_saved_stack_ptr\n  sd x12, 0(x16)\n  la x15, addmod_runtime_scratch\n  addi x5, x0, -1\n  sd x5, 0(x15)\n  sd x5, 8(x15)\n  sd x5, 16(x15)\n  sd x5, 24(x15)\n  ld x5, 32(x12)\n  sd x5, 32(x15)\n  ld x5, 40(x12)\n  sd x5, 40(x15)\n  ld x5, 48(x12)\n  sd x5, 48(x15)\n  ld x5, 56(x12)\n  sd x5, 56(x15)\n  mv x12, x15\n  jal x1, .Laddmod_mod_callable\n  la x16, addmod_saved_stack_ptr\n  ld x12, 0(x16)\n  la x15, addmod_runtime_scratch\n  ld x5, 32(x15)\n  addi x6, x5, 1\n  sltiu x7, x6, 1\n  sd x6, 64(x15)\n  ld x5, 40(x15)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 72(x15)\n  ld x5, 48(x15)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 80(x15)\n  ld x5, 56(x15)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 88(x15)\n  ld x5, 32(x12)\n  sd x5, 96(x15)\n  ld x5, 40(x12)\n  sd x5, 104(x15)\n  ld x5, 48(x12)\n  sd x5, 112(x15)\n  ld x5, 56(x12)\n  sd x5, 120(x15)\n  addi x12, x15, 64\n  jal x1, .Laddmod_mod_callable\n  la x16, addmod_saved_stack_ptr\n  ld x12, 0(x16)\n  la x15, addmod_runtime_scratch\n  ld x5, 32(x12)\n  sd x5, 64(x12)\n  ld x5, 40(x12)\n  sd x5, 72(x12)\n  ld x5, 48(x12)\n  sd x5, 80(x12)\n  ld x5, 56(x12)\n  sd x5, 88(x12)\n  jal x1, .Laddmod_mod_callable\n  addi x12, x12, -32\n  ld x5, 32(x12)\n  sd x5, 0(x12)\n  ld x5, 40(x12)\n  sd x5, 8(x12)\n  ld x5, 48(x12)\n  sd x5, 16(x12)\n  ld x5, 56(x12)\n  sd x5, 24(x12)\n  la x15, addmod_runtime_scratch\n  ld x5, 96(x15)\n  sd x5, 32(x12)\n  ld x5, 104(x15)\n  sd x5, 40(x12)\n  ld x5, 112(x15)\n  sd x5, 48(x12)\n  ld x5, 120(x15)\n  sd x5, 56(x12)",
    emitProgram EvmAsm.Evm64.evm_add,
    "  bne x5, x0, .Laddmod_sub_n\n  ld x6, 24(x12)\n  ld x7, 56(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 16(x12)\n  ld x7, 48(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 8(x12)\n  ld x7, 40(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 0(x12)\n  ld x7, 32(x12)\n  bltu x6, x7, .Laddmod_done\n.Laddmod_sub_n:\n  ld x6, 0(x12)\n  ld x7, 32(x12)\n  sub x5, x6, x7\n  sltu x11, x6, x7\n  sd x5, 0(x12)\n  ld x6, 8(x12)\n  ld x7, 40(x12)\n  sub x5, x6, x7\n  sltu x10, x6, x7\n  sub x5, x5, x11\n  sltu x11, x5, x11\n  or x11, x10, x11\n  sd x5, 8(x12)\n  ld x6, 16(x12)\n  ld x7, 48(x12)\n  sub x5, x6, x7\n  sltu x10, x6, x7\n  sub x5, x5, x11\n  sltu x11, x5, x11\n  or x11, x10, x11\n  sd x5, 16(x12)\n  ld x6, 24(x12)\n  ld x7, 56(x12)\n  sub x5, x6, x7\n  sub x5, x5, x11\n  sd x5, 24(x12)\n  j .Laddmod_done\n.Laddmod_no_carry:\n  jal x1, .Laddmod_mod_callable\n  j .Laddmod_done\n.Laddmod_zero:",
    emitProgram EvmAsm.Evm64.evm_addmod_phase2_zero_path,
    emitProgram EvmAsm.Evm64.evm_addmod_epilogue,
    ".Laddmod_done:\n  mv x10, x14\n  addi x10, x10, 1\n  j .dispatch_loop\n.Laddmod_mod_callable:",
    emitProgram EvmAsm.Evm64.evm_mod_callable_v4]

/-- Runtime ADDMOD handler assembly. Supports the no-carry lane by reusing
    `evmAddmodComposed`'s snippets, but rejects carry-out sums explicitly.
    The full ADDMOD semantics need 257-bit reduction `(c * 2^256 + r) mod N`;
    until that lands, `x7 != 0` is an unsupported development halt
    (`halt_kind = 3`) rather than a false successful low-256-bit result. -/
private def addmodRuntimeAsm : String :=
  "  mv x14, x10\n" ++
  emitProgram EvmAsm.Evm64.evm_addmod_prologue ++ "\n" ++
  emitProgram EvmAsm.Evm64.evm_addmod_phase1_carry ++ "\n" ++
  "  bnez x7, .exit_invalid_op\n" ++
  emitProgram (EvmAsm.Evm64.evm_addmod_phase2_reduce 8) ++ "\n" ++
  emitProgram (single (Instr.JAL .x0 (1376 : BitVec 21))) ++ "\n" ++
  emitProgram EvmAsm.Evm64.evm_mod_callable_v4 ++ "\n" ++
  "  mv x10, x14\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop"

/-- EXP (0x0a) handler body: the double-fixed verified EXP body inlined
    with `mul_callable`, mirroring `evmAddmodComposed`.

    Composition:
      - `evm_exp_..._fixed_fixed_canonical 200 92`: 84 instr (336 B). The
        two interior `JAL .x1` MUL-call sites target `mul_callable`.
      - skip-JAL `JAL .x0 +260`: 1 instr (4 B) at byte 336 — jumps past
        the inlined callable to the handler tail (260 = 4 + 256).
      - `mul_callable`: 64 instr (256 B) at byte 340.

    **MUL-call offsets shift +4 vs the standalone `evm_exp_from_input`.**
    There, `mul_callable` sits immediately after the body (byte 336), so
    the canonical offsets are 196 / 88. Here the 4-byte skip-JAL pushes
    `mul_callable` to byte 340, so the squaring / cond-multiply JAL sites
    (at body bytes 140 / 248) need offsets `340-140 = 200` and
    `340-248 = 92`. The internal branch offsets (cond-mul skip BEQ,
    loop-back BNE) are unaffected — they stay inside the 336-byte body
    and use the canonical `_fixed` values.

    The skip-JAL is required because EXP's loop exits by *falling through*
    `exp_epilogue` (which has no trailing jump); without it, control would
    run straight into `mul_callable`. ADDMOD doesn't need this shape
    because its single MUL call is the last thing before the callable.

    Net `x12` advance: `exp_epilogue` does one `ADDI x12, x12, 32` (pops 2,
    pushes 1); the per-iteration call marshal/un-marshal nets zero. -/
def evmExpComposed : Program :=
  EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_fixed_canonical
    (200 : BitVec 21) (92 : BitVec 21) ;;
  single (Instr.JAL .x0 (260 : BitVec 21)) ;;
  EvmAsm.Evm64.mul_callable

/-- Tail for EXP (0x0a): like `signedDivModTail` (the inner `JAL .x1` into
    `mul_callable` clobbers `x1`, so `ret` would jump to garbage → use
    `j .dispatch_loop`), plus a `la sp, lp64_sp_top` to restore the LP64
    stack pointer that h_EXP's `preBody` repointed at `exp_scratch` for the
    EXP body's result accumulator. -/
private def expTail : HandlerTail :=
  .custom ("  mv x10, x14\n" ++
           "  la sp, lp64_sp_top\n" ++
           "  addi x10, x10, 1\n" ++
           "  j .dispatch_loop")

/-- M10 self-calling handlers. Currently just ADDMOD; EXP is
    deferred (see the milestone-header comment). Reuses
    `signedDivModTail` because the wrapper's inner `JAL .x1` into
    the inline callable clobbers `x1`, so the standard `ret` (=
    `jalr x0, x1, 0`) would jump to garbage. -/
def selfCallingHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_ADDMOD"
      opcodes       := [0x08]
      preBody       := stackUnderflowGuardAsm 3 ++ "\n  mv x14, x10"
      body          := []
      tail          := evmAddmodRuntimeTail }
  , { label         := "h_EXP"
      opcodes       := [0x0a]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n" ++ expDynamicGasAsm ++ "  mv x14, x10\n  la x2, exp_scratch"
      body          := evmExpComposed
      tail          := expTail } ]

/-- STOP: transitions out of the dispatcher loop instead of returning
    to it. The body is empty; the dispatcher's `jalr` lands on
    `h_STOP:` which jumps to `.exit_label`. -/
def stopHandler : OpcodeHandlerSpec :=
  { label   := "h_STOP"
    opcodes := [0x00]
    body    := []
    tail    := .custom "  j .exit_label" }

/-- M5b dispatch registry. Order doesn't affect correctness — the
    256-entry jump table is built by `jumpTargetLabel`, which scans
    the list for a spec whose `opcodes` contains the byte. -/
def tinyInterpRegistry : List OpcodeHandlerSpec :=
  pushHandlers ++ dupHandlers ++ swapHandlers ++ singletonHandlers ++
  memoryHandlers ++ memoryMetadataHandlers ++ gasHandlers ++ envHandlers ++ slotnumContextHandlers ++
  blobContextHandlers ++ blockHashHandlers ++ calldataHandlers ++ codeHandlers ++
  controlFlowHandlers ++ hashHandlers ++ logHandlers ++
  balanceWitnessHandlers ++ accountWitnessHandlers ++ extcodecopyWitnessHandlers ++ storageHandlers ++
  mcopyHandlers ++ haltHandlers ++ pushZeroHandlers ++ returnDataHandlers ++
  popPushZeroHandlers ++ copyNoopHandlers ++ childFrameHandlers ++
  arithNoopHandlers ++ mulmodHandlers ++ divModHandlers ++ signedDivModHandlers ++
  selfCallingHandlers ++ [stopHandler]

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
