/-
  EvmAsm.Evm64.Transient.StoreProgram

  RISC-V program implementing the append core of the EVM `TSTORE` opcode
  (0x5d, EIP-1153 transient storage).

  TSTORE appends a fresh 128-byte transient-storage-log entry
  (`EvmAsm/Evm64/StorageAssertions.lean`) at `TRANSIENT_STORAGE_LOG_BASE +
  128 * log_length`, then bumps the live length counter (`env+464`) and pops
  the two consumed stack words. Transient storage keeps no gas-refund state,
  so `original` is always written 0 and there is no scan — every TSTORE just
  appends (later TLOADs scan from the end and find the most-recent value).

  This program is the la-FREE append body of the `h_TSTORE` dispatcher handler
  (`EvmAsm/Codegen/Programs/Storage.lean`); the stack-underflow and
  static-context guards stay in the handler `preBody` glue. The instructions
  here are a byte-identical reorder of the handler's former `preBody` append
  text (now emitted from this verified `Program` via `emitProgram`) followed by
  the `ADDI x12, x12, 64` pop that used to be the handler `body`.

  Implementation (35 instructions = 140 bytes), `envReg = x20`:

    LD   x15 envReg 464         -- x15 = transient log_length n
    LI   x14 0xa0830000         -- x14 = transient log base
    SLLI x16 x15  7             -- x16 = n * 128
    ADD  x14 x14 x16            -- x14 = base + 128*n  (append target)
    -- addrHash = env.ADDRESS (env+0..24)  →  target+0..24
    LD x16 envReg 0  ; SD x14 x16 0
    LD x16 envReg 8  ; SD x14 x16 8
    LD x16 envReg 16 ; SD x14 x16 16
    LD x16 envReg 24 ; SD x14 x16 24
    -- slotKey = stack word 0 (x12+0..24)  →  target+32..56
    LD x16 x12 0  ; SD x14 x16 32
    LD x16 x12 8  ; SD x14 x16 40
    LD x16 x12 16 ; SD x14 x16 48
    LD x16 x12 24 ; SD x14 x16 56
    -- original = 0 (unused for transient)  →  target+64..88
    SD x14 x0 64 ; SD x14 x0 72 ; SD x14 x0 80 ; SD x14 x0 88
    -- current = stack word 1 (x12+32..56)  →  target+96..120
    LD x16 x12 32 ; SD x14 x16 96
    LD x16 x12 40 ; SD x14 x16 104
    LD x16 x12 48 ; SD x14 x16 112
    LD x16 x12 56 ; SD x14 x16 120
    ADDI x15 x15 1  ; SD x20 x15 464   -- log_length := n + 1
    ADDI x12 x12 64                    -- pop the two consumed stack words
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace Transient

open EvmAsm.Rv64

/-- Byte offset of the transient-log length cell in the env block
    (`EvmEnv.transientLogLengthOff = 464`). -/
def transientLogLengthOff : Nat := 464

/-- The concrete transient-storage-log base immediate (`0xa0830000`,
    `EvmAsm/Evm64/StorageAssertions.lean` `TRANSIENT_STORAGE_LOG_BASE`). Loaded
    with a plain `li` (no relocation), so this body is a verifiable `Program`. -/
def transientLogBaseImm : Word := 0xa0830000

/-- Parameterized RISC-V program implementing the `TSTORE` append core.
    `envReg` holds the env-block base (the handler uses `x20`); the body
    clobbers the caller-saved temporaries `x14`, `x15`, `x16`.
    35 instructions = 140 bytes. -/
def evm_tstore (envReg : Reg) : Program :=
  -- compute the append target x14 = base + 128 * log_length
  LD .x15 envReg (BitVec.ofNat 12 transientLogLengthOff) ;;
  LI .x14 transientLogBaseImm ;;
  SLLI .x16 .x15 (7 : BitVec 6) ;;
  ADD .x14 .x14 .x16 ;;
  -- addrHash = env.ADDRESS (env+0..24) → target+0..24
  LD .x16 envReg (BitVec.ofNat 12 0)  ;; SD .x14 .x16 (BitVec.ofNat 12 0)  ;;
  LD .x16 envReg (BitVec.ofNat 12 8)  ;; SD .x14 .x16 (BitVec.ofNat 12 8)  ;;
  LD .x16 envReg (BitVec.ofNat 12 16) ;; SD .x14 .x16 (BitVec.ofNat 12 16) ;;
  LD .x16 envReg (BitVec.ofNat 12 24) ;; SD .x14 .x16 (BitVec.ofNat 12 24) ;;
  -- slotKey = stack word 0 (x12+0..24) → target+32..56
  LD .x16 .x12 (BitVec.ofNat 12 0)  ;; SD .x14 .x16 (BitVec.ofNat 12 32) ;;
  LD .x16 .x12 (BitVec.ofNat 12 8)  ;; SD .x14 .x16 (BitVec.ofNat 12 40) ;;
  LD .x16 .x12 (BitVec.ofNat 12 16) ;; SD .x14 .x16 (BitVec.ofNat 12 48) ;;
  LD .x16 .x12 (BitVec.ofNat 12 24) ;; SD .x14 .x16 (BitVec.ofNat 12 56) ;;
  -- original = 0 (unused for transient) → target+64..88
  SD .x14 .x0 (BitVec.ofNat 12 64) ;;
  SD .x14 .x0 (BitVec.ofNat 12 72) ;;
  SD .x14 .x0 (BitVec.ofNat 12 80) ;;
  SD .x14 .x0 (BitVec.ofNat 12 88) ;;
  -- current = stack word 1 (x12+32..56) → target+96..120
  LD .x16 .x12 (BitVec.ofNat 12 32) ;; SD .x14 .x16 (BitVec.ofNat 12 96)  ;;
  LD .x16 .x12 (BitVec.ofNat 12 40) ;; SD .x14 .x16 (BitVec.ofNat 12 104) ;;
  LD .x16 .x12 (BitVec.ofNat 12 48) ;; SD .x14 .x16 (BitVec.ofNat 12 112) ;;
  LD .x16 .x12 (BitVec.ofNat 12 56) ;; SD .x14 .x16 (BitVec.ofNat 12 120) ;;
  -- log_length := n + 1
  ADDI .x15 .x15 (BitVec.ofNat 12 1) ;;
  SD envReg .x15 (BitVec.ofNat 12 transientLogLengthOff) ;;
  -- pop the two consumed stack words
  ADDI .x12 .x12 (BitVec.ofNat 12 64)

abbrev evm_tstore_code (envReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_tstore envReg)

/-- First 24 instructions of `evm_tstore`: setup (target computation) + the
    `addrHash` and `slotKey` limb copies + the four `original := 0` writes. The
    proof composes this with `evm_tstore_p2` (see `evm_tstore_split`); the split
    keeps each `runBlock` block small enough to compose. -/
abbrev evm_tstore_p1 (envReg : Reg) : Program :=
  LD .x15 envReg (BitVec.ofNat 12 transientLogLengthOff) ;;
  LI .x14 transientLogBaseImm ;;
  SLLI .x16 .x15 (7 : BitVec 6) ;;
  ADD .x14 .x14 .x16 ;;
  LD .x16 envReg (BitVec.ofNat 12 0)  ;; SD .x14 .x16 (BitVec.ofNat 12 0)  ;;
  LD .x16 envReg (BitVec.ofNat 12 8)  ;; SD .x14 .x16 (BitVec.ofNat 12 8)  ;;
  LD .x16 envReg (BitVec.ofNat 12 16) ;; SD .x14 .x16 (BitVec.ofNat 12 16) ;;
  LD .x16 envReg (BitVec.ofNat 12 24) ;; SD .x14 .x16 (BitVec.ofNat 12 24) ;;
  LD .x16 .x12 (BitVec.ofNat 12 0)  ;; SD .x14 .x16 (BitVec.ofNat 12 32) ;;
  LD .x16 .x12 (BitVec.ofNat 12 8)  ;; SD .x14 .x16 (BitVec.ofNat 12 40) ;;
  LD .x16 .x12 (BitVec.ofNat 12 16) ;; SD .x14 .x16 (BitVec.ofNat 12 48) ;;
  LD .x16 .x12 (BitVec.ofNat 12 24) ;; SD .x14 .x16 (BitVec.ofNat 12 56) ;;
  SD .x14 .x0 (BitVec.ofNat 12 64) ;;
  SD .x14 .x0 (BitVec.ofNat 12 72) ;;
  SD .x14 .x0 (BitVec.ofNat 12 80) ;;
  SD .x14 .x0 (BitVec.ofNat 12 88)

/-- Last 11 instructions of `evm_tstore`: the `current` limb copies + the
    length-cell bump + the two-word stack pop. -/
abbrev evm_tstore_p2 (envReg : Reg) : Program :=
  LD .x16 .x12 (BitVec.ofNat 12 32) ;; SD .x14 .x16 (BitVec.ofNat 12 96)  ;;
  LD .x16 .x12 (BitVec.ofNat 12 40) ;; SD .x14 .x16 (BitVec.ofNat 12 104) ;;
  LD .x16 .x12 (BitVec.ofNat 12 48) ;; SD .x14 .x16 (BitVec.ofNat 12 112) ;;
  LD .x16 .x12 (BitVec.ofNat 12 56) ;; SD .x14 .x16 (BitVec.ofNat 12 120) ;;
  ADDI .x15 .x15 (BitVec.ofNat 12 1) ;;
  SD envReg .x15 (BitVec.ofNat 12 transientLogLengthOff) ;;
  ADDI .x12 .x12 (BitVec.ofNat 12 64)

/-- Code-requirement abbrevs for the two halves. Wrapping `ofProg` in a named
    abbrev (rather than passing `CodeReq.ofProg` directly) keeps `runBlock`'s
    `deltaTarget` unfolding the abbrev to `ofProg` — passing `ofProg` bare makes
    it delta-unfold `ofProg` itself, which leaves the goal metavariable open. -/
abbrev evm_tstore_p1_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_tstore_p1 .x20)

abbrev evm_tstore_p2_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_tstore_p2 .x20)

theorem evm_tstore_split (envReg : Reg) :
    evm_tstore envReg = evm_tstore_p1 envReg ++ evm_tstore_p2 envReg := by
  rfl

theorem evm_tstore_p1_length (envReg : Reg) :
    (evm_tstore_p1 envReg).length = 24 := by
  simp [evm_tstore_p1, LD, LI, SLLI, ADD, SD, single, seq, Program.length_append]

/-- `evm_tstore` is exactly 35 RISC-V instructions = 140 bytes. -/
theorem evm_tstore_length (envReg : Reg) :
    (evm_tstore envReg).length = 35 := by
  simp [evm_tstore, LD, LI, SLLI, ADD, SD, ADDI, single, seq,
        Program.length_append]

theorem evm_tstore_byte_length (envReg : Reg) :
    4 * (evm_tstore envReg).length = 140 := by
  rw [evm_tstore_length]

end Transient
end EvmAsm.Evm64
