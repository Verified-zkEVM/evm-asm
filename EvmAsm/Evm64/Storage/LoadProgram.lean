/-
  EvmAsm.Evm64.Storage.LoadProgram

  RISC-V program implementing the reverse-scan core of the EVM `SLOAD` opcode
  (0x5c, EIP-1153 persistent storage).

  SLOAD scans the persistent-storage exec-log (`EvmAsm/Evm64/StorageAssertions.lean`)
  from the END (most-recent entry first) for an entry matching the executing
  frame's `env.ADDRESS` (4 limbs) and the slot key at the stack top (4 limbs).
  On a match it copies that entry's `current` word to the stack top IN PLACE
  (pop-1-push-1: `x12` unchanged); if no entry matches (or the log is empty) it
  writes zero. Because TSTORE only ever appends, the first match found scanning
  backwards is the most-recent write — the EIP-1153 value.

  This program is the la-FREE scan body of the `h_SLOAD` dispatcher handler
  (`EvmAsm/Codegen/Programs/Storage.lean`); the stack-underflow guard stays in
  the handler `preBody` glue. The instructions here are a byte-identical
  encoding of the handler's former inline scan text: the numeric local labels
  (`1:`/`3:`/`4:`/`5:`) become concrete PC-relative branch offsets, and the
  `li x14, 0xa0630000` pseudo-instruction becomes its exact GNU-as expansion
  `lui x14, 0xa ; addiw x14, x14, 99 ; slli x14, x14, 16` (verified against
  `riscv64-elf-as`: both forms assemble to identical machine code), so the
  Lean `Program` layout (4 bytes per instruction) equals the machine layout
  and every branch offset below is the real encoded offset.

  Layout (47 instructions = 188 bytes), `envReg = x20`:

     +0   LD   x15 envReg 448     ; x15 = persistent log_length n
     +4   BEQ  x15 x0 +168        ; empty log → zero arm (+172)
     +8   LUI  x14 0xa            ; \
     +12  ADDIW x14 x14 99       ;  } x14 = 0xa0630000 (persistent log base)
     +16  SLLI x14 x14 16         ; /
     +20  SLLI x16 x15 7          ; x16 = n * 128
     +24  ADD  x14 x14 x16        ; x14 = one-past-end = base + 128*n
     +28  ADDI x14 x14 -128       ; loop entry (label 1): step back one entry
     +32  LD x16 0(x14)  ; +36 LD x17 0(x20)  ; +40  BNE x16 x17 +124  → +164
     +44  LD x16 8(x14)  ; +48 LD x17 8(x20)  ; +52  BNE x16 x17 +112  → +164
     +56  LD x16 16(x14) ; +60 LD x17 16(x20) ; +64  BNE x16 x17 +100  → +164
     +68  LD x16 24(x14) ; +72 LD x17 24(x20) ; +76  BNE x16 x17 +88   → +164
     +80  LD x16 32(x14) ; +84 LD x17 0(x12)  ; +88  BNE x16 x17 +76   → +164
     +92  LD x16 40(x14) ; +96 LD x17 8(x12)  ; +100 BNE x16 x17 +64   → +164
     +104 LD x16 48(x14) ; +108 LD x17 16(x12); +112 BNE x16 x17 +52   → +164
     +116 LD x16 56(x14) ; +120 LD x17 24(x12); +124 BNE x16 x17 +40   → +164
     +128 LD x16 96(x14)  ; +132 SD x16 0(x12)   ; MATCH: copy current
     +136 LD x16 104(x14) ; +140 SD x16 8(x12)
     +144 LD x16 112(x14) ; +148 SD x16 16(x12)
     +152 LD x16 120(x14) ; +156 SD x16 24(x12)
     +160 JAL x0 +28              ; skip decrement + zero arm → +188
     +164 ADDI x15 x15 -1         ; label 3: one fewer entry left
     +168 BNE x15 x0 -140         ; more entries → loop entry (+28)
     +172 SD x0 0(x12)            ; label 4: zero arm (no match)
     +176 SD x0 8(x12)
     +180 SD x0 16(x12)
     +184 SD x0 24(x12)
     +188 (exit; label 5)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic
import EvmAsm.Evm64.Environment.Layout

namespace EvmAsm.Evm64
namespace Storage

open EvmAsm.Rv64

/-- Byte offset of the persistent-log length cell in the env block
    (`EvmEnv.persistentLogLengthOff = 448`). SLOAD loads `x15` from here. -/
def persistentLogLengthOff : Nat := 448

/-- First 7 instructions of `evm_sload`: load the log length, exit to the zero
    arm when it is 0, materialize the persistent log base
    (`lui`/`addiw`/`slli` — the exact GNU-as `li 0xa0630000` expansion), and
    compute the one-past-end scan pointer `x14 = base + 128 * n`. -/
def evm_sload_head (envReg : Reg) : Program :=
  LD .x15 envReg (BitVec.ofNat 12 persistentLogLengthOff) ;;
  BEQ .x15 .x0 (BitVec.ofNat 13 168) ;;
  LUI .x14 (BitVec.ofNat 20 0xa) ;;
  ADDIW .x14 .x14 (BitVec.ofNat 12 99) ;;
  SLLI .x14 .x14 (16 : BitVec 6) ;;
  SLLI .x16 .x15 (7 : BitVec 6) ;;
  ADD .x14 .x14 .x16

/-- The 25-instruction compare block of one loop iteration: step `x14` back one
    entry, then compare the entry's `addrHash` limbs against `env.ADDRESS`
    (env+0..24) and its `slotKey` limbs against the stack top (x12+0..24).
    Any mismatch exits to the decrement block (loop-slice offset +136). -/
def evm_sload_cmp (envReg : Reg) : Program :=
  ADDI .x14 .x14 (-128 : BitVec 12) ;;
  LD .x16 .x14 (BitVec.ofNat 12 0)  ;; LD .x17 envReg (BitVec.ofNat 12 0)  ;;
  BNE .x16 .x17 (BitVec.ofNat 13 124) ;;
  LD .x16 .x14 (BitVec.ofNat 12 8)  ;; LD .x17 envReg (BitVec.ofNat 12 8)  ;;
  BNE .x16 .x17 (BitVec.ofNat 13 112) ;;
  LD .x16 .x14 (BitVec.ofNat 12 16) ;; LD .x17 envReg (BitVec.ofNat 12 16) ;;
  BNE .x16 .x17 (BitVec.ofNat 13 100) ;;
  LD .x16 .x14 (BitVec.ofNat 12 24) ;; LD .x17 envReg (BitVec.ofNat 12 24) ;;
  BNE .x16 .x17 (BitVec.ofNat 13 88) ;;
  LD .x16 .x14 (BitVec.ofNat 12 32) ;; LD .x17 .x12 (BitVec.ofNat 12 0)  ;;
  BNE .x16 .x17 (BitVec.ofNat 13 76) ;;
  LD .x16 .x14 (BitVec.ofNat 12 40) ;; LD .x17 .x12 (BitVec.ofNat 12 8)  ;;
  BNE .x16 .x17 (BitVec.ofNat 13 64) ;;
  LD .x16 .x14 (BitVec.ofNat 12 48) ;; LD .x17 .x12 (BitVec.ofNat 12 16) ;;
  BNE .x16 .x17 (BitVec.ofNat 13 52) ;;
  LD .x16 .x14 (BitVec.ofNat 12 56) ;; LD .x17 .x12 (BitVec.ofNat 12 24) ;;
  BNE .x16 .x17 (BitVec.ofNat 13 40)

/-- The 9-instruction match arm: copy the matched entry's `current` word
    (x14+96..120) to the stack top in place, then jump past the decrement and
    zero arms to the exit. -/
def evm_sload_copy : Program :=
  LD .x16 .x14 (BitVec.ofNat 12 96)  ;; SD .x12 .x16 (BitVec.ofNat 12 0)  ;;
  LD .x16 .x14 (BitVec.ofNat 12 104) ;; SD .x12 .x16 (BitVec.ofNat 12 8)  ;;
  LD .x16 .x14 (BitVec.ofNat 12 112) ;; SD .x12 .x16 (BitVec.ofNat 12 16) ;;
  LD .x16 .x14 (BitVec.ofNat 12 120) ;; SD .x12 .x16 (BitVec.ofNat 12 24) ;;
  JAL .x0 (BitVec.ofNat 21 28)

/-- The 6-instruction loop tail: decrement the remaining-entry counter; loop
    back to the compare block while nonzero, else fall into the zero arm
    (no entry matched → push 0). -/
def evm_sload_tail : Program :=
  ADDI .x15 .x15 (-1 : BitVec 12) ;;
  BNE .x15 .x0 (-140 : BitVec 13) ;;
  SD .x12 .x0 (BitVec.ofNat 12 0)  ;;
  SD .x12 .x0 (BitVec.ofNat 12 8)  ;;
  SD .x12 .x0 (BitVec.ofNat 12 16) ;;
  SD .x12 .x0 (BitVec.ofNat 12 24)

/-- The 40-instruction loop slice (everything after the head): compare block,
    match-copy arm, decrement/zero tail. In situ it occupies program offsets
    +28..+188; all loop-internal branch offsets stay inside this slice
    (backward `BNE -140` returns to the slice start). -/
def evm_sload_loop (envReg : Reg) : Program :=
  evm_sload_cmp envReg ++ evm_sload_copy ++ evm_sload_tail

/-- Parameterized RISC-V program implementing the `SLOAD` reverse scan.
    `envReg` holds the env-block base (the handler uses `x20`); the body
    clobbers the caller-saved temporaries `x14`, `x15`, `x16`, `x17`.
    47 instructions = 188 bytes. -/
def evm_sload (envReg : Reg) : Program :=
  evm_sload_head envReg ++ evm_sload_loop envReg

/-! ## Code-requirement abbrevs

Wrapping `ofProg` in a named abbrev (rather than passing `CodeReq.ofProg`
directly) keeps `runBlock`'s `deltaTarget` unfolding the abbrev to `ofProg` —
passing `ofProg` bare makes it delta-unfold `ofProg` itself, which leaves the
goal metavariable open (see `StoreProgram.lean`). -/

abbrev evm_sload_code (envReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sload envReg)

abbrev evm_sload_loop_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sload_loop .x20)

abbrev evm_sload_cmp_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sload_cmp .x20)

abbrev evm_sload_copy_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_sload_copy

abbrev evm_sload_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_sload_tail

/-! ## Lengths and splits -/

theorem evm_sload_cmp_length (envReg : Reg) :
    (evm_sload_cmp envReg).length = 25 := by
  simp [evm_sload_cmp, ADDI, LD, BNE, single, seq, Program.length_append]

theorem evm_sload_copy_length : evm_sload_copy.length = 9 := by
  simp [evm_sload_copy, LD, SD, JAL, single, seq, Program.length_append]

theorem evm_sload_tail_length : evm_sload_tail.length = 6 := by
  simp [evm_sload_tail, ADDI, BNE, SD, single, seq, Program.length_append]

theorem evm_sload_loop_length (envReg : Reg) :
    (evm_sload_loop envReg).length = 40 := by
  simp [evm_sload_loop, Program.length_append,
        evm_sload_cmp_length, evm_sload_copy_length, evm_sload_tail_length]

theorem evm_sload_head_length (envReg : Reg) :
    (evm_sload_head envReg).length = 7 := by
  simp [evm_sload_head, LD, BEQ, LUI, ADDIW, SLLI, ADD, single, seq,
        Program.length_append]

/-- `evm_sload` is exactly 47 RISC-V instructions = 188 bytes. -/
theorem evm_sload_length (envReg : Reg) :
    (evm_sload envReg).length = 47 := by
  simp [evm_sload, Program.length_append,
        evm_sload_head_length, evm_sload_loop_length]

theorem evm_sload_byte_length (envReg : Reg) :
    4 * (evm_sload envReg).length = 188 := by
  rw [evm_sload_length]

theorem evm_sload_split (envReg : Reg) :
    evm_sload envReg = evm_sload_head envReg ++ evm_sload_loop envReg := rfl

theorem evm_sload_loop_split (envReg : Reg) :
    evm_sload_loop envReg = evm_sload_cmp envReg ++ evm_sload_copy ++ evm_sload_tail := rfl

end Storage
end EvmAsm.Evm64
