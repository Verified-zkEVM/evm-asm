/-
  EvmAsm.Evm64.Mcopy.Program

  RISC-V program implementing the overlap-aware copy core of the EVM `MCOPY`
  opcode (0x5e, EIP-5656; see `EvmAsm/Codegen/Programs/EvmMcopyHandlers.lean`).

  MCOPY copies `length` bytes of EVM memory from `srcOffset` to `destOffset`
  within the SAME memory buffer, with `memmove` semantics so overlapping ranges
  are handled correctly. The handler first reads the three low limbs
  (`destOffset` at `x12+0`, `srcOffset` at `x12+32`, `length` at `x12+64`), runs
  the range guard + dynamic-gas + MSIZE-update glue, and pops the three stack
  words (`addi x12, x12, 96`). This program is the **la-free / label-free copy
  core** that follows that glue: it computes the absolute src/dst byte pointers,
  chooses a copy direction to preserve the source, and runs the byte loop. The
  stack-underflow guard, range guard, gas, and MSIZE bookkeeping stay in the
  handler `preBody`/glue (unverified per DRIFT, exactly as for CALLDATACOPY).

  Register roles (matching the emitted `h_MCOPY` instantiation):

    `memBaseReg`  (x13) — EVM memory buffer base.
    `dstOffReg`   (x14) — destination offset (low limb).
    `srcOffReg`   (x15) — source offset (low limb).
    `cntReg`      (x16) — length; the loop counter, decremented each iteration.
    `dstPtrReg`   (x17) — running absolute destination byte pointer.
    `srcPtrReg`   (x18) — running absolute source byte pointer.
    `scratchReg`  (x19) — source-end offset for the overlap test, then reused as
                          the per-iteration byte scratch.

  Overlap decision (compares OFFSETS, sound because both pointers share
  `memBaseReg`): take the forward (low→high) loop when `destOff ≤ srcOff`
  (`bleu x14,x15` = `BGEU x15,x14`) or `destOff ≥ srcOff+length`
  (`bgeu x14,x19`, no overlap); otherwise (`srcOff < destOff < srcOff+length`)
  take the backward (high→low) loop after advancing both pointers one-past-end.

  Layout (21 instructions = 84 bytes); byte offsets are relative to the copy
  core's entry. Verified byte-identical against `riscv64-elf-as` + `objdump`:

     +0   ADD  dstPtr memBase dstOff       ; dstPtr = memBase + destOff
     +4   ADD  srcPtr memBase srcOff       ; srcPtr = memBase + srcOff
     +8   ADD  scratch srcOff cnt          ; scratch = srcOff + length (src end)
     +12  BGEU srcOff dstOff +44           ; destOff ≤ srcOff       → forward (+56)
     +16  BGEU dstOff scratch +40          ; destOff ≥ srcEnd       → forward (+56)
     +20  ADD  dstPtr dstPtr cnt           ; backward: point one-past-end
     +24  ADD  srcPtr srcPtr cnt
     +28  backward_loop: BEQ cnt x0 +56    ; cnt == 0 → done (+84)
     +32  ADDI dstPtr dstPtr -1
     +36  ADDI srcPtr srcPtr -1
     +40  LBU  scratch srcPtr 0
     +44  SB   dstPtr scratch 0
     +48  ADDI cnt cnt -1
     +52  JAL  x0 -24                       ; back to backward_loop (+28)
     +56  forward: BEQ cnt x0 +28          ; cnt == 0 → done (+84)
     +60  LBU  scratch srcPtr 0
     +64  SB   dstPtr scratch 0
     +68  ADDI srcPtr srcPtr 1
     +72  ADDI dstPtr dstPtr 1
     +76  ADDI cnt cnt -1
     +80  JAL  x0 -24                       ; back to forward (+56)
     +84  (exit; .Lmcopy_done glue `addi x10,x10,1 ; ret` stays in the handler)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace Mcopy

open EvmAsm.Rv64

/-- Overlap-aware copy core of the EVM `MCOPY` opcode. See the file header for
    the register roles, the overlap-direction decision, and the byte layout.

    21 instructions = 84 bytes. -/
def evm_mcopy
    (memBaseReg dstOffReg srcOffReg cntReg dstPtrReg srcPtrReg
      scratchReg : Reg) : Program :=
  -- Pointer setup and overlap decision.
  ADD dstPtrReg memBaseReg dstOffReg ;;                        -- +0
  ADD srcPtrReg memBaseReg srcOffReg ;;                        -- +4
  ADD scratchReg srcOffReg cntReg ;;                           -- +8
  single (.BGEU srcOffReg dstOffReg (BitVec.ofNat 13 44)) ;;   -- +12 → forward
  single (.BGEU dstOffReg scratchReg (BitVec.ofNat 13 40)) ;;  -- +16 → forward
  ADD dstPtrReg dstPtrReg cntReg ;;                            -- +20
  ADD srcPtrReg srcPtrReg cntReg ;;                            -- +24
  -- Backward loop (high→low): entry at +28.
  single (.BEQ cntReg .x0 (BitVec.ofNat 13 56)) ;;             -- +28 → done
  ADDI dstPtrReg dstPtrReg (-1 : BitVec 12) ;;                 -- +32
  ADDI srcPtrReg srcPtrReg (-1 : BitVec 12) ;;                 -- +36
  LBU scratchReg srcPtrReg 0 ;;                                -- +40
  SB dstPtrReg scratchReg 0 ;;                                 -- +44
  ADDI cntReg cntReg (-1 : BitVec 12) ;;                       -- +48
  single (.JAL .x0 (-24 : BitVec 21)) ;;                       -- +52 → backward
  -- Forward loop (low→high): entry at +56.
  single (.BEQ cntReg .x0 (BitVec.ofNat 13 28)) ;;             -- +56 → done
  LBU scratchReg srcPtrReg 0 ;;                                -- +60
  SB dstPtrReg scratchReg 0 ;;                                 -- +64
  ADDI srcPtrReg srcPtrReg 1 ;;                                -- +68
  ADDI dstPtrReg dstPtrReg 1 ;;                                -- +72
  ADDI cntReg cntReg (-1 : BitVec 12) ;;                       -- +76
  single (.JAL .x0 (-24 : BitVec 21))                          -- +80 → forward

/-- `CodeReq` for `evm_mcopy` placed at `base`. -/
abbrev evm_mcopy_code
    (memBaseReg dstOffReg srcOffReg cntReg dstPtrReg srcPtrReg
      scratchReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_mcopy memBaseReg dstOffReg srcOffReg cntReg dstPtrReg srcPtrReg
      scratchReg)

/-- `evm_mcopy` is exactly 21 RISC-V instructions. -/
theorem evm_mcopy_length
    (memBaseReg dstOffReg srcOffReg cntReg dstPtrReg srcPtrReg
      scratchReg : Reg) :
    (evm_mcopy memBaseReg dstOffReg srcOffReg cntReg dstPtrReg srcPtrReg
        scratchReg).length = 21 := by
  simp [evm_mcopy, ADD, ADDI, LBU, SB, single, seq, Program.length_append]

/-- `evm_mcopy` occupies 84 bytes in RV64 code memory. -/
theorem evm_mcopy_byte_length
    (memBaseReg dstOffReg srcOffReg cntReg dstPtrReg srcPtrReg
      scratchReg : Reg) :
    4 * (evm_mcopy memBaseReg dstOffReg srcOffReg cntReg dstPtrReg srcPtrReg
        scratchReg).length = 84 := by
  rw [evm_mcopy_length]

end Mcopy
end EvmAsm.Evm64
