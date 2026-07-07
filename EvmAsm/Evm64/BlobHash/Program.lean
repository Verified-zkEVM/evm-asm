/-
  EvmAsm.Evm64.BlobHash.Program

  RISC-V program implementing the EVM `BLOBHASH` opcode (0x49, EIP-4844).

  BLOBHASH pops an index and pushes `tx.blob_versioned_hashes[index]`, or zero
  when the index is out of range (any nonzero high limb, or low limb ≥ the
  number of hashes). The dispatcher prologue copies up to 16 versioned hashes
  into the `evm_blob_hashes` table (32 bytes each) and stores the copied count
  in the env block at offset 544.

  This verified program is parameterized over `tableBaseReg`, which the
  handler `preBody` glue seeds with the `evm_blob_hashes` address (`la` — a
  link-time pseudo-instruction that stays outside the verified body, the
  CALLDATALOAD staging precedent). The body replaces the popped index word
  in place at the stack top (`x12` unchanged — pop one, push one).

  Layout (24 instructions = 96 bytes; branch offsets to the zero arm at +80):

     +0   LD   tmpReg x12  8        ; index limb 1
     +4   BNE  tmpReg x0   +76      ; nonzero high limb → zero
     +8   LD   tmpReg x12  16       ; index limb 2
     +12  BNE  tmpReg x0   +68
     +16  LD   tmpReg x12  24       ; index limb 3
     +20  BNE  tmpReg x0   +60
     +24  LD   idxReg x12  0        ; low 64-bit index
     +28  LD   tmpReg envBaseReg 544 ; copied blob-hash count
     +32  BGEU idxReg tmpReg +48    ; index ≥ count → zero
     +36  SLLI idxReg idxReg 5      ; 32 bytes per versioned hash
     +40  ADD  tableBaseReg tableBaseReg idxReg
     +44  LD   valReg tableBaseReg 0   ; copy hash limbs to stack top
     +48  SD   x12 valReg 0
     +52  LD   valReg tableBaseReg 8
     +56  SD   x12 valReg 8
     +60  LD   valReg tableBaseReg 16
     +64  SD   x12 valReg 16
     +68  LD   valReg tableBaseReg 24
     +72  SD   x12 valReg 24
     +76  JAL  x0 +20               ; skip the zero arm → +96
     +80  SD   x12 x0 0             ; zero arm: push 0
     +84  SD   x12 x0 8
     +88  SD   x12 x0 16
     +92  SD   x12 x0 24
     +96  (exit)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace BlobHash

open EvmAsm.Rv64

/-- Byte offset of the copied blob-hash count within the dispatcher env
    block. Seeded by the runtime prologue (≤ 16). -/
def blobHashCountOff : Nat := 544

/-- Parameterized RISC-V program implementing `BLOBHASH`. Registers:
    `envBaseReg` env-block base; `tableBaseReg` seeded with the
    `evm_blob_hashes` address by handler glue (clobbered on the taken path);
    `idxReg`/`tmpReg`/`valReg` caller-saved temporaries. All distinct from
    each other and from `x0`/`x12`. 24 instructions = 96 bytes. -/
def evm_blobhash (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg) : Program :=
  LD tmpReg .x12 8 ;;
  BNE tmpReg .x0 (BitVec.ofNat 13 76) ;;
  LD tmpReg .x12 16 ;;
  BNE tmpReg .x0 (BitVec.ofNat 13 68) ;;
  LD tmpReg .x12 24 ;;
  BNE tmpReg .x0 (BitVec.ofNat 13 60) ;;
  LD idxReg .x12 0 ;;
  LD tmpReg envBaseReg (BitVec.ofNat 12 blobHashCountOff) ;;
  BGEU idxReg tmpReg (BitVec.ofNat 13 48) ;;
  SLLI idxReg idxReg 5 ;;
  ADD tableBaseReg tableBaseReg idxReg ;;
  LD valReg tableBaseReg 0 ;;
  SD .x12 valReg 0 ;;
  LD valReg tableBaseReg 8 ;;
  SD .x12 valReg 8 ;;
  LD valReg tableBaseReg 16 ;;
  SD .x12 valReg 16 ;;
  LD valReg tableBaseReg 24 ;;
  SD .x12 valReg 24 ;;
  JAL .x0 (BitVec.ofNat 21 20) ;;
  SD .x12 .x0 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

abbrev evm_blobhash_code
    (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_blobhash envBaseReg tableBaseReg idxReg tmpReg valReg)

/-- `evm_blobhash` is exactly 24 RISC-V instructions = 96 bytes. -/
theorem evm_blobhash_length (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg) :
    (evm_blobhash envBaseReg tableBaseReg idxReg tmpReg valReg).length = 24 := by
  simp [evm_blobhash, LD, SD, BNE, BGEU, SLLI, ADD, JAL, single, seq,
        Program.length_append]

theorem evm_blobhash_byte_length (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg) :
    4 * (evm_blobhash envBaseReg tableBaseReg idxReg tmpReg valReg).length = 96 := by
  rw [evm_blobhash_length]

end BlobHash
end EvmAsm.Evm64
