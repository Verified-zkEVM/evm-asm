/-
  EvmAsm.Evm64.MStore.LimbSpec

  Level-1 executable specs for MSTORE byte-unpack blocks.
-/

import EvmAsm.Evm64.MStore.ByteAlg
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the eight SRLI/SB byte-unpack steps in one MSTORE limb. -/
def mstoreByteUnpackEightCode
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (base : Word) : CodeReq :=
  ((CodeReq.singleton base
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 0) * 8)))).union
   (CodeReq.singleton (base + 4) (.SB addrReg byteReg off0))).union
  (((CodeReq.singleton (base + 8)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 1) * 8)))).union
    (CodeReq.singleton (base + 12) (.SB addrReg byteReg off1))).union
  (((CodeReq.singleton (base + 16)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 2) * 8)))).union
    (CodeReq.singleton (base + 20) (.SB addrReg byteReg off2))).union
  (((CodeReq.singleton (base + 24)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 3) * 8)))).union
    (CodeReq.singleton (base + 28) (.SB addrReg byteReg off3))).union
  (((CodeReq.singleton (base + 32)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 4) * 8)))).union
    (CodeReq.singleton (base + 36) (.SB addrReg byteReg off4))).union
  (((CodeReq.singleton (base + 40)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 5) * 8)))).union
    (CodeReq.singleton (base + 44) (.SB addrReg byteReg off5))).union
  (((CodeReq.singleton (base + 48)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 6) * 8)))).union
    (CodeReq.singleton (base + 52) (.SB addrReg byteReg off6))).union
   ((CodeReq.singleton (base + 56)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 7) * 8)))).union
    (CodeReq.singleton (base + 60) (.SB addrReg byteReg off7)))))))))

/-- CodeReq for one MSTORE limb: load a source limb, then emit eight
    byte-unpack SRLI/SB steps. -/
def mstoreOneLimbCode
    (addrReg byteReg accReg : Reg)
    (srcOff off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD accReg .x12 srcOff)).union
    (mstoreByteUnpackEightCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 off7 (base + 4))

/-- Bundled precondition for the upcoming one-limb MSTORE spec. It contains
    the address/scratch registers, the two destination dwords that may be
    touched by an unaligned 8-byte limb write, and the source EVM-stack limb
    loaded from `sp + signExtend12 srcOff`. -/
@[irreducible]
def mstoreOneLimbPre
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (srcOff : BitVec 12) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 srcOff) ↦ₘ limbVal)

theorem mstoreOneLimbPre_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (srcOff : BitVec 12) :
    mstoreOneLimbPre addrReg byteReg accReg
        addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal srcOff =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 srcOff) ↦ₘ limbVal)) := by
  delta mstoreOneLimbPre
  rfl

/-- Bundled postcondition for the upcoming one-limb MSTORE spec. The source
    limb has been loaded into `accReg`, the final `byteReg` value is the last
    SRLI result, and the low/high destination dwords are updated by the pure
    eight-byte fold `mstoreDwordPairStoreLimb`. -/
@[irreducible]
def mstoreOneLimbPost
    (addrReg byteReg accReg : Reg)
    (addrPtr loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (srcOff : BitVec 12) : Assertion :=
  let stored := MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
  (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 srcOff) ↦ₘ limbVal)

theorem mstoreOneLimbPost_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (srcOff : BitVec 12) :
    mstoreOneLimbPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp limbVal start srcOff =
    (let stored := MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
     (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 srcOff) ↦ₘ limbVal)) := by
  delta mstoreOneLimbPost
  rfl

/-- One-instruction source-limb load used by `mstore_one_limb_spec_within`. -/
theorem mstore_one_limb_load_spec_within
    (accReg : Reg) (sp accOld limbVal : Word)
    (srcOff : BitVec 12) (base : Word)
    (h_acc_ne_x0 : accReg ≠ .x0) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD accReg .x12 srcOff))
      (((.x12 : Reg) ↦ᵣ sp) ** (accReg ↦ᵣ accOld) **
       ((sp + signExtend12 srcOff) ↦ₘ limbVal))
      (((.x12 : Reg) ↦ᵣ sp) ** (accReg ↦ᵣ limbVal) **
       ((sp + signExtend12 srcOff) ↦ₘ limbVal)) :=
  ld_spec_gen_within accReg .x12 sp accOld limbVal srcOff base h_acc_ne_x0

/-- Two-instruction MSTORE byte-unpack step:
    shift the selected byte of `accReg` into `byteReg`, then store that
    low byte to `addrReg + dstOff`.

    The byte index is written in the program's descending form: `k = 0`
    selects byte 7, and `k = 7` selects byte 0. -/
theorem mstore_byte_unpack_step_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal byteOld wordOld : Word)
    (dwordAddr : Word)
    (k : Nat) (dstOff : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_k_lt : k < 8)
    (h_align : alignToDword (addrPtr + signExtend12 dstOff) = dwordAddr)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 dstOff) = true) :
    let shift := BitVec.ofNat 6 ((7 - k) * 8)
    let byteVal := accVal >>> shift.toNat
    let storedByte := extractByte accVal (7 - k)
    let cr :=
      (CodeReq.singleton base (.SRLI byteReg accReg shift)).union
        (CodeReq.singleton (base + 4) (.SB addrReg byteReg dstOff))
    cpsTripleWithin 2 base (base + 8) cr
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteOld) **
       (dwordAddr ↦ₘ wordOld))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteVal) **
       (dwordAddr ↦ₘ
         replaceByte wordOld (byteOffset (addrPtr + signExtend12 dstOff)) storedByte)) := by
  intro shift byteVal storedByte cr
  have h_shift_toNat : shift.toNat = (7 - k) * 8 := by
    unfold shift
    simp [BitVec.toNat_ofNat]
    omega
  have h_stored :
      byteVal.truncate 8 = storedByte := by
    rw [show byteVal = accVal >>> ((7 - k) * 8) by
      unfold byteVal
      rw [h_shift_toNat]]
    rw [show storedByte = extractByte accVal (7 - k) by rfl]
    rw [← MStore.extractByte_shr_zero_descending accVal k h_k_lt]
    rfl
  have S := srli_spec_gen_within byteReg accReg byteOld accVal shift base h_byte_ne_x0
  have B := sb_spec_gen_within addrReg byteReg addrPtr byteVal dstOff (base + 4)
    dwordAddr wordOld h_align h_valid
  rw [h_stored] at B
  runBlock S B

end EvmAsm.Evm64
