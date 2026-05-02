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
