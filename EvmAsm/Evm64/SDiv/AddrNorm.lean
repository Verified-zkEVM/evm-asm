/-
  EvmAsm.Evm64.SDiv.AddrNorm

  Address-normalization simp set for SDIV composition proofs.

  The base `signExtend12` literals live in `Rv64.AddrNorm`; this module
  re-tags the SDIV stack-slot subset and records the composed address
  equalities that recur in the SDIV bridge layer.
-/

import EvmAsm.Rv64.AddrNorm
import EvmAsm.Evm64.SDiv.AddrNormAttr
import EvmAsm.Evm64.SDiv.Program

namespace EvmAsm.Evm64.SDiv.AddrNorm

attribute [sdiv_addr]
  EvmAsm.Rv64.AddrNorm.se12_0
  EvmAsm.Rv64.AddrNorm.se12_8
  EvmAsm.Rv64.AddrNorm.se12_16
  EvmAsm.Rv64.AddrNorm.se12_24
  EvmAsm.Rv64.AddrNorm.se12_32
  EvmAsm.Rv64.AddrNorm.se12_40
  EvmAsm.Rv64.AddrNorm.se12_48
  EvmAsm.Rv64.AddrNorm.se12_56

@[sdiv_addr, grind =] theorem stackSlot0 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12) : Word) = sp := by
  rw [EvmAsm.Rv64.AddrNorm.se12_0]
  simp

@[sdiv_addr, grind =] theorem stackSlot8 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12) : Word) = sp + 8 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_8]

@[sdiv_addr, grind =] theorem stackSlot16 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12) : Word) = sp + 16 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_16]

@[sdiv_addr, grind =] theorem stackSlot24 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12) : Word) = sp + 24 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_24]

@[sdiv_addr, grind =] theorem stackSlot32 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12) : Word) = sp + 32 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_32]

@[sdiv_addr, grind =] theorem stackSlot40 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12) : Word) = sp + 40 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_40]

@[sdiv_addr, grind =] theorem stackSlot48 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12) : Word) = sp + 48 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_48]

@[sdiv_addr, grind =] theorem stackSlot56 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12) : Word) = sp + 56 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_56]

@[sdiv_addr, grind =] theorem divisorBaseSlot0 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12) : Word) = sp + 32 := by
  exact stackSlot32 sp

@[sdiv_addr, grind =] theorem divisorBaseSlot8 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12) : Word) = (sp + 32) + 8 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_40]
  bv_omega

@[sdiv_addr, grind =] theorem divisorBaseSlot16 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12) : Word) = (sp + 32) + 16 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_48]
  bv_omega

@[sdiv_addr, grind =] theorem divisorBaseSlot24 (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12) : Word) = (sp + 32) + 24 := by
  rw [EvmAsm.Rv64.AddrNorm.se12_56]
  bv_omega

@[sdiv_addr, grind =] theorem dividendTopSlot (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff : Word) =
      sp + 24 := by
  unfold EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  exact stackSlot24 sp

@[sdiv_addr, grind =] theorem divisorTopSlot (sp : Word) :
    (sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff : Word) =
      sp + 56 := by
  unfold EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  exact stackSlot56 sp

/-- The wrapper starts at the enclosing SDIV program base. -/
@[sdiv_addr]
theorem wrapperStart_addr (base : Word) :
    base = base + BitVec.ofNat 64 (4 * 0) := by
  bv_omega

/-- The appended unsigned DIV callable starts after the 71-instruction wrapper,
    at byte offset 284 from the enclosing SDIV program base. -/
@[sdiv_addr]
theorem divCallableStart_addr (base : Word) :
    base + (284 : Word) =
      base + BitVec.ofNat 64 (4 * 71) := by
  bv_omega

end EvmAsm.Evm64.SDiv.AddrNorm
