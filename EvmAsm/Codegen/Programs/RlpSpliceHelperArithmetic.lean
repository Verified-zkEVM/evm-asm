/-
  EvmAsm.Codegen.Programs.RlpSpliceHelperArithmetic

  Layout-independent Word/byte arithmetic facts shared by the
  `RlpSpliceHelperSpec` `rlp_item_size` triples.  Keep this module free of
  `GuestAddrs`, `RegionMap`, and emitted-program imports so guest-layout
  changes do not rebuild these facts.
-/

import EvmAsm.Rv64.Instructions

namespace EvmAsm.Codegen.RlpSpliceHelperSpec

open EvmAsm.Rv64

/-- `zeroExtend 64` of a byte keeps its `toNat`. -/
theorem toNat_zx (b : BitVec 8) : (b.zeroExtend 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := b.isLt; omega)

/-- `ult` from a `toNat` bound (byte, zero-extended, against a literal). -/
theorem ult_zx_of_lt (b : BitVec 8) (c : Word) (h : b.toNat < c.toNat) :
    BitVec.ult (b.zeroExtend 64) c := by
  have hN := toNat_zx b
  simpa [BitVec.ult, decide_eq_true_eq, hN] using h

/-- `¬ ult` from a `toNat` bound (byte, zero-extended, against a literal). -/
theorem not_ult_zx_of_ge (b : BitVec 8) (c : Word) (h : c.toNat ≤ b.toNat) :
    ¬ BitVec.ult (b.zeroExtend 64) c := by
  have hN := toNat_zx b
  simp only [BitVec.ult, decide_eq_true_eq, hN]
  omega

/-- The short-string span: `(zx b - 128) + 1 = b - 127` for `b ≥ 0x80`. -/
theorem ris_result_128 (b : BitVec 8) (h : 128 ≤ b.toNat) :
    ((b.zeroExtend 64) + signExtend12 (-128 : BitVec 12)) + signExtend12 (1 : BitVec 12)
      = BitVec.ofNat 64 (b.toNat - 127) := by
  have hb := b.isLt
  have h1 : (signExtend12 (-128 : BitVec 12) : Word).toNat = 2 ^ 64 - 128 := by decide
  have h2 : (signExtend12 (1 : BitVec 12) : Word).toNat = 1 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, h1, h2, BitVec.toNat_ofNat]
  omega

/-- The short-list span: `(zx b - 192) + 1 = b - 191` for `b ≥ 0xc0`. -/
theorem ris_result_192 (b : BitVec 8) (h : 192 ≤ b.toNat) :
    ((b.zeroExtend 64) + signExtend12 (-192 : BitVec 12)) + signExtend12 (1 : BitVec 12)
      = BitVec.ofNat 64 (b.toNat - 191) := by
  have hb := b.isLt
  have h1 : (signExtend12 (-192 : BitVec 12) : Word).toNat = 2 ^ 64 - 192 := by decide
  have h2 : (signExtend12 (1 : BitVec 12) : Word).toNat = 1 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, h1, h2, BitVec.toNat_ofNat]
  omega

end EvmAsm.Codegen.RlpSpliceHelperSpec
