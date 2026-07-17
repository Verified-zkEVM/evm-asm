/-
  EvmAsm.Codegen.Programs.LogsBloomCopyArithmetic

  Layout-independent arithmetic facts shared by the header and receipt
  `logs_bloom` copy-loop proofs.  Keep this module free of `GuestAddrs`,
  `RegionMap`, and emitted-program imports so guest-layout changes do not
  rebuild these facts.
-/

import EvmAsm.Rv64.Instructions

namespace EvmAsm.Codegen.LogsBloomCopyArithmetic

open EvmAsm.Rv64

theorem succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]
    omega
  intro hc
  rw [hc] at ht
  simp at ht

theorem advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

theorem ofNat_toNat (fo : Word) : (BitVec.ofNat 64 fo.toNat : Word) = fo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt fo.isLt

end EvmAsm.Codegen.LogsBloomCopyArithmetic
