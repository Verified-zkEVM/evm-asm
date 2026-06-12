/-
  EvmAsm.Rv64.RLP.Phase2LongLengthBridge

  Semantic bridge for the RLP long-form length loop: the big-endian shift-add
  accumulation that the Phase 2 loop closures leave in `x11` equals the value
  the **pure** RLP spec decodes via `Nat.fromBytesBE`.

  For length-of-length `N ∈ {1..8}`, the closure
  `rlp_phase2_long_loop_{N}_byte_post` (with `len = 0`) sets `x11` to
  `(((0 <<< 8) + b1) <<< 8 + b2) … + bN`, where each `bi = ei.zeroExtend 64`
  is a zero-extended byte (`ei.toNat < 256`). Since `N ≤ 8`, the decoded value
  is `< 256 ^ 8 = 2 ^ 64`, so there is no 64-bit overflow and the accumulation
  equals `BitVec.ofNat 64 (Nat.fromBytesBE [e0, …, e_{N-1}])`.

  These per-`N` equalities are consumed by the `…_fromBytesBE` full-path
  restatements (`Phase1E3LongStringFromBytesBE.lean` /
  `Phase1E5LongListFromBytesBE.lean`) to express the decoder's end-to-end
  output length in spec terms. Each LHS is transcribed to match the
  corresponding `rlp_phase2_long_loop_{N}_byte_post` `length'` exactly, so the
  downstream rewrites fire.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopEight
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- A single zero-extended byte already *is* its own big-endian decode:
    `Nat.fromBytesBE [e0] = e0.toNat`. Used for the `lenLen = 1` long-string
    path (`0xB8`), whose closure collapses `(0 <<< 8) + e0` to `e0`. -/
theorem rlp_be_byte_eq_fromBytesBE (e0 : Byte) :
    e0.zeroExtend 64 = BitVec.ofNat 64 (Nat.fromBytesBE [e0]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.fromBytesBE,
             List.length_nil]
  have h0 := e0.isLt
  omega

/-- Shared simp set + closing `omega` for the long-form length bridge: push
    `toNat` through the shift-add chain, unfold `Nat.fromBytesBE` over the
    concrete byte list, and discharge the (literal-modulus, byte-bounded)
    arithmetic. -/
theorem rlp_be_len_1_eq_fromBytesBE (e0 : Byte) :
    ((0 : Word) <<< 8) + e0.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt
  omega

theorem rlp_be_len_2_eq_fromBytesBE (e0 e1 : Byte) :
    (((0 : Word) <<< 8) + e0.zeroExtend 64) <<< 8 + e1.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_cons, List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt; have h1 := e1.isLt
  omega

theorem rlp_be_len_3_eq_fromBytesBE (e0 e1 e2 : Byte) :
    ((((0 : Word) <<< 8) + e0.zeroExtend 64) <<< 8 + e1.zeroExtend 64) <<< 8
        + e2.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_cons, List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt; have h1 := e1.isLt; have h2 := e2.isLt
  omega

theorem rlp_be_len_4_eq_fromBytesBE (e0 e1 e2 e3 : Byte) :
    (((((0 : Word) <<< 8) + e0.zeroExtend 64) <<< 8 + e1.zeroExtend 64) <<< 8
        + e2.zeroExtend 64) <<< 8 + e3.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_cons, List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt; have h1 := e1.isLt; have h2 := e2.isLt; have h3 := e3.isLt
  omega

theorem rlp_be_len_5_eq_fromBytesBE (e0 e1 e2 e3 e4 : Byte) :
    ((((((0 : Word) <<< 8) + e0.zeroExtend 64) <<< 8 + e1.zeroExtend 64) <<< 8
        + e2.zeroExtend 64) <<< 8 + e3.zeroExtend 64) <<< 8 + e4.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_cons, List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt; have h1 := e1.isLt; have h2 := e2.isLt; have h3 := e3.isLt
  have h4 := e4.isLt
  omega

theorem rlp_be_len_6_eq_fromBytesBE (e0 e1 e2 e3 e4 e5 : Byte) :
    (((((((0 : Word) <<< 8) + e0.zeroExtend 64) <<< 8 + e1.zeroExtend 64) <<< 8
        + e2.zeroExtend 64) <<< 8 + e3.zeroExtend 64) <<< 8 + e4.zeroExtend 64) <<< 8
        + e5.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_cons, List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt; have h1 := e1.isLt; have h2 := e2.isLt; have h3 := e3.isLt
  have h4 := e4.isLt; have h5 := e5.isLt
  omega

theorem rlp_be_len_7_eq_fromBytesBE (e0 e1 e2 e3 e4 e5 e6 : Byte) :
    ((((((((0 : Word) <<< 8) + e0.zeroExtend 64) <<< 8 + e1.zeroExtend 64) <<< 8
        + e2.zeroExtend 64) <<< 8 + e3.zeroExtend 64) <<< 8 + e4.zeroExtend 64) <<< 8
        + e5.zeroExtend 64) <<< 8 + e6.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5, e6]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_cons, List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt; have h1 := e1.isLt; have h2 := e2.isLt; have h3 := e3.isLt
  have h4 := e4.isLt; have h5 := e5.isLt; have h6 := e6.isLt
  omega

theorem rlp_be_len_8_eq_fromBytesBE (e0 e1 e2 e3 e4 e5 e6 e7 : Byte) :
    (((((((((0 : Word) <<< 8) + e0.zeroExtend 64) <<< 8 + e1.zeroExtend 64) <<< 8
        + e2.zeroExtend 64) <<< 8 + e3.zeroExtend 64) <<< 8 + e4.zeroExtend 64) <<< 8
        + e5.zeroExtend 64) <<< 8 + e6.zeroExtend 64) <<< 8 + e7.zeroExtend 64
      = BitVec.ofNat 64 (Nat.fromBytesBE [e0, e1, e2, e3, e4, e5, e6, e7]) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.fromBytesBE,
             List.length_cons, List.length_nil]
  have hz : BitVec.toNat (0 : Word) = 0 := rfl
  have h0 := e0.isLt; have h1 := e1.isLt; have h2 := e2.isLt; have h3 := e3.isLt
  have h4 := e4.isLt; have h5 := e5.isLt; have h6 := e6.isLt; have h7 := e7.isLt
  omega

-- Concrete sanity checks: the bridge yields the *spec value*, not just a
-- well-typed term. `[0x01, 0x00]` big-endian = 256.
example : ((0 : Word) <<< 8) + (0x05 : Byte).zeroExtend 64
    = BitVec.ofNat 64 (Nat.fromBytesBE [(0x05 : Byte)]) := by decide
example : Nat.fromBytesBE [(0x01 : Byte), (0x00 : Byte)] = 256 := by decide

end EvmAsm.Rv64.RLP
