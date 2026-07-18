/-
  Ambient dual of extract walk_next calls.

  Leaf `rlp_walk_next_spec_within` is already ambient-capable
  (`srcBase` + abs `srcOff` + full `srcBytes`). Pass
  `regionBase` / `absOff` / `bs` — same packaging as slice with renamed params.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextArgs
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextRest
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec

/-- Ambient walk_next0 call: regionBase + absOff into full blob. -/
theorem extractWalkNext0Call_ambient
    (regionBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (absOff : Nat) (old1 : Word)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff < bs.length)
    (hover : regionBase.toNat + absOff < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff) = true)
    (hss : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        absOff + 1 < bs.length ∧ regionBase.toNat + (absOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (regionBase + BitVec.ofNat 64 absOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old regionBase bs)
      (extractWalkNext0Post regionBase endPtr bs absOff) :=
  extractWalkNext0Call regionBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs absOff old1 hsalign hoff hover hvalid hss hls hll

/-- Bridge slice-relative pfx byte to ambient absOff via `txSlice_getElem`. -/
theorem walk_next_pfx_byte_ambient
    (bs : List (BitVec 8)) (off len rel : Nat)
    (hrel : rel < len) (hbound : off + len ≤ bs.length) :
    let absOff := ambientAbsOff off rel
    have hrel' : rel < (txSlice bs off len).length := by
      rw [txSlice_length bs off len hbound]; exact hrel
    have hoff : absOff < bs.length := ambientAbsOff_lt bs off rel len hrel hbound
    (txSlice bs off len)[rel]'hrel' = bs[absOff]'hoff :=
  txSlice_getElem bs off len rel hrel hbound

/-- Cursor after ambient load+inner: loadPtr+innerW = regionBase+absOff. -/
theorem loadPtr_add_inner_eq_abs
    (regionBase loadPtr innerW : Word) (off : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan : regionBase.toNat + (off + innerW.toNat) < 2 ^ 64) :
    loadPtr + innerW =
      regionBase + BitVec.ofNat 64 (ambientAbsOff off innerW.toNat) := by
  simp only [ambientAbsOff]
  have h1 := loadPtr_add_rel_eq regionBase loadPtr off innerW.toNat hptr hspan
  -- h1 : loadPtr + ofNat inner.toNat = regionBase + ofNat (off + inner.toNat)
  have hinner : BitVec.ofNat 64 innerW.toNat = innerW := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (BitVec.isLt innerW)
  simpa only [hinner] using h1

#print axioms extractWalkNext0Call_ambient
#print axioms walk_next_pfx_byte_ambient
#print axioms loadPtr_add_inner_eq_abs

/-- Ambient walk_next1 call: regionBase + absOff into full blob. -/
theorem extractWalkNext1Call_ambient
    (regionBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (absOff : Nat) (old1 : Word)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff < bs.length)
    (hover : regionBase.toNat + absOff < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff) = true)
    (hss : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        absOff + 1 < bs.length ∧ regionBase.toNat + (absOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (regionBase + BitVec.ofNat 64 absOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old regionBase bs)
      (extractWalkNext1Post regionBase endPtr bs absOff) :=
  extractWalkNext1Call regionBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs absOff old1 hsalign hoff hover hvalid hss hls hll

#print axioms extractWalkNext1Call_ambient

/-- Ambient walk_next2 call: regionBase + absOff into full blob. -/
theorem extractWalkNext2Call_ambient
    (regionBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (absOff : Nat) (old1 : Word)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff < bs.length)
    (hover : regionBase.toNat + absOff < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff) = true)
    (hss : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        absOff + 1 < bs.length ∧ regionBase.toNat + (absOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkNextPrest (regionBase + BitVec.ofNat 64 absOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old regionBase bs)
      (extractWalkNext2Post regionBase endPtr bs absOff) :=
  extractWalkNext2Call regionBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs absOff old1 hsalign hoff hover hvalid hss hls hll

#print axioms extractWalkNext2Call_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
