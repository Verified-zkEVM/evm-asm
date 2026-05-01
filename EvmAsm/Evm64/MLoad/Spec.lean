/-
  EvmAsm.Evm64.MLoad.Spec

  Stack-level bridge lemmas for the MLOAD result word.  The instruction
  composition proves four packed 64-bit output limbs; this file packages
  those limbs as a single `EvmWord` and folds the four destination cells into
  `evmWordIs`.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.Evm64.MLoad.LimbSpecEight

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the two-instruction MLOAD address prologue. -/
def mloadPrologueCode
    (offReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD offReg .x12 0)).union
    (CodeReq.singleton (base + 4) (.ADD addrReg memBaseReg offReg))

/--
  MLOAD prologue spec: load the low 64-bit offset limb from the EVM stack and
  compute the concrete byte address `memBase + offset` used by the four
  subsequent limb-load blocks.
-/
theorem mload_prologue_spec_within
    (offReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mloadPrologueCode offReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  unfold mloadPrologueCode
  have h_ld := ld_spec_within offReg (.x12 : Reg) sp offOld offset 0 base h_off_ne_x0
  rw [show (sp + signExtend12 (0 : BitVec 12) : Word) = sp from by
    rw [signExtend12_0]; bv_omega] at h_ld
  have h_add := add_spec_gen_within addrReg memBaseReg offReg memBase offset addrOld
    (base + 4) h_addr_ne_x0
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at h_add
  runBlock h_ld h_add

/-- The 256-bit value assembled by MLOAD from four little-endian output limbs. -/
def mloadLoadedWord (l0 l1 l2 l3 : Word) : EvmWord :=
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => l0
    | 1 => l1
    | 2 => l2
    | 3 => l3

theorem getLimbN_mloadLoadedWord_0 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 0 = l0 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

theorem getLimbN_mloadLoadedWord_1 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 1 = l1 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

theorem getLimbN_mloadLoadedWord_2 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 2 = l2 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

theorem getLimbN_mloadLoadedWord_3 (l0 l1 l2 l3 : Word) :
    (mloadLoadedWord l0 l1 l2 l3).getLimbN 3 = l3 := by
  simp [mloadLoadedWord, EvmWord.getLimbN, EvmWord.getLimb_fromLimbs]

/-- Fold the four MLOAD destination limbs into a single `evmWordIs` assertion. -/
theorem mloadLoadedWord_evmWordIs_fold (sp l0 l1 l2 l3 : Word) :
    ((sp ↦ₘ l0) ** ((sp + 8) ↦ₘ l1) **
     ((sp + 16) ↦ₘ l2) ** ((sp + 24) ↦ₘ l3)) =
    evmWordIs sp (mloadLoadedWord l0 l1 l2 l3) := by
  rw [evmWordIs_sp_unfold]
  rw [getLimbN_mloadLoadedWord_0, getLimbN_mloadLoadedWord_1,
    getLimbN_mloadLoadedWord_2, getLimbN_mloadLoadedWord_3]

/-- Pack eight consecutive MLOAD bytes into one 64-bit big-endian limb. -/
def mloadPackedLimb
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : Word :=
  b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7

/-- Runtime shift/or byte packing computes the same big-endian limb. -/
theorem mloadPackedLimb_eq_fold
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((((((((b0.zeroExtend 64
        <<< (8 : Nat)) ||| b1.zeroExtend 64)
        <<< (8 : Nat)) ||| b2.zeroExtend 64)
        <<< (8 : Nat)) ||| b3.zeroExtend 64)
        <<< (8 : Nat)) ||| b4.zeroExtend 64)
        <<< (8 : Nat)) ||| b5.zeroExtend 64)
        <<< (8 : Nat)) ||| b6.zeroExtend 64)
        <<< (8 : Nat)) ||| b7.zeroExtend 64)
      = mloadPackedLimb b0 b1 b2 b3 b4 b5 b6 b7 := by
  unfold mloadPackedLimb
  bv_decide

/--
  Select the `i`th byte of an 8-byte MLOAD limb window from two adjacent
  source dwords.  `start` is the byte offset of the first byte within `lo`.
  When `start + i ≥ 8`, the byte comes from `hi` at wrapped position
  `(start + i) % 8`.
-/
def mloadByteFromDwordPair (lo hi : Word) (start i : Nat) : BitVec 8 :=
  let pos := start + i
  extractByte (if pos < 8 then lo else hi) (pos % 8)

theorem mloadByteFromDwordPair_low
    (lo hi : Word) {start i : Nat} (h_pos : start + i < 8) :
    mloadByteFromDwordPair lo hi start i = extractByte lo ((start + i) % 8) := by
  simp [mloadByteFromDwordPair, h_pos]

theorem mloadByteFromDwordPair_high
    (lo hi : Word) {start i : Nat} (h_pos : 8 ≤ start + i) :
    mloadByteFromDwordPair lo hi start i = extractByte hi ((start + i) % 8) := by
  simp [mloadByteFromDwordPair, show ¬ start + i < 8 from by omega]

/--
  Pack eight consecutive bytes starting at byte offset `start` in `lo`,
  crossing into adjacent dword `hi` when needed.
-/
def mloadPackedLimbFromDwordPair (lo hi : Word) (start : Nat) : Word :=
  mloadPackedLimb
    (mloadByteFromDwordPair lo hi start 0)
    (mloadByteFromDwordPair lo hi start 1)
    (mloadByteFromDwordPair lo hi start 2)
    (mloadByteFromDwordPair lo hi start 3)
    (mloadByteFromDwordPair lo hi start 4)
    (mloadByteFromDwordPair lo hi start 5)
    (mloadByteFromDwordPair lo hi start 6)
    (mloadByteFromDwordPair lo hi start 7)

/--
  Runtime shift/or byte packing for an unaligned 8-byte window computes the
  same big-endian limb as `mloadPackedLimbFromDwordPair`.
-/
theorem mloadPackedLimbFromDwordPair_eq_fold
    (lo hi : Word) (start : Nat) :
    let b0 := mloadByteFromDwordPair lo hi start 0
    let b1 := mloadByteFromDwordPair lo hi start 1
    let b2 := mloadByteFromDwordPair lo hi start 2
    let b3 := mloadByteFromDwordPair lo hi start 3
    let b4 := mloadByteFromDwordPair lo hi start 4
    let b5 := mloadByteFromDwordPair lo hi start 5
    let b6 := mloadByteFromDwordPair lo hi start 6
    let b7 := mloadByteFromDwordPair lo hi start 7
    ((((((((((((((b0.zeroExtend 64
        <<< (8 : Nat)) ||| b1.zeroExtend 64)
        <<< (8 : Nat)) ||| b2.zeroExtend 64)
        <<< (8 : Nat)) ||| b3.zeroExtend 64)
        <<< (8 : Nat)) ||| b4.zeroExtend 64)
        <<< (8 : Nat)) ||| b5.zeroExtend 64)
        <<< (8 : Nat)) ||| b6.zeroExtend 64)
        <<< (8 : Nat)) ||| b7.zeroExtend 64)
      = mloadPackedLimbFromDwordPair lo hi start := by
  dsimp only []
  exact mloadPackedLimb_eq_fold
    (mloadByteFromDwordPair lo hi start 0)
    (mloadByteFromDwordPair lo hi start 1)
    (mloadByteFromDwordPair lo hi start 2)
    (mloadByteFromDwordPair lo hi start 3)
    (mloadByteFromDwordPair lo hi start 4)
    (mloadByteFromDwordPair lo hi start 5)
    (mloadByteFromDwordPair lo hi start 6)
    (mloadByteFromDwordPair lo hi start 7)

/--
  Precondition shape for an unaligned one-limb MLOAD proof: the 8-byte
  source window may read from the low dword, the high dword, or both.
-/
@[irreducible]
def mloadOneLimbUnalignedPre
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr sp dstWordOld : Word)
    (dstOff : BitVec 12) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 dstOff) ↦ₘ dstWordOld)

theorem mloadOneLimbUnalignedPre_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr accOld byteOld loVal hiVal loAddr hiAddr sp dstWordOld : Word}
    {dstOff : BitVec 12} :
    mloadOneLimbUnalignedPre addrReg byteReg accReg
        addrPtr accOld byteOld loVal hiVal loAddr hiAddr sp dstWordOld dstOff =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 dstOff) ↦ₘ dstWordOld)) := by
  delta mloadOneLimbUnalignedPre; rfl

/--
  Postcondition shape for an unaligned one-limb MLOAD proof, after folding
  the runtime shift/or accumulator into `mloadPackedLimbFromDwordPair`.
-/
@[irreducible]
def mloadOneLimbUnalignedPost
    (addrReg byteReg accReg : Reg)
    (addrPtr loVal hiVal loAddr hiAddr sp : Word)
    (start : Nat) (dstOff : BitVec 12) : Assertion :=
  let lastByte := (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64
  let accFinal := mloadPackedLimbFromDwordPair loVal hiVal start
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ lastByte) ** (accReg ↦ᵣ accFinal) **
  (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 dstOff) ↦ₘ accFinal)

theorem mloadOneLimbUnalignedPost_unfold
    {addrReg byteReg accReg : Reg}
    {addrPtr loVal hiVal loAddr hiAddr sp : Word}
    {start : Nat} {dstOff : BitVec 12} :
    mloadOneLimbUnalignedPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp start dstOff =
    (let lastByte := (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64
     let accFinal := mloadPackedLimbFromDwordPair loVal hiVal start
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ lastByte) ** (accReg ↦ᵣ accFinal) **
     (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 dstOff) ↦ₘ accFinal)) := by
  delta mloadOneLimbUnalignedPost; rfl

/--
  The 256-bit value loaded by MLOAD from 32 consecutive EVM-memory bytes.

  `b00` is the most-significant byte at the requested offset and `b31` is
  the least-significant byte.  The resulting `EvmWord` uses little-endian
  64-bit limbs, so bytes 24..31 form limb 0 and bytes 0..7 form limb 3.
-/
def mloadLoadedWordFromBytes
    (b00 b01 b02 b03 b04 b05 b06 b07 : BitVec 8)
    (b08 b09 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (b16 b17 b18 b19 b20 b21 b22 b23 : BitVec 8)
    (b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) : EvmWord :=
  mloadLoadedWord
    (mloadPackedLimb b24 b25 b26 b27 b28 b29 b30 b31)
    (mloadPackedLimb b16 b17 b18 b19 b20 b21 b22 b23)
    (mloadPackedLimb b08 b09 b10 b11 b12 b13 b14 b15)
    (mloadPackedLimb b00 b01 b02 b03 b04 b05 b06 b07)

theorem getLimbN_mloadLoadedWordFromBytes_0
    (b00 b01 b02 b03 b04 b05 b06 b07 : BitVec 8)
    (b08 b09 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (b16 b17 b18 b19 b20 b21 b22 b23 : BitVec 8)
    (b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    (mloadLoadedWordFromBytes
      b00 b01 b02 b03 b04 b05 b06 b07
      b08 b09 b10 b11 b12 b13 b14 b15
      b16 b17 b18 b19 b20 b21 b22 b23
      b24 b25 b26 b27 b28 b29 b30 b31).getLimbN 0 =
    mloadPackedLimb b24 b25 b26 b27 b28 b29 b30 b31 := by
  simp [mloadLoadedWordFromBytes, getLimbN_mloadLoadedWord_0]

theorem getLimbN_mloadLoadedWordFromBytes_1
    (b00 b01 b02 b03 b04 b05 b06 b07 : BitVec 8)
    (b08 b09 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (b16 b17 b18 b19 b20 b21 b22 b23 : BitVec 8)
    (b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    (mloadLoadedWordFromBytes
      b00 b01 b02 b03 b04 b05 b06 b07
      b08 b09 b10 b11 b12 b13 b14 b15
      b16 b17 b18 b19 b20 b21 b22 b23
      b24 b25 b26 b27 b28 b29 b30 b31).getLimbN 1 =
    mloadPackedLimb b16 b17 b18 b19 b20 b21 b22 b23 := by
  simp [mloadLoadedWordFromBytes, getLimbN_mloadLoadedWord_1]

theorem getLimbN_mloadLoadedWordFromBytes_2
    (b00 b01 b02 b03 b04 b05 b06 b07 : BitVec 8)
    (b08 b09 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (b16 b17 b18 b19 b20 b21 b22 b23 : BitVec 8)
    (b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    (mloadLoadedWordFromBytes
      b00 b01 b02 b03 b04 b05 b06 b07
      b08 b09 b10 b11 b12 b13 b14 b15
      b16 b17 b18 b19 b20 b21 b22 b23
      b24 b25 b26 b27 b28 b29 b30 b31).getLimbN 2 =
    mloadPackedLimb b08 b09 b10 b11 b12 b13 b14 b15 := by
  simp [mloadLoadedWordFromBytes, getLimbN_mloadLoadedWord_2]

theorem getLimbN_mloadLoadedWordFromBytes_3
    (b00 b01 b02 b03 b04 b05 b06 b07 : BitVec 8)
    (b08 b09 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (b16 b17 b18 b19 b20 b21 b22 b23 : BitVec 8)
    (b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    (mloadLoadedWordFromBytes
      b00 b01 b02 b03 b04 b05 b06 b07
      b08 b09 b10 b11 b12 b13 b14 b15
      b16 b17 b18 b19 b20 b21 b22 b23
      b24 b25 b26 b27 b28 b29 b30 b31).getLimbN 3 =
    mloadPackedLimb b00 b01 b02 b03 b04 b05 b06 b07 := by
  simp [mloadLoadedWordFromBytes, getLimbN_mloadLoadedWord_3]

/-- Fold the four byte-packed MLOAD limbs directly into the loaded-word assertion. -/
theorem mloadLoadedWordFromBytes_evmWordIs_fold
    (sp : Word)
    (b00 b01 b02 b03 b04 b05 b06 b07 : BitVec 8)
    (b08 b09 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (b16 b17 b18 b19 b20 b21 b22 b23 : BitVec 8)
    (b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    ((sp ↦ₘ mloadPackedLimb b24 b25 b26 b27 b28 b29 b30 b31) **
     ((sp + 8) ↦ₘ mloadPackedLimb b16 b17 b18 b19 b20 b21 b22 b23) **
     ((sp + 16) ↦ₘ mloadPackedLimb b08 b09 b10 b11 b12 b13 b14 b15) **
     ((sp + 24) ↦ₘ mloadPackedLimb b00 b01 b02 b03 b04 b05 b06 b07)) =
    evmWordIs sp
      (mloadLoadedWordFromBytes
        b00 b01 b02 b03 b04 b05 b06 b07
        b08 b09 b10 b11 b12 b13 b14 b15
        b16 b17 b18 b19 b20 b21 b22 b23
        b24 b25 b26 b27 b28 b29 b30 b31) := by
  rw [mloadLoadedWordFromBytes, mloadLoadedWord_evmWordIs_fold]

end EvmAsm.Evm64
