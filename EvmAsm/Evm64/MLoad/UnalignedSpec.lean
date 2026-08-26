/-
  EvmAsm.Evm64.MLoad.UnalignedSpec

  Unaligned MLOAD byte-window helpers and the one-limb unaligned MLOAD
  composition spec. Split out of `MLoad.Spec` (issue #1885 / beads
  evm-asm-qgjp) to keep individual files under the 1500-line file-size
  guardrail.

  Contents:
    * `mloadPackedLimbFromDwordPair` — pure byte-pack helper for the eight
      consecutive bytes of an unaligned 64-bit MLOAD limb.
    * Concrete byte-split equations for each `start ∈ 0..7`.
    * `mloadOneLimbUnalignedPre` / `mloadOneLimbUnalignedPost` — assertion
      shapes used by the one-limb unaligned composition.
    * `mload_one_limb_unaligned_spec_within` — eight byte-pack loads plus
      the trailing store, packaged as a single `cpsTriple`.
    * `mloadLoadedWordFromBytes` and the byte-window stack-fold bridges.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Evm64.MLoad.Spec

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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

theorem mloadByteFromDwordPair_start_zero
    (lo hi : Word) {i : Nat} (h_i : i < 8) :
    mloadByteFromDwordPair lo hi 0 i = extractByte lo i := by
  rw [mloadByteFromDwordPair_low lo hi (by simpa using h_i)]
  rw [show (0 + i) % 8 = i from by simpa using Nat.mod_eq_of_lt h_i]

theorem mloadPackedLimbFromDwordPair_start_zero (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 0 =
      mloadPackedLimb
        (extractByte lo 0) (extractByte lo 1) (extractByte lo 2) (extractByte lo 3)
        (extractByte lo 4) (extractByte lo 5) (extractByte lo 6) (extractByte lo 7) := by
  unfold mloadPackedLimbFromDwordPair
  simp [mloadByteFromDwordPair]

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

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 0. -/
theorem mloadPackedLimbFromDwordPair_start0 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 0 =
      mloadPackedLimb
        (extractByte lo 0) (extractByte lo 1) (extractByte lo 2) (extractByte lo 3)
        (extractByte lo 4) (extractByte lo 5) (extractByte lo 6) (extractByte lo 7) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 1. -/
theorem mloadPackedLimbFromDwordPair_start1 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 1 =
      mloadPackedLimb
        (extractByte lo 1) (extractByte lo 2) (extractByte lo 3) (extractByte lo 4)
        (extractByte lo 5) (extractByte lo 6) (extractByte lo 7) (extractByte hi 0) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 2. -/
theorem mloadPackedLimbFromDwordPair_start2 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 2 =
      mloadPackedLimb
        (extractByte lo 2) (extractByte lo 3) (extractByte lo 4) (extractByte lo 5)
        (extractByte lo 6) (extractByte lo 7) (extractByte hi 0) (extractByte hi 1) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 3. -/
theorem mloadPackedLimbFromDwordPair_start3 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 3 =
      mloadPackedLimb
        (extractByte lo 3) (extractByte lo 4) (extractByte lo 5) (extractByte lo 6)
        (extractByte lo 7) (extractByte hi 0) (extractByte hi 1) (extractByte hi 2) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 4. -/
theorem mloadPackedLimbFromDwordPair_start4 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 4 =
      mloadPackedLimb
        (extractByte lo 4) (extractByte lo 5) (extractByte lo 6) (extractByte lo 7)
        (extractByte hi 0) (extractByte hi 1) (extractByte hi 2) (extractByte hi 3) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 5. -/
theorem mloadPackedLimbFromDwordPair_start5 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 5 =
      mloadPackedLimb
        (extractByte lo 5) (extractByte lo 6) (extractByte lo 7) (extractByte hi 0)
        (extractByte hi 1) (extractByte hi 2) (extractByte hi 3) (extractByte hi 4) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 6. -/
theorem mloadPackedLimbFromDwordPair_start6 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 6 =
      mloadPackedLimb
        (extractByte lo 6) (extractByte lo 7) (extractByte hi 0) (extractByte hi 1)
        (extractByte hi 2) (extractByte hi 3) (extractByte hi 4) (extractByte hi 5) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

/-- Concrete byte split for an 8-byte MLOAD window starting at dword byte 7. -/
theorem mloadPackedLimbFromDwordPair_start7 (lo hi : Word) :
    mloadPackedLimbFromDwordPair lo hi 7 =
      mloadPackedLimb
        (extractByte lo 7) (extractByte hi 0) (extractByte hi 1) (extractByte hi 2)
        (extractByte hi 3) (extractByte hi 4) (extractByte hi 5) (extractByte hi 6) := by
  simp [mloadPackedLimbFromDwordPair, mloadByteFromDwordPair]

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

/-- Full one-limb unaligned MLOAD composition: eight byte-pack loads plus trailing store. -/
theorem mload_one_limb_unaligned_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr sp dstWordOld : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12)
    (start : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_window : mloadLimbWindowOk addrPtr loAddr hiAddr start
      off0 off1 off2 off3 off4 off5 off6 off7) :
    cpsTripleWithin 23 base (base + 92)
      (mloadOneLimbCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff base)
      (mloadOneLimbUnalignedPre addrReg byteReg accReg
        addrPtr accOld byteOld loVal hiVal loAddr hiAddr sp dstWordOld dstOff)
      (mloadOneLimbUnalignedPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp start dstOff) := by
  rw [mloadOneLimbUnalignedPre_unfold, mloadOneLimbUnalignedPost_unfold]
  dsimp only []
  set b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
  set b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
  set b2 := (mloadByteFromDwordPair loVal hiVal start 2).zeroExtend 64
  set b3 := (mloadByteFromDwordPair loVal hiVal start 3).zeroExtend 64
  set b4 := (mloadByteFromDwordPair loVal hiVal start 4).zeroExtend 64
  set b5 := (mloadByteFromDwordPair loVal hiVal start 5).zeroExtend 64
  set b6 := (mloadByteFromDwordPair loVal hiVal start 6).zeroExtend 64
  set b7 := (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64
  unfold mloadOneLimbCode
  rw [show (23 : Nat) = 22 + 1 from rfl,
      show (base + 92 : Word) = base + 88 + 4 from by bv_omega]
  have eight := mload_byte_pack_eight_pair_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal hiVal loAddr hiAddr
    off0 off1 off2 off3 off4 off5 off6 off7 start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have eightPacked : cpsTripleWithin 22 base (base + 88)
      (mloadBytePackEightCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 base)
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) **
       (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal hiVal start) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        rw [← mloadPackedLimbFromDwordPair_eq_fold loVal hiVal start]
        exact hp)
      eight
  have sd := generic_sd_spec_within (.x12 : Reg) accReg sp
    (mloadPackedLimbFromDwordPair loVal hiVal start) dstWordOld dstOff (base + 88)
  have eightF := cpsTripleWithin_frameR
    (F := ((.x12 : Reg) ↦ᵣ sp) ** ((sp + signExtend12 dstOff) ↦ₘ dstWordOld))
    (by pcFree) eightPacked
  have sdF := cpsTripleWithin_frameL
    (F := (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) **
      (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
    (by pcFree) sd
  have hMid :
      (((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) **
        (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) **
        (((.x12 : Reg) ↦ᵣ sp) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal hiVal start) **
         ((sp + signExtend12 dstOff) ↦ₘ dstWordOld))) =
      (((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) **
        (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal hiVal start) **
        (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) **
        (((.x12 : Reg) ↦ᵣ sp) **
         ((sp + signExtend12 dstOff) ↦ₘ dstWordOld))) := by ac_rfl
  have hd_step : CodeReq.Disjoint
      (mloadBytePackEightCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 base)
      (CodeReq.singleton (base + 88) (.SD (.x12 : Reg) accReg dstOff)) := by
    unfold mloadBytePackEightCode mloadBytePackSevenCode mloadBytePackSixCode
      mloadBytePackFiveCode mloadBytePackFourCode mloadBytePackThreeCode
      mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 88 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            (CodeReq.singleton (base + 88) (.SD (.x12 : Reg) accReg dstOff)) := by
      intro a i h88
      exact CodeReq.Disjoint.singleton h88
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_left ?_ ?_
        · refine CodeReq.Disjoint.union_left ?_ ?_
          · refine CodeReq.Disjoint.union_left ?_ ?_
            · refine CodeReq.Disjoint.union_left ?_ ?_
              · refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
                refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
                refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
                exact leaf (by bv_omega)
              · refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
                refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
                exact leaf (by bv_omega)
            · refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
              exact leaf (by bv_omega)
          · refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
            refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
            exact leaf (by bv_omega)
        · refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
          exact leaf (by bv_omega)
      · refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
        exact leaf (by bv_omega)
    · refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_left (leaf (by bv_omega)) ?_
      exact leaf (by bv_omega)
  have composed := cpsTripleWithin_seq hd_step (hMid ▸ eightF) sdF
  exact cpsTripleWithin_weaken
    (fun h hp => by sep_perm hp)
    (fun h hp => by sep_perm hp)
    composed

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

/-- Fold the byte-window MLOAD result and existing stack tail into one stack assertion. -/
theorem mloadLoadedWordFromBytes_evmStackIs_fold
    (sp : Word) (rest : List EvmWord)
    (b00 b01 b02 b03 b04 b05 b06 b07 : BitVec 8)
    (b08 b09 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (b16 b17 b18 b19 b20 b21 b22 b23 : BitVec 8)
    (b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    (((sp ↦ₘ mloadPackedLimb b24 b25 b26 b27 b28 b29 b30 b31) **
      ((sp + 8) ↦ₘ mloadPackedLimb b16 b17 b18 b19 b20 b21 b22 b23) **
      ((sp + 16) ↦ₘ mloadPackedLimb b08 b09 b10 b11 b12 b13 b14 b15) **
      ((sp + 24) ↦ₘ mloadPackedLimb b00 b01 b02 b03 b04 b05 b06 b07)) **
      evmStackIs (sp + 32) rest) =
    evmStackIs sp
      ((mloadLoadedWordFromBytes
        b00 b01 b02 b03 b04 b05 b06 b07
        b08 b09 b10 b11 b12 b13 b14 b15
        b16 b17 b18 b19 b20 b21 b22 b23
        b24 b25 b26 b27 b28 b29 b30 b31) :: rest) := by
  rw [mloadLoadedWordFromBytes_evmWordIs_fold]
  rfl

end EvmAsm.Evm64
