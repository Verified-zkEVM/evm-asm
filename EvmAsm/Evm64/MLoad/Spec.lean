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

/-- Select the source dword address for byte `i` in an unaligned limb window. -/
def mloadDwordPairAddr (loAddr hiAddr : Word) (start i : Nat) : Word :=
  if start + i < 8 then loAddr else hiAddr

theorem mloadDwordPairAddr_low
    (loAddr hiAddr : Word) {start i : Nat} (h_pos : start + i < 8) :
    mloadDwordPairAddr loAddr hiAddr start i = loAddr := by
  simp [mloadDwordPairAddr, h_pos]

theorem mloadDwordPairAddr_high
    (loAddr hiAddr : Word) {start i : Nat} (h_pos : 8 ≤ start + i) :
    mloadDwordPairAddr loAddr hiAddr start i = hiAddr := by
  simp [mloadDwordPairAddr, show ¬ start + i < 8 from by omega]

/-- Select the source dword value for byte `i` in an unaligned limb window. -/
def mloadDwordPairVal (loVal hiVal : Word) (start i : Nat) : Word :=
  if start + i < 8 then loVal else hiVal

theorem mloadDwordPairVal_low
    (loVal hiVal : Word) {start i : Nat} (h_pos : start + i < 8) :
    mloadDwordPairVal loVal hiVal start i = loVal := by
  simp [mloadDwordPairVal, h_pos]

theorem mloadDwordPairVal_high
    (loVal hiVal : Word) {start i : Nat} (h_pos : 8 ≤ start + i) :
    mloadDwordPairVal loVal hiVal start i = hiVal := by
  simp [mloadDwordPairVal, show ¬ start + i < 8 from by omega]

theorem mloadByteFromDwordPair_eq_extractByte_pair
    (loVal hiVal : Word) (start i : Nat) :
    mloadByteFromDwordPair loVal hiVal start i =
      extractByte (mloadDwordPairVal loVal hiVal start i) ((start + i) % 8) := by
  simp [mloadByteFromDwordPair, mloadDwordPairVal]

theorem mloadByteFromDwordPair_zeroExtend_eq
    (loVal hiVal : Word) (start i : Nat) :
    (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64 =
      (extractByte (mloadDwordPairVal loVal hiVal start i)
        ((start + i) % 8)).zeroExtend 64 := by
  rw [mloadByteFromDwordPair_eq_extractByte_pair]

theorem mloadByteFromDwordPair_eq_extractByte_low_of_byteOffset
    (loVal hiVal addr : Word) {start i : Nat}
    (h_pos : start + i < 8)
    (h_byte : byteOffset addr = (start + i) % 8) :
    mloadByteFromDwordPair loVal hiVal start i =
      extractByte loVal (byteOffset addr) := by
  rw [mloadByteFromDwordPair_low loVal hiVal h_pos, h_byte]

theorem mloadByteFromDwordPair_eq_extractByte_high_of_byteOffset
    (loVal hiVal addr : Word) {start i : Nat}
    (h_pos : 8 ≤ start + i)
    (h_byte : byteOffset addr = (start + i) % 8) :
    mloadByteFromDwordPair loVal hiVal start i =
      extractByte hiVal (byteOffset addr) := by
  rw [mloadByteFromDwordPair_high loVal hiVal h_pos, h_byte]

theorem mloadByteFromDwordPair_zeroExtend_eq_extractByte_low_of_byteOffset
    (loVal hiVal addr : Word) {start i : Nat}
    (h_pos : start + i < 8)
    (h_byte : byteOffset addr = (start + i) % 8) :
    (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64 =
      (extractByte loVal (byteOffset addr)).zeroExtend 64 := by
  rw [mloadByteFromDwordPair_eq_extractByte_low_of_byteOffset
    loVal hiVal addr h_pos h_byte]

theorem mloadByteFromDwordPair_zeroExtend_eq_extractByte_high_of_byteOffset
    (loVal hiVal addr : Word) {start i : Nat}
    (h_pos : 8 ≤ start + i)
    (h_byte : byteOffset addr = (start + i) % 8) :
    (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64 =
      (extractByte hiVal (byteOffset addr)).zeroExtend 64 := by
  rw [mloadByteFromDwordPair_eq_extractByte_high_of_byteOffset
    loVal hiVal addr h_pos h_byte]

/-- Initial byte-pack load for an unaligned limb when the byte is in the low dword. -/
theorem mload_byte_pack_init_pair_low_spec_within
    (addrReg accReg : Reg)
    (addrPtr accOld loVal hiVal loAddr hiAddr : Word)
    (offset : BitVec 12) (start i : Nat) (base : Word)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_pos : start + i < 8)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = loAddr)
    (h_byte : byteOffset (addrPtr + signExtend12 offset) = (start + i) % 8)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext := (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU accReg addrReg offset))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ byteZext) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro byteZext
  have init := mload_byte_pack_init_spec_within addrReg accReg
    addrPtr accOld loVal loAddr offset base h_acc_ne_x0 h_align h_valid
  rw [show (extractByte loVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64 =
      byteZext from by
        rw [← mloadByteFromDwordPair_zeroExtend_eq_extractByte_low_of_byteOffset
          loVal hiVal (addrPtr + signExtend12 offset) h_pos h_byte]] at init
  have initF := cpsTripleWithin_frameR
    (F := hiAddr ↦ₘ hiVal) (by pcFree) init
  exact cpsTripleWithin_weaken
    (fun h hp => by sep_perm hp)
    (fun h hp => by sep_perm hp)
    initF

/-- Initial byte-pack load for an unaligned limb when the byte is in the high dword. -/
theorem mload_byte_pack_init_pair_high_spec_within
    (addrReg accReg : Reg)
    (addrPtr accOld loVal hiVal loAddr hiAddr : Word)
    (offset : BitVec 12) (start i : Nat) (base : Word)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_pos : 8 ≤ start + i)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = hiAddr)
    (h_byte : byteOffset (addrPtr + signExtend12 offset) = (start + i) % 8)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext := (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU accReg addrReg offset))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ byteZext) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro byteZext
  have init := mload_byte_pack_init_spec_within addrReg accReg
    addrPtr accOld hiVal hiAddr offset base h_acc_ne_x0 h_align h_valid
  rw [show (extractByte hiVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64 =
      byteZext from by
        rw [← mloadByteFromDwordPair_zeroExtend_eq_extractByte_high_of_byteOffset
          loVal hiVal (addrPtr + signExtend12 offset) h_pos h_byte]] at init
  have initF := cpsTripleWithin_frameL
    (F := loAddr ↦ₘ loVal) (by pcFree) init
  exact cpsTripleWithin_weaken
    (fun h hp => by sep_perm hp)
    (fun h hp => by sep_perm hp)
    initF

/-- Initial byte-pack load for an unaligned limb, selecting low/high dword by byte index. -/
theorem mload_byte_pack_init_pair_spec_within
    (addrReg accReg : Reg)
    (addrPtr accOld loVal hiVal loAddr hiAddr : Word)
    (offset : BitVec 12) (start i : Nat) (base : Word)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align :
      alignToDword (addrPtr + signExtend12 offset) =
        mloadDwordPairAddr loAddr hiAddr start i)
    (h_byte : byteOffset (addrPtr + signExtend12 offset) = (start + i) % 8)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext := (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU accReg addrReg offset))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ byteZext) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  by_cases h_pos : start + i < 8
  · have h_addr := mloadDwordPairAddr_low loAddr hiAddr h_pos
    rw [h_addr] at h_align
    exact mload_byte_pack_init_pair_low_spec_within addrReg accReg
      addrPtr accOld loVal hiVal loAddr hiAddr offset start i base
      h_acc_ne_x0 h_pos h_align h_byte h_valid
  · have h_ge : 8 ≤ start + i := by omega
    have h_addr := mloadDwordPairAddr_high loAddr hiAddr h_ge
    rw [h_addr] at h_align
    exact mload_byte_pack_init_pair_high_spec_within addrReg accReg
      addrPtr accOld loVal hiVal loAddr hiAddr offset start i base
      h_acc_ne_x0 h_ge h_align h_byte h_valid

/-- One byte-pack step for an unaligned limb when the byte is in the low dword. -/
theorem mload_byte_pack_step_pair_low_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (offset : BitVec 12) (start i : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_pos : start + i < 8)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = loAddr)
    (h_byte : byteOffset (addrPtr + signExtend12 offset) = (start + i) % 8)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext := (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64
    let accNew := (accOld <<< (8 : Nat)) ||| byteZext
    let cr :=
      (CodeReq.singleton base (.LBU byteReg addrReg offset)).union
        ((CodeReq.singleton (base + 4) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
         (CodeReq.singleton (base + 8) (.OR accReg accReg byteReg)))
    cpsTripleWithin 3 base (base + 12) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteZext) ** (accReg ↦ᵣ accNew) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro byteZext accNew cr
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal loAddr offset base
    h_byte_ne_x0 h_acc_ne_x0 h_align h_valid
  rw [show (extractByte loVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64 =
      byteZext from by
        rw [← mloadByteFromDwordPair_zeroExtend_eq_extractByte_low_of_byteOffset
          loVal hiVal (addrPtr + signExtend12 offset) h_pos h_byte]] at step
  have stepF := cpsTripleWithin_frameR
    (F := hiAddr ↦ₘ hiVal) (by pcFree) step
  exact cpsTripleWithin_weaken
    (fun h hp => by
      sep_perm hp)
    (fun h hp => by
      dsimp only [accNew] at hp ⊢
      sep_perm hp)
    stepF

/-- One byte-pack step for an unaligned limb when the byte is in the high dword. -/
theorem mload_byte_pack_step_pair_high_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (offset : BitVec 12) (start i : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_pos : 8 ≤ start + i)
    (h_align : alignToDword (addrPtr + signExtend12 offset) = hiAddr)
    (h_byte : byteOffset (addrPtr + signExtend12 offset) = (start + i) % 8)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext := (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64
    let accNew := (accOld <<< (8 : Nat)) ||| byteZext
    let cr :=
      (CodeReq.singleton base (.LBU byteReg addrReg offset)).union
        ((CodeReq.singleton (base + 4) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
         (CodeReq.singleton (base + 8) (.OR accReg accReg byteReg)))
    cpsTripleWithin 3 base (base + 12) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteZext) ** (accReg ↦ᵣ accNew) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro byteZext accNew cr
  have step := mload_byte_pack_step_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld hiVal hiAddr offset base
    h_byte_ne_x0 h_acc_ne_x0 h_align h_valid
  rw [show (extractByte hiVal (byteOffset (addrPtr + signExtend12 offset))).zeroExtend 64 =
      byteZext from by
        rw [← mloadByteFromDwordPair_zeroExtend_eq_extractByte_high_of_byteOffset
          loVal hiVal (addrPtr + signExtend12 offset) h_pos h_byte]] at step
  have stepF := cpsTripleWithin_frameL
    (F := loAddr ↦ₘ loVal) (by pcFree) step
  exact cpsTripleWithin_weaken
    (fun h hp => by
      sep_perm hp)
    (fun h hp => by
      dsimp only [accNew] at hp ⊢
      sep_perm hp)
    stepF

/-- One byte-pack step for an unaligned limb, selecting low/high dword by byte index. -/
theorem mload_byte_pack_step_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (offset : BitVec 12) (start i : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align :
      alignToDword (addrPtr + signExtend12 offset) =
        mloadDwordPairAddr loAddr hiAddr start i)
    (h_byte : byteOffset (addrPtr + signExtend12 offset) = (start + i) % 8)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 offset) = true) :
    let byteZext := (mloadByteFromDwordPair loVal hiVal start i).zeroExtend 64
    let accNew := (accOld <<< (8 : Nat)) ||| byteZext
    let cr :=
      (CodeReq.singleton base (.LBU byteReg addrReg offset)).union
        ((CodeReq.singleton (base + 4) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
         (CodeReq.singleton (base + 8) (.OR accReg accReg byteReg)))
    cpsTripleWithin 3 base (base + 12) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteZext) ** (accReg ↦ᵣ accNew) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  by_cases h_pos : start + i < 8
  · have h_addr := mloadDwordPairAddr_low loAddr hiAddr h_pos
    rw [h_addr] at h_align
    exact mload_byte_pack_step_pair_low_spec_within addrReg byteReg accReg
      addrPtr accOld byteOld loVal hiVal loAddr hiAddr offset start i base
      h_byte_ne_x0 h_acc_ne_x0 h_pos h_align h_byte h_valid
  · have h_ge : 8 ≤ start + i := by omega
    have h_addr := mloadDwordPairAddr_high loAddr hiAddr h_ge
    rw [h_addr] at h_align
    exact mload_byte_pack_step_pair_high_spec_within addrReg byteReg accReg
      addrPtr accOld byteOld loVal hiVal loAddr hiAddr offset start i base
      h_byte_ne_x0 h_acc_ne_x0 h_ge h_align h_byte h_valid

/--
  Two-byte big-endian byte-pack composition for an unaligned source window.
  This is the first composition rung over the low/high dword pair wrappers:
  the seed `LBU` loads byte 0 into `accReg`, then one pair step folds byte 1
  into `(b0 <<< 8) ||| b1`.
-/
theorem mload_byte_pack_two_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (off0 off1 : BitVec 12) (start : Nat) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0  : accReg  ≠ .x0)
    (h_align0 :
      alignToDword (addrPtr + signExtend12 off0) =
        mloadDwordPairAddr loAddr hiAddr start 0)
    (h_byte0 : byteOffset (addrPtr + signExtend12 off0) = (start + 0) % 8)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_align1 :
      alignToDword (addrPtr + signExtend12 off1) =
        mloadDwordPairAddr loAddr hiAddr start 1)
    (h_byte1 : byteOffset (addrPtr + signExtend12 off1) = (start + 1) % 8)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true) :
    let b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
    let b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
    let accFinal := (b0 <<< (8 : Nat)) ||| b1
    let cr := mloadBytePackTwoCode addrReg byteReg accReg off0 off1 base
    cpsTripleWithin 4 base (base + 16) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b1) ** (accReg ↦ᵣ accFinal) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro b0 b1 accFinal cr
  have init := mload_byte_pack_init_pair_spec_within addrReg accReg
    addrPtr accOld loVal hiVal loAddr hiAddr off0 start 0 base
    h_acc_ne_x0 h_align0 h_byte0 h_valid0
  have initF := cpsTripleWithin_frameR (F := byteReg ↦ᵣ byteOld)
    (by pcFree) init
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU accReg addrReg off0))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ b0) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      initF
  have step := mload_byte_pack_step_pair_spec_within addrReg byteReg accReg
    addrPtr b0 byteOld loVal hiVal loAddr hiAddr off1 start 1 (base + 4)
    h_byte_ne_x0 h_acc_ne_x0 h_align1 h_byte1 h_valid1
  rw [show (base + 4 : Word) + 12 = base + 16 from by bv_omega] at step
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega,
      show (base + 4 : Word) + 8 = base + 12 from by bv_omega] at step
  have h01 : base ≠ base + 4 := by bv_omega
  have h02 : base ≠ base + 8 := by bv_omega
  have h03 : base ≠ base + 12 := by bv_omega
  have hd_step : CodeReq.Disjoint
      (CodeReq.singleton base (.LBU accReg addrReg off0))
      ((CodeReq.singleton (base + 4) (.LBU byteReg addrReg off1)).union
       ((CodeReq.singleton (base + 8) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 12) (.OR accReg accReg byteReg)))) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton h01)
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h02)
        (CodeReq.Disjoint.singleton h03))
  exact cpsTripleWithin_seq hd_step s1 step

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
