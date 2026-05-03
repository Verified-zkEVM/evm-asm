/-
  EvmAsm.Evm64.MLoad.Spec

  Stack-level bridge lemmas for the MLOAD result word.  The instruction
  composition proves four packed 64-bit output limbs; this file packages
  those limbs as a single `EvmWord` and folds the four destination cells into
  `evmWordIs`.

  Authored by @pirapira; implemented by Codex.
-/
-- file-size-exception: temporary bridge-file overage; split tracked by evm-asm-qgjp.

import EvmAsm.Evm64.MLoad.LimbSpecEight

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the two-instruction MLOAD address prologue. -/
def mloadPrologueCode
    (offReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD offReg .x12 0)).union
    (CodeReq.singleton (base + 4) (.ADD addrReg memBaseReg offReg))

theorem mloadPrologueCode_eq_ofProg
    (offReg addrReg memBaseReg : Reg) (base : Word) :
    mloadPrologueCode offReg addrReg memBaseReg base =
      CodeReq.ofProg base
        (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg) := by
  unfold mloadPrologueCode LD ADD single seq
  change _ =
    CodeReq.ofProg base
      [.LD offReg .x12 0, .ADD addrReg memBaseReg offReg]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_singleton]

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

theorem mload_prologue_ofProg_spec_within
    (offReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base
        (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  rw [← mloadPrologueCode_eq_ofProg]
  exact mload_prologue_spec_within offReg addrReg memBaseReg
    sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0

theorem evm_mload_code_prologue_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (CodeReq.ofProg base (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg)) a =
        some i →
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) a =
        some i := by
  unfold evm_mload_code
  exact CodeReq.ofProg_mono_sub base base
    (evm_mload offReg byteReg accReg addrReg memBaseReg)
    (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg) 0
    (by bv_omega)
    (evm_mload_prologue_slice offReg byteReg accReg addrReg memBaseReg)
    (by
      rw [evm_mload_length]
      change 2 ≤ 94
      norm_num)
    (by
      rw [evm_mload_length]
      norm_num)

theorem mload_prologue_evm_mload_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  exact cpsTripleWithin_extend_code
    (h := mload_prologue_ofProg_spec_within offReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0)
    (hmono := evm_mload_code_prologue_sub
      offReg byteReg accReg addrReg memBaseReg base)

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
  Three-byte big-endian byte-pack composition for an unaligned source window,
  extending `mload_byte_pack_two_pair_spec_within` with one more pair step.
-/
theorem mload_byte_pack_three_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (off0 off1 off2 : BitVec 12) (start : Nat) (base : Word)
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
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        mloadDwordPairAddr loAddr hiAddr start 2)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true) :
    let b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
    let b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
    let b2 := (mloadByteFromDwordPair loVal hiVal start 2).zeroExtend 64
    let accAfter2 := (b0 <<< (8 : Nat)) ||| b1
    let accFinal := (accAfter2 <<< (8 : Nat)) ||| b2
    let cr := mloadBytePackThreeCode addrReg byteReg accReg off0 off1 off2 base
    cpsTripleWithin 7 base (base + 28) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b2) ** (accReg ↦ᵣ accFinal) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro b0 b1 b2 accAfter2 accFinal cr
  have two := mload_byte_pack_two_pair_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal hiVal loAddr hiAddr off0 off1 start base
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_byte0 h_valid0 h_align1 h_byte1 h_valid1
  have step := mload_byte_pack_step_pair_spec_within addrReg byteReg accReg
    addrPtr accAfter2 b1 loVal hiVal loAddr hiAddr off2 start 2 (base + 16)
    h_byte_ne_x0 h_acc_ne_x0 h_align2 h_byte2 h_valid2
  rw [show (base + 16 : Word) + 12 = base + 28 from by bv_omega] at step
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega,
      show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at step
  have h_b_b16  : base ≠ base + 16 := by bv_omega
  have h_b_b20  : base ≠ base + 20 := by bv_omega
  have h_b_b24  : base ≠ base + 24 := by bv_omega
  have h_b4_b16 : base + 4 ≠ base + 16 := by bv_omega
  have h_b4_b20 : base + 4 ≠ base + 20 := by bv_omega
  have h_b4_b24 : base + 4 ≠ base + 24 := by bv_omega
  have h_b8_b16 : base + 8 ≠ base + 16 := by bv_omega
  have h_b8_b20 : base + 8 ≠ base + 20 := by bv_omega
  have h_b8_b24 : base + 8 ≠ base + 24 := by bv_omega
  have h_b12_b16 : base + 12 ≠ base + 16 := by bv_omega
  have h_b12_b20 : base + 12 ≠ base + 20 := by bv_omega
  have h_b12_b24 : base + 12 ≠ base + 24 := by bv_omega
  have hd_step : CodeReq.Disjoint
      (mloadBytePackTwoCode addrReg byteReg accReg off0 off1 base)
      ((CodeReq.singleton (base + 16) (.LBU byteReg addrReg off2)).union
       ((CodeReq.singleton (base + 20) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 24) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackTwoCode
    refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_
      (CodeReq.Disjoint.union_left ?_ ?_))
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b_b20)
        (CodeReq.Disjoint.singleton h_b_b24)
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b4_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b4_b20)
        (CodeReq.Disjoint.singleton h_b4_b24)
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b8_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b8_b20)
        (CodeReq.Disjoint.singleton h_b8_b24)
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b12_b16) ?_
      exact CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton h_b12_b20)
        (CodeReq.Disjoint.singleton h_b12_b24)
  exact cpsTripleWithin_seq hd_step two step

/--
  Four-byte big-endian byte-pack composition for an unaligned source window,
  extending `mload_byte_pack_three_pair_spec_within` with one more pair step.
-/
theorem mload_byte_pack_four_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (off0 off1 off2 off3 : BitVec 12) (start : Nat) (base : Word)
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
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        mloadDwordPairAddr loAddr hiAddr start 2)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 off3) =
        mloadDwordPairAddr loAddr hiAddr start 3)
    (h_byte3 : byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true) :
    let b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
    let b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
    let b2 := (mloadByteFromDwordPair loVal hiVal start 2).zeroExtend 64
    let b3 := (mloadByteFromDwordPair loVal hiVal start 3).zeroExtend 64
    let accAfter3 := (((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2
    let accFinal := (accAfter3 <<< (8 : Nat)) ||| b3
    let cr := mloadBytePackFourCode addrReg byteReg accReg off0 off1 off2 off3 base
    cpsTripleWithin 10 base (base + 40) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b3) ** (accReg ↦ᵣ accFinal) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro b0 b1 b2 b3 accAfter3 accFinal cr
  have three := mload_byte_pack_three_pair_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal hiVal loAddr hiAddr off0 off1 off2 start base
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_byte0 h_valid0 h_align1 h_byte1 h_valid1
    h_align2 h_byte2 h_valid2
  have step := mload_byte_pack_step_pair_spec_within addrReg byteReg accReg
    addrPtr accAfter3 b2 loVal hiVal loAddr hiAddr off3 start 3 (base + 28)
    h_byte_ne_x0 h_acc_ne_x0 h_align3 h_byte3 h_valid3
  rw [show (base + 28 : Word) + 12 = base + 40 from by bv_omega] at step
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega,
      show (base + 28 : Word) + 8 = base + 36 from by bv_omega] at step
  have h_b_b28   : base ≠ base + 28 := by bv_omega
  have h_b_b32   : base ≠ base + 32 := by bv_omega
  have h_b_b36   : base ≠ base + 36 := by bv_omega
  have h_b4_b28  : base + 4  ≠ base + 28 := by bv_omega
  have h_b4_b32  : base + 4  ≠ base + 32 := by bv_omega
  have h_b4_b36  : base + 4  ≠ base + 36 := by bv_omega
  have h_b8_b28  : base + 8  ≠ base + 28 := by bv_omega
  have h_b8_b32  : base + 8  ≠ base + 32 := by bv_omega
  have h_b8_b36  : base + 8  ≠ base + 36 := by bv_omega
  have h_b12_b28 : base + 12 ≠ base + 28 := by bv_omega
  have h_b12_b32 : base + 12 ≠ base + 32 := by bv_omega
  have h_b12_b36 : base + 12 ≠ base + 36 := by bv_omega
  have h_b16_b28 : base + 16 ≠ base + 28 := by bv_omega
  have h_b16_b32 : base + 16 ≠ base + 32 := by bv_omega
  have h_b16_b36 : base + 16 ≠ base + 36 := by bv_omega
  have h_b20_b28 : base + 20 ≠ base + 28 := by bv_omega
  have h_b20_b32 : base + 20 ≠ base + 32 := by bv_omega
  have h_b20_b36 : base + 20 ≠ base + 36 := by bv_omega
  have h_b24_b28 : base + 24 ≠ base + 28 := by bv_omega
  have h_b24_b32 : base + 24 ≠ base + 32 := by bv_omega
  have h_b24_b36 : base + 24 ≠ base + 36 := by bv_omega
  have hd_step : CodeReq.Disjoint
      (mloadBytePackThreeCode addrReg byteReg accReg off0 off1 off2 base)
      ((CodeReq.singleton (base + 28) (.LBU byteReg addrReg off3)).union
       ((CodeReq.singleton (base + 32) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 36) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackThreeCode mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 28 → a ≠ base + 32 → a ≠ base + 36 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 28) (.LBU byteReg addrReg off3)).union
             ((CodeReq.singleton (base + 32) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 36) (.OR accReg accReg byteReg)))) := by
      intro a i h28 h32 h36
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h28)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h32)
          (CodeReq.Disjoint.singleton h36))
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_left (leaf h_b_b28 h_b_b32 h_b_b36) ?_
      refine CodeReq.Disjoint.union_left (leaf h_b4_b28 h_b4_b32 h_b4_b36) ?_
      refine CodeReq.Disjoint.union_left (leaf h_b8_b28 h_b8_b32 h_b8_b36) ?_
      exact leaf h_b12_b28 h_b12_b32 h_b12_b36
    · refine CodeReq.Disjoint.union_left (leaf h_b16_b28 h_b16_b32 h_b16_b36) ?_
      refine CodeReq.Disjoint.union_left (leaf h_b20_b28 h_b20_b32 h_b20_b36) ?_
      exact leaf h_b24_b28 h_b24_b32 h_b24_b36
  exact cpsTripleWithin_seq hd_step three step

/-- Five-byte big-endian byte-pack composition for an unaligned source window. -/
theorem mload_byte_pack_five_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (off0 off1 off2 off3 off4 : BitVec 12) (start : Nat) (base : Word)
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
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        mloadDwordPairAddr loAddr hiAddr start 2)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 off3) =
        mloadDwordPairAddr loAddr hiAddr start 3)
    (h_byte3 : byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 off4) =
        mloadDwordPairAddr loAddr hiAddr start 4)
    (h_byte4 : byteOffset (addrPtr + signExtend12 off4) = (start + 4) % 8)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true) :
    let b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
    let b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
    let b2 := (mloadByteFromDwordPair loVal hiVal start 2).zeroExtend 64
    let b3 := (mloadByteFromDwordPair loVal hiVal start 3).zeroExtend 64
    let b4 := (mloadByteFromDwordPair loVal hiVal start 4).zeroExtend 64
    let accAfter4 :=
      ((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3
    let accFinal := (accAfter4 <<< (8 : Nat)) ||| b4
    let cr := mloadBytePackFiveCode addrReg byteReg accReg off0 off1 off2 off3 off4 base
    cpsTripleWithin 13 base (base + 52) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b4) ** (accReg ↦ᵣ accFinal) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro b0 b1 b2 b3 b4 accAfter4 accFinal cr
  have four := mload_byte_pack_four_pair_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal hiVal loAddr hiAddr off0 off1 off2 off3 start base
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_byte0 h_valid0 h_align1 h_byte1 h_valid1
    h_align2 h_byte2 h_valid2 h_align3 h_byte3 h_valid3
  have step := mload_byte_pack_step_pair_spec_within addrReg byteReg accReg
    addrPtr accAfter4 b3 loVal hiVal loAddr hiAddr off4 start 4 (base + 40)
    h_byte_ne_x0 h_acc_ne_x0 h_align4 h_byte4 h_valid4
  rw [show (base + 40 : Word) + 12 = base + 52 from by bv_omega] at step
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega,
      show (base + 40 : Word) + 8 = base + 48 from by bv_omega] at step
  have hd_step : CodeReq.Disjoint
      (mloadBytePackFourCode addrReg byteReg accReg off0 off1 off2 off3 base)
      ((CodeReq.singleton (base + 40) (.LBU byteReg addrReg off4)).union
       ((CodeReq.singleton (base + 44) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 48) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackFourCode mloadBytePackThreeCode mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 40 → a ≠ base + 44 → a ≠ base + 48 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 40) (.LBU byteReg addrReg off4)).union
             ((CodeReq.singleton (base + 44) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 48) (.OR accReg accReg byteReg)))) := by
      intro a i h40 h44 h48
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h40)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h44)
          (CodeReq.Disjoint.singleton h48))
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
      · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
    · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
  exact cpsTripleWithin_seq hd_step four step

/-- Six-byte big-endian byte-pack composition for an unaligned source window. -/
theorem mload_byte_pack_six_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (off0 off1 off2 off3 off4 off5 : BitVec 12) (start : Nat) (base : Word)
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
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        mloadDwordPairAddr loAddr hiAddr start 2)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 off3) =
        mloadDwordPairAddr loAddr hiAddr start 3)
    (h_byte3 : byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 off4) =
        mloadDwordPairAddr loAddr hiAddr start 4)
    (h_byte4 : byteOffset (addrPtr + signExtend12 off4) = (start + 4) % 8)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 off5) =
        mloadDwordPairAddr loAddr hiAddr start 5)
    (h_byte5 : byteOffset (addrPtr + signExtend12 off5) = (start + 5) % 8)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true) :
    let b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
    let b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
    let b2 := (mloadByteFromDwordPair loVal hiVal start 2).zeroExtend 64
    let b3 := (mloadByteFromDwordPair loVal hiVal start 3).zeroExtend 64
    let b4 := (mloadByteFromDwordPair loVal hiVal start 4).zeroExtend 64
    let b5 := (mloadByteFromDwordPair loVal hiVal start 5).zeroExtend 64
    let accAfter5 :=
      (((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4
    let accFinal := (accAfter5 <<< (8 : Nat)) ||| b5
    let cr := mloadBytePackSixCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 base
    cpsTripleWithin 16 base (base + 64) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b5) ** (accReg ↦ᵣ accFinal) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro b0 b1 b2 b3 b4 b5 accAfter5 accFinal cr
  have five := mload_byte_pack_five_pair_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal hiVal loAddr hiAddr
    off0 off1 off2 off3 off4 start base
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_byte0 h_valid0 h_align1 h_byte1 h_valid1
    h_align2 h_byte2 h_valid2 h_align3 h_byte3 h_valid3
    h_align4 h_byte4 h_valid4
  have step := mload_byte_pack_step_pair_spec_within addrReg byteReg accReg
    addrPtr accAfter5 b4 loVal hiVal loAddr hiAddr off5 start 5 (base + 52)
    h_byte_ne_x0 h_acc_ne_x0 h_align5 h_byte5 h_valid5
  rw [show (base + 52 : Word) + 12 = base + 64 from by bv_omega] at step
  rw [show (base + 52 : Word) + 4 = base + 56 from by bv_omega,
      show (base + 52 : Word) + 8 = base + 60 from by bv_omega] at step
  have hd_step : CodeReq.Disjoint
      (mloadBytePackFiveCode addrReg byteReg accReg off0 off1 off2 off3 off4 base)
      ((CodeReq.singleton (base + 52) (.LBU byteReg addrReg off5)).union
       ((CodeReq.singleton (base + 56) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 60) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackFiveCode mloadBytePackFourCode mloadBytePackThreeCode
      mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 52 → a ≠ base + 56 → a ≠ base + 60 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 52) (.LBU byteReg addrReg off5)).union
             ((CodeReq.singleton (base + 56) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 60) (.OR accReg accReg byteReg)))) := by
      intro a i h52 h56 h60
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h52)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h56)
          (CodeReq.Disjoint.singleton h60))
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_left ?_ ?_
        · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
        · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
      · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
    · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
  exact cpsTripleWithin_seq hd_step five step

/-- Seven-byte big-endian byte-pack composition for an unaligned source window. -/
theorem mload_byte_pack_seven_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 : BitVec 12) (start : Nat) (base : Word)
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
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        mloadDwordPairAddr loAddr hiAddr start 2)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 off3) =
        mloadDwordPairAddr loAddr hiAddr start 3)
    (h_byte3 : byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 off4) =
        mloadDwordPairAddr loAddr hiAddr start 4)
    (h_byte4 : byteOffset (addrPtr + signExtend12 off4) = (start + 4) % 8)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 off5) =
        mloadDwordPairAddr loAddr hiAddr start 5)
    (h_byte5 : byteOffset (addrPtr + signExtend12 off5) = (start + 5) % 8)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 off6) =
        mloadDwordPairAddr loAddr hiAddr start 6)
    (h_byte6 : byteOffset (addrPtr + signExtend12 off6) = (start + 6) % 8)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 off6) = true) :
    let b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
    let b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
    let b2 := (mloadByteFromDwordPair loVal hiVal start 2).zeroExtend 64
    let b3 := (mloadByteFromDwordPair loVal hiVal start 3).zeroExtend 64
    let b4 := (mloadByteFromDwordPair loVal hiVal start 4).zeroExtend 64
    let b5 := (mloadByteFromDwordPair loVal hiVal start 5).zeroExtend 64
    let b6 := (mloadByteFromDwordPair loVal hiVal start 6).zeroExtend 64
    let accAfter6 :=
      ((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5
    let accFinal := (accAfter6 <<< (8 : Nat)) ||| b6
    let cr := mloadBytePackSevenCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 base
    cpsTripleWithin 19 base (base + 76) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b6) ** (accReg ↦ᵣ accFinal) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro b0 b1 b2 b3 b4 b5 b6 accAfter6 accFinal cr
  have six := mload_byte_pack_six_pair_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal hiVal loAddr hiAddr
    off0 off1 off2 off3 off4 off5 start base
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_byte0 h_valid0 h_align1 h_byte1 h_valid1
    h_align2 h_byte2 h_valid2 h_align3 h_byte3 h_valid3
    h_align4 h_byte4 h_valid4 h_align5 h_byte5 h_valid5
  have step := mload_byte_pack_step_pair_spec_within addrReg byteReg accReg
    addrPtr accAfter6 b5 loVal hiVal loAddr hiAddr off6 start 6 (base + 64)
    h_byte_ne_x0 h_acc_ne_x0 h_align6 h_byte6 h_valid6
  rw [show (base + 64 : Word) + 12 = base + 76 from by bv_omega] at step
  rw [show (base + 64 : Word) + 4 = base + 68 from by bv_omega,
      show (base + 64 : Word) + 8 = base + 72 from by bv_omega] at step
  have hd_step : CodeReq.Disjoint
      (mloadBytePackSixCode addrReg byteReg accReg off0 off1 off2 off3 off4 off5 base)
      ((CodeReq.singleton (base + 64) (.LBU byteReg addrReg off6)).union
       ((CodeReq.singleton (base + 68) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 72) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackSixCode mloadBytePackFiveCode mloadBytePackFourCode
      mloadBytePackThreeCode mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 64 → a ≠ base + 68 → a ≠ base + 72 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 64) (.LBU byteReg addrReg off6)).union
             ((CodeReq.singleton (base + 68) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 72) (.OR accReg accReg byteReg)))) := by
      intro a i h64 h68 h72
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h64)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h68)
          (CodeReq.Disjoint.singleton h72))
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_left ?_ ?_
        · refine CodeReq.Disjoint.union_left ?_ ?_
          · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
          · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
        · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
      · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
    · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
  exact cpsTripleWithin_seq hd_step six step

/-- Eight-byte big-endian byte-pack composition for an unaligned source window. -/
theorem mload_byte_pack_eight_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accOld byteOld loVal hiVal loAddr hiAddr : Word)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) (start : Nat) (base : Word)
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
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        mloadDwordPairAddr loAddr hiAddr start 2)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 off3) =
        mloadDwordPairAddr loAddr hiAddr start 3)
    (h_byte3 : byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 off4) =
        mloadDwordPairAddr loAddr hiAddr start 4)
    (h_byte4 : byteOffset (addrPtr + signExtend12 off4) = (start + 4) % 8)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 off5) =
        mloadDwordPairAddr loAddr hiAddr start 5)
    (h_byte5 : byteOffset (addrPtr + signExtend12 off5) = (start + 5) % 8)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 off6) =
        mloadDwordPairAddr loAddr hiAddr start 6)
    (h_byte6 : byteOffset (addrPtr + signExtend12 off6) = (start + 6) % 8)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 off6) = true)
    (h_align7 :
      alignToDword (addrPtr + signExtend12 off7) =
        mloadDwordPairAddr loAddr hiAddr start 7)
    (h_byte7 : byteOffset (addrPtr + signExtend12 off7) = (start + 7) % 8)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 off7) = true) :
    let b0 := (mloadByteFromDwordPair loVal hiVal start 0).zeroExtend 64
    let b1 := (mloadByteFromDwordPair loVal hiVal start 1).zeroExtend 64
    let b2 := (mloadByteFromDwordPair loVal hiVal start 2).zeroExtend 64
    let b3 := (mloadByteFromDwordPair loVal hiVal start 3).zeroExtend 64
    let b4 := (mloadByteFromDwordPair loVal hiVal start 4).zeroExtend 64
    let b5 := (mloadByteFromDwordPair loVal hiVal start 5).zeroExtend 64
    let b6 := (mloadByteFromDwordPair loVal hiVal start 6).zeroExtend 64
    let b7 := (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64
    let accAfter7 :=
      (((((((b0 <<< (8 : Nat)) ||| b1) <<< (8 : Nat)) ||| b2) <<< (8 : Nat) ||| b3)
        <<< (8 : Nat) ||| b4) <<< (8 : Nat) ||| b5) <<< (8 : Nat) ||| b6
    let accFinal := (accAfter7 <<< (8 : Nat)) ||| b7
    let cr := mloadBytePackEightCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 off7 base
    cpsTripleWithin 22 base (base + 88) cr
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ b7) ** (accReg ↦ᵣ accFinal) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 accAfter7 accFinal cr
  have seven := mload_byte_pack_seven_pair_spec_within addrReg byteReg accReg
    addrPtr accOld byteOld loVal hiVal loAddr hiAddr
    off0 off1 off2 off3 off4 off5 off6 start base
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_byte0 h_valid0 h_align1 h_byte1 h_valid1
    h_align2 h_byte2 h_valid2 h_align3 h_byte3 h_valid3
    h_align4 h_byte4 h_valid4 h_align5 h_byte5 h_valid5
    h_align6 h_byte6 h_valid6
  have step := mload_byte_pack_step_pair_spec_within addrReg byteReg accReg
    addrPtr accAfter7 b6 loVal hiVal loAddr hiAddr off7 start 7 (base + 76)
    h_byte_ne_x0 h_acc_ne_x0 h_align7 h_byte7 h_valid7
  rw [show (base + 76 : Word) + 12 = base + 88 from by bv_omega] at step
  rw [show (base + 76 : Word) + 4 = base + 80 from by bv_omega,
      show (base + 76 : Word) + 8 = base + 84 from by bv_omega] at step
  have hd_step : CodeReq.Disjoint
      (mloadBytePackSevenCode addrReg byteReg accReg off0 off1 off2 off3 off4 off5 off6 base)
      ((CodeReq.singleton (base + 76) (.LBU byteReg addrReg off7)).union
       ((CodeReq.singleton (base + 80) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
        (CodeReq.singleton (base + 84) (.OR accReg accReg byteReg)))) := by
    unfold mloadBytePackSevenCode mloadBytePackSixCode mloadBytePackFiveCode
      mloadBytePackFourCode mloadBytePackThreeCode mloadBytePackTwoCode
    have leaf : ∀ {a : Word} {i : Instr},
        a ≠ base + 76 → a ≠ base + 80 → a ≠ base + 84 →
        CodeReq.Disjoint (CodeReq.singleton a i)
            ((CodeReq.singleton (base + 76) (.LBU byteReg addrReg off7)).union
             ((CodeReq.singleton (base + 80) (.SLLI accReg accReg (BitVec.ofNat 6 8))).union
              (CodeReq.singleton (base + 84) (.OR accReg accReg byteReg)))) := by
      intro a i h76 h80 h84
      exact CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h76)
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton h80)
          (CodeReq.Disjoint.singleton h84))
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_left ?_ ?_
      · refine CodeReq.Disjoint.union_left ?_ ?_
        · refine CodeReq.Disjoint.union_left ?_ ?_
          · refine CodeReq.Disjoint.union_left ?_ ?_
            · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
            · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
              exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
          · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
            exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
        · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
          exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
      · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
        exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
    · refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      refine CodeReq.Disjoint.union_left (leaf (by bv_omega) (by bv_omega) (by bv_omega)) ?_
      exact leaf (by bv_omega) (by bv_omega) (by bv_omega)
  exact cpsTripleWithin_seq hd_step seven step

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
    (h_align0 :
      alignToDword (addrPtr + signExtend12 off0) =
        mloadDwordPairAddr loAddr hiAddr start 0)
    (h_byte0 : byteOffset (addrPtr + signExtend12 off0) = (start + 0) % 8)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_align1 :
      alignToDword (addrPtr + signExtend12 off1) =
        mloadDwordPairAddr loAddr hiAddr start 1)
    (h_byte1 : byteOffset (addrPtr + signExtend12 off1) = (start + 1) % 8)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        mloadDwordPairAddr loAddr hiAddr start 2)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 off3) =
        mloadDwordPairAddr loAddr hiAddr start 3)
    (h_byte3 : byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 off4) =
        mloadDwordPairAddr loAddr hiAddr start 4)
    (h_byte4 : byteOffset (addrPtr + signExtend12 off4) = (start + 4) % 8)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 off5) =
        mloadDwordPairAddr loAddr hiAddr start 5)
    (h_byte5 : byteOffset (addrPtr + signExtend12 off5) = (start + 5) % 8)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 off6) =
        mloadDwordPairAddr loAddr hiAddr start 6)
    (h_byte6 : byteOffset (addrPtr + signExtend12 off6) = (start + 6) % 8)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 off6) = true)
    (h_align7 :
      alignToDword (addrPtr + signExtend12 off7) =
        mloadDwordPairAddr loAddr hiAddr start 7)
    (h_byte7 : byteOffset (addrPtr + signExtend12 off7) = (start + 7) % 8)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 off7) = true) :
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
    h_byte_ne_x0 h_acc_ne_x0
    h_align0 h_byte0 h_valid0 h_align1 h_byte1 h_valid1
    h_align2 h_byte2 h_valid2 h_align3 h_byte3 h_valid3
    h_align4 h_byte4 h_valid4 h_align5 h_byte5 h_valid5
    h_align6 h_byte6 h_valid6 h_align7 h_byte7 h_valid7
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

end EvmAsm.Evm64
