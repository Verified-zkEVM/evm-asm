/-
  EvmAsm.Evm64.MStore.LimbSpec

  Level-1 executable specs for MSTORE byte-unpack blocks.
-/

import EvmAsm.Evm64.MStore.ByteAlg
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the eight SRLI/SB byte-unpack steps in one MSTORE limb. -/
def mstoreByteUnpackEightCode
    (addrReg byteReg accReg : Reg)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (base : Word) : CodeReq :=
  ((CodeReq.singleton base
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 0) * 8)))).union
   (CodeReq.singleton (base + 4) (.SB addrReg byteReg off0))).union
  (((CodeReq.singleton (base + 8)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 1) * 8)))).union
    (CodeReq.singleton (base + 12) (.SB addrReg byteReg off1))).union
  (((CodeReq.singleton (base + 16)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 2) * 8)))).union
    (CodeReq.singleton (base + 20) (.SB addrReg byteReg off2))).union
  (((CodeReq.singleton (base + 24)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 3) * 8)))).union
    (CodeReq.singleton (base + 28) (.SB addrReg byteReg off3))).union
  (((CodeReq.singleton (base + 32)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 4) * 8)))).union
    (CodeReq.singleton (base + 36) (.SB addrReg byteReg off4))).union
  (((CodeReq.singleton (base + 40)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 5) * 8)))).union
    (CodeReq.singleton (base + 44) (.SB addrReg byteReg off5))).union
  (((CodeReq.singleton (base + 48)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 6) * 8)))).union
    (CodeReq.singleton (base + 52) (.SB addrReg byteReg off6))).union
   ((CodeReq.singleton (base + 56)
      (.SRLI byteReg accReg (BitVec.ofNat 6 ((7 - 7) * 8)))).union
    (CodeReq.singleton (base + 60) (.SB addrReg byteReg off7)))))))))

/-- CodeReq for one MSTORE limb: load a source limb, then emit eight
    byte-unpack SRLI/SB steps. -/
def mstoreOneLimbCode
    (addrReg byteReg accReg : Reg)
    (srcOff off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD accReg .x12 srcOff)).union
    (mstoreByteUnpackEightCode addrReg byteReg accReg
      off0 off1 off2 off3 off4 off5 off6 off7 (base + 4))

/-- Bundled precondition for the upcoming one-limb MSTORE spec. It contains
    the address/scratch registers, the two destination dwords that may be
    touched by an unaligned 8-byte limb write, and the source EVM-stack limb
    loaded from `sp + signExtend12 srcOff`. -/
@[irreducible]
def mstoreOneLimbPre
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (srcOff : BitVec 12) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
  (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 srcOff) ↦ₘ limbVal)

theorem mstoreOneLimbPre_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (srcOff : BitVec 12) :
    mstoreOneLimbPre addrReg byteReg accReg
        addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal srcOff =
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
     (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 srcOff) ↦ₘ limbVal)) := by
  delta mstoreOneLimbPre
  rfl

/-- Bundled postcondition for the upcoming one-limb MSTORE spec. The source
    limb has been loaded into `accReg`, the final `byteReg` value is the last
    SRLI result, and the low/high destination dwords are updated by the pure
    eight-byte fold `mstoreDwordPairStoreLimb`. -/
@[irreducible]
def mstoreOneLimbPost
    (addrReg byteReg accReg : Reg)
    (addrPtr loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (srcOff : BitVec 12) : Assertion :=
  let stored := MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
  (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
  (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) ** ((.x12 : Reg) ↦ᵣ sp) **
  ((sp + signExtend12 srcOff) ↦ₘ limbVal)

theorem mstoreOneLimbPost_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat) (srcOff : BitVec 12) :
    mstoreOneLimbPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp limbVal start srcOff =
    (let stored := MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
     (addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
     (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) ** ((.x12 : Reg) ↦ᵣ sp) **
     ((sp + signExtend12 srcOff) ↦ₘ limbVal)) := by
  delta mstoreOneLimbPost
  rfl

/-- One-instruction source-limb load used by `mstore_one_limb_spec_within`. -/
theorem mstore_one_limb_load_spec_within
    (accReg : Reg) (sp accOld limbVal : Word)
    (srcOff : BitVec 12) (base : Word)
    (h_acc_ne_x0 : accReg ≠ .x0) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD accReg .x12 srcOff))
      (((.x12 : Reg) ↦ᵣ sp) ** (accReg ↦ᵣ accOld) **
       ((sp + signExtend12 srcOff) ↦ₘ limbVal))
      (((.x12 : Reg) ↦ᵣ sp) ** (accReg ↦ᵣ limbVal) **
       ((sp + signExtend12 srcOff) ↦ₘ limbVal)) :=
  ld_spec_gen_within accReg .x12 sp accOld limbVal srcOff base h_acc_ne_x0

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

/-- Bundled precondition for the dword-pair byte-unpack step lemmas. It pairs
    the address/scratch registers with the two destination dwords that the
    step may touch, before the SB stores its byte. -/
@[irreducible]
def mstoreBytePairStepPre
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal byteOld loVal hiVal loAddr hiAddr : Word) : Assertion :=
  (addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteOld) **
  (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)

theorem mstoreBytePairStepPre_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal byteOld loVal hiVal loAddr hiAddr : Word) :
    mstoreBytePairStepPre addrReg byteReg accReg
        addrPtr accVal byteOld loVal hiVal loAddr hiAddr =
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal)) := by
  delta mstoreBytePairStepPre
  rfl

/-- Bundled postcondition for the dword-pair byte-unpack step lemmas. It
    captures the post-SRLI byte value in `byteReg` and the updated low/high
    destination dwords. -/
@[irreducible]
def mstoreBytePairStepPost
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal storedLo storedHi loAddr hiAddr : Word)
    (k : Nat) : Assertion :=
  let shift := BitVec.ofNat 6 ((7 - k) * 8)
  let byteVal := accVal >>> shift.toNat
  (addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteVal) **
  (loAddr ↦ₘ storedLo) ** (hiAddr ↦ₘ storedHi)

theorem mstoreBytePairStepPost_unfold
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal storedLo storedHi loAddr hiAddr : Word)
    (k : Nat) :
    mstoreBytePairStepPost addrReg byteReg accReg
        addrPtr accVal storedLo storedHi loAddr hiAddr k =
      (let shift := BitVec.ofNat 6 ((7 - k) * 8)
       let byteVal := accVal >>> shift.toNat
       (addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteVal) **
       (loAddr ↦ₘ storedLo) ** (hiAddr ↦ₘ storedHi)) := by
  delta mstoreBytePairStepPost
  rfl

/-- Low-dword form of `mstore_byte_unpack_step_spec_within` for an unaligned
    low/high destination dword pair. The byte position `start + i` is still
    inside the low dword, so the high dword is framed through unchanged. -/
theorem mstore_byte_unpack_step_pair_low_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal byteOld loVal hiVal : Word)
    (loAddr hiAddr : Word)
    (k start i : Nat) (dstOff : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_k_lt : k < 8)
    (h_pos : start + i < 8)
    (h_align : alignToDword (addrPtr + signExtend12 dstOff) = loAddr)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 dstOff) = true)
    (h_byte : byteOffset (addrPtr + signExtend12 dstOff) = (start + i) % 8) :
    let storedByte := extractByte accVal (7 - k)
    let stored := MStore.mstoreDwordPairReplaceByte loVal hiVal start i storedByte
    let shift := BitVec.ofNat 6 ((7 - k) * 8)
    let cr :=
      (CodeReq.singleton base (.SRLI byteReg accReg shift)).union
        (CodeReq.singleton (base + 4) (.SB addrReg byteReg dstOff))
    cpsTripleWithin 2 base (base + 8) cr
      (mstoreBytePairStepPre addrReg byteReg accReg
        addrPtr accVal byteOld loVal hiVal loAddr hiAddr)
      (mstoreBytePairStepPost addrReg byteReg accReg
        addrPtr accVal stored.1 stored.2 loAddr hiAddr k) := by
  intro storedByte stored shift cr
  rw [mstoreBytePairStepPre_unfold, mstoreBytePairStepPost_unfold]
  have step := mstore_byte_unpack_step_spec_within
    addrReg byteReg accReg addrPtr accVal byteOld loVal loAddr
    k dstOff base h_byte_ne_x0 h_k_lt h_align h_valid
  dsimp only at step
  have framed := cpsTripleWithin_frameR (hiAddr ↦ₘ hiVal) (by pcFree) step
  rw [show stored = (replaceByte loVal ((start + i) % 8) storedByte, hiVal) by
    unfold stored
    rw [MStore.mstoreDwordPairReplaceByte_low loVal hiVal storedByte h_pos]]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      rw [h_byte] at hp
      dsimp only at hp ⊢
      xperm_hyp hp)
    framed

/-- High-dword form of `mstore_byte_unpack_step_spec_within` for an unaligned
    low/high destination dword pair. The byte position `start + i` has crossed
    into the high dword, so the low dword is framed through unchanged. -/
theorem mstore_byte_unpack_step_pair_high_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal byteOld loVal hiVal : Word)
    (loAddr hiAddr : Word)
    (k start i : Nat) (dstOff : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_k_lt : k < 8)
    (h_pos : 8 ≤ start + i)
    (h_align : alignToDword (addrPtr + signExtend12 dstOff) = hiAddr)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 dstOff) = true)
    (h_byte : byteOffset (addrPtr + signExtend12 dstOff) = (start + i) % 8) :
    let storedByte := extractByte accVal (7 - k)
    let stored := MStore.mstoreDwordPairReplaceByte loVal hiVal start i storedByte
    let shift := BitVec.ofNat 6 ((7 - k) * 8)
    let cr :=
      (CodeReq.singleton base (.SRLI byteReg accReg shift)).union
        (CodeReq.singleton (base + 4) (.SB addrReg byteReg dstOff))
    cpsTripleWithin 2 base (base + 8) cr
      (mstoreBytePairStepPre addrReg byteReg accReg
        addrPtr accVal byteOld loVal hiVal loAddr hiAddr)
      (mstoreBytePairStepPost addrReg byteReg accReg
        addrPtr accVal stored.1 stored.2 loAddr hiAddr k) := by
  intro storedByte stored shift cr
  rw [mstoreBytePairStepPre_unfold, mstoreBytePairStepPost_unfold]
  have step := mstore_byte_unpack_step_spec_within
    addrReg byteReg accReg addrPtr accVal byteOld hiVal hiAddr
    k dstOff base h_byte_ne_x0 h_k_lt h_align h_valid
  dsimp only at step
  have framed := cpsTripleWithin_frameL (loAddr ↦ₘ loVal) (by pcFree) step
  rw [show stored = (loVal, replaceByte hiVal ((start + i) % 8) storedByte) by
    unfold stored
    rw [MStore.mstoreDwordPairReplaceByte_high loVal hiVal storedByte h_pos]]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      rw [h_byte] at hp
      dsimp only at hp ⊢
      xperm_hyp hp)
    framed

/-- Dword-pair form of `mstore_byte_unpack_step_spec_within` that dispatches
    to the low or high destination dword according to
    `MStore.mstoreDwordPairAddr`. This is the uniform byte-step lemma used by
    the one-limb MSTORE composition. -/
theorem mstore_byte_unpack_step_pair_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr accVal byteOld loVal hiVal : Word)
    (loAddr hiAddr : Word)
    (k start i : Nat) (dstOff : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_k_lt : k < 8)
    (h_align :
      alignToDword (addrPtr + signExtend12 dstOff) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start i)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 dstOff) = true)
    (h_byte : byteOffset (addrPtr + signExtend12 dstOff) = (start + i) % 8) :
    let shift := BitVec.ofNat 6 ((7 - k) * 8)
    let byteVal := accVal >>> shift.toNat
    let storedByte := extractByte accVal (7 - k)
    let stored := MStore.mstoreDwordPairReplaceByte loVal hiVal start i storedByte
    let cr :=
      (CodeReq.singleton base (.SRLI byteReg accReg shift)).union
        (CodeReq.singleton (base + 4) (.SB addrReg byteReg dstOff))
    cpsTripleWithin 2 base (base + 8) cr
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ accVal) ** (byteReg ↦ᵣ byteVal) **
       (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2)) := by
  by_cases h_pos : start + i < 8
  · have h_align_low :
        alignToDword (addrPtr + signExtend12 dstOff) = loAddr := by
      rw [MStore.mstoreDwordPairAddr_low loAddr hiAddr h_pos] at h_align
      exact h_align
    have h := mstore_byte_unpack_step_pair_low_spec_within
      addrReg byteReg accReg addrPtr accVal byteOld loVal hiVal loAddr hiAddr
      k start i dstOff base h_byte_ne_x0 h_k_lt h_pos h_align_low h_valid h_byte
    simp only [mstoreBytePairStepPre_unfold, mstoreBytePairStepPost_unfold] at h
    exact h
  · have h_high : 8 ≤ start + i := by omega
    have h_align_high :
        alignToDword (addrPtr + signExtend12 dstOff) = hiAddr := by
      rw [MStore.mstoreDwordPairAddr_high loAddr hiAddr h_high] at h_align
      exact h_align
    have h := mstore_byte_unpack_step_pair_high_spec_within
      addrReg byteReg accReg addrPtr accVal byteOld loVal hiVal loAddr hiAddr
      k start i dstOff base h_byte_ne_x0 h_k_lt h_high h_align_high h_valid h_byte
    simp only [mstoreBytePairStepPre_unfold, mstoreBytePairStepPost_unfold] at h
    exact h

/-- Final dword-pair byte-unpack step for one MSTORE limb. At `k = 7`, the
    runtime `SRLI` is a zero shift, so the final value left in `byteReg` is the
    source limb itself. -/
theorem mstore_byte_unpack_step_pair_last_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr limbVal byteOld loVal hiVal : Word)
    (loAddr hiAddr : Word)
    (start : Nat) (dstOff : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_align :
      alignToDword (addrPtr + signExtend12 dstOff) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 7)
    (h_valid : isValidByteAccess (addrPtr + signExtend12 dstOff) = true)
    (h_byte : byteOffset (addrPtr + signExtend12 dstOff) = (start + 7) % 8) :
    let shift := BitVec.ofNat 6 ((7 - 7) * 8)
    let storedByte := extractByte limbVal (7 - 7)
    let stored := MStore.mstoreDwordPairReplaceByte loVal hiVal start 7 storedByte
    let cr :=
      (CodeReq.singleton base (.SRLI byteReg accReg shift)).union
        (CodeReq.singleton (base + 4) (.SB addrReg byteReg dstOff))
    cpsTripleWithin 2 base (base + 8) cr
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ limbVal) ** (byteReg ↦ᵣ byteOld) **
       (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))
      ((addrReg ↦ᵣ addrPtr) ** (accReg ↦ᵣ limbVal) ** (byteReg ↦ᵣ limbVal) **
       (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2)) := by
  intro shift storedByte stored cr
  have step := mstore_byte_unpack_step_pair_spec_within
    addrReg byteReg accReg addrPtr limbVal byteOld loVal hiVal loAddr hiAddr
    7 start 7 dstOff base h_byte_ne_x0 (by decide) h_align h_valid h_byte
  dsimp only at step
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      try dsimp only at hp ⊢
      simp at hp ⊢
      unfold stored
      unfold storedByte
      simp
      xperm_hyp hp)
    step

/-- One MSTORE source limb: load the limb from the EVM stack, then store its
    eight big-endian bytes into an unaligned low/high destination dword pair. -/
theorem mstore_one_limb_spec_within
    (addrReg byteReg accReg : Reg)
    (addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal : Word)
    (start : Nat)
    (srcOff off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12) (base : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_align0 :
      alignToDword (addrPtr + signExtend12 off0) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 0)
    (h_valid0 : isValidByteAccess (addrPtr + signExtend12 off0) = true)
    (h_byte0 : byteOffset (addrPtr + signExtend12 off0) = (start + 0) % 8)
    (h_align1 :
      alignToDword (addrPtr + signExtend12 off1) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 1)
    (h_valid1 : isValidByteAccess (addrPtr + signExtend12 off1) = true)
    (h_byte1 : byteOffset (addrPtr + signExtend12 off1) = (start + 1) % 8)
    (h_align2 :
      alignToDword (addrPtr + signExtend12 off2) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 2)
    (h_valid2 : isValidByteAccess (addrPtr + signExtend12 off2) = true)
    (h_byte2 : byteOffset (addrPtr + signExtend12 off2) = (start + 2) % 8)
    (h_align3 :
      alignToDword (addrPtr + signExtend12 off3) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 3)
    (h_valid3 : isValidByteAccess (addrPtr + signExtend12 off3) = true)
    (h_byte3 : byteOffset (addrPtr + signExtend12 off3) = (start + 3) % 8)
    (h_align4 :
      alignToDword (addrPtr + signExtend12 off4) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 4)
    (h_valid4 : isValidByteAccess (addrPtr + signExtend12 off4) = true)
    (h_byte4 : byteOffset (addrPtr + signExtend12 off4) = (start + 4) % 8)
    (h_align5 :
      alignToDword (addrPtr + signExtend12 off5) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 5)
    (h_valid5 : isValidByteAccess (addrPtr + signExtend12 off5) = true)
    (h_byte5 : byteOffset (addrPtr + signExtend12 off5) = (start + 5) % 8)
    (h_align6 :
      alignToDword (addrPtr + signExtend12 off6) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 6)
    (h_valid6 : isValidByteAccess (addrPtr + signExtend12 off6) = true)
    (h_byte6 : byteOffset (addrPtr + signExtend12 off6) = (start + 6) % 8)
    (h_align7 :
      alignToDword (addrPtr + signExtend12 off7) =
        MStore.mstoreDwordPairAddr loAddr hiAddr start 7)
    (h_valid7 : isValidByteAccess (addrPtr + signExtend12 off7) = true)
    (h_byte7 : byteOffset (addrPtr + signExtend12 off7) = (start + 7) % 8) :
    cpsTripleWithin 17 base (base + 68)
      (mstoreOneLimbCode addrReg byteReg accReg
        srcOff off0 off1 off2 off3 off4 off5 off6 off7 base)
      (mstoreOneLimbPre addrReg byteReg accReg
        addrPtr byteOld accOld loVal hiVal loAddr hiAddr sp limbVal srcOff)
      (mstoreOneLimbPost addrReg byteReg accReg
        addrPtr loVal hiVal loAddr hiAddr sp limbVal start srcOff) := by
  rw [mstoreOneLimbPre_unfold, mstoreOneLimbPost_unfold]
  dsimp only []
  let p0 := MStore.mstoreDwordPairReplaceByte loVal hiVal start 0 (extractByte limbVal 7)
  let p1 := MStore.mstoreDwordPairReplaceByte p0.1 p0.2 start 1 (extractByte limbVal 6)
  let p2 := MStore.mstoreDwordPairReplaceByte p1.1 p1.2 start 2 (extractByte limbVal 5)
  let p3 := MStore.mstoreDwordPairReplaceByte p2.1 p2.2 start 3 (extractByte limbVal 4)
  let p4 := MStore.mstoreDwordPairReplaceByte p3.1 p3.2 start 4 (extractByte limbVal 3)
  let p5 := MStore.mstoreDwordPairReplaceByte p4.1 p4.2 start 5 (extractByte limbVal 2)
  let p6 := MStore.mstoreDwordPairReplaceByte p5.1 p5.2 start 6 (extractByte limbVal 1)
  let p7 := MStore.mstoreDwordPairReplaceByte p6.1 p6.2 start 7 (extractByte limbVal 0)
  let b0 := limbVal >>> (BitVec.ofNat 6 ((7 - 0) * 8)).toNat
  let b1 := limbVal >>> (BitVec.ofNat 6 ((7 - 1) * 8)).toNat
  let b2 := limbVal >>> (BitVec.ofNat 6 ((7 - 2) * 8)).toNat
  let b3 := limbVal >>> (BitVec.ofNat 6 ((7 - 3) * 8)).toNat
  let b4 := limbVal >>> (BitVec.ofNat 6 ((7 - 4) * 8)).toNat
  let b5 := limbVal >>> (BitVec.ofNat 6 ((7 - 5) * 8)).toNat
  let b6 := limbVal >>> (BitVec.ofNat 6 ((7 - 6) * 8)).toNat
  have composed :
      cpsTripleWithin 17 base (base + 68)
        (mstoreOneLimbCode addrReg byteReg accReg
          srcOff off0 off1 off2 off3 off4 off5 off6 off7 base)
        ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) ** ((.x12 : Reg) ↦ᵣ sp) **
         ((sp + signExtend12 srcOff) ↦ₘ limbVal))
        ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ p7.1) ** (hiAddr ↦ₘ p7.2) ** ((.x12 : Reg) ↦ᵣ sp) **
         ((sp + signExtend12 srcOff) ↦ₘ limbVal)) := by
    unfold mstoreOneLimbCode mstoreByteUnpackEightCode
    have L := mstore_one_limb_load_spec_within accReg sp accOld limbVal srcOff base h_acc_ne_x0
    have S0 := mstore_byte_unpack_step_pair_spec_within
      addrReg byteReg accReg addrPtr limbVal byteOld loVal hiVal loAddr hiAddr
      0 start 0 off0 (base + 4) h_byte_ne_x0 (by decide) h_align0 h_valid0 h_byte0
    have S1 := mstore_byte_unpack_step_pair_spec_within
      addrReg byteReg accReg addrPtr limbVal b0 p0.1 p0.2 loAddr hiAddr
      1 start 1 off1 (base + 12) h_byte_ne_x0 (by decide) h_align1 h_valid1 h_byte1
    have S2 := mstore_byte_unpack_step_pair_spec_within
      addrReg byteReg accReg addrPtr limbVal b1 p1.1 p1.2 loAddr hiAddr
      2 start 2 off2 (base + 20) h_byte_ne_x0 (by decide) h_align2 h_valid2 h_byte2
    have S3 := mstore_byte_unpack_step_pair_spec_within
      addrReg byteReg accReg addrPtr limbVal b2 p2.1 p2.2 loAddr hiAddr
      3 start 3 off3 (base + 28) h_byte_ne_x0 (by decide) h_align3 h_valid3 h_byte3
    have S4 := mstore_byte_unpack_step_pair_spec_within
      addrReg byteReg accReg addrPtr limbVal b3 p3.1 p3.2 loAddr hiAddr
      4 start 4 off4 (base + 36) h_byte_ne_x0 (by decide) h_align4 h_valid4 h_byte4
    have S5 := mstore_byte_unpack_step_pair_spec_within
      addrReg byteReg accReg addrPtr limbVal b4 p4.1 p4.2 loAddr hiAddr
      5 start 5 off5 (base + 44) h_byte_ne_x0 (by decide) h_align5 h_valid5 h_byte5
    have S6 := mstore_byte_unpack_step_pair_spec_within
      addrReg byteReg accReg addrPtr limbVal b5 p5.1 p5.2 loAddr hiAddr
      6 start 6 off6 (base + 52) h_byte_ne_x0 (by decide) h_align6 h_valid6 h_byte6
    have S7 := mstore_byte_unpack_step_pair_last_spec_within
      addrReg byteReg accReg addrPtr limbVal b6 p6.1 p6.2 loAddr hiAddr
      start off7 (base + 60) h_byte_ne_x0 h_align7 h_valid7 h_byte7
    exact by
      (runBlock L S0 S1 S2 S3 S4 S5 S6 S7)
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      rw [MStore.mstoreDwordPairStoreLimb_unfold loVal hiVal limbVal start]
      dsimp only []
      xperm_hyp hp)
    composed

end EvmAsm.Evm64
