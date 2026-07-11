/-
  EvmAsm.Evm64.MLoad.MemoryRegionStackSpec

  The canonical public MLOAD stack spec against `evmMemoryIs`. Each of the
  four byte-packing quarters peels only its adjacent dword pair and folds the
  region before the next quarter, so overlapping pairs remain satisfiable at
  every byte alignment. Region-placement facts discharge the load side
  conditions, and the value pushed on the EVM stack is
  `evmMemoryReadWord contents offset.toNat` — the 32 bytes at the
  requested offset, big-endian, exactly the EVM-spec MLOAD result.
-/

import EvmAsm.Evm64.StateAssertions
import EvmAsm.Evm64.MLoad.UnalignedFramedStackSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-! ## The MLOAD result as a function of the region contents -/

/-- The 256-bit value MLOAD reads from region bytes `[k, k+32)`:
    big-endian (byte `k` is most significant), zero-padded past the end of
    the list — the EVM's zero-extended-tail read semantics. -/
def evmMemoryReadWord (bs : List (BitVec 8)) (k : Nat) : EvmWord :=
  mloadLoadedWordFromBytes
    (getByteAt bs k) (getByteAt bs (k + 1)) (getByteAt bs (k + 2))
    (getByteAt bs (k + 3)) (getByteAt bs (k + 4)) (getByteAt bs (k + 5))
    (getByteAt bs (k + 6)) (getByteAt bs (k + 7))
    (getByteAt bs (k + 8)) (getByteAt bs (k + 9)) (getByteAt bs (k + 10))
    (getByteAt bs (k + 11)) (getByteAt bs (k + 12)) (getByteAt bs (k + 13))
    (getByteAt bs (k + 14)) (getByteAt bs (k + 15))
    (getByteAt bs (k + 16)) (getByteAt bs (k + 17)) (getByteAt bs (k + 18))
    (getByteAt bs (k + 19)) (getByteAt bs (k + 20)) (getByteAt bs (k + 21))
    (getByteAt bs (k + 22)) (getByteAt bs (k + 23))
    (getByteAt bs (k + 24)) (getByteAt bs (k + 25)) (getByteAt bs (k + 26))
    (getByteAt bs (k + 27)) (getByteAt bs (k + 28)) (getByteAt bs (k + 29))
    (getByteAt bs (k + 30)) (getByteAt bs (k + 31))

/-- Extract the adjacent dword pair used by one unaligned MLOAD quarter while
    leaving the rest of an EVM-memory region framed.  Unlike the obsolete
    eight-cell public precondition, callers use this equality one quarter at a
    time and fold the pair back before extracting the next one. -/
theorem evmMemoryIs_quarter_pair
    (memBase : Word) (capacity : Nat) (contents : List (BitVec 8))
    (offset : Word) (w : Nat)
    (hlen : contents.length = capacity) (h_w_le : w ≤ 24)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      evmMemoryIs memBase capacity contents =
        (front ** (((memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8))) ↦ₘ
          dwordAt contents (8 * ((offset.toNat + w) / 8))) **
          (((memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8)) ↦ₘ
            dwordAt contents (8 * ((offset.toNat + w) / 8) + 8)) ** rest))) := by
  rw [evmMemoryIs_eq_bytesRegion hlen]
  exact bytesRegion_dword_pair_at memBase contents ((offset.toNat + w) / 8) (by omega)

/-- Decode one byte from an unaligned quarter pair back to the byte list.
    This is the byte-level bridge used after each framed one-limb execution. -/
theorem mloadByteFromDwordPair_dwordAt_unaligned
    (contents : List (BitVec 8)) (offset : Word) (w i : Nat)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24) (h_i : i < 8)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length) :
    mloadByteFromDwordPair
      (dwordAt contents (8 * ((offset.toNat + w) / 8)))
      (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
      (offset.toNat % 8) i = getByteAt contents (offset.toNat + w + i) := by
  by_cases h_lo : offset.toNat % 8 + i < 8
  · rw [mloadByteFromDwordPair_low _ _ h_lo,
        show (offset.toNat % 8 + i) % 8 = offset.toNat % 8 + i from
          Nat.mod_eq_of_lt h_lo]
    unfold dwordAt
    rw [extractByte_packBytes _ _ h_lo
      (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    unfold getByteAt
    rw [dif_pos (by omega : offset.toNat + w + i < contents.length)]
    congr 1
    omega
  · rw [mloadByteFromDwordPair_high _ _ (by omega),
        show (offset.toNat % 8 + i) % 8 = offset.toNat % 8 + i - 8 by omega]
    unfold dwordAt
    rw [extractByte_packBytes _ _ (by omega)
      (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
    unfold getByteAt
    rw [dif_pos (by omega : offset.toNat + w + i < contents.length)]
    congr 1
    omega

/-- The four unaligned region-backed quarter pairs assemble to the EVM MLOAD
    word.  The pairs are ordered in execution/stack-limb order (24,16,8,0). -/
theorem mloadStackOutputWordFromDwordPairs_dwordAt_unaligned
    (contents : List (BitVec 8)) (offset : Word)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length) :
    mloadStackOutputWordFromDwordPairs
      (dwordAt contents (8 * ((offset.toNat + 24) / 8)))
      (dwordAt contents (8 * ((offset.toNat + 24) / 8) + 8)) (offset.toNat % 8)
      (dwordAt contents (8 * ((offset.toNat + 16) / 8)))
      (dwordAt contents (8 * ((offset.toNat + 16) / 8) + 8)) (offset.toNat % 8)
      (dwordAt contents (8 * ((offset.toNat + 8) / 8)))
      (dwordAt contents (8 * ((offset.toNat + 8) / 8) + 8)) (offset.toNat % 8)
      (dwordAt contents (8 * ((offset.toNat + 0) / 8)))
      (dwordAt contents (8 * ((offset.toNat + 0) / 8) + 8)) (offset.toNat % 8) =
      evmMemoryReadWord contents offset.toNat := by
  rw [mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs,
      mloadLoadedWordFromDwordPairs_eq_mloadLoadedWordFromBytes]
  repeat' first
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 0
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 1
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 2
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 3
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 4
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 5
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 6
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 0 7
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 0
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 1
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 2
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 3
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 4
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 5
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 6
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 8 7
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 0
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 1
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 2
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 3
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 4
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 5
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 6
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 16 7
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 0
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 1
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 2
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 3
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 4
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 5
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 6
      (by decide) (by decide) (by decide) hin]
  | rw [mloadByteFromDwordPair_dwordAt_unaligned contents offset 24 7
      (by decide) (by decide) (by decide) hin]
  rfl

/-- One unaligned MLOAD quarter executed against a folded `evmMemoryIs`
    resource.  The backing pair is peeled only for this execution and folded
    immediately afterwards, so adjacent quarters may safely share a dword. -/
theorem mload_one_limb_unaligned_spec_within_evmMemoryIs
    (addrReg byteReg accReg : Reg)
    (memBase offset sp byteOld accOld dstOld : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (w : Nat)
    (off0 off1 off2 off3 off4 off5 off6 off7 dstOff : BitVec 12) (qb : Word)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity) (h_w_le : w ≤ 24)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_window : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8))
      (offset.toNat % 8) off0 off1 off2 off3 off4 off5 off6 off7) :
    cpsTripleWithin 23 qb (qb + 92)
      (mloadOneLimbCode addrReg byteReg accReg
        off0 off1 off2 off3 off4 off5 off6 off7 dstOff qb)
      ((addrReg ↦ᵣ (memBase + offset)) ** (byteReg ↦ᵣ byteOld) **
       (accReg ↦ᵣ accOld) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 dstOff) ↦ₘ dstOld) **
       evmMemoryIs memBase capacity contents)
      ((addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ
         (mloadByteFromDwordPair
           (dwordAt contents (8 * ((offset.toNat + w) / 8)))
           (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
           (offset.toNat % 8) 7).zeroExtend 64) **
       (accReg ↦ᵣ
         mloadPackedLimbFromDwordPair
           (dwordAt contents (8 * ((offset.toNat + w) / 8)))
           (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
           (offset.toNat % 8)) ** ((.x12 : Reg) ↦ᵣ sp) **
       ((sp + signExtend12 dstOff) ↦ₘ
         mloadPackedLimbFromDwordPair
           (dwordAt contents (8 * ((offset.toNat + w) / 8)))
           (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
           (offset.toNat % 8)) ** evmMemoryIs memBase capacity contents) := by
  obtain ⟨front, rest, h_front, h_rest, heq⟩ :=
    evmMemoryIs_quarter_pair memBase capacity contents offset w hlen h_w_le hin
  rw [heq]
  have h_core := mload_one_limb_unaligned_spec_within addrReg byteReg accReg
    (memBase + offset) accOld byteOld
    (dwordAt contents (8 * ((offset.toNat + w) / 8)))
    (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
    (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8)))
    (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8))
    sp dstOld off0 off1 off2 off3 off4 off5 off6 off7 dstOff
    (offset.toNat % 8) qb h_byte_ne_x0 h_acc_ne_x0 h_window
  rw [mloadOneLimbUnalignedPre_unfold, mloadOneLimbUnalignedPost_unfold] at h_core
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest)
      (pcFree_sepConj h_front h_rest) h_core)

def mloadRegionLimb (contents : List (BitVec 8)) (offset : Word) (w : Nat) : Word :=
  mloadPackedLimbFromDwordPair
    (dwordAt contents (8 * ((offset.toNat + w) / 8)))
    (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
    (offset.toNat % 8)

def mloadRegionByte7 (contents : List (BitVec 8)) (offset : Word) (w : Nat) : Word :=
  (mloadByteFromDwordPair
    (dwordAt contents (8 * ((offset.toNat + w) / 8)))
    (dwordAt contents (8 * ((offset.toNat + w) / 8) + 8))
    (offset.toNat % 8) 7).zeroExtend 64

def mloadRegionMid
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp memBase offset byteVal accVal c0 c1 c2 c3 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) : Assertion :=
  ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
  (addrReg ↦ᵣ (memBase + offset)) ** (byteReg ↦ᵣ byteVal) ** (accReg ↦ᵣ accVal) **
  (sp ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) ** ((sp + 16) ↦ₘ c2) **
  ((sp + 24) ↦ₘ c3) ** evmMemoryIs memBase capacity contents

theorem mloadRegionMid_unfold
    {offReg byteReg accReg addrReg memBaseReg : Reg}
    {sp memBase offset byteVal accVal c0 c1 c2 c3 : Word}
    {capacity : Nat} {contents : List (BitVec 8)} :
    mloadRegionMid offReg byteReg accReg addrReg memBaseReg
      sp memBase offset byteVal accVal c0 c1 c2 c3 capacity contents =
    (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
     (addrReg ↦ᵣ (memBase + offset)) ** (byteReg ↦ᵣ byteVal) **
     (accReg ↦ᵣ accVal) ** (sp ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) **
     ((sp + 16) ↦ₘ c2) ** ((sp + 24) ↦ₘ c3) **
     evmMemoryIs memBase capacity contents) := rfl

section RegionSteps

variable (offReg byteReg accReg addrReg memBaseReg : Reg)
variable (sp memBase offset byteOld accOld d1 d2 d3 : Word)
variable (capacity : Nat) (contents : List (BitVec 8)) (base : Word)

private theorem mload_region_step_q0
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_window : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8) + 8))
      (offset.toNat % 8) 24 25 26 27 28 29 30 31) :
    cpsTripleWithin 23 (base + 8) (base + 100)
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8))
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset byteOld accOld offset d1 d2 d3 capacity contents)
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 24)
        (mloadRegionLimb contents offset 24)
        (mloadRegionLimb contents offset 24) d1 d2 d3 capacity contents) := by
  have h_core := mload_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp byteOld accOld offset
    capacity contents 24 24 25 26 27 28 29 30 31 0 (base + 8)
    h_byte_ne_x0 h_acc_ne_x0 hlen (by decide) hin h_window
  rw [show (base + 8) + 92 = base + 100 from by bv_omega,
      show sp + signExtend12 (0 : BitVec 12) = sp from by
        rw [signExtend12_0]; bv_omega] at h_core
  simp only [mloadRegionMid_unfold, mloadRegionByte7, mloadRegionLimb]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR
      ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
       ((sp + 8) ↦ₘ d1) ** ((sp + 16) ↦ₘ d2) ** ((sp + 24) ↦ₘ d3))
      (by pcFree) h_core)

private theorem mload_region_step_q1
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_window : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8) + 8))
      (offset.toNat % 8) 16 17 18 19 20 21 22 23) :
    cpsTripleWithin 23 (base + 100) (base + 192)
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100))
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 24)
        (mloadRegionLimb contents offset 24)
        (mloadRegionLimb contents offset 24) d1 d2 d3 capacity contents)
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 16)
        (mloadRegionLimb contents offset 16)
        (mloadRegionLimb contents offset 24) (mloadRegionLimb contents offset 16)
        d2 d3 capacity contents) := by
  have h_core := mload_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp
    (mloadRegionByte7 contents offset 24) (mloadRegionLimb contents offset 24) d1
    capacity contents 16 16 17 18 19 20 21 22 23 8 (base + 100)
    h_byte_ne_x0 h_acc_ne_x0 hlen (by decide) hin h_window
  rw [show (base + 100) + 92 = base + 192 from by bv_omega,
      show sp + signExtend12 (8 : BitVec 12) = sp + 8 from by rw [signExtend12_8]] at h_core
  have h_framed := cpsTripleWithin_frameR
    ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
     (sp ↦ₘ mloadRegionLimb contents offset 24) **
     ((sp + 16) ↦ₘ d2) ** ((sp + 24) ↦ₘ d3)) (by pcFree) h_core
  simp only [mloadRegionByte7, mloadRegionLimb] at h_framed
  simp only [mloadRegionMid_unfold, mloadRegionByte7, mloadRegionLimb]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    h_framed

private theorem mload_region_step_q2
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_window : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8) + 8))
      (offset.toNat % 8) 8 9 10 11 12 13 14 15) :
    cpsTripleWithin 23 (base + 192) (base + 284)
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192))
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 16)
        (mloadRegionLimb contents offset 16)
        (mloadRegionLimb contents offset 24) (mloadRegionLimb contents offset 16)
        d2 d3 capacity contents)
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 8)
        (mloadRegionLimb contents offset 8)
        (mloadRegionLimb contents offset 24) (mloadRegionLimb contents offset 16)
        (mloadRegionLimb contents offset 8) d3 capacity contents) := by
  have h_core := mload_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp
    (mloadRegionByte7 contents offset 16) (mloadRegionLimb contents offset 16) d2
    capacity contents 8 8 9 10 11 12 13 14 15 16 (base + 192)
    h_byte_ne_x0 h_acc_ne_x0 hlen (by decide) hin h_window
  rw [show (base + 192) + 92 = base + 284 from by bv_omega,
      show sp + signExtend12 (16 : BitVec 12) = sp + 16 from by rw [signExtend12_16]] at h_core
  have h_framed := cpsTripleWithin_frameR
    ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
     (sp ↦ₘ mloadRegionLimb contents offset 24) **
     ((sp + 8) ↦ₘ mloadRegionLimb contents offset 16) **
     ((sp + 24) ↦ₘ d3)) (by pcFree) h_core
  simp only [mloadRegionByte7, mloadRegionLimb] at h_framed
  simp only [mloadRegionMid_unfold, mloadRegionByte7, mloadRegionLimb]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    h_framed

private theorem mload_region_step_q3
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_window : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8) + 8))
      (offset.toNat % 8) 0 1 2 3 4 5 6 7) :
    cpsTripleWithin 23 (base + 284) (base + 376)
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284))
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 8)
        (mloadRegionLimb contents offset 8)
        (mloadRegionLimb contents offset 24) (mloadRegionLimb contents offset 16)
        (mloadRegionLimb contents offset 8) d3 capacity contents)
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 0)
        (mloadRegionLimb contents offset 0)
        (mloadRegionLimb contents offset 24) (mloadRegionLimb contents offset 16)
        (mloadRegionLimb contents offset 8) (mloadRegionLimb contents offset 0)
        capacity contents) := by
  have h_core := mload_one_limb_unaligned_spec_within_evmMemoryIs
    addrReg byteReg accReg memBase offset sp
    (mloadRegionByte7 contents offset 8) (mloadRegionLimb contents offset 8) d3
    capacity contents 0 0 1 2 3 4 5 6 7 24 (base + 284)
    h_byte_ne_x0 h_acc_ne_x0 hlen (by decide) hin h_window
  rw [show (base + 284) + 92 = base + 376 from by bv_omega,
      show sp + signExtend12 (24 : BitVec 12) = sp + 24 from by rw [signExtend12_24]] at h_core
  have h_framed := cpsTripleWithin_frameR
    ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
     (sp ↦ₘ mloadRegionLimb contents offset 24) **
     ((sp + 8) ↦ₘ mloadRegionLimb contents offset 16) **
     ((sp + 16) ↦ₘ mloadRegionLimb contents offset 8)) (by pcFree) h_core
  simp only [mloadRegionByte7, mloadRegionLimb] at h_framed
  simp only [mloadRegionMid_unfold, mloadRegionByte7, mloadRegionLimb]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    h_framed

end RegionSteps

private theorem evm_mload_region_cells_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld d1 d2 d3 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_window0 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8) + 8))
      (offset.toNat % 8) 24 25 26 27 28 29 30 31)
    (h_window1 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8) + 8))
      (offset.toNat % 8) 16 17 18 19 20 21 22 23)
    (h_window2 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8) + 8))
      (offset.toNat % 8) 8 9 10 11 12 13 14 15)
    (h_window3 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8) + 8))
      (offset.toNat % 8) 0 1 2 3 4 5 6 7) :
    cpsTripleWithin (2 + (23 + 23 + 23 + 23)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset) ** ((sp + 8) ↦ₘ d1) ** ((sp + 16) ↦ₘ d2) **
       ((sp + 24) ↦ₘ d3) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       evmMemoryIs memBase capacity contents)
      (mloadRegionMid offReg byteReg accReg addrReg memBaseReg
        sp memBase offset (mloadRegionByte7 contents offset 0)
        (mloadRegionLimb contents offset 0)
        (mloadRegionLimb contents offset 24) (mloadRegionLimb contents offset 16)
        (mloadRegionLimb contents offset 8) (mloadRegionLimb contents offset 0)
        capacity contents) := by
  let Fpre : Assertion :=
    (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
    ((sp + 8) ↦ₘ d1) ** ((sp + 16) ↦ₘ d2) ** ((sp + 24) ↦ₘ d3) **
    evmMemoryIs memBase capacity contents
  have hp := evm_mload_prologue_stack_spec_within_framed
    offReg byteReg accReg addrReg memBaseReg sp offset offOld addrOld memBase base
    Fpre (by dsimp only [Fpre]; pcFree) h_off_ne_x0 h_addr_ne_x0
  have h0 := cpsTripleWithin_evm_mload_of_one_limb_q0
    offReg byteReg accReg addrReg memBaseReg base
    (mload_region_step_q0 offReg byteReg accReg addrReg memBaseReg
      sp memBase offset byteOld accOld d1 d2 d3 capacity contents base
      h_byte_ne_x0 h_acc_ne_x0 hlen hin h_window0)
  have h1 := cpsTripleWithin_evm_mload_of_one_limb_q1
    offReg byteReg accReg addrReg memBaseReg base
    (mload_region_step_q1 offReg byteReg accReg addrReg memBaseReg
      sp memBase offset d1 d2 d3 capacity contents base
      h_byte_ne_x0 h_acc_ne_x0 hlen hin h_window1)
  have h2 := cpsTripleWithin_evm_mload_of_one_limb_q2
    offReg byteReg accReg addrReg memBaseReg base
    (mload_region_step_q2 offReg byteReg accReg addrReg memBaseReg
      sp memBase offset d2 d3 capacity contents base
      h_byte_ne_x0 h_acc_ne_x0 hlen hin h_window2)
  have h3 := cpsTripleWithin_evm_mload_of_one_limb_q3
    offReg byteReg accReg addrReg memBaseReg base
    (mload_region_step_q3 offReg byteReg accReg addrReg memBaseReg
      sp memBase offset d3 capacity contents base
      h_byte_ne_x0 h_acc_ne_x0 hlen hin h_window3)
  have hbody := evm_mload_public_one_limb_sequence_spec_within
    offReg byteReg accReg addrReg memBaseReg base h0 h1 h2 h3
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hs => by
      dsimp only [Fpre] at hs
      rw [mloadRegionMid_unfold]
      sep_perm hs)
    (cpsTripleWithin_weaken (fun _ hs => by
      dsimp only [Fpre]
      sep_perm hs) (fun _ hs => hs) hp)
    hbody

theorem evm_mload_stack_spec_within_composed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord : EvmWord) (rest : List EvmWord)
    (dstOld1 dstOld2 dstOld3 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = dstOld1)
    (h_offset2 : offsetWord.getLimbN 2 = dstOld2)
    (h_offset3 : offsetWord.getLimbN 3 = dstOld3)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_window0 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 24) / 8) + 8))
      (offset.toNat % 8) 24 25 26 27 28 29 30 31)
    (h_window1 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 16) / 8) + 8))
      (offset.toNat % 8) 16 17 18 19 20 21 22 23)
    (h_window2 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 8) / 8) + 8))
      (offset.toNat % 8) 8 9 10 11 12 13 14 15)
    (h_window3 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + 0) / 8) + 8))
      (offset.toNat % 8) 0 1 2 3 4 5 6 7) :
    cpsTripleWithin (2 + (23 + 23 + 23 + 23)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       evmStackIs sp (offsetWord :: rest) ** (byteReg ↦ᵣ byteOld) **
       (accReg ↦ᵣ accOld) ** evmMemoryIs memBase capacity contents)
      (evmStackIs sp (evmMemoryReadWord contents offset.toNat :: rest) **
       ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ (getByteAt contents (offset.toNat + 7)).zeroExtend 64) **
       (accReg ↦ᵣ (evmMemoryReadWord contents offset.toNat).getLimbN 3) **
       evmMemoryIs memBase capacity contents) := by
  have h_cells := evm_mload_region_cells_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase byteOld accOld dstOld1 dstOld2 dstOld3
    capacity contents base h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    hlen hin h_window0 h_window1 h_window2 h_window3
  have h_framed := cpsTripleWithin_frameR
    (evmStackIs (sp + 32) rest) (by pcFree) h_cells
  have hword := mloadStackOutputWordFromDwordPairs_dwordAt_unaligned contents offset hin
  have hbyte := mloadByteFromDwordPair_dwordAt_unaligned
    contents offset 0 7 (by decide) (by decide) (by decide) hin
  have hl0 : (evmMemoryReadWord contents offset.toNat).getLimbN 0 =
      mloadRegionLimb contents offset 24 := by
    rw [← hword, mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs,
        getLimbN_mloadLoadedWordFromDwordPairs_0]
    rfl
  have hl1 : (evmMemoryReadWord contents offset.toNat).getLimbN 1 =
      mloadRegionLimb contents offset 16 := by
    rw [← hword, mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs,
        getLimbN_mloadLoadedWordFromDwordPairs_1]
    rfl
  have hl2 : (evmMemoryReadWord contents offset.toNat).getLimbN 2 =
      mloadRegionLimb contents offset 8 := by
    rw [← hword, mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs,
        getLimbN_mloadLoadedWordFromDwordPairs_2]
    rfl
  have hl3 : (evmMemoryReadWord contents offset.toNat).getLimbN 3 =
      mloadRegionLimb contents offset 0 := by
    rw [← hword, mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs,
        getLimbN_mloadLoadedWordFromDwordPairs_3]
    rfl
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_cons, evmWordIs_sp_limbs_eq sp offsetWord
        offset dstOld1 dstOld2 dstOld3 h_offset0 h_offset1 h_offset2 h_offset3] at hp
      sep_perm hp)
    (fun _ hp => by
      rw [mloadRegionMid_unfold] at hp
      rw [mloadRegionByte7, hbyte] at hp
      rw [evmStackIs_cons, evmWordIs_sp_limbs_eq sp
        (evmMemoryReadWord contents offset.toNat)
        (mloadRegionLimb contents offset 24) (mloadRegionLimb contents offset 16)
        (mloadRegionLimb contents offset 8) (mloadRegionLimb contents offset 0)
        hl0 hl1 hl2 hl3]
      rw [hl3]
      sep_perm hp)
    h_framed

private theorem mload_region_window_byte_fact
    (memBase offset : Word) (contents : List (BitVec 8))
    (halignB : memBase.toNat % 8 = 0)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (j : Nat) (h_j : j < 32) (off : BitVec 12)
    (h_se : signExtend12 off = BitVec.ofNat 64 j) :
    alignToDword ((memBase + offset) + signExtend12 off) =
        memBase + BitVec.ofNat 64 (8 * ((offset.toNat + j) / 8)) ∧
      isValidByteAccess ((memBase + offset) + signExtend12 off) = true ∧
      byteOffset ((memBase + offset) + signExtend12 off) =
        (offset.toNat + j) % 8 := by
  have h_addr : (memBase + offset) + signExtend12 off =
      memBase + BitVec.ofNat 64 (offset.toNat + j) := by
    rw [h_se, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h_off_lt := offset.isLt
    omega
  have h_over : memBase.toNat + (offset.toNat + j) < 2 ^ 64 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [h_addr]
    exact alignToDword_add_ofNat_of_aligned halignB h_over
  · rw [h_addr, isValidByteAccess_eq]
    exact hvalid _ (by omega)
  · rw [h_addr]
    exact byteOffset_add_ofNat_of_aligned halignB h_over

private theorem mload_region_window_byte_conjuncts
    (memBase offset : Word) (contents : List (BitVec 8))
    (halignB : memBase.toNat % 8 = 0)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (w i : Nat) (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24) (h_i : i < 8)
    (off : BitVec 12) (h_se : signExtend12 off = BitVec.ofNat 64 (w + i)) :
    alignToDword ((memBase + offset) + signExtend12 off) =
        mloadDwordPairAddr
          (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8)))
          (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8))
          (offset.toNat % 8) i ∧
      isValidByteAccess ((memBase + offset) + signExtend12 off) = true ∧
      byteOffset ((memBase + offset) + signExtend12 off) =
        (offset.toNat % 8 + i) % 8 := by
  obtain ⟨h_align, h_valid, h_byte⟩ := mload_region_window_byte_fact
    memBase offset contents halignB hbound hvalid hin (w + i) (by omega) off h_se
  refine ⟨?_, h_valid, ?_⟩
  · rw [h_align]
    by_cases h_lo : offset.toNat % 8 + i < 8
    · rw [mloadDwordPairAddr_low _ _ h_lo]
      have h_div : 8 * ((offset.toNat + (w + i)) / 8) =
          8 * ((offset.toNat + w) / 8) := by omega
      rw [h_div]
    · rw [mloadDwordPairAddr_high _ _ (by omega)]
      have h_div : 8 * ((offset.toNat + (w + i)) / 8) =
          8 * ((offset.toNat + w) / 8) + 8 := by omega
      rw [h_div]
  · rw [h_byte]
    omega

theorem mloadLimbWindowOk_region
    (memBase offset : Word) (contents : List (BitVec 8)) (w : Nat)
    (off0 off1 off2 off3 off4 off5 off6 off7 : BitVec 12)
    (halignB : memBase.toNat % 8 = 0)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (h_w_mod : w % 8 = 0) (h_w_le : w ≤ 24)
    (h_se0 : signExtend12 off0 = BitVec.ofNat 64 (w + 0))
    (h_se1 : signExtend12 off1 = BitVec.ofNat 64 (w + 1))
    (h_se2 : signExtend12 off2 = BitVec.ofNat 64 (w + 2))
    (h_se3 : signExtend12 off3 = BitVec.ofNat 64 (w + 3))
    (h_se4 : signExtend12 off4 = BitVec.ofNat 64 (w + 4))
    (h_se5 : signExtend12 off5 = BitVec.ofNat 64 (w + 5))
    (h_se6 : signExtend12 off6 = BitVec.ofNat 64 (w + 6))
    (h_se7 : signExtend12 off7 = BitVec.ofNat 64 (w + 7)) :
    mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8)))
      (memBase + BitVec.ofNat 64 (8 * ((offset.toNat + w) / 8) + 8))
      (offset.toNat % 8) off0 off1 off2 off3 off4 off5 off6 off7 := by
  obtain ⟨a0, v0, b0⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 0 h_w_mod h_w_le (by omega) off0 h_se0
  obtain ⟨a1, v1, b1⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 1 h_w_mod h_w_le (by omega) off1 h_se1
  obtain ⟨a2, v2, b2⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 2 h_w_mod h_w_le (by omega) off2 h_se2
  obtain ⟨a3, v3, b3⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 3 h_w_mod h_w_le (by omega) off3 h_se3
  obtain ⟨a4, v4, b4⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 4 h_w_mod h_w_le (by omega) off4 h_se4
  obtain ⟨a5, v5, b5⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 5 h_w_mod h_w_le (by omega) off5 h_se5
  obtain ⟨a6, v6, b6⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 6 h_w_mod h_w_le (by omega) off6 h_se6
  obtain ⟨a7, v7, b7⟩ := mload_region_window_byte_conjuncts
    memBase offset contents halignB hbound hvalid hin w 7 h_w_mod h_w_le (by omega) off7 h_se7
  exact ⟨a0, v0, b0, a1, v1, b1, a2, v2, b2, a3, v3, b3,
    a4, v4, b4, a5, v5, b5, a6, v6, b6, a7, v7, b7⟩

/-- Canonical region-backed MLOAD stack specification.  It covers every byte
    alignment by peeling and refolding one adjacent dword pair per quarter. -/
theorem evm_mload_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord : EvmWord) (rest : List EvmWord)
    (dstOld1 dstOld2 dstOld3 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = dstOld1)
    (h_offset2 : offsetWord.getLimbN 2 = dstOld2)
    (h_offset3 : offsetWord.getLimbN 3 = dstOld3)
    (h_off_ne_x0 : offReg ≠ .x0) (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (halignB : memBase.toNat % 8 = 0)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (2 + (23 + 23 + 23 + 23)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       evmStackIs sp (offsetWord :: rest) ** (byteReg ↦ᵣ byteOld) **
       (accReg ↦ᵣ accOld) ** evmMemoryIs memBase capacity contents)
      (evmStackIs sp (evmMemoryReadWord contents offset.toNat :: rest) **
       ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ (getByteAt contents (offset.toNat + 7)).zeroExtend 64) **
       (accReg ↦ᵣ (evmMemoryReadWord contents offset.toNat).getLimbN 3) **
       evmMemoryIs memBase capacity contents) := by
  have hw0 := mloadLimbWindowOk_region memBase offset contents 24
    24 25 26 27 28 29 30 31 halignB hbound hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hw1 := mloadLimbWindowOk_region memBase offset contents 16
    16 17 18 19 20 21 22 23 halignB hbound hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hw2 := mloadLimbWindowOk_region memBase offset contents 8
    8 9 10 11 12 13 14 15 halignB hbound hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hw3 := mloadLimbWindowOk_region memBase offset contents 0
    0 1 2 3 4 5 6 7 halignB hbound hvalid hin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact evm_mload_stack_spec_within_composed
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase byteOld accOld offsetWord rest
    dstOld1 dstOld2 dstOld3 capacity contents base
    h_offset0 h_offset1 h_offset2 h_offset3
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0 hlen hin
    hw0 hw1 hw2 hw3

/-! ## Bridges: window-pair byte algebra → region bytes -/

/-- With `start = 0` a window byte comes from the lo dword only, and the
    lo dword of the region at dword-aligned `c` holds bytes `[c, c+8)`. -/
theorem mloadByteFromDwordPair_dwordAt (bs : List (BitVec 8)) (c i : Nat)
    (hiVal : Word) (hi : i < 8) (hin : c + 8 ≤ bs.length) :
    mloadByteFromDwordPair (dwordAt bs c) hiVal 0 i = getByteAt bs (c + i) := by
  rw [mloadByteFromDwordPair_start_zero _ _ hi]
  unfold dwordAt
  rw [extractByte_packBytes _ i hi
    (by rw [List.length_take, List.length_drop]; omega)]
  rw [List.getElem_take, List.getElem_drop]
  unfold getByteAt
  rw [dif_pos (by omega : c + i < bs.length)]

/-- The word the proven MLOAD spec pushes, instantiated with the region's
    window dwords at aligned offset `k`, is the region read
    `evmMemoryReadWord bs k`. The hi dwords are scratch (unread at
    `start = 0`), so they are arbitrary. -/
theorem mloadStackOutputWordFromDwordPairs_dwordAt
    (bs : List (BitVec 8)) (k : Nat) (h0 h1 h2 h3 : Word)
    (hin : k + 32 ≤ bs.length) :
    mloadStackOutputWordFromDwordPairs
      (dwordAt bs (k + 24)) h0 0 (dwordAt bs (k + 16)) h1 0
      (dwordAt bs (k + 8)) h2 0 (dwordAt bs k) h3 0 =
      evmMemoryReadWord bs k := by
  unfold mloadStackOutputWordFromDwordPairs evmMemoryReadWord
  rw [mloadByteFromDwordPair_dwordAt bs k 0 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 1 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 2 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 3 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 4 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 5 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 6 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 7 h3 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 0 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 1 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 2 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 3 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 4 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 5 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 6 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 8) 7 h2 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 0 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 1 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 2 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 3 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 4 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 5 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 6 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 16) 7 h1 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 0 h0 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 1 h0 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 2 h0 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 3 h0 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 4 h0 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 5 h0 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 6 h0 (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs (k + 24) 7 h0 (by omega) (by omega)]
  rw [show k + 0 = k from rfl,
      show k + 8 + 0 = k + 8 from rfl,
      show k + 8 + 1 = k + 9 from by omega,
      show k + 8 + 2 = k + 10 from by omega,
      show k + 8 + 3 = k + 11 from by omega,
      show k + 8 + 4 = k + 12 from by omega,
      show k + 8 + 5 = k + 13 from by omega,
      show k + 8 + 6 = k + 14 from by omega,
      show k + 8 + 7 = k + 15 from by omega,
      show k + 16 + 0 = k + 16 from rfl,
      show k + 16 + 1 = k + 17 from by omega,
      show k + 16 + 2 = k + 18 from by omega,
      show k + 16 + 3 = k + 19 from by omega,
      show k + 16 + 4 = k + 20 from by omega,
      show k + 16 + 5 = k + 21 from by omega,
      show k + 16 + 6 = k + 22 from by omega,
      show k + 16 + 7 = k + 23 from by omega,
      show k + 24 + 0 = k + 24 from rfl,
      show k + 24 + 1 = k + 25 from by omega,
      show k + 24 + 2 = k + 26 from by omega,
      show k + 24 + 3 = k + 27 from by omega,
      show k + 24 + 4 = k + 28 from by omega,
      show k + 24 + 5 = k + 29 from by omega,
      show k + 24 + 6 = k + 30 from by omega,
      show k + 24 + 7 = k + 31 from by omega]

/-- Scratch-register bridge: the packed limb the guest leaves in the
    accumulator is the MSB limb of the region read. -/
theorem mloadPackedLimbFromDwordPair_dwordAt
    (bs : List (BitVec 8)) (k : Nat) (hiVal : Word) (hin : k + 32 ≤ bs.length) :
    mloadPackedLimbFromDwordPair (dwordAt bs k) hiVal 0 =
      (evmMemoryReadWord bs k).getLimbN 3 := by
  unfold mloadPackedLimbFromDwordPair evmMemoryReadWord
  rw [getLimbN_mloadLoadedWordFromBytes_3]
  rw [mloadByteFromDwordPair_dwordAt bs k 0 hiVal (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 1 hiVal (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 2 hiVal (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 3 hiVal (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 4 hiVal (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 5 hiVal (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 6 hiVal (by omega) (by omega),
      mloadByteFromDwordPair_dwordAt bs k 7 hiVal (by omega) (by omega)]
  rw [show k + 0 = k from rfl]

/-! ## Window side conditions from region facts -/

/-- Discharge one aligned (`start = 0`) MLOAD limb window from
    region-placement facts: base and offset dword-aligned, the access
    inside the addressable region, and every region byte a valid guest
    address. `c ∈ {0, 8, 16, 24}` selects the limb; the lo dword is the
    region dword at `k + c` and the hi dword is the (unread) scratch
    dword at `k + (c + 32)`. -/
theorem mloadLimbWindowOk_aligned_region
    (memBase offset : Word) (k c len : Nat)
    (hk : offset.toNat = k)
    (halignB : memBase.toNat % 8 = 0)
    (hk8 : k % 8 = 0) (hc8 : c % 8 = 0) (hc : c ≤ 24)
    (hbound : memBase.toNat + len ≤ 2 ^ 64)
    (hin : k + 64 ≤ len)
    (hvalid : ∀ i : Nat, i < len →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true) :
    mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (k + c))
      (memBase + BitVec.ofNat 64 (k + (c + 32))) 0
      (BitVec.ofNat 12 c) (BitVec.ofNat 12 (c + 1)) (BitVec.ofNat 12 (c + 2))
      (BitVec.ofNat 12 (c + 3)) (BitVec.ofNat 12 (c + 4)) (BitVec.ofNat 12 (c + 5))
      (BitVec.ofNat 12 (c + 6)) (BitVec.ofNat 12 (c + 7)) := by
  have hmb := memBase.isLt
  have hoffl := offset.isLt
  have hptr : memBase + offset = memBase + BitVec.ofNat 64 k := by
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  have halignFact : ∀ m i : Nat, c + i = m → i < 8 →
      alignToDword ((memBase + offset) + BitVec.ofNat 64 m) =
        memBase + BitVec.ofNat 64 (k + c) := by
    intro m i hm hi
    rw [hptr, add_ofNat_add_ofNat,
        alignToDword_add_ofNat_of_aligned halignB (by omega)]
    have hdiv : 8 * ((k + m) / 8) = k + c := by omega
    rw [hdiv]
  have hboFact : ∀ m i : Nat, c + i = m → i < 8 →
      byteOffset ((memBase + offset) + BitVec.ofNat 64 m) = (0 + i) % 8 := by
    intro m i hm hi
    rw [hptr, add_ofNat_add_ofNat,
        byteOffset_add_ofNat_of_aligned halignB (by omega)]
    omega
  have hvalFact : ∀ m i : Nat, c + i = m → i < 8 →
      isValidByteAccess ((memBase + offset) + BitVec.ofNat 64 m) = true := by
    intro m i hm hi
    rw [hptr, add_ofNat_add_ofNat, isValidByteAccess_eq]
    exact hvalid (k + m) (by omega)
  unfold mloadLimbWindowOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact c 0 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact c 0 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact c 0 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact (c + 1) 1 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact (c + 1) 1 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact (c + 1) 1 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact (c + 2) 2 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact (c + 2) 2 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact (c + 2) 2 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact (c + 3) 3 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact (c + 3) 3 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact (c + 3) 3 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact (c + 4) 4 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact (c + 4) 4 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact (c + 4) 4 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact (c + 5) 5 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact (c + 5) 5 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact (c + 5) 5 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact (c + 6) 6 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact (c + 6) 6 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact (c + 6) 6 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega), mloadDwordPairAddr_low _ _ (by omega)]
    exact halignFact (c + 7) 7 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hvalFact (c + 7) 7 rfl (by omega)
  · rw [signExtend12_ofNat_small (by omega)]
    exact hboFact (c + 7) 7 rfl (by omega)


/-- The reframed MLOAD spec at the guest's actual EVM memory slab:
    `memBase = EVM_MEMORY_AREA`, `capacity = EVM_MEMORY_CAPACITY`. The
    alignment/validity/no-wrap side conditions of the generic theorem are
    discharged from the region-placement facts in `StateAssertions`. -/
theorem evm_mload_stack_spec_within_evmMemoryArea
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld byteOld accOld : Word)
    (offsetWord : EvmWord) (rest : List EvmWord)
    (dstOld1 dstOld2 dstOld3 : Word)
    (contents : List (BitVec 8)) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = dstOld1)
    (h_offset2 : offsetWord.getLimbN 2 = dstOld2)
    (h_offset3 : offsetWord.getLimbN 3 = dstOld3)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = EVM_MEMORY_CAPACITY)
    (hin : 8 * (offset.toNat / 8) + 40 ≤ contents.length) :
    cpsTripleWithin (2 + (23 + 23 + 23 + 23)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ Stateless.EVM_MEMORY_AREA) ** (addrReg ↦ᵣ addrOld) **
       evmStackIs sp (offsetWord :: rest) **
       (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       evmMemoryIs Stateless.EVM_MEMORY_AREA EVM_MEMORY_CAPACITY contents)
      (evmStackIs sp (evmMemoryReadWord contents offset.toNat :: rest) **
       ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ Stateless.EVM_MEMORY_AREA) **
       (addrReg ↦ᵣ (Stateless.EVM_MEMORY_AREA + offset)) **
       (byteReg ↦ᵣ (getByteAt contents (offset.toNat + 7)).zeroExtend 64) **
       (accReg ↦ᵣ (evmMemoryReadWord contents offset.toNat).getLimbN 3) **
       evmMemoryIs Stateless.EVM_MEMORY_AREA EVM_MEMORY_CAPACITY contents) := by
  exact evm_mload_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld Stateless.EVM_MEMORY_AREA byteOld accOld
    offsetWord rest dstOld1 dstOld2 dstOld3
    EVM_MEMORY_CAPACITY contents base
    h_offset0 h_offset1 h_offset2 h_offset3
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    hlen EVM_MEMORY_AREA_aligned hin
    (by rw [hlen, EVM_MEMORY_AREA_toNat]; decide)
    (fun i hi => isValidMemAddr_evmMemoryArea (hlen ▸ hi))

/-- The canonical MLOAD window bound is nonvacuous at an ordinary aligned
    offset in the real EVM-memory allocation. -/
theorem mload_precondition_reachable :
    ∃ contents : List (BitVec 8),
      contents.length = EVM_MEMORY_CAPACITY ∧
      8 * (((0 : Word).toNat) / 8) + 40 ≤ contents.length := by
  have h_bound : 8 * (((0 : Word).toNat) / 8) + 40 ≤ EVM_MEMORY_CAPACITY := by
    decide
  refine ⟨List.replicate EVM_MEMORY_CAPACITY 0, by simp, ?_⟩
  simpa only [List.length_replicate] using h_bound

#print axioms evm_mload_stack_spec_within

end EvmAsm.Evm64
