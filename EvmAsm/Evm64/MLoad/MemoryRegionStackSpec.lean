/-
  EvmAsm.Evm64.MLoad.MemoryRegionStackSpec

  The public MLOAD stack spec restated against `evmMemoryIs` — the
  load-bearing check that `evmMemoryIs` (EvmAsm/Evm64/StateAssertions.lean)
  describes the guest's *actual* EVM memory region.

  `evm_mload_stack_spec_within` frames against eight raw dword cells (four
  lo/hi window pairs governed by `mloadLimbWindowOk`). Here we consume the
  proven spec and repackage that footprint: the pre/post own a single
  `evmMemoryIs memBase capacity contents` resource, the touched 64-byte
  dword window is peeled out via `evmMemoryIs_peel_window64`, the window
  side conditions are discharged from the region-placement facts, and the
  value pushed on the EVM stack is shown to be
  `evmMemoryReadWord contents offset.toNat` — the 32 bytes at the
  requested offset, big-endian, exactly the EVM-spec MLOAD result.

  Scope: the dword-aligned case (`start = 0`, i.e. `offset ≡ 0 (mod 8)`
  with a dword-aligned `memBase`). For `start ≠ 0` adjacent limb windows
  of the public spec share a dword cell, so its separated eight-cell
  precondition is only instantiable in the aligned case; the aligned spec
  is the one the proven pipeline exercises.
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

/-! ## The reframed public MLOAD stack spec -/

/-- **MLOAD against `evmMemoryIs`** (aligned case). The proven public
    MLOAD stack spec `evm_mload_stack_spec_within`, with its raw
    eight-dword window footprint repackaged as the single region resource
    `evmMemoryIs memBase capacity contents`: the region is unchanged, and
    the word pushed on the EVM stack is `evmMemoryReadWord contents
    offset.toNat` — the 32 region bytes at the requested offset. This is
    the honesty gate for `evmMemoryIs`: it is derived from (not assumed
    of) the guest's proven MLOAD routine.

    Region side conditions: `contents` covers the full static allocation
    (`hlen`), the region is addressable without wrap (`hbound`) and valid
    (`hvalid` — discharged by `isValidMemAddr_evmMemoryArea` for the real
    `EVM_MEMORY_AREA` slab, see `evm_mload_stack_spec_within_evmMemoryArea`),
    and the access window `[offset, offset+64)` is in bounds (`hin` — the
    extra 32 bytes past the loaded word are the four scratch hi-dwords of
    the guest's limb windows). -/
theorem evm_mload_stack_spec_within_evmMemoryIs
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord : EvmWord) (rest : List EvmWord)
    (dstOld1 dstOld2 dstOld3 : Word)
    (capacity : Nat) (contents : List (BitVec 8)) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = dstOld1)
    (h_offset2 : offsetWord.getLimbN 2 = dstOld2)
    (h_offset3 : offsetWord.getLimbN 3 = dstOld3)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (hlen : contents.length = capacity)
    (halignB : memBase.toNat % 8 = 0)
    (hoff8 : offset.toNat % 8 = 0)
    (hin : offset.toNat + 64 ≤ contents.length)
    (hbound : memBase.toNat + contents.length ≤ 2 ^ 64)
    (hvalid : ∀ i : Nat, i < contents.length →
      isValidMemAddr (memBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (2 + (23 + 23 + 23 + 23)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       evmStackIs sp (offsetWord :: rest) **
       (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
       evmMemoryIs memBase capacity contents)
      (evmStackIs sp (evmMemoryReadWord contents offset.toNat :: rest) **
       ((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (byteReg ↦ᵣ (getByteAt contents (offset.toNat + 7)).zeroExtend 64) **
       (accReg ↦ᵣ (evmMemoryReadWord contents offset.toNat).getLimbN 3) **
       evmMemoryIs memBase capacity contents) := by
  set k := offset.toNat with hkdef
  -- The four aligned limb windows, coerced to the numeral-offset shapes
  -- the public spec expects (definitional equalities only).
  have hw0 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (k + 24)) (memBase + BitVec.ofNat 64 (k + 56)) 0
      24 25 26 27 28 29 30 31 :=
    mloadLimbWindowOk_aligned_region memBase offset k 24 contents.length rfl
      halignB hoff8 (by omega) (by omega) hbound hin hvalid
  have hw1 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (k + 16)) (memBase + BitVec.ofNat 64 (k + 48)) 0
      16 17 18 19 20 21 22 23 :=
    mloadLimbWindowOk_aligned_region memBase offset k 16 contents.length rfl
      halignB hoff8 (by omega) (by omega) hbound hin hvalid
  have hw2 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 (k + 8)) (memBase + BitVec.ofNat 64 (k + 40)) 0
      8 9 10 11 12 13 14 15 :=
    mloadLimbWindowOk_aligned_region memBase offset k 8 contents.length rfl
      halignB hoff8 (by omega) (by omega) hbound hin hvalid
  have hw3 : mloadLimbWindowOk (memBase + offset)
      (memBase + BitVec.ofNat 64 k) (memBase + BitVec.ofNat 64 (k + 32)) 0
      0 1 2 3 4 5 6 7 :=
    mloadLimbWindowOk_aligned_region memBase offset k 0 contents.length rfl
      halignB hoff8 (by omega) (by omega) hbound hin hvalid
  -- The proven public spec, instantiated with the region's window dwords.
  have hCore := evm_mload_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase byteOld accOld offsetWord rest
    dstOld1 dstOld2 dstOld3
    (memBase + BitVec.ofNat 64 (k + 24)) (memBase + BitVec.ofNat 64 (k + 56))
    (dwordAt contents (k + 24)) (dwordAt contents (k + 56))
    (memBase + BitVec.ofNat 64 (k + 16)) (memBase + BitVec.ofNat 64 (k + 48))
    (dwordAt contents (k + 16)) (dwordAt contents (k + 48))
    (memBase + BitVec.ofNat 64 (k + 8)) (memBase + BitVec.ofNat 64 (k + 40))
    (dwordAt contents (k + 8)) (dwordAt contents (k + 40))
    (memBase + BitVec.ofNat 64 k) (memBase + BitVec.ofNat 64 (k + 32))
    (dwordAt contents k) (dwordAt contents (k + 32))
    0 base
    h_offset0 h_offset1 h_offset2 h_offset3
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    hw0 hw1 hw2 hw3
  dsimp only at hCore
  -- Frame the untouched front/tail of the region around the core spec.
  have hFramed := cpsTripleWithin_frameR
    (bytesRegion memBase (contents.take k) **
     bytesRegion (memBase + BitVec.ofNat 64 (k + 64)) (contents.drop (k + 64)))
    (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
    hCore
  -- Peel/fold equality for the region and value bridges.
  have hpeel := evmMemoryIs_peel_window64 memBase capacity k contents hlen hoff8 hin
  have hword := mloadStackOutputWordFromDwordPairs_dwordAt contents k
    (dwordAt contents (k + 56)) (dwordAt contents (k + 48))
    (dwordAt contents (k + 40)) (dwordAt contents (k + 32)) (by omega)
  have hbyte := mloadByteFromDwordPair_dwordAt contents k 7
    (dwordAt contents (k + 32)) (by omega) (by omega)
  have hlimb := mloadPackedLimbFromDwordPair_dwordAt contents k
    (dwordAt contents (k + 32)) (by omega)
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [hpeel] at hp
      sep_perm hp)
    (fun _ hq => by
      rw [hword, hbyte, hlimb] at hq
      rw [hpeel]
      sep_perm hq)
    hFramed

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
    (hoff8 : offset.toNat % 8 = 0)
    (hin : offset.toNat + 64 ≤ contents.length) :
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
  exact evm_mload_stack_spec_within_evmMemoryIs
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld Stateless.EVM_MEMORY_AREA byteOld accOld
    offsetWord rest dstOld1 dstOld2 dstOld3
    EVM_MEMORY_CAPACITY contents base
    h_offset0 h_offset1 h_offset2 h_offset3
    h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
    hlen EVM_MEMORY_AREA_aligned hoff8 hin
    (by rw [hlen, EVM_MEMORY_AREA_toNat]; decide)
    (fun i hi => isValidMemAddr_evmMemoryArea (hlen ▸ hi))

end EvmAsm.Evm64
