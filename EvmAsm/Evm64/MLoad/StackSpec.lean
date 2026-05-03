/-
  EvmAsm.Evm64.MLoad.StackSpec

  Stack-level bridge helpers for MLOAD.
-/

import EvmAsm.Evm64.MLoad.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for all four MLOAD output-limb byte-pack blocks, placed after the
    two-instruction address prologue. -/
def mloadFourLimbsCode
    (addrReg byteReg accReg : Reg) (base : Word) : CodeReq :=
  (mloadOneLimbCode addrReg byteReg accReg
      24 25 26 27 28 29 30 31 0 (base + 8)).union
    ((mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100)).union
      ((mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)).union
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284))))

/-- Compact CodeReq for the full MLOAD program: address prologue followed by
    the four unaligned output-limb blocks. -/
def mloadStackCode
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (mloadPrologueCode offReg addrReg memBaseReg base).union
    (mloadFourLimbsCode addrReg byteReg accReg base)

theorem mloadStackCode_prologue_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mloadPrologueCode offReg addrReg memBaseReg base) a = some i →
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  unfold mloadStackCode
  exact CodeReq.union_mono_left

theorem mload_prologue_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  exact cpsTripleWithin_extend_code
    (h := mload_prologue_spec_within offReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0)
    (hmono := mloadStackCode_prologue_sub offReg byteReg accReg addrReg memBaseReg base)

/--
  The 256-bit value loaded by MLOAD when each output limb is assembled from
  an adjacent low/high dword pair. The four limbs are stored in EVM-stack
  little-endian order: limb 0 at `sp`, limb 3 at `sp + 24`.
-/
def mloadLoadedWordFromDwordPairs
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) : EvmWord :=
  mloadLoadedWord
    (mloadPackedLimbFromDwordPair lo0 hi0 start0)
    (mloadPackedLimbFromDwordPair lo1 hi1 start1)
    (mloadPackedLimbFromDwordPair lo2 hi2 start2)
    (mloadPackedLimbFromDwordPair lo3 hi3 start3)

theorem getLimbN_mloadLoadedWordFromDwordPairs_0
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 0 =
    mloadPackedLimbFromDwordPair lo0 hi0 start0 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_0]

theorem getLimbN_mloadLoadedWordFromDwordPairs_1
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 1 =
    mloadPackedLimbFromDwordPair lo1 hi1 start1 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_1]

theorem getLimbN_mloadLoadedWordFromDwordPairs_2
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 2 =
    mloadPackedLimbFromDwordPair lo2 hi2 start2 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_2]

theorem getLimbN_mloadLoadedWordFromDwordPairs_3
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 3 =
    mloadPackedLimbFromDwordPair lo3 hi3 start3 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_3]

/--
  Fold the four unaligned dword-pair MLOAD destination limbs into one
  `evmWordIs` assertion.
-/
theorem mloadLoadedWordFromDwordPairs_evmWordIs_fold
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair lo0 hi0 start0) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair lo1 hi1 start1) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair lo2 hi2 start2) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair lo3 hi3 start3)) =
    evmWordIs sp
      (mloadLoadedWordFromDwordPairs
        lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3) := by
  rw [mloadLoadedWordFromDwordPairs, mloadLoadedWord_evmWordIs_fold]

/--
  The dword-pair representation used by the unaligned executable proof is the
  same byte-level MLOAD word as `mloadLoadedWordFromBytes`. Pair 3 supplies
  bytes 0..7 (the most-significant EVM bytes); pair 0 supplies bytes 24..31
  (the least-significant EVM bytes stored at stack limb 0).
-/
theorem mloadLoadedWordFromDwordPairs_eq_mloadLoadedWordFromBytes
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 =
    mloadLoadedWordFromBytes
      (mloadByteFromDwordPair lo3 hi3 start3 0)
      (mloadByteFromDwordPair lo3 hi3 start3 1)
      (mloadByteFromDwordPair lo3 hi3 start3 2)
      (mloadByteFromDwordPair lo3 hi3 start3 3)
      (mloadByteFromDwordPair lo3 hi3 start3 4)
      (mloadByteFromDwordPair lo3 hi3 start3 5)
      (mloadByteFromDwordPair lo3 hi3 start3 6)
      (mloadByteFromDwordPair lo3 hi3 start3 7)
      (mloadByteFromDwordPair lo2 hi2 start2 0)
      (mloadByteFromDwordPair lo2 hi2 start2 1)
      (mloadByteFromDwordPair lo2 hi2 start2 2)
      (mloadByteFromDwordPair lo2 hi2 start2 3)
      (mloadByteFromDwordPair lo2 hi2 start2 4)
      (mloadByteFromDwordPair lo2 hi2 start2 5)
      (mloadByteFromDwordPair lo2 hi2 start2 6)
      (mloadByteFromDwordPair lo2 hi2 start2 7)
      (mloadByteFromDwordPair lo1 hi1 start1 0)
      (mloadByteFromDwordPair lo1 hi1 start1 1)
      (mloadByteFromDwordPair lo1 hi1 start1 2)
      (mloadByteFromDwordPair lo1 hi1 start1 3)
      (mloadByteFromDwordPair lo1 hi1 start1 4)
      (mloadByteFromDwordPair lo1 hi1 start1 5)
      (mloadByteFromDwordPair lo1 hi1 start1 6)
      (mloadByteFromDwordPair lo1 hi1 start1 7)
      (mloadByteFromDwordPair lo0 hi0 start0 0)
      (mloadByteFromDwordPair lo0 hi0 start0 1)
      (mloadByteFromDwordPair lo0 hi0 start0 2)
      (mloadByteFromDwordPair lo0 hi0 start0 3)
      (mloadByteFromDwordPair lo0 hi0 start0 4)
      (mloadByteFromDwordPair lo0 hi0 start0 5)
      (mloadByteFromDwordPair lo0 hi0 start0 6)
      (mloadByteFromDwordPair lo0 hi0 start0 7) := by
  rfl

/--
  Direct stack fold for the unaligned executable result into the byte-level
  MLOAD semantic word.
-/
theorem mloadLoadedWordFromDwordPairs_evmWordIs_fold_bytes
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair lo0 hi0 start0) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair lo1 hi1 start1) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair lo2 hi2 start2) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair lo3 hi3 start3)) =
    evmWordIs sp
      (mloadLoadedWordFromBytes
        (mloadByteFromDwordPair lo3 hi3 start3 0)
        (mloadByteFromDwordPair lo3 hi3 start3 1)
        (mloadByteFromDwordPair lo3 hi3 start3 2)
        (mloadByteFromDwordPair lo3 hi3 start3 3)
        (mloadByteFromDwordPair lo3 hi3 start3 4)
        (mloadByteFromDwordPair lo3 hi3 start3 5)
        (mloadByteFromDwordPair lo3 hi3 start3 6)
        (mloadByteFromDwordPair lo3 hi3 start3 7)
        (mloadByteFromDwordPair lo2 hi2 start2 0)
        (mloadByteFromDwordPair lo2 hi2 start2 1)
        (mloadByteFromDwordPair lo2 hi2 start2 2)
        (mloadByteFromDwordPair lo2 hi2 start2 3)
        (mloadByteFromDwordPair lo2 hi2 start2 4)
        (mloadByteFromDwordPair lo2 hi2 start2 5)
        (mloadByteFromDwordPair lo2 hi2 start2 6)
        (mloadByteFromDwordPair lo2 hi2 start2 7)
        (mloadByteFromDwordPair lo1 hi1 start1 0)
        (mloadByteFromDwordPair lo1 hi1 start1 1)
        (mloadByteFromDwordPair lo1 hi1 start1 2)
        (mloadByteFromDwordPair lo1 hi1 start1 3)
        (mloadByteFromDwordPair lo1 hi1 start1 4)
        (mloadByteFromDwordPair lo1 hi1 start1 5)
        (mloadByteFromDwordPair lo1 hi1 start1 6)
        (mloadByteFromDwordPair lo1 hi1 start1 7)
        (mloadByteFromDwordPair lo0 hi0 start0 0)
        (mloadByteFromDwordPair lo0 hi0 start0 1)
        (mloadByteFromDwordPair lo0 hi0 start0 2)
        (mloadByteFromDwordPair lo0 hi0 start0 3)
        (mloadByteFromDwordPair lo0 hi0 start0 4)
        (mloadByteFromDwordPair lo0 hi0 start0 5)
        (mloadByteFromDwordPair lo0 hi0 start0 6)
        (mloadByteFromDwordPair lo0 hi0 start0 7)) := by
  rw [mloadLoadedWordFromDwordPairs_evmWordIs_fold]
  rw [mloadLoadedWordFromDwordPairs_eq_mloadLoadedWordFromBytes]

/--
  The byte-level MLOAD result word described by the four unaligned dword-pair
  source windows. This names the semantic word used by the final stack-level
  MLOAD theorem without exposing all 32 byte projections in that theorem's
  postcondition.
-/
def mloadStackOutputWordFromDwordPairs
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) : EvmWord :=
  mloadLoadedWordFromBytes
    (mloadByteFromDwordPair lo3 hi3 start3 0)
    (mloadByteFromDwordPair lo3 hi3 start3 1)
    (mloadByteFromDwordPair lo3 hi3 start3 2)
    (mloadByteFromDwordPair lo3 hi3 start3 3)
    (mloadByteFromDwordPair lo3 hi3 start3 4)
    (mloadByteFromDwordPair lo3 hi3 start3 5)
    (mloadByteFromDwordPair lo3 hi3 start3 6)
    (mloadByteFromDwordPair lo3 hi3 start3 7)
    (mloadByteFromDwordPair lo2 hi2 start2 0)
    (mloadByteFromDwordPair lo2 hi2 start2 1)
    (mloadByteFromDwordPair lo2 hi2 start2 2)
    (mloadByteFromDwordPair lo2 hi2 start2 3)
    (mloadByteFromDwordPair lo2 hi2 start2 4)
    (mloadByteFromDwordPair lo2 hi2 start2 5)
    (mloadByteFromDwordPair lo2 hi2 start2 6)
    (mloadByteFromDwordPair lo2 hi2 start2 7)
    (mloadByteFromDwordPair lo1 hi1 start1 0)
    (mloadByteFromDwordPair lo1 hi1 start1 1)
    (mloadByteFromDwordPair lo1 hi1 start1 2)
    (mloadByteFromDwordPair lo1 hi1 start1 3)
    (mloadByteFromDwordPair lo1 hi1 start1 4)
    (mloadByteFromDwordPair lo1 hi1 start1 5)
    (mloadByteFromDwordPair lo1 hi1 start1 6)
    (mloadByteFromDwordPair lo1 hi1 start1 7)
    (mloadByteFromDwordPair lo0 hi0 start0 0)
    (mloadByteFromDwordPair lo0 hi0 start0 1)
    (mloadByteFromDwordPair lo0 hi0 start0 2)
    (mloadByteFromDwordPair lo0 hi0 start0 3)
    (mloadByteFromDwordPair lo0 hi0 start0 4)
    (mloadByteFromDwordPair lo0 hi0 start0 5)
    (mloadByteFromDwordPair lo0 hi0 start0 6)
    (mloadByteFromDwordPair lo0 hi0 start0 7)

theorem mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    mloadStackOutputWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 =
    mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 := by
  rw [mloadStackOutputWordFromDwordPairs]
  rw [mloadLoadedWordFromDwordPairs_eq_mloadLoadedWordFromBytes]

/--
  Named stack postcondition for the four output limbs of unaligned MLOAD.
  The executable composition can target this compact assertion and use
  `mloadStackOutputPost_evmWordIs_fold` to consume the four produced cells.
-/
@[irreducible]
def mloadStackOutputPost
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) : Assertion :=
  evmWordIs sp
    (mloadStackOutputWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3)

theorem mloadStackOutputPost_unfold
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    mloadStackOutputPost sp
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 =
    evmWordIs sp
      (mloadStackOutputWordFromDwordPairs
        lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3) := by
  delta mloadStackOutputPost
  rfl

theorem mloadStackOutputPost_evmWordIs_fold
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair lo0 hi0 start0) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair lo1 hi1 start1) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair lo2 hi2 start2) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair lo3 hi3 start3)) =
    mloadStackOutputPost sp
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 := by
  rw [mloadStackOutputPost_unfold]
  rw [mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs]
  rw [mloadLoadedWordFromDwordPairs_evmWordIs_fold]

/--
  The 256-bit value loaded by a 32-byte unaligned MLOAD window spanning five
  consecutive RV64 dwords. The single `start` byte offset applies to each
  8-byte EVM limb window; adjacent limbs share boundary dwords.
-/
def mloadLoadedWordFromFiveDwords
    (d0 d1 d2 d3 d4 : Word) (start : Nat) : EvmWord :=
  mloadLoadedWordFromDwordPairs
    d3 d4 start
    d2 d3 start
    d1 d2 start
    d0 d1 start

theorem mloadLoadedWordFromFiveDwords_eq_mloadLoadedWordFromDwordPairs
    (d0 d1 d2 d3 d4 : Word) (start : Nat) :
    mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start =
      mloadLoadedWordFromDwordPairs
        d3 d4 start
        d2 d3 start
        d1 d2 start
        d0 d1 start := by
  rfl

/--
  Fold the four output limbs from a five-dword unaligned MLOAD source window
  into one `evmWordIs` assertion.
-/
theorem mloadLoadedWordFromFiveDwords_evmWordIs_fold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair d3 d4 start) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair d2 d3 start) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair d1 d2 start) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair d0 d1 start)) =
    evmWordIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start) := by
  rw [mloadLoadedWordFromFiveDwords_eq_mloadLoadedWordFromDwordPairs]
  rw [mloadLoadedWordFromDwordPairs_evmWordIs_fold]

/--
  Compact stack postcondition for the five-dword unaligned MLOAD source shape.
-/
@[irreducible]
def mloadStackOutputPostFiveDwords
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) : Assertion :=
  evmWordIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start)

theorem mloadStackOutputPostFiveDwords_unfold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) :
    mloadStackOutputPostFiveDwords sp d0 d1 d2 d3 d4 start =
      evmWordIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start) := by
  delta mloadStackOutputPostFiveDwords
  rfl

theorem mloadStackOutputPostFiveDwords_evmWordIs_fold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair d3 d4 start) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair d2 d3 start) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair d1 d2 start) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair d0 d1 start)) =
    mloadStackOutputPostFiveDwords sp d0 d1 d2 d3 d4 start := by
  rw [mloadStackOutputPostFiveDwords_unfold]
  rw [mloadLoadedWordFromFiveDwords_evmWordIs_fold]

end EvmAsm.Evm64
