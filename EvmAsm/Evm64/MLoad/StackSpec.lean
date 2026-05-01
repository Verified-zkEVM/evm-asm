/-
  EvmAsm.Evm64.MLoad.StackSpec

  Stack-level bridge helpers for MLOAD.
-/

import EvmAsm.Evm64.MLoad.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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

end EvmAsm.Evm64
