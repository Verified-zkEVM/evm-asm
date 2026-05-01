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

end EvmAsm.Evm64
