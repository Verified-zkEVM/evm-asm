/-
  EvmAsm.Stateless.SpecRef.PrecompilesTable

  The COMPLETE `PRE_COMPILED_CONTRACTS` dispatch table
  (`execution-specs/src/ethereum/forks/amsterdam/vm/precompiled_contracts/mapping.py`
  `@tests-zkevm@v0.5.0`, `bd8c673`) — all 18 implementations — and the
  full execution seam `elExecute` built from it.

  This supersedes the staging table in `Precompiles.lean` (4
  implementations + reject-on-contact placeholders) and the hybrid
  fallback: with every implementation present, `elExecuteWith` this
  table IS `elExecute` (docs/4ch8f-top-spec.md §4, bead
  `evm-asm-4ch8f.10`), and the seam default (`Stateless.lean` /
  `Guest.lean`) points here.
-/

import EvmAsm.Stateless.SpecRef.PrecompilesKzg
import EvmAsm.Stateless.SpecRef.PrecompilesBlsMap

namespace EvmAsm.Stateless.SpecRef

/-- `PRE_COMPILED_CONTRACTS` (`mapping.py`) — complete. -/
def specRefPrecompilesFull : PrecompileMap :=
  [(ECRECOVER_ADDRESS, pEcrecover),
   (SHA256_ADDRESS, pSha256),
   (RIPEMD160_ADDRESS, pRipemd160),
   (IDENTITY_ADDRESS, pIdentity),
   (MODEXP_ADDRESS, pModexp),
   (ALT_BN128_ADD_ADDRESS, pAltBn128Add),
   (ALT_BN128_MUL_ADDRESS, pAltBn128Mul),
   (ALT_BN128_PAIRING_CHECK_ADDRESS, pAltBn128PairingCheck),
   (BLAKE2F_ADDRESS, pBlake2f),
   (POINT_EVALUATION_ADDRESS, pPointEvaluation),
   (BLS12_G1_ADD_ADDRESS, pBls12G1Add),
   (BLS12_G1_MSM_ADDRESS, pBls12G1Msm),
   (BLS12_G2_ADD_ADDRESS, pBls12G2Add),
   (BLS12_G2_MSM_ADDRESS, pBls12G2Msm),
   (BLS12_PAIRING_ADDRESS, pBls12Pairing),
   (BLS12_MAP_FP_TO_G1_ADDRESS, pBls12MapFpToG1),
   (BLS12_MAP_FP2_TO_G2_ADDRESS, pBls12MapFp2ToG2),
   (P256VERIFY_ADDRESS, pP256Verify)]

/-- THE execution seam: `execute_new_payload_request` over the complete
    precompile table.  No fallback — every rejection is the pinned
    spec's own. -/
def elExecute : ExecutionSeam := elExecuteWith specRefPrecompilesFull

end EvmAsm.Stateless.SpecRef
