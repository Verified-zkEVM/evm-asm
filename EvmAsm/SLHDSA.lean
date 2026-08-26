/-
  EvmAsm.SLHDSA

  Aggregate module for the formally verified RISC-V (RV64) SLH-DSA (FIPS 205)
  verifier.  Importing this builds the whole development:

  * the ported FIPS 205 specification (`Scheme` and its dependencies),
  * the concrete demonstration instance (`DemoInstance`) and its equivalence
    to the specification (`DemoCorrect`),
  * the SAsm verifier program (`VerifySAsm`), and
  * its functional-correctness proof (`VerifyProof`).
-/

import EvmAsm.SLHDSA.Scheme
import EvmAsm.SLHDSA.DemoInstance
import EvmAsm.SLHDSA.DemoCorrect
import EvmAsm.SLHDSA.VerifySAsm
import EvmAsm.SLHDSA.VerifyProof
