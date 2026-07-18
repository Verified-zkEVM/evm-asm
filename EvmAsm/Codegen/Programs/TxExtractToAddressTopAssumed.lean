/-
  ExtractAssumed packaging substrate.

  - nExtractSteps covers type234 creation/copy E2E (≈949/956).
  - Residual: of_forall pre peels + honesty pure (hdrop/hok/hnext/hcre)
    from extractSuccess; post memIs→memOwn reshape (epiAmbient pattern).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nExtractSteps nTypeSteps)

/-- Matches private `nFrontCreationSteps` in TopFrontE2E. -/
def nFrontCreationSteps' : Nat :=
  (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) + ((1 + 81) + (1 + (1 + 1)))) +
    (((((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)))

/-- Matches private `nFrontCopySteps` in TopFrontE2ECopy. -/
def nFrontCopySteps' : Nat :=
  (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) + ((1 + 81) + (1 + (1 + 1)))) +
    (((((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        ((1 + 1) +
          ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)))

theorem nFrontCreation_le_nExtract : nFrontCreationSteps' ≤ nExtractSteps := by
  simp only [nFrontCreationSteps', nExtractSteps, nTypeSteps]
  omega

theorem nFrontCopy_le_nExtract : nFrontCopySteps' ≤ nExtractSteps := by
  simp only [nFrontCopySteps', nExtractSteps, nTypeSteps]
  omega

#print axioms nFrontCreation_le_nExtract
#print axioms nFrontCopy_le_nExtract

end EvmAsm.Codegen.TxExtractToAddressSpec
