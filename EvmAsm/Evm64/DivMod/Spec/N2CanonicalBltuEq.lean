/-
  EvmAsm.Evm64.DivMod.Spec.N2CanonicalBltuEq

  Definitional unfolding equation lemmas for the canonical N2 bltu values.
  Simp lemmas for downstream normalization of the canonical predicates.
-/

import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[simp] theorem n2V4CanonicalBltu2_eq (a b : EvmWord) :
    n2V4CanonicalBltu2 a b =
      BitVec.ult
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 :=
  rfl

@[simp] theorem n2V4CanonicalBltu1_eq (a b : EvmWord) :
    n2V4CanonicalBltu1 a b =
      BitVec.ult
        (fullDivN2R2V4 (n2V4CanonicalBltu2 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 :=
  rfl

@[simp] theorem n2V4CanonicalBltu0_eq (a b : EvmWord) :
    n2V4CanonicalBltu0 a b =
      BitVec.ult
        (fullDivN2R1V4 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 :=
  rfl

end EvmAsm.Evm64
