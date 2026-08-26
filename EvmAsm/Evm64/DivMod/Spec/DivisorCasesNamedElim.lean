/-
  EvmAsm.Evm64.DivMod.Spec.DivisorCasesNamedElim

  Case eliminator over `EvmWord` using the named shape predicates
  `NkShapeIs`. Convenient downstream pattern for proving any motive in five
  cases: bzero, N1, N2, N3, N4.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.UnifiedDivisorCases
public import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Case eliminator: any motive `P : EvmWord → Sort _` is established for
    every `b` if it holds in each of the five disjoint cases. -/
theorem DivisorLimbCase.elim_named
    {P : EvmWord → Prop}
    (b : EvmWord)
    (hbzero : b = 0 → P b)
    (hn1 : N1ShapeIs b → P b)
    (hn2 : N2ShapeIs b → P b)
    (hn3 : N3ShapeIs b → P b)
    (hn4 : N4ShapeIs b → P b) :
    P b := by
  cases divisorLimbCase b with
  | bzero hbz => exact hbzero hbz
  | n1 hbnz _ hb3z hb2z hb1z hb0nz =>
      exact hn1 ⟨hbnz, hb3z, hb2z, hb1z, hb0nz⟩
  | n2 hbnz _ hb3z hb2z hb1nz =>
      exact hn2 ⟨hbnz, hb3z, hb2z, hb1nz⟩
  | n3 hbnz _ hb3z hb2nz =>
      exact hn3 ⟨hbnz, hb3z, hb2nz⟩
  | n4 hbnz _ hb3nz =>
      exact hn4 ⟨hbnz, hb3nz⟩

end EvmAsm.Evm64
