/-
  EvmAsm.Evm64.DivMod.Spec.N1Harith

  Compact arithmetic helpers for the n=1 DIV path.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Raw final-remainder bound target for the n=1 schoolbook loop. -/
abbrev fullDivN1RemainderLt (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
    EvmWord.val256 b0 b1 b2 b3

/-- Package raw n=1 schoolbook correctness plus a final-remainder bound into
    the arithmetic pair consumed by trial-bundled wrappers. -/
theorem fullDivN1Harith_of_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hrem_lt : fullDivN1RemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 ∧
      fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 := by
  refine ⟨hmulsub, ?_⟩
  exact fullDivN1QuotientOverestimate_of_mulsub_remainder_lt
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt

end EvmAsm.Evm64
