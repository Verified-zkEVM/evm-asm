/-
  EvmAsm.Evm64.SDiv.Args

  Pure stack-argument bridge for SDIV (GH #90).
-/

module

public import EvmAsm.Evm64.EvmWordArith.SDiv

@[expose] public section

namespace EvmAsm.Evm64
namespace SDivArgs

/-- SDIV stack arguments: dividend and divisor. -/
structure Args where
  dividend : EvmWord
  divisor : EvmWord
  deriving Repr

/-- SDIV pops two stack words: dividend and divisor. -/
def stackArgumentCount : Nat := 2

/-- SDIV pushes one result word. -/
def resultCount : Nat := 1

/-- Convenience builder for SDIV stack arguments. -/
def sdivArgs (dividend divisor : EvmWord) : Args :=
  { dividend := dividend, divisor := divisor }

/-- SDIV result computed from decoded stack arguments. -/
def sdivResultFromArgs (args : Args) : EvmWord :=
  EvmWord.sdiv args.dividend args.divisor

/-- Stack after the SDIV result replaces the two operands. -/
def stackAfterSDiv (args : Args) (rest : List EvmWord) : List EvmWord :=
  sdivResultFromArgs args :: rest

theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl

theorem resultCount_eq_one : resultCount = 1 := rfl

theorem sdivArgs_dividend (dividend divisor : EvmWord) :
    (sdivArgs dividend divisor).dividend = dividend := rfl

theorem sdivArgs_divisor (dividend divisor : EvmWord) :
    (sdivArgs dividend divisor).divisor = divisor := rfl

theorem sdivResultFromArgs_eq (args : Args) :
    sdivResultFromArgs args = EvmWord.sdiv args.dividend args.divisor := rfl

theorem stackAfterSDiv_eq (args : Args) (rest : List EvmWord) :
    stackAfterSDiv args rest = sdivResultFromArgs args :: rest := rfl

@[simp] theorem stackAfterSDiv_length (args : Args) (rest : List EvmWord) :
    (stackAfterSDiv args rest).length = rest.length + 1 := by
  simp [stackAfterSDiv]

@[simp] theorem sdivResultFromArgs_zero_divisor (dividend : EvmWord) :
    sdivResultFromArgs (sdivArgs dividend 0) = 0 := by
  exact EvmWord.sdiv_zero_right

@[simp] theorem sdivResultFromArgs_zero_dividend (divisor : EvmWord) :
    sdivResultFromArgs (sdivArgs 0 divisor) = 0 := by
  exact EvmWord.zero_sdiv_left

theorem sdivResultFromArgs_intMin_neg_one :
    sdivResultFromArgs (sdivArgs (BitVec.intMin 256) (-1)) =
      BitVec.intMin 256 := by
  exact EvmWord.sdiv_intMin_neg_one

theorem sdivResultFromArgs_neg_one_two :
    sdivResultFromArgs (sdivArgs (-1) 2) = 0 := by
  exact EvmWord.sdiv_neg_one_two

theorem sdivResultFromArgs_pos_neg_trunc :
    sdivResultFromArgs (sdivArgs 7 (-2)) = (-3 : EvmWord) := by
  exact EvmWord.sdiv_pos_neg_trunc

theorem sdivResultFromArgs_neg_pos_trunc :
    sdivResultFromArgs (sdivArgs (-7) 2) = (-3 : EvmWord) := by
  exact EvmWord.sdiv_neg_pos_trunc

end SDivArgs
end EvmAsm.Evm64
