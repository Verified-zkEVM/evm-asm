/-
  EvmAsm.Evm64.SMod.Args

  Pure stack-argument bridge for SMOD (GH #90).
-/

module

public import EvmAsm.Evm64.EvmWordArith.SMod

@[expose] public section

namespace EvmAsm.Evm64
namespace SModArgs

/-- SMOD stack arguments: dividend and divisor. -/
structure Args where
  dividend : EvmWord
  divisor : EvmWord
  deriving Repr

/-- SMOD pops two stack words: dividend and divisor. -/
def stackArgumentCount : Nat := 2

/-- SMOD pushes one result word. -/
def resultCount : Nat := 1

/-- Convenience builder for SMOD stack arguments. -/
def smodArgs (dividend divisor : EvmWord) : Args :=
  { dividend := dividend, divisor := divisor }

/-- SMOD result computed from decoded stack arguments. -/
def smodResultFromArgs (args : Args) : EvmWord :=
  EvmWord.smod args.dividend args.divisor

/-- Stack after the SMOD result replaces the two operands. -/
def stackAfterSMod (args : Args) (rest : List EvmWord) : List EvmWord :=
  smodResultFromArgs args :: rest

theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl

theorem resultCount_eq_one : resultCount = 1 := rfl

theorem smodArgs_dividend (dividend divisor : EvmWord) :
    (smodArgs dividend divisor).dividend = dividend := rfl

theorem smodArgs_divisor (dividend divisor : EvmWord) :
    (smodArgs dividend divisor).divisor = divisor := rfl

theorem smodResultFromArgs_eq (args : Args) :
    smodResultFromArgs args = EvmWord.smod args.dividend args.divisor := rfl

theorem stackAfterSMod_eq (args : Args) (rest : List EvmWord) :
    stackAfterSMod args rest = smodResultFromArgs args :: rest := rfl

@[simp] theorem stackAfterSMod_length (args : Args) (rest : List EvmWord) :
    (stackAfterSMod args rest).length = rest.length + 1 := by
  simp [stackAfterSMod]

@[simp] theorem smodResultFromArgs_zero_divisor (dividend : EvmWord) :
    smodResultFromArgs (smodArgs dividend 0) = 0 := by
  exact EvmWord.smod_zero_right

@[simp] theorem smodResultFromArgs_zero_dividend (divisor : EvmWord) :
    smodResultFromArgs (smodArgs 0 divisor) = 0 := by
  exact EvmWord.zero_smod_left

theorem smodResultFromArgs_intMin_neg_one :
    smodResultFromArgs (smodArgs (BitVec.intMin 256) (-1)) = 0 := by
  exact EvmWord.smod_intMin_neg_one

theorem smodResultFromArgs_neg_pos_sign :
    smodResultFromArgs (smodArgs (-3) 2) = (-1 : EvmWord) := by
  exact EvmWord.smod_neg_pos_sign

theorem smodResultFromArgs_pos_neg_sign :
    smodResultFromArgs (smodArgs 3 (-2)) = (1 : EvmWord) := by
  exact EvmWord.smod_pos_neg_sign

theorem smodResultFromArgs_neg_neg_sign :
    smodResultFromArgs (smodArgs (-3) (-2)) = (-1 : EvmWord) := by
  exact EvmWord.smod_neg_neg_sign

end SModArgs
end EvmAsm.Evm64
