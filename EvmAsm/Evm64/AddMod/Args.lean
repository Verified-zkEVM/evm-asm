/-
  EvmAsm.Evm64.AddMod.Args

  Pure stack-argument bridge for ADDMOD (GH #91).
-/

import EvmAsm.Evm64.EvmWordArith.AddMod

namespace EvmAsm.Evm64
namespace AddModArgs

/-- ADDMOD stack arguments: first addend, second addend, and modulus. -/
structure Args where
  a : EvmWord
  b : EvmWord
  N : EvmWord
  deriving Repr

/-- ADDMOD pops three stack words. -/
def stackArgumentCount : Nat := 3

/-- ADDMOD pushes one result word. -/
def resultCount : Nat := 1

/-- Convenience builder for ADDMOD stack arguments. -/
def addmodArgs (a b N : EvmWord) : Args :=
  { a := a, b := b, N := N }

/-- ADDMOD result computed from decoded stack arguments. -/
def addmodResultFromArgs (args : Args) : EvmWord :=
  EvmWord.addmod args.a args.b args.N

/-- Stack after the ADDMOD result replaces the three operands. -/
def stackAfterAddMod (args : Args) (rest : List EvmWord) : List EvmWord :=
  addmodResultFromArgs args :: rest

theorem stackArgumentCount_eq_three : stackArgumentCount = 3 := rfl

theorem resultCount_eq_one : resultCount = 1 := rfl

theorem addmodArgs_a (a b N : EvmWord) :
    (addmodArgs a b N).a = a := rfl

theorem addmodArgs_b (a b N : EvmWord) :
    (addmodArgs a b N).b = b := rfl

theorem addmodArgs_N (a b N : EvmWord) :
    (addmodArgs a b N).N = N := rfl

theorem addmodResultFromArgs_eq (args : Args) :
    addmodResultFromArgs args = EvmWord.addmod args.a args.b args.N := rfl

theorem stackAfterAddMod_eq (args : Args) (rest : List EvmWord) :
    stackAfterAddMod args rest = addmodResultFromArgs args :: rest := rfl

@[simp] theorem stackAfterAddMod_length (args : Args) (rest : List EvmWord) :
    (stackAfterAddMod args rest).length = rest.length + 1 := by
  simp [stackAfterAddMod]

@[simp] theorem addmodResultFromArgs_zero_modulus (a b : EvmWord) :
    addmodResultFromArgs (addmodArgs a b 0) = 0 := by
  exact EvmWord.addmod_zero a b

end AddModArgs
end EvmAsm.Evm64
