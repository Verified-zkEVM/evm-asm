/-
  EvmAsm.Evm64.CreateArgs

  Pure stack-argument records for CREATE-family opcodes (GH #115).
-/

import EvmAsm.Evm64.EvmWord

namespace EvmAsm.Evm64

namespace CreateArgs

/-- Memory slice containing initcode, described by an EVM offset and byte size. -/
structure InitcodeRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- CREATE stack arguments: value plus initcode memory range. -/
structure Create where
  value : EvmWord
  initcode : InitcodeRange
  deriving Repr

/-- CREATE2 stack arguments: value, initcode memory range, and salt. -/
structure Create2 where
  value : EvmWord
  initcode : InitcodeRange
  salt : EvmWord
  deriving Repr

/-- Opcode family classifier for CREATE-family stack argument decoding. -/
inductive Kind where
  | create
  | create2
  deriving DecidableEq, Repr

/-- The CREATE-family opcode kinds covered by GH #115. -/
def allKinds : List Kind :=
  [.create, .create2]

def argumentCount : Kind → Nat
  | .create => 3
  | .create2 => 4

def resultCount (_kind : Kind) : Nat := 1

def initcodeRangeCount (_kind : Kind) : Nat := 1

def usesSalt : Kind → Bool
  | .create => false
  | .create2 => true

def hasInitcodeRange (_kind : Kind) : Bool := true

theorem createArgumentCount :
    argumentCount .create = 3 := rfl

theorem create2ArgumentCount :
    argumentCount .create2 = 4 := rfl

theorem allKinds_nodup :
    allKinds.Nodup := by
  decide

theorem mem_allKinds (kind : Kind) :
    kind ∈ allKinds := by
  cases kind <;> decide

theorem allKinds_argumentCounts :
    allKinds.map argumentCount = [3, 4] := rfl

theorem resultCount_eq_one (kind : Kind) :
    resultCount kind = 1 := rfl

theorem initcodeRangeCount_eq_one (kind : Kind) :
    initcodeRangeCount kind = 1 := rfl

theorem hasInitcodeRange_eq_true (kind : Kind) :
    hasInitcodeRange kind = true := rfl

theorem argumentCount_eq_three_plus_salt (kind : Kind) :
    argumentCount kind = 3 + if usesSalt kind then 1 else 0 := by
  cases kind <;> rfl

theorem createUsesNoSalt :
    usesSalt .create = false := rfl

theorem create2UsesSalt :
    usesSalt .create2 = true := rfl

theorem usesSalt_iff_create2 (kind : Kind) :
    usesSalt kind = true ↔ kind = .create2 := by
  cases kind <;> decide

theorem not_usesSalt_iff_create (kind : Kind) :
    usesSalt kind = false ↔ kind = .create := by
  cases kind <;> decide

theorem argumentCount_eq_three_iff_create (kind : Kind) :
    argumentCount kind = 3 ↔ kind = .create := by
  cases kind <;> decide

theorem argumentCount_eq_four_iff_create2 (kind : Kind) :
    argumentCount kind = 4 ↔ kind = .create2 := by
  cases kind <;> decide

theorem create2_argumentCount_eq_succ_create :
    argumentCount .create2 = argumentCount .create + 1 := rfl

theorem create_initcode (args : Create) :
    args.initcode = { offset := args.initcode.offset, size := args.initcode.size } := by
  cases args.initcode
  rfl

theorem create2_initcode (args : Create2) :
    args.initcode = { offset := args.initcode.offset, size := args.initcode.size } := by
  cases args.initcode
  rfl

end CreateArgs

end EvmAsm.Evm64
