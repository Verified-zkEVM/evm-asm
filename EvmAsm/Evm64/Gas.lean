/-
  EvmAsm.Evm64.Gas

  Static gas-cost table for the opcode families currently modeled under
  `EvmAsm.Evm64` (GH #117 slice 1).

  The table records Shanghai static/base costs. Dynamic add-ons (EXP byte
  cost, memory expansion, storage cold/warm access, logging data/topic
  costs, etc.) intentionally live outside this first slice.
-/

namespace EvmAsm.Evm64

/-- EVM opcode identifiers for opcode families that already have an
    implementation or specification subtree in `EvmAsm.Evm64`. Parameterized
    families keep their EVM width/index as data so handler code can share one
    gas theorem across all concrete opcodes in the family. -/
inductive EvmOpcode where
  | ADD
  | MUL
  | SUB
  | DIV
  | MOD
  | EXP
  | SIGNEXTEND
  | LT
  | GT
  | SLT
  | SGT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  | SHL
  | SHR
  | SAR
  | POP
  | MLOAD
  | MSTORE
  | MSTORE8
  | MSIZE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | PUSH0
  | PUSH (n : Nat)
  | DUP (n : Nat)
  | SWAP (n : Nat)
  deriving DecidableEq, Repr

namespace EvmOpcode

/-- Valid immediate width for PUSH1 through PUSH32. -/
def validPushWidth (n : Nat) : Bool :=
  1 ≤ n && n ≤ 32

/-- Valid stack slot index for DUP1 through DUP16. -/
def validDupIndex (n : Nat) : Bool :=
  1 ≤ n && n ≤ 16

/-- Valid stack slot index for SWAP1 through SWAP16. -/
def validSwapIndex (n : Nat) : Bool :=
  1 ≤ n && n ≤ 16

/-- Concrete EVM opcode byte when this identifier denotes one bytecode. Invalid
    parameterized identifiers return `none`, keeping the gas table total while
    making bytecode emission validate widths explicitly. -/
def byte? : EvmOpcode → Option Nat
  | ADD => some 0x01
  | MUL => some 0x02
  | SUB => some 0x03
  | DIV => some 0x04
  | MOD => some 0x06
  | EXP => some 0x0a
  | SIGNEXTEND => some 0x0b
  | LT => some 0x10
  | GT => some 0x11
  | SLT => some 0x12
  | SGT => some 0x13
  | EQ => some 0x14
  | ISZERO => some 0x15
  | AND => some 0x16
  | OR => some 0x17
  | XOR => some 0x18
  | NOT => some 0x19
  | BYTE => some 0x1a
  | SHL => some 0x1b
  | SHR => some 0x1c
  | SAR => some 0x1d
  | POP => some 0x50
  | MLOAD => some 0x51
  | MSTORE => some 0x52
  | MSTORE8 => some 0x53
  | MSIZE => some 0x59
  | CALLDATALOAD => some 0x35
  | CALLDATASIZE => some 0x36
  | CALLDATACOPY => some 0x37
  | PUSH0 => some 0x5f
  | PUSH n => if validPushWidth n then some (0x5f + n) else none
  | DUP n => if validDupIndex n then some (0x7f + n) else none
  | SWAP n => if validSwapIndex n then some (0x8f + n) else none

/-- Shanghai static/base gas cost. Costs that also have dynamic components
    return only the fixed part charged before the dynamic add-on. -/
def staticGasCost : EvmOpcode → Nat
  | ADD => 3
  | MUL => 5
  | SUB => 3
  | DIV => 5
  | MOD => 5
  | EXP => 10
  | SIGNEXTEND => 5
  | LT => 3
  | GT => 3
  | SLT => 3
  | SGT => 3
  | EQ => 3
  | ISZERO => 3
  | AND => 3
  | OR => 3
  | XOR => 3
  | NOT => 3
  | BYTE => 3
  | SHL => 3
  | SHR => 3
  | SAR => 3
  | POP => 2
  | MLOAD => 3
  | MSTORE => 3
  | MSTORE8 => 3
  | MSIZE => 2
  | CALLDATALOAD => 3
  | CALLDATASIZE => 2
  | CALLDATACOPY => 3
  | PUSH0 => 2
  | PUSH _ => 3
  | DUP _ => 3
  | SWAP _ => 3

theorem staticGasCost_PUSH (n : Nat) :
    staticGasCost (PUSH n) = 3 := rfl

theorem staticGasCost_DUP (n : Nat) :
    staticGasCost (DUP n) = 3 := rfl

theorem staticGasCost_SWAP (n : Nat) :
    staticGasCost (SWAP n) = 3 := rfl

theorem byte?_PUSH_of_valid {n : Nat} (h : validPushWidth n = true) :
    byte? (PUSH n) = some (0x5f + n) := by
  simp [byte?, h]

theorem byte?_DUP_of_valid {n : Nat} (h : validDupIndex n = true) :
    byte? (DUP n) = some (0x7f + n) := by
  simp [byte?, h]

theorem byte?_SWAP_of_valid {n : Nat} (h : validSwapIndex n = true) :
    byte? (SWAP n) = some (0x8f + n) := by
  simp [byte?, h]

theorem byte?_PUSH0 : byte? PUSH0 = some 0x5f := rfl

theorem staticGasCost_push0 : staticGasCost PUSH0 = 2 := rfl

theorem staticGasCost_msize : staticGasCost MSIZE = 2 := rfl

theorem staticGasCost_calldataLoad : staticGasCost CALLDATALOAD = 3 := rfl

theorem staticGasCost_calldataSize : staticGasCost CALLDATASIZE = 2 := rfl

theorem staticGasCost_calldataCopyBase : staticGasCost CALLDATACOPY = 3 := rfl

theorem staticGasCost_expBase : staticGasCost EXP = 10 := rfl

end EvmOpcode

end EvmAsm.Evm64
