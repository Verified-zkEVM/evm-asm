/-
  EvmAsm.Evm64

  Root import file for the 64-bit EVM opcode implementations (RV64IM).
-/

-- Foundations (Basic and Stack are transitively imported by every
-- opcode Program file via Stack → Basic).
import EvmAsm.Evm64.CodeRegion

-- Stack operations
import EvmAsm.Evm64.Pop
import EvmAsm.Evm64.Push0
import EvmAsm.Evm64.Push
import EvmAsm.Evm64.Dup
import EvmAsm.Evm64.Swap

-- Bitwise operations
import EvmAsm.Evm64.And
import EvmAsm.Evm64.Or
import EvmAsm.Evm64.Xor
import EvmAsm.Evm64.Not

-- Arithmetic (Add.Spec transitively imports EvmWordArith)
import EvmAsm.Evm64.Add
import EvmAsm.Evm64.Sub

-- EvmWordArith umbrella — pulls in helpers (AddbackPinning,
-- Div128NoWrapDischarge → Div128PhaseNoWrap) used by DivMod V4.
-- Most leaves are already transitively reached via Add/DivMod; this
-- import wires the remaining stragglers so they participate in the
-- visible module graph.
import EvmAsm.Evm64.EvmWordArith

-- Comparisons (Lt.Spec transitively imports Compare.LimbSpec)
import EvmAsm.Evm64.Lt
import EvmAsm.Evm64.Gt
import EvmAsm.Evm64.Eq
import EvmAsm.Evm64.IsZero
import EvmAsm.Evm64.Slt
import EvmAsm.Evm64.Sgt

-- Shifts
import EvmAsm.Evm64.Shift

-- Byte and SignExtend
import EvmAsm.Evm64.Byte
import EvmAsm.Evm64.SignExtend

-- Multiply
import EvmAsm.Evm64.Multiply

-- Exp (skeleton — GH #92, square-and-multiply over 256-bit exponent)
import EvmAsm.Evm64.Exp

-- DivMod (Knuth Algorithm D)
import EvmAsm.Evm64.DivMod

-- Calling convention (LP64)
import EvmAsm.Evm64.CallingConvention

-- Execution-context structure (#100 slice 1; envIs assertion lands in slice 3)
import EvmAsm.Evm64.Environment
import EvmAsm.Evm64.Environment.Layout
import EvmAsm.Evm64.Environment.Assertion

-- EVM memory model (issue #99)
import EvmAsm.Evm64.Memory
import EvmAsm.Evm64.MSize
import EvmAsm.Evm64.MStore8
import EvmAsm.Evm64.MLoad
