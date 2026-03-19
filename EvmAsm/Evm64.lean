/-
  EvmAsm.Evm64

  Root import file for the 64-bit EVM opcode implementations (RV64IM).
-/

-- Foundations
import EvmAsm.Evm64.Basic
import EvmAsm.Evm64.Stack

-- Stack operations
import EvmAsm.Evm64.Pop
import EvmAsm.Evm64.Push0
import EvmAsm.Evm64.Dup
import EvmAsm.Evm64.Swap

-- Bitwise operations
import EvmAsm.Evm64.Bitwise
import EvmAsm.Evm64.And
import EvmAsm.Evm64.Or
import EvmAsm.Evm64.Xor
import EvmAsm.Evm64.Not

-- Arithmetic
import EvmAsm.Evm64.Arithmetic
import EvmAsm.Evm64.Add
import EvmAsm.Evm64.Sub

-- Comparisons
import EvmAsm.Evm64.Comparison
import EvmAsm.Evm64.Lt
import EvmAsm.Evm64.Gt
import EvmAsm.Evm64.Eq
import EvmAsm.Evm64.IsZero
import EvmAsm.Evm64.Slt
import EvmAsm.Evm64.Sgt

-- Shifts (program definitions + tests only; specs need CodeReq migration repair)
import EvmAsm.Evm64.Shift

-- Byte and SignExtend
import EvmAsm.Evm64.Byte
import EvmAsm.Evm64.SignExtend
import EvmAsm.Evm64.SignExtendSpec

-- Multiply
import EvmAsm.Evm64.Multiply
import EvmAsm.Evm64.MultiplySpec

-- DivMod (Knuth Algorithm D)
import EvmAsm.Evm64.DivMod
import EvmAsm.Evm64.DivModSpec
import EvmAsm.Evm64.DivModCompose
