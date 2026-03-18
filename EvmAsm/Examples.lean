/-
  EvmAsm.Examples

  Demonstration of using the macro assembler to build small programs
  and verify their behavior. Each example is in its own file.
-/

import EvmAsm.Examples.Swap
import EvmAsm.Examples.Zero
import EvmAsm.Examples.Multiply
import EvmAsm.Examples.LoadModifyStore
import EvmAsm.Examples.Combining
import EvmAsm.Examples.Halting
import EvmAsm.Examples.Commit
import EvmAsm.Examples.Write
import EvmAsm.Examples.FullPipeline
import EvmAsm.Examples.HelloWorld
import EvmAsm.Examples.Echo

-- 256-bit EVM operations
import EvmAsm.Evm32.Basic
import EvmAsm.Evm32.Stack
import EvmAsm.Evm32.Bitwise
import EvmAsm.Evm32.And
import EvmAsm.Evm32.Or
import EvmAsm.Evm32.Xor
import EvmAsm.Evm32.Not
import EvmAsm.Evm32.Arithmetic
import EvmAsm.Evm32.ArithmeticSpec
import EvmAsm.Evm32.Comparison
import EvmAsm.Evm32.ComparisonSpec
import EvmAsm.Evm32.Shift
