/-
  EvmAsm.Examples.HelloWorld

  A "hello world" program that stores ASCII characters to memory
  and outputs them via the SP1 WRITE syscall, with formal verification
  of output correctness and termination.

  Characters are packed 4 per word in little-endian order.
-/

import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.CPSSpec

namespace EvmAsm.Examples

-- "hello world" as 11 ASCII bytes.
def helloWorldBytes : List (BitVec 8) :=
  [0x68, 0x65, 0x6C, 0x6C,  -- "hell"
   0x6F, 0x20, 0x77, 0x6F,  -- "o wo"
   0x72, 0x6C, 0x64]         -- "rld"

-- The hello world program:
--   1. Store 4 ASCII characters per word to memory at 0x100
--   2. WRITE fd=13 (public values), buf=0x100, nbytes=11
--   3. HALT with exit code 0
def helloWorld : Program :=
  LI .x7 0x100 ;;
  LI .x6 0x6C6C6568 ;; SW .x7 .x6 0 ;;    -- "hell" (LE)
  LI .x6 0x6F77206F ;; SW .x7 .x6 4 ;;    -- "o wo" (LE)
  LI .x6 0x00646C72 ;; SW .x7 .x6 8 ;;    -- "rld\0" (LE)
  WRITE 13 0x100 11 ;;
  HALT 0

def helloInitState : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- The program is 15 instructions long. -/
example : helloWorld.length = 15 := by native_decide

/-- After 14 steps, publicValues contains "hello world" as bytes. -/
example : let s0 := { helloInitState with code := loadProgram 0 helloWorld }
    (stepN 14 s0).bind
    (fun s => some s.publicValues) = some helloWorldBytes := by
  native_decide

/-- After 14 steps, the next step is HALT. -/
example : let s0 := { helloInitState with code := loadProgram 0 helloWorld }
    ((stepN 14 s0).bind
    (fun s => step s)).isNone = true := by
  native_decide

end EvmAsm.Examples
