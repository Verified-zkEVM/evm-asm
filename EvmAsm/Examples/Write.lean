/-
  EvmAsm.Examples.Write

  WRITE syscall examples: writing words from memory to public values.
-/

import EvmAsm.Rv32.Execution

namespace EvmAsm.Examples

-- ============================================================================
-- WRITE syscall — single word from memory
-- ============================================================================

/-- Store 42 at address 0x100, WRITE 4 bytes from 0x100 to fd 13 (public values). -/
def write_single_word : Program :=
  LI .x6 42 ;;            -- t1 := 42
  LI .x7 0x100 ;;         -- t2 := 0x100 (address)
  SW .x7 .x6 0 ;;         -- mem[0x100] := 42
  WRITE 13 0x100 4        -- WRITE fd=13, buf=0x100, nbytes=4

def write_single_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After executing write_single_word, publicValues = [0x2A, 0, 0, 0] (42 as LE bytes). -/
example : let steps := write_single_word.length
          let s0 := { write_single_state with code := loadProgram 0 write_single_word }
          (stepN steps s0).bind (fun s =>
            some s.publicValues) = some [0x2A, 0, 0, 0] := by
  native_decide

-- ============================================================================
-- WRITE syscall — two words from memory
-- ============================================================================

/-- Store 42 and 99 at addresses 0x100 and 0x104, WRITE 8 bytes. -/
def write_two_words : Program :=
  LI .x6 42 ;;
  LI .x7 0x100 ;;
  SW .x7 .x6 0 ;;          -- mem[0x100] := 42
  LI .x6 99 ;;
  SW .x7 .x6 4 ;;          -- mem[0x104] := 99
  WRITE 13 0x100 8          -- WRITE fd=13, buf=0x100, nbytes=8

def write_two_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After executing write_two_words, publicValues = [0x2A, 0, 0, 0, 0x63, 0, 0, 0] (42, 99 as LE bytes). -/
example : let steps := write_two_words.length
          let s0 := { write_two_state with code := loadProgram 0 write_two_words }
          (stepN steps s0).bind (fun s =>
            some s.publicValues) = some [0x2A, 0, 0, 0, 0x63, 0, 0, 0] := by
  native_decide

-- ============================================================================
-- WRITE with non-13 fd (no-op for public values)
-- ============================================================================

/-- WRITE to fd=1 (stdout) should not affect publicValues. -/
def write_stdout : Program :=
  LI .x6 42 ;;
  LI .x7 0x100 ;;
  SW .x7 .x6 0 ;;
  WRITE 1 0x100 4          -- WRITE fd=1 (not public values)

def write_stdout_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After WRITE to fd=1, publicValues is still empty. -/
example : let steps := write_stdout.length
          let s0 := { write_stdout_state with code := loadProgram 0 write_stdout }
          (stepN steps s0).bind (fun s =>
            some s.publicValues) = some [] := by
  native_decide

end EvmAsm.Examples
