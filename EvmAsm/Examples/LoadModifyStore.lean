/-
  EvmAsm.Examples.LoadModifyStore

  A load-modify-store pattern.
-/

import EvmAsm.Rv32.Program

namespace EvmAsm.Examples

-- ============================================================================
-- Load-modify-store pattern
-- ============================================================================

/-- Load a value from memory, add a constant, store it back.
    inc_mem base offset tmp :=
      LW tmp, offset(base)
      ADDI tmp, tmp, 1
      SW base, tmp, offset
-/
def inc_mem (base tmp : Reg) (offset : BitVec 12) : Program :=
  LW tmp base offset ;;
  ADDI tmp tmp 1 ;;
  SW base tmp offset

end EvmAsm.Examples
