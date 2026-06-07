/-
  EvmAsm.Codegen.Programs.RlpListCountProbe

  zisk probe for rlp_list_count_items.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## rlp_list_count_items -- PR-K47
    The function body lives in `EvmAsm/Codegen/Programs/RlpRead.lean`.
    This module hosts only the zisk probe BuildUnit. -/

/-- `zisk_rlp_list_count_items`: probe BuildUnit. Reads
    (list_len, list_bytes) from host input, writes
    (status, count) to OUTPUT. -/
def ziskRlpListCountItemsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # list_len\n" ++
  "  addi a0, a3, 16             # list ptr\n" ++
  "  li a2, 0xa0010008           # count out at OUTPUT + 8\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lrlc_pdone\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  ".Lrlc_pdone:"

def ziskRlpListCountItemsDataSection : String :=
  ".section .data\n" ++
  "rlc_pad:\n" ++
  "  .zero 8"

def ziskRlpListCountItemsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpListCountItemsPrologue
  dataAsm     := ziskRlpListCountItemsDataSection
}

end EvmAsm.Codegen
