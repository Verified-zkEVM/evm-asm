/-
  EvmAsm.Codegen.Programs.BalModeledSystem

  Classifier for standalone BAL probes.  The live guest records these rows
  through the authenticated execution maps; it no longer uses this classifier
  as a formula-side skip.

  GH #10753 bridge module: the program itself lives in the leaf
  `BalModeledSystemProg.lean` parameterised over the abstract `GuestLayout`;
  this module applies the concrete `guestLayout` and re-exposes
  `balAccountIsModeledSystem_prog` with its original name and type, so every consumer
  (and the concrete-render drift gate, whose key is `emitProgram`
  `balAccountIsModeledSystem_prog`) compiles unchanged.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.BalModeledSystemProg
import EvmAsm.Codegen.GuestLayoutInstance

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_is_modeled_system

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a0 (output) = 1 EIP-2935 row / 2 EIP-4788 row / 0 other row / 3 parse failure.

    The live verdict no longer calls this classifier; it is retained only by
    the standalone BAL probe units. -/
def balAccountIsModeledSystem_prog : Program := balAccountIsModeledSystem_prog_of guestLayout

def ziskBalAccountIsModeledSystemDataSection : String :=
  ".balign 8\n" ++
  "bams_addr_ptr:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bams_addr_2935:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  ".balign 32\n" ++
  "bams_addr_4788:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02\n"

end EvmAsm.Codegen
