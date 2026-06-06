/-
  EvmAsm.Codegen.Programs.EvmDivModWrappers

  Patched DIV/MOD wrapper helpers used by standalone codegen units and
  dispatcher handlers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SMod.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## divK NOP-splice helpers (used by both M2 standalone DIV/MOD
    wrappers and the M8 dispatcher handlers). -/

/-- `EvmAsm.Evm64.evm_div` with the NOP "exit PC" at internal index 267
    replaced by a forward `JAL .x0 +304` that skips the 75-instruction
    inline `divK_div128_v4` subroutine and lands at the instruction
    immediately following the body. In the M2 standalone wrapper that
    landing site is the start of `evmAddEpilogue`; in the M8
    dispatcher wrapper (M5b registry) it is the `mv x10, x9` of the
    handler's `x10RestoreAdvance1` tail. -/
def evmDivPatched : Program :=
  (EvmAsm.Evm64.evm_div : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_div : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_mod` with the same NOP-splice as `evmDivPatched`.
    Same +304 byte offset because the MOD body has the identical
    343-instruction layout (267 main + NOP + 75 subroutine). -/
def evmModPatched : Program :=
  (EvmAsm.Evm64.evm_mod : List Instr).take 267 ++
  [Instr.JAL .x0 (304 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_mod : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_sdiv` with the leading `ADDI .x18 .x1 0`
    save_ra_block removed (413 instructions instead of 414). The
    M9 trampoline handler sets `x18 = &h_SDIV_done` in `preBody`;
    the body's existing `JALR x0, x18, 0` then jumps to our
    restore stub instead of clobbering `x18` with `x1`.

    The first instruction of `evm_sdiv_wrapper` is
    `evm_sdiv_save_ra_block .x18` = `ADDI .x18 .x1 0`
    (`EvmAsm/Evm64/SDiv/Program.lean:180`). Splicing it off lets
    our trampoline target stick. -/
def evmSdivPatched : Program :=
  (EvmAsm.Evm64.evm_sdiv : List Instr).drop 1

/-- `EvmAsm.Evm64.evm_smod` with the same leading-save_ra splice
    as `evmSdivPatched`. SMOD's wrapper is structurally identical
    to SDIV's at the entry/exit boundary (only the conditional-
    negate path differs). -/
def evmSmodPatched : Program :=
  (EvmAsm.Evm64.evm_smod : List Instr).drop 1

/-- `EvmAsm.Evm64.evm_div_v5` with the NOP exit slot patched to skip the
    longer 85-instruction v5 div128 subroutine. -/
def evmDivV5Patched : Program :=
  (EvmAsm.Evm64.evm_div_v5 : List Instr).take 267 ++
  [Instr.JAL .x0 (344 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_div_v5 : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_mod_v5` with the same v5 NOP-splice as
    `evmDivV5Patched`. -/
def evmModV5Patched : Program :=
  (EvmAsm.Evm64.evm_mod_v5 : List Instr).take 267 ++
  [Instr.JAL .x0 (344 : BitVec 21)] ++
  (EvmAsm.Evm64.evm_mod_v5 : List Instr).drop 268

/-- `EvmAsm.Evm64.evm_sdiv_v5` with the leading save-ra block removed for
    trampoline-style handlers. -/
def evmSdivV5Patched : Program :=
  (EvmAsm.Evm64.evm_sdiv_v5 : List Instr).drop 1

/-- `EvmAsm.Evm64.evm_smod_v5` with the leading save-ra block removed for
    trampoline-style handlers. -/
def evmSmodV5Patched : Program :=
  (EvmAsm.Evm64.evm_smod_v5 : List Instr).drop 1

end EvmAsm.Codegen
