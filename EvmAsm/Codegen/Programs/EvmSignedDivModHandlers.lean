/-
  EvmAsm.Codegen.Programs.EvmSignedDivModHandlers

  Dispatcher handlers for signed SDIV and SMOD.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmDivModWrappers

namespace EvmAsm.Codegen

/-- Tail for SDIV/SMOD: restore `x10` from `x14`, advance the EVM
    code pointer by 1, then jump directly to `.dispatch_loop`
    rather than `ret`-ing. The standard `ret` (= `jalr x0, x1, 0`)
    won't work for these handlers because the wrapper's inner
    `JAL .x1` into `evm_div_callable_v4` / `evm_mod_callable_v4`
    clobbers `x1` mid-body; `x1` no longer holds the dispatcher's
    continuation by the time control reaches this tail. -/
private def signedDivModTail : HandlerTail :=
  .custom "  mv x10, x14\n  addi x10, x10, 1\n  j .dispatch_loop"

/-- M9 signed division handlers: SDIV (0x05) and SMOD (0x07).

    Different wrapping than M8's DIV/MOD because `evm_sdiv` /
    `evm_smod` end with a "saved-ra-ret" pattern (`JALR x0, x18, 0`
    after the wrapper copies `x1` into `x18` at entry). This
    bypasses the dispatcher's standard `.advanceAndRet` tail entirely.

    The pre-body installs one post-body label per handler in `x18`,
    then uses `evmSdivPatched` / `evmSmodPatched`, which drop the
    leading save-ra block so it cannot overwrite the trampoline target. -/
def signedDivModHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_SDIV"
      opcodes       := [0x05]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10\n  la x18, h_SDIV_done"
      body          := evmSdivPatched
      postBodyLabel := some "h_SDIV_done"
      tail          := signedDivModTail }
  , { label         := "h_SMOD"
      opcodes       := [0x07]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10\n  la x18, h_SMOD_done"
      body          := evmSmodPatched
      postBodyLabel := some "h_SMOD_done"
      tail          := signedDivModTail } ]

end EvmAsm.Codegen
