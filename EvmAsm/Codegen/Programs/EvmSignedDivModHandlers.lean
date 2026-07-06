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
-- Like h_DIV/h_MOD, `evm_sdiv` / `evm_smod` run the verified DIV/MOD core
-- (`evm_div_callable_v4` / `evm_mod_callable_v4`), which uses `x2` (= `sp`) as a
-- general-purpose working register. In the dispatcher `sp` is the LP64
-- helper-call stack pointer (`lp64_sp_top`), so restore it before resuming
-- `.dispatch_loop` or the next helper-call prologue (`sd ra, 0(sp)`) faults on a
-- garbage `sp` (ziskemu `mem.rs:593` invalid addr). Mirrors `divModTail` /
-- `expTail`.
private def signedDivModTail : HandlerTail :=
  -- 4ch8f.10.3: `ret` to the dispatch resume point (the wrapper's inner
  -- `JAL .x1` clobbered x1, so restore the continuation explicitly) instead
  -- of `j .dispatch_loop`, so the handler satisfies the callRegS contract.
  .custom ("  mv x13, x15\n  mv x10, x14\n  la sp, lp64_sp_top\n  addi x10, x10, 1\n" ++
    dispatchContinueRet)

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
      preBody       := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10\n  mv x15, x13\n  la x18, h_SDIV_done"
      body          := evmSdivPatched
      postBodyLabel := some "h_SDIV_done"
      tail          := signedDivModTail }
  , { label         := "h_SMOD"
      opcodes       := [0x07]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10\n  mv x15, x13\n  la x18, h_SMOD_done"
      body          := evmSmodPatched
      postBodyLabel := some "h_SMOD_done"
      tail          := signedDivModTail } ]

end EvmAsm.Codegen
