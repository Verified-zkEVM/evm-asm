/-
  EvmAsm.Evm64.Dispatch.TailSpec

  LD/JALR tail-call sub-spec for the RV64 opcode dispatch sequence (GH #106).
-/

module

public import EvmAsm.Evm64.Dispatch.Program
public import EvmAsm.Rv64.ControlFlow
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.RunBlock

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Dispatch

open EvmAsm.Rv64

/-- CodeReq for the dispatch tail block: `LD rOp rOp 0`, then
    `JALR x0 rOp 0`. -/
def tailCode (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD rOp rOp handlerLdOff)).union
    (CodeReq.singleton (base + 4) (.JALR .x0 rOp handlerJumpOff))

/-- Final two-step tail of `evm_dispatch`.

    Starting with `rOp` holding the selected jump-table entry address,
    the tail loads the handler address from that cell and jumps to it
    with `JALR x0`, preserving the table-entry memory cell. -/
theorem evm_dispatch_tail_spec_within
    (base entryAddr handlerAddr : Word) :
    cpsTripleWithin 2 base
      ((handlerAddr + signExtend12 handlerJumpOff) &&& ~~~1)
      (tailCode base)
      ((rOp ↦ᵣ entryAddr) **
        ((entryAddr + signExtend12 handlerLdOff) ↦ₘ handlerAddr))
      ((rOp ↦ᵣ handlerAddr) **
        ((entryAddr + signExtend12 handlerLdOff) ↦ₘ handlerAddr)) := by
  have L := ld_spec_gen_same_within rOp entryAddr handlerAddr
    handlerLdOff base (by decide)
  have J := jalr_x0_spec_gen_within rOp handlerAddr
    handlerJumpOff (base + 4)
  runBlock L J

end Dispatch
end EvmAsm.Evm64
