/-
  Driver for scripts/check-guarded-handler-bytes.sh (bead evm-asm-vgyg9).

  Renders the *verified* guarded ADD handler Program
  (`EvmAsm.Codegen.Proofs.guardedCleanRetHandlerProgram`, the CodeReq the
  byte-tie theorem pins) as GNU-as text at the concrete `la` immediates the
  linked guest uses, so the caller can assemble it and byte-compare with the
  emitted `h_ADD` subroutine at the dispatch-table address.

  Usage: lake env lean --run scripts/emit_guarded_handler_driver.lean \
           <hi1> <lo1> <hi2> <lo2>
  where hi/lo are the auipc/addi immediates (decimal, lo may be negative)
  for `la x14, evm_cur_stack_top` at h_ADD+0 and `la x6, evm_halt_flag`
  at h_ADD+24.
-/
import EvmAsm.Codegen.Proofs.GuardedHandlerSpecs

open EvmAsm.Codegen EvmAsm.Codegen.Proofs

def main (args : List String) : IO Unit := do
  match args with
  | [hi1, lo1, hi2, lo2] =>
    let toI (s : String) : Int := s.toInt!
    let prog := guardedCleanRetHandlerProgram
      (BitVec.ofInt 20 (toI hi1)) (BitVec.ofInt 12 (toI lo1))
      (BitVec.ofInt 20 (toI hi2)) (BitVec.ofInt 12 (toI lo2))
      (BitVec.ofInt 12 (-64))
      EvmAsm.Evm64.evm_add 1
    IO.println (emitProgram prog)
  | _ => IO.eprintln "usage: emit_guarded_handler_driver.lean <hi1> <lo1> <hi2> <lo2>"
