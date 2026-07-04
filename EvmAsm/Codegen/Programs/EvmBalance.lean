/-
  EvmAsm.Codegen.Programs.EvmBalance

  Runtime dispatcher BALANCE handler backed by account-witness state.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas

namespace EvmAsm.Codegen

/-- Copy an EVM stack address word into natural 20-byte address order.

    Stack bytes 0..19 hold the low 160-bit address little-endian; trie lookup
    helpers expect the big-endian byte string whose keccak selects the account
    path. `x12` is the EVM stack pointer and `t1` points at
    `eahsr_address_scratch`. -/
private def balanceWitnessAddressCopy : String :=
  String.intercalate "" <|
    (List.range 20).map fun i =>
      s!"  lbu t2, {19 - i}(x12)
  sb t2, {i}(t1)
"

/-- Copy the big-endian u256 returned by `balance_at_header_state_root` into
    the dispatcher's little-endian stack-word layout. -/
private def balanceWitnessOutputCopy : String :=
  String.intercalate "" <|
    (List.range 32).map fun i =>
      s!"  lbu t2, {31 - i}(t0)
  sb t2, {i}(x12)
"

/-- Raw dispatcher handler for BALANCE backed by `balance_at_header_state_root`.

    Net stack delta is zero: the input address word is overwritten with the
    account balance, or zero for missing accounts / missing witness context. -/
private def balanceWitnessTail : HandlerTail :=
  .custom <|
    "  la t1, eahsr_address_scratch
" ++
    balanceWitnessAddressCopy ++
    "  addi sp, sp, -32
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x21, 16(sp)
" ++
    "  sd x13, 24(sp)
" ++
    "  la a0, eahsr_address_scratch
" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "
" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "
" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "
" ++
    "  jal ra, runtime_access_account_charge
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x21, 16(sp)
" ++
    "  ld x13, 24(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  ld t0, 584(x20)
" ++
    "  beqz t0, .Lbalance_no_context
" ++
    "  addi sp, sp, -32
" ++
    "  sd x10, 0(sp)
" ++
    "  sd x12, 8(sp)
" ++
    "  sd x21, 16(sp)
" ++
    "  sd x13, 24(sp)
" ++
    "  ld a0, 576(x20)
" ++         -- header ptr
    "  ld a1, 584(x20)
" ++         -- header len
    "  la a2, eahsr_address_scratch
" ++
    "  ld a3, 592(x20)
" ++         -- witness.state ptr
    "  ld a4, 600(x20)
" ++         -- witness.state len
    "  la a5, bal_output_scratch
" ++
    "  jal ra, balance_at_header_state_root
" ++
    "  ld x10, 0(sp)
" ++
    "  ld x12, 8(sp)
" ++
    "  ld x21, 16(sp)
" ++
    "  ld x13, 24(sp)
" ++
    "  addi sp, sp, 32
" ++
    "  la t0, bal_output_scratch
" ++
    balanceWitnessOutputCopy ++
    "  addi x10, x10, 1
" ++
    "  j .dispatch_loop
" ++
    ".Lbalance_no_context:
" ++
    "  sd zero, 0(x12)
" ++
    "  sd zero, 8(x12)
" ++
    "  sd zero, 16(x12)
" ++
    "  sd zero, 24(x12)
" ++
    "  addi x10, x10, 1
" ++
    "  j .dispatch_loop"

def balanceWitnessHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_BALANCE"
    , opcodes := [0x31]
    , preBody := stackUnderflowGuardAsm 1
    , body := []
    , tail := balanceWitnessTail } ]

end EvmAsm.Codegen
