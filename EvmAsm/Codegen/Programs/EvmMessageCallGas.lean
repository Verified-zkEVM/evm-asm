/-
  EvmAsm.Codegen.Programs.EvmMessageCallGas

  Standalone EIP-150 CALL gas-forwarding helper/probe. The calculation mirrors
  execution-specs Amsterdam `calculate_message_call_gas` and
  `max_message_call_gas`.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## message_call_gas -- EIP-150 CALL forwarding helper

    Mirrors execution-specs Amsterdam `calculate_message_call_gas` /
    `max_message_call_gas` for u64 gas quantities:

      stipend = 0 when value is zero, otherwise 2300
      if gas_left < extra_gas + memory_cost:
        cost = requested_gas + extra_gas
        sub_call = requested_gas + stipend
      else:
        capped = min(requested_gas,
                     available - floor(available / 64))
        cost = capped + extra_gas
        sub_call = capped + stipend

    Calling convention:
      a0 = value_nonzero flag
      a1 = requested call gas
      a2 = gas_left in the current frame
      a3 = memory_cost
      a4 = extra_gas (value transfer/new-account additions)

    Returns:
      a0 = status: 0 ok, 1 input sum overflow, 2 output sum overflow
      a1 = caller-frame charge excluding memory_cost
      a2 = gas made available to the child frame
      a3 = capped requested gas actually selected
-/
def messageCallGasFunction : String :=
  "message_call_gas:\n" ++
  "  mv t0, a0                   # value_nonzero\n" ++
  "  mv t1, a1                   # requested gas\n" ++
  "  mv t2, a2                   # gas_left\n" ++
  "  mv t3, a3                   # memory_cost\n" ++
  "  mv t4, a4                   # extra_gas\n" ++
  "  add t5, t3, t4              # memory_cost + extra_gas\n" ++
  "  bltu t5, t3, .Lmcg_input_overflow\n" ++
  "  li t6, 0\n" ++
  "  beqz t0, .Lmcg_have_stipend\n" ++
  "  li t6, 2300\n" ++
  ".Lmcg_have_stipend:\n" ++
  "  bltu t2, t5, .Lmcg_uncapped\n" ++
  "  sub a5, t2, t5              # available after memory/extra\n" ++
  "  srli a6, a5, 6\n" ++
  "  sub a6, a5, a6              # max_message_call_gas\n" ++
  "  mv a3, t1\n" ++
  "  bgeu a6, t1, .Lmcg_have_capped\n" ++
  "  mv a3, a6\n" ++
  "  j .Lmcg_have_capped\n" ++
  ".Lmcg_uncapped:\n" ++
  "  mv a3, t1\n" ++
  ".Lmcg_have_capped:\n" ++
  "  add a1, a3, t4              # cost\n" ++
  "  bltu a1, a3, .Lmcg_output_overflow\n" ++
  "  add a2, a3, t6              # sub_call\n" ++
  "  bltu a2, a3, .Lmcg_output_overflow\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lmcg_input_overflow:\n" ++
  "  li a0, 1\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  li a3, 0\n" ++
  "  ret\n" ++
  ".Lmcg_output_overflow:\n" ++
  "  li a0, 2\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  li a3, 0\n" ++
  "  ret"

/-- `zisk_message_call_gas`: focused probe for EIP-150 message-call gas math.
    Host input payload after the zisk length prefix:
      +0  value_nonzero u64
      +8  requested_gas u64
      +16 gas_left u64
      +24 memory_cost u64
      +32 extra_gas u64

    Output:
      +0  status
      +8  cost
      +16 sub_call
      +24 capped requested gas. -/
def ziskMessageCallGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  ld a0, 8(s0)\n" ++
  "  ld a1, 16(s0)\n" ++
  "  ld a2, 24(s0)\n" ++
  "  ld a3, 32(s0)\n" ++
  "  ld a4, 40(s0)\n" ++
  "  jal ra, message_call_gas\n" ++
  "  sd a0, 0(s1)\n" ++
  "  sd a1, 8(s1)\n" ++
  "  sd a2, 16(s1)\n" ++
  "  sd a3, 24(s1)\n" ++
  "  j .Lmcg_probe_done\n" ++
  messageCallGasFunction ++ "\n" ++
  ".Lmcg_probe_done:"

def ziskMessageCallGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMessageCallGasPrologue
  dataAsm     := ".section .data\n.balign 8\n"
}

end EvmAsm.Codegen
