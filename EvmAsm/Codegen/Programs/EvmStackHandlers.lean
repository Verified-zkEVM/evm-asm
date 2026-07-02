/-
  EvmAsm.Codegen.Programs.EvmStackHandlers

  Dispatcher handler families for PUSH, DUP, SWAP, and EIP-8024's
  immediate-indexed DUPN/SWAPN/EXCHANGE opcodes.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Swap.Program

namespace EvmAsm.Codegen

/-! ## stack opcode handler families -/

/-- PUSH0..PUSH32. Opcode byte = `0x5f + n`; the handler advances
    `x10` by `1 + n` (one opcode byte + `n` immediate bytes). -/
def pushHandlers : List OpcodeHandlerSpec :=
  (List.range 33).map (fun n =>
    { label   := s!"h_PUSH{n}"
      opcodes := [0x5f + n]
      preBody := stackOverflowGuardAsm
      body    := EvmAsm.Evm64.evm_push n
      tail    := .advanceAndRet (1 + n) })

/-- DUP1..DUP16. Opcode byte = `0x7f + n` (so DUP1 = `0x80`);
    width 1. `evm_dup n` duplicates the n-th stack item (1-indexed
    from top) onto the top. -/
def dupHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_DUP{n}"
      opcodes := [0x7f + n]
      preBody := stackUnderflowGuardAsm n ++ "\n" ++ stackOverflowGuardAsm
      body    := EvmAsm.Evm64.evm_dup n
      tail    := .advanceAndRet 1 })

/-- SWAP1..SWAP16. Opcode byte = `0x8f + n` (so SWAP1 = `0x90`);
    width 1. `evm_swap n` swaps the top with the (n+1)-th stack
    item. -/
def swapHandlers : List OpcodeHandlerSpec :=
  (List.range 16).map (fun i =>
    let n := i + 1
    { label   := s!"h_SWAP{n}"
      opcodes := [0x8f + n]
      preBody := stackUnderflowGuardAsm (n + 1)
      body    := EvmAsm.Evm64.evm_swap n
      tail    := .advanceAndRet 1 })


/-- Load the EIP-8024 immediate byte into `x14`.

    Python execution-specs reads the byte after the opcode through
    `buffer_read`, so a missing immediate decodes as zero rather than
    reading the next packed input segment. -/
def eip8024LoadImmediateAsm (afterLabel : String) : String :=
  "  sub x15, x10, x21\n" ++
  "  addi x15, x15, 1\n" ++
  "  ld x16, 496(x20)\n" ++
  "  li x14, 0\n" ++
  s!"  bgeu x15, x16, {afterLabel}\n" ++
  "  lbu x14, 1(x10)\n" ++
  s!"{afterLabel}:\n"

/-- EIP-8024 `decode_single`: valid immediates are `0..90` and
    `128..255`; result is `(imm + 145) mod 256`, so `17..235`. -/
def eip8024DecodeSingleAsm (afterLoadLabel decodedLabel : String) : String :=
  eip8024LoadImmediateAsm afterLoadLabel ++
  "  li x15, 90\n" ++
  s!"  bleu x14, x15, {decodedLabel}\n" ++
  "  li x15, 128\n" ++
  "  bltu x14, x15, .exit_invalid_op\n" ++
  s!"{decodedLabel}:\n" ++
  "  addi x14, x14, 145\n" ++
  "  andi x14, x14, 255\n"

/-- Copy a 256-bit EVM stack word from address register `srcReg` to
    address register `dstReg`, using `x15` as the temporary limb. -/
def copyWordAsm (srcReg dstReg : String) : String :=
  s!"  ld x15, 0({srcReg})\n" ++
  s!"  sd x15, 0({dstReg})\n" ++
  s!"  ld x15, 8({srcReg})\n" ++
  s!"  sd x15, 8({dstReg})\n" ++
  s!"  ld x15, 16({srcReg})\n" ++
  s!"  sd x15, 16({dstReg})\n" ++
  s!"  ld x15, 24({srcReg})\n" ++
  s!"  sd x15, 24({dstReg})\n"

/-- Swap two 256-bit EVM stack words at address registers `lhsReg` and
    `rhsReg`, using `x15`/`x16` as temporary limbs. -/
def swapWordAsm (lhsReg rhsReg : String) : String :=
  s!"  ld x15, 0({lhsReg})\n" ++
  s!"  ld x16, 0({rhsReg})\n" ++
  s!"  sd x16, 0({lhsReg})\n" ++
  s!"  sd x15, 0({rhsReg})\n" ++
  s!"  ld x15, 8({lhsReg})\n" ++
  s!"  ld x16, 8({rhsReg})\n" ++
  s!"  sd x16, 8({lhsReg})\n" ++
  s!"  sd x15, 8({rhsReg})\n" ++
  s!"  ld x15, 16({lhsReg})\n" ++
  s!"  ld x16, 16({rhsReg})\n" ++
  s!"  sd x16, 16({lhsReg})\n" ++
  s!"  sd x15, 16({rhsReg})\n" ++
  s!"  ld x15, 24({lhsReg})\n" ++
  s!"  ld x16, 24({rhsReg})\n" ++
  s!"  sd x16, 24({lhsReg})\n" ++
  s!"  sd x15, 24({rhsReg})\n"

def dupnHandlerAsm : String :=
  eip8024DecodeSingleAsm ".dupn_imm_loaded" ".dupn_imm_valid" ++
  "  mv x11, x14\n" ++
  stackOverflowGuardAsm ++ "\n" ++
  "  mv x14, x11\n" ++
  "  slli x15, x14, 5\n" ++
  "  la x16, evm_stack_top\n" ++
  "  sub x16, x16, x15\n" ++
  "  bltu x16, x12, .exit_stack_underflow\n" ++
  "  addi x12, x12, -32\n" ++
  "  add x16, x12, x15\n" ++
  copyWordAsm "x16" "x12"

def swapnHandlerAsm : String :=
  eip8024DecodeSingleAsm ".swapn_imm_loaded" ".swapn_imm_valid" ++
  "  addi x14, x14, 1\n" ++
  "  slli x15, x14, 5\n" ++
  "  la x16, evm_stack_top\n" ++
  "  sub x16, x16, x15\n" ++
  "  bltu x16, x12, .exit_stack_underflow\n" ++
  "  addi x14, x14, -1\n" ++
  "  slli x15, x14, 5\n" ++
  "  add x17, x12, x15\n" ++
  swapWordAsm "x12" "x17"

def exchangeHandlerAsm : String :=
  eip8024LoadImmediateAsm ".exchange_imm_loaded" ++
  "  li x15, 81\n" ++
  "  bleu x14, x15, .exchange_imm_valid\n" ++
  "  li x15, 128\n" ++
  "  bltu x14, x15, .exit_invalid_op\n" ++
  ".exchange_imm_valid:\n" ++
  "  xori x14, x14, 143\n" ++
  "  srli x15, x14, 4\n" ++
  "  andi x16, x14, 15\n" ++
  "  bltu x15, x16, .exchange_q_lt_r\n" ++
  "  addi x17, x16, 1\n" ++
  "  li x18, 29\n" ++
  "  sub x18, x18, x15\n" ++
  "  j .exchange_decoded\n" ++
  ".exchange_q_lt_r:\n" ++
  "  addi x17, x15, 1\n" ++
  "  addi x18, x16, 1\n" ++
  ".exchange_decoded:\n" ++
  "  bleu x17, x18, .exchange_depth_m\n" ++
  "  mv x19, x17\n" ++
  "  j .exchange_depth_ready\n" ++
  ".exchange_depth_m:\n" ++
  "  mv x19, x18\n" ++
  ".exchange_depth_ready:\n" ++
  "  addi x19, x19, 1\n" ++
  "  slli x19, x19, 5\n" ++
  "  la x15, evm_stack_top\n" ++
  "  sub x15, x15, x19\n" ++
  "  bltu x15, x12, .exit_stack_underflow\n" ++
  "  slli x17, x17, 5\n" ++
  "  slli x18, x18, 5\n" ++
  "  add x17, x12, x17\n" ++
  "  add x18, x12, x18\n" ++
  swapWordAsm "x17" "x18"

/-- EIP-8024 stack-access opcodes. The runtime immediate determines the
    stack index, so these handlers are raw dispatcher asm rather than
    static-offset verified `Program`s. -/
def eip8024StackHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_DUPN", opcodes := [0xe6], preBody := dupnHandlerAsm, body := [], tail := .advanceAndRet 2 }
  , { label := "h_SWAPN", opcodes := [0xe7], preBody := swapnHandlerAsm, body := [], tail := .advanceAndRet 2 }
  , { label := "h_EXCHANGE", opcodes := [0xe8], preBody := exchangeHandlerAsm, body := [], tail := .advanceAndRet 2 } ]

end EvmAsm.Codegen
