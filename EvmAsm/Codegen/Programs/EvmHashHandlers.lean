/-
  EvmAsm.Codegen.Programs.EvmHashHandlers

  Dispatcher handler for KECCAK256.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

/-- M16 hash / precompile-via-syscall opcodes. KECCAK256 (0x20) is the
    first ECALL-bridge opcode wired into the dispatcher.

    The handler does NOT have a verified body (`Instr` has no CSRS
    variant; the Zisk `csrs 0x800, a0` accelerator is encoded as a
    raw `.4byte 0x80052073` inside the `zkvm_keccak256` subroutine).
    Like `stopHandler` and the M15 JUMP/JUMPI handlers, this uses
    `body := []` + `tail := .custom "..."` with the full asm inline.

    **Calling convention.** The handler must navigate the conflict
    between LP64 (a0/a1/a2 = x10/x11/x12) and the dispatcher's
    preserved state (x10 = EVM code ptr, x12 = EVM stack ptr).
    Solution: save `x10` to `s10` and `x12` to `s11` (callee-saved
    in LP64, preserved across the keccak call), set up a0/a1/a2 as
    keccak args, then restore after the call.

    **Stack delta**: pop 2 words (offset + size, 64 B) and push 1
    word (32-byte digest). Net x12 advance = +32 (one word).

    **Tail return mechanism**: `j .dispatch_loop` (NOT `ret`),
    because the `jal x1, zkvm_keccak256` clobbers `x1`. Same fix as
    M9's `signedDivModTail`.

    **Endianness**: the keccak subroutine writes the 32-byte digest
    to `a2` in standard byte order (`digest[0]` first). The
    dispatcher's epilogue (e.g. `evmAddEpilogue`) copies x12+0..x12+31
    verbatim to OUTPUT_ADDR. So `expectedOutHex` in test cases is
    the standard keccak digest hex. -/
def hashHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_KECCAK256"
    , opcodes := [0x20]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 keccakRangeGuardAsm ++
                 "  ld x14, 0(x12)\n" ++
                 "  ld x15, 32(x12)\n" ++
                 keccakWordGasAsm "x15" ++
                 updateActiveMemorySizeAsm "keccak" "x14" "x15" "x16" "x17" "x18" "x6" true
    , body    := []
    , tail    := .custom (
        "  mv s10, x10\n" ++           -- save EVM code ptr
        "  ld t0, 0(x12)\n" ++          -- t0 = offset_low (low 64 bits of top word)
        "  ld a1, 32(x12)\n" ++         -- a1 = size_low
        "  addi x12, x12, 32\n" ++      -- net stack delta: pop 2 (64), push 1 (-32) = +32
        "  add a0, x13, t0\n" ++        -- a0 = evm_memory + offset (input ptr)
        "  mv a2, x12\n" ++             -- a2 = result slot (= new EVM stack top)
        "  mv s11, x12\n" ++            -- save EVM stack ptr across the call
        "  jal x1, zkvm_keccak256\n" ++ -- call keccak (clobbers x1, a0, a1, a2)
        "  mv x10, s10\n" ++            -- restore EVM code ptr
        "  mv x12, s11\n" ++            -- restore EVM stack ptr
        "  addi x10, x10, 1\n" ++       -- advance PC by 1
        "  j .dispatch_loop") } ]

end EvmAsm.Codegen
