/-
  EvmAsm.Evm64.Push.Program

  256-bit EVM PUSH1..PUSH32: read `n` immediate bytes from the EVM code
  region, zero-extend them (right-aligned, big-endian) into a 256-bit
  EvmWord, push the result onto the EVM stack.

  Calling convention for PUSH (slice 2 of #101):
    x10  — EVM code pointer (pointing at the PUSHn opcode byte; the
           immediate bytes live at +1 .. +n)
    x12  — EVM stack pointer (decremented by 32 to allocate the new top
           slot, in line with the rest of the Evm64 opcode subroutines)
    x0   — hardwired zero, used by SD to zero the four limbs in one go
    x7   — temporary, holds the LBU'd byte before the SB

  The PC advance for `x10` is intentionally NOT added in this slice;
  the design note (`docs/push-opcode-design.md`) defers the EVM-level
  "PC advances by 1+n" claim to the spec slices (#101 slice 4).

  Total RISC-V instructions: 5 + 2 * n.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Read one immediate byte and store it into the new EVM stack slot.

    `n` is the PUSH width (1..32) and `i` is the byte index in
    `[0, n)` counted from the most-significant byte of the immediate.
    The big-endian semantics mean immediate byte `i` (which lives at
    `code[pc + 1 + i]`) is the byte at integer position `n - 1 - i`,
    so it goes into memory offset `n - 1 - i` from the new stack
    pointer (which holds limb 0's LSB at offset 0). -/
private def push_one_byte (n i : Nat) : Program :=
  LBU .x7 .x10 (BitVec.ofNat 12 (1 + i)) ;;
  SB .x12 .x7 (BitVec.ofNat 12 (n - 1 - i))

/-- Sequence `push_one_byte n 0 ;; push_one_byte n 1 ;; ... ;; push_one_byte n (k-1)`.

    Defined by recursion on `k` so `evm_push n` can be expressed for
    arbitrary symbolic `n` while keeping the per-byte block uniform. -/
private def push_bytes (n : Nat) : Nat → Program
  | 0     => prog_skip
  | k + 1 => push_bytes n k ;; push_one_byte n k

/-- Generic PUSHn program.

    Layout (5 + 2n instructions):
      1. `ADDI x12, x12, -32`       — allocate a new 32-byte stack slot
      2. four `SD x12, x0, 8*j`    — zero-fill the four 64-bit limbs
      3. n × (LBU + SB) pairs       — copy immediate bytes into place

    For PUSH1 through PUSH32 the offsets stay below 2^11, so the
    `BitVec.ofNat 12` casts in the helpers behave like the natural
    encoding (no sign-extension surprises). -/
def evm_push (n : Nat) : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;
  push_bytes n n

/-- CodeReq for `evm_push n`.

    Symbolic `n` prevents `CodeReq.ofProg` from fully reducing, but for
    this slice (program-only) we only need a buildable definition. The
    spec slices (#101 slices 3-4) may refactor this into an explicit
    `CodeReq.singleton` union chain mirroring `evm_dup_code` if proofs
    require it. -/
abbrev evm_push_code (base : Word) (n : Nat) : CodeReq :=
  CodeReq.ofProg base (evm_push n)

end EvmAsm.Evm64
