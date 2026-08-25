/-
  EvmAsm.Evm64.Dispatch.Program

  Slice 2 of GH #106 (opcode dispatch via jump table).

  Defines the 5-instruction RV64 dispatch program that, given a pointer
  to the next opcode byte and the base of a 256-entry jump table, loads
  the corresponding handler address and tail-calls into it:

      LBU  rOp,   rOpPtr, 0     -- opcode byte ← (rOpPtr)[0]
      SLLI rOp,   rOp,    3     -- opcode * 8
      ADD  rOp,   rOp,    rTable -- table_base + 8 * opcode
      LD   rOp,   rOp,    0     -- handler address
      JALR x0,    rOp,    0     -- tail-call into handler (no return)

  The Hoare triple (`dispatch_spec`) lands in slice 3
  (`evm-asm-afkny`); this slice only fixes the program skeleton plus
  the named offset constants + register aliases shared with later
  slices.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
  Refs GH #106, beads `evm-asm-kvygx`, parent `evm-asm-77w8s`.
-/

module

public import EvmAsm.Rv64.Program

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace Dispatch

/-! ### Register aliases for the dispatch program.

The dispatch sequence is a leaf snippet (no callee-saved regs touched);
inputs and the lone scratch register share `t`-class temporaries.
Centralising the names here keeps slice-3's `dispatch_spec` and
slice-5's interpreter wire-up in sync. -/

/-- Holds the address of the opcode byte (`code_base + evm_pc`) on
    entry. Caller-saved (t0). -/
abbrev rOpPtr : Reg := .x5

/-- Holds the jump-table base address on entry. Caller-saved (t1). -/
abbrev rTable : Reg := .x6

/-- Single scratch register: starts as the loaded opcode byte, becomes
    the byte-offset (`opcode * 8`), then the table-entry address, and
    finally the loaded handler address. Caller-saved (t2). -/
abbrev rOp : Reg := .x7

/-! ### Named offsets.

Each LBU/LD here uses offset `0`: the input registers already point
straight at the byte / table entry. Naming them keeps later compose
proofs (slice 3) symbolic and matches the convention in
`OPCODE_TEMPLATE.md`. -/

/-- Offset for the LBU that reads the opcode byte. The opcode pointer
    register already holds the exact byte address. -/
def opcodeLbuOff : BitVec 12 := 0

/-- Shift amount: each table entry is 8 bytes, so the byte offset of
    entry `k` is `k <<< 3`. -/
def entryShiftAmt : BitVec 6 := 3

/-- Offset for the LD that fetches the handler address. The address
    register already holds `table_base + 8 * opcode`. -/
def handlerLdOff : BitVec 12 := 0

/-- Offset for the JALR tail-call. The handler-address register holds
    the absolute target address. -/
def handlerJumpOff : BitVec 12 := 0

/-! ### The dispatch program. -/

/-- Five-instruction RV64 dispatch sequence. Reads the next opcode
    byte through `rOpPtr`, computes the table entry address using
    `rTable + 8 * opcode`, loads the handler address, and JALRs into
    it (with `rd = x0`, so no return address is saved — control will
    only come back through the interpreter loop, not through this
    JALR). -/
def evm_dispatch : Program :=
  LBU  rOp   rOpPtr opcodeLbuOff   ;;
  SLLI rOp   rOp    entryShiftAmt  ;;
  ADD  rOp   rOp    rTable         ;;
  LD   rOp   rOp    handlerLdOff   ;;
  JALR .x0   rOp    handlerJumpOff

/-- The dispatch program is exactly 5 instructions. -/
@[simp] theorem evm_dispatch_length : evm_dispatch.length = 5 := rfl

/-- Convenience: byte-offset address of the dispatch program's tail
    (one past the last instruction), expressed in RV64 4-byte units.
    Useful for compose proofs that step past the JALR. Each RV64
    instruction is 4 bytes wide; the dispatch program occupies bytes
    `[base, base + 20)`. -/
def codeBytes : Nat := 4 * 5

@[simp] theorem codeBytes_eq : codeBytes = 20 := rfl

end Dispatch

end EvmAsm.Evm64
