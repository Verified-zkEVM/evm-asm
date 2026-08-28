/-
  EvmAsm.Codegen.Programs.EvmHashHandlerProg

  `Program` view of the KECCAK256 dispatcher handler `h_KECCAK256`
  (GH #12204, the proving witness for the handler lane).

  This is the FIRST `h_*` opcode handler with a `Program` view: before it,
  0 of the MANIFEST's converted routines covered any dispatcher handler, and
  the two structural blockers were the ones #12204 scoped away —

    * numeric GNU-as local labels (`137f` / `137:`) in
      `stackUnderflowGuardAsm`, taught to the converter in step 2; and
    * the eleven conditional branches to `.exit_outofgas` (eight `bnez`,
      three `bltu`), ~65 KB out of B-type reach, which GNU-as relaxes to
      `b<inv> .+8 ; j .exit_outofgas`.  Step 1 chose
      the symbolic-branch reloc kind (`AsmSym.br`) over trampolines, so the
      `Program` carries the relaxed PAIR with the `j` target resolved through
      `jalOff GuestAddrs.exit_outofgas` while the EMITTED text keeps the one
      source line.  `h_KECCAK256` is the first CONVERTED routine to carry a
      `.br` reloc, i.e. the first to exercise that arm of `emitProgramR`
      outside the two examples pinned in `Emit.lean`.

  Two views, the standard wave-.9.3 shape:

    * `hKeccak256_prog`     — the VERIFICATION view: concrete guest-linked
      immediates (`laHi`/`laLo`/`jalOff GuestAddrs.…`), 162 instructions =
      648 bytes, exactly the extent from `h_KECCAK256` to the next `.text`
      symbol `h_LOG0` in the linker facts.
    * `hKeccak256Function`  — the EMISSION view: `emitProgramR` keeps
      `la`/`jal`/`b<cond>` symbolic, so every linked image relocates it
      against its own layout.

  **What ties this to the SHIPPED handler.**  The deployed text is not a
  literal: it is `OpcodeHandlerSpec.emitSubroutine` applied to the head of
  `hashHandlers`, assembled from `stackUnderflowGuardAsm`,
  `keccakRangeGuardAsm`, `keccakWordGasAsm`, `updateActiveMemorySizeAsm` and
  `dispatchContinueRet`.  A `rfl` against that string is NOT available: the
  emitted source uses assembler spellings a `Program` render cannot produce
  (`137f` / `.Lkeccak_range_ok` labels, `bnez`, `ret`, `zero`), and forcing
  string equality would mean rewriting five helpers shared by every other
  handler.  The tie is therefore the byte one, which is also the one #12204's
  acceptance line asks for:

    1. `scripts/asm-fixtures/hKeccak256Function.s` is the emitter's output,
       and `check-asm-to-program.sh` assembles the real Lean render of
       `hKeccak256Function` against it — `.text`-identical, 648/648 bytes —
       and separately checks that the CONCRETE Program's baked immediates
       match what the guest link produces for the symbolic form;
    2. the `guestImageEntries` row `(GuestAddrs.h_KECCAK256, hKeccak256_prog)`
       is compared against the LINKED ELF at the real entry address by
       `scripts/check-guest-image-program-bytes.py` (run from
       `codegen-stateless-link-check.sh`).  That ELF is produced from
       `emitSubroutine`, so an edit to any of the five helpers moves the
       shipped bytes and fails this gate — the fixture cannot go stale
       silently.
-/

import EvmAsm.Codegen.Programs.EvmHashHandlers

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Verification view of the emitted `h_KECCAK256` subroutine: 162
    instructions (648 bytes) at `GuestAddrs.h_KECCAK256`, with the
    link-layout-dependent operands carried as `laHi`/`laLo`/`jalOff`
    against the guest address table. -/
def hKeccak256_prog : Program :=
  [ .AUIPC .x14 (laHi GuestAddrs.evm_cur_stack_top (GuestAddrs.h_KECCAK256 + 0)),
    .ADDI .x14 .x14 (laLo GuestAddrs.evm_cur_stack_top (GuestAddrs.h_KECCAK256 + 0)),
    .LD .x14 .x14 (0 : BitVec 12),
    .ADDI .x14 .x14 (-64 : BitVec 12),
    .BGEU .x14 .x12 (24 : BitVec 13),
    .LI .x5 (7 : Word),
    .AUIPC .x6 (laHi GuestAddrs.evm_halt_flag (GuestAddrs.h_KECCAK256 + 24)),
    .ADDI .x6 .x6 (laLo GuestAddrs.evm_halt_flag (GuestAddrs.h_KECCAK256 + 24)),
    .SD .x6 .x5 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LD .x5 .x12 (40 : BitVec 12),
    .BEQ .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 48)),
    .LD .x5 .x12 (48 : BitVec 12),
    .BEQ .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 60)),
    .LD .x5 .x12 (56 : BitVec 12),
    .BEQ .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 72)),
    .LD .x15 .x12 (32 : BitVec 12),
    .BEQ .x15 .x0 (56 : BitVec 13),
    .LD .x5 .x12 (8 : BitVec 12),
    .BEQ .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 92)),
    .LD .x5 .x12 (16 : BitVec 12),
    .BEQ .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 104)),
    .LD .x5 .x12 (24 : BitVec 12),
    .BEQ .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 116)),
    .LD .x14 .x12 (0 : BitVec 12),
    .ADD .x5 .x14 .x15,
    .BGEU .x5 .x14 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 132)),
    .LD .x14 .x12 (0 : BitVec 12),
    .LD .x15 .x12 (32 : BitVec 12),
    .ADDI .x5 .x15 (31 : BitVec 12),
    .BGEU .x5 .x15 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 152)),
    .SRLI .x5 .x5 (5 : BitVec 6),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x6 .x6 .x5,
    .ADD .x6 .x6 .x5,
    .LD .x5 .x20 (568 : BitVec 12),
    .BGEU .x5 .x6 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 180)),
    .SUB .x5 .x5 .x6,
    .SD .x20 .x5 (568 : BitVec 12),
    .BEQ .x15 .x0 (brOff (GuestAddrs.h_KECCAK256 + 336) (GuestAddrs.h_KECCAK256 + 192)),
    .ADD .x16 .x14 .x15,
    .ADDI .x16 .x16 (31 : BitVec 12),
    .LI .x18 (-32 : Word),
    .AND .x16 .x16 .x18,
    .LD .x17 .x20 (488 : BitVec 12),
    .BGEU .x17 .x16 (brOff (GuestAddrs.h_KECCAK256 + 336) (GuestAddrs.h_KECCAK256 + 216)),
    .SRLI .x18 .x16 (5 : BitVec 6),
    .MULHU .x6 .x18 .x18,
    .BEQ .x6 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 232)),
    .MUL .x6 .x18 .x18,
    .SRLI .x6 .x6 (9 : BitVec 6),
    .ADD .x6 .x6 .x18,
    .ADD .x6 .x6 .x18,
    .ADD .x6 .x6 .x18,
    .SRLI .x18 .x17 (5 : BitVec 6),
    .MUL .x17 .x18 .x18,
    .SRLI .x17 .x17 (9 : BitVec 6),
    .ADD .x17 .x17 .x18,
    .ADD .x17 .x17 .x18,
    .ADD .x17 .x17 .x18,
    .SUB .x6 .x6 .x17,
    .LD .x18 .x20 (568 : BitVec 12),
    .BGEU .x18 .x6 (8 : BitVec 13),
    .JAL .x0 (jalOff GuestAddrs.exit_outofgas (GuestAddrs.h_KECCAK256 + 292)),
    .SUB .x18 .x18 .x6,
    .SD .x20 .x18 (568 : BitVec 12),
    .LD .x17 .x20 (488 : BitVec 12),
    .ADD .x18 .x13 .x17,
    .ADD .x6 .x13 .x16,
    .BEQ .x18 .x6 (16 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .ADDI .x18 .x18 (8 : BitVec 12),
    .JAL .x0 (-12 : BitVec 21),
    .SD .x20 .x16 (488 : BitVec 12),
    .MV .x26 .x10,
    .LD .x5 .x12 (0 : BitVec 12),
    .LD .x11 .x12 (32 : BitVec 12),
    .ADDI .x12 .x12 (32 : BitVec 12),
    .ADD .x10 .x13 .x5,
    .MV .x12 .x12,
    .MV .x27 .x12,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.h_KECCAK256 + 364)),
    .MV .x10 .x26,
    .MV .x12 .x27,
    .LBU .x7 .x12 (0 : BitVec 12),
    .LBU .x28 .x12 (31 : BitVec 12),
    .SB .x12 .x28 (0 : BitVec 12),
    .SB .x12 .x7 (31 : BitVec 12),
    .LBU .x7 .x12 (1 : BitVec 12),
    .LBU .x28 .x12 (30 : BitVec 12),
    .SB .x12 .x28 (1 : BitVec 12),
    .SB .x12 .x7 (30 : BitVec 12),
    .LBU .x7 .x12 (2 : BitVec 12),
    .LBU .x28 .x12 (29 : BitVec 12),
    .SB .x12 .x28 (2 : BitVec 12),
    .SB .x12 .x7 (29 : BitVec 12),
    .LBU .x7 .x12 (3 : BitVec 12),
    .LBU .x28 .x12 (28 : BitVec 12),
    .SB .x12 .x28 (3 : BitVec 12),
    .SB .x12 .x7 (28 : BitVec 12),
    .LBU .x7 .x12 (4 : BitVec 12),
    .LBU .x28 .x12 (27 : BitVec 12),
    .SB .x12 .x28 (4 : BitVec 12),
    .SB .x12 .x7 (27 : BitVec 12),
    .LBU .x7 .x12 (5 : BitVec 12),
    .LBU .x28 .x12 (26 : BitVec 12),
    .SB .x12 .x28 (5 : BitVec 12),
    .SB .x12 .x7 (26 : BitVec 12),
    .LBU .x7 .x12 (6 : BitVec 12),
    .LBU .x28 .x12 (25 : BitVec 12),
    .SB .x12 .x28 (6 : BitVec 12),
    .SB .x12 .x7 (25 : BitVec 12),
    .LBU .x7 .x12 (7 : BitVec 12),
    .LBU .x28 .x12 (24 : BitVec 12),
    .SB .x12 .x28 (7 : BitVec 12),
    .SB .x12 .x7 (24 : BitVec 12),
    .LBU .x7 .x12 (8 : BitVec 12),
    .LBU .x28 .x12 (23 : BitVec 12),
    .SB .x12 .x28 (8 : BitVec 12),
    .SB .x12 .x7 (23 : BitVec 12),
    .LBU .x7 .x12 (9 : BitVec 12),
    .LBU .x28 .x12 (22 : BitVec 12),
    .SB .x12 .x28 (9 : BitVec 12),
    .SB .x12 .x7 (22 : BitVec 12),
    .LBU .x7 .x12 (10 : BitVec 12),
    .LBU .x28 .x12 (21 : BitVec 12),
    .SB .x12 .x28 (10 : BitVec 12),
    .SB .x12 .x7 (21 : BitVec 12),
    .LBU .x7 .x12 (11 : BitVec 12),
    .LBU .x28 .x12 (20 : BitVec 12),
    .SB .x12 .x28 (11 : BitVec 12),
    .SB .x12 .x7 (20 : BitVec 12),
    .LBU .x7 .x12 (12 : BitVec 12),
    .LBU .x28 .x12 (19 : BitVec 12),
    .SB .x12 .x28 (12 : BitVec 12),
    .SB .x12 .x7 (19 : BitVec 12),
    .LBU .x7 .x12 (13 : BitVec 12),
    .LBU .x28 .x12 (18 : BitVec 12),
    .SB .x12 .x28 (13 : BitVec 12),
    .SB .x12 .x7 (18 : BitVec 12),
    .LBU .x7 .x12 (14 : BitVec 12),
    .LBU .x28 .x12 (17 : BitVec 12),
    .SB .x12 .x28 (14 : BitVec 12),
    .SB .x12 .x7 (17 : BitVec 12),
    .LBU .x7 .x12 (15 : BitVec 12),
    .LBU .x28 .x12 (16 : BitVec 12),
    .SB .x12 .x28 (15 : BitVec 12),
    .SB .x12 .x7 (16 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .AUIPC .x1 (laHi GuestAddrs.dispatch_resume (GuestAddrs.h_KECCAK256 + 636)),
    .ADDI .x1 .x1 (laLo GuestAddrs.dispatch_resume (GuestAddrs.h_KECCAK256 + 636)),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `hKeccak256_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def hKeccak256_relocs : RelocTable :=
  [ (0, .la .x14 "evm_cur_stack_top"),
    (6, .la .x6 "evm_halt_flag"),
    (11, .br .bne .x5 .x0 ".exit_outofgas"),
    (14, .br .bne .x5 .x0 ".exit_outofgas"),
    (17, .br .bne .x5 .x0 ".exit_outofgas"),
    (22, .br .bne .x5 .x0 ".exit_outofgas"),
    (25, .br .bne .x5 .x0 ".exit_outofgas"),
    (28, .br .bne .x5 .x0 ".exit_outofgas"),
    (32, .br .bltu .x5 .x14 ".exit_outofgas"),
    (37, .br .bltu .x5 .x15 ".exit_outofgas"),
    (44, .br .bltu .x5 .x6 ".exit_outofgas"),
    (57, .br .bne .x6 .x0 ".exit_outofgas"),
    (72, .br .bltu .x18 .x6 ".exit_outofgas"),
    (91, .jal .x1 "zkvm_keccak256"),
    (159, .la .x1 ".dispatch_resume") ]

def hKeccak256Function : String :=
  "h_KECCAK256:\n" ++ emitProgramR hKeccak256_prog hKeccak256_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `hKeccak256_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem hKeccak256Function_eq_prog :
    hKeccak256Function = "h_KECCAK256:\n" ++ emitProgramR hKeccak256_prog hKeccak256_relocs := rfl

#guard hKeccak256Function.startsWith "h_KECCAK256:\n"
#guard hKeccak256_prog.length = 162

/-! Extent cross-check against the linker facts: the handler runs from
    `h_KECCAK256` to the next `.text` symbol `h_LOG0`, an extent of
    `162 * 4 = 648` bytes.  Stated as `4 * length` rather than a pinned
    byte literal so it cannot drift away from the Program above; the
    addresses themselves are never spelled here, they live in
    `GuestAddrs` and in `scripts/asm-fixtures/symbol-addresses.tsv`. -/
#guard 4 * hKeccak256_prog.length = 648

end EvmAsm.Codegen
