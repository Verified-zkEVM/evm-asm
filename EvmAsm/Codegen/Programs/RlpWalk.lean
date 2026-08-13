/-
  EvmAsm.Codegen.Programs.RlpWalk

  Cursor-advancing RLP walker primitives -- a single-pass
  alternative to the index-based `rlp_list_nth_item` (PR-K20) used
  by the container decoders in `Tx.lean` / `TxDecode{1559,2930,
  4844,7702}.lean`.

  Motivation: every call to `rlp_list_nth_item` / `rlp_field_to_*`
  re-walks the list from byte 0, so decoding all N fields of one
  container costs 0+1+...+(N-1) = O(N^2) item visits. The pair
  here walks the list exactly once: `rlp_walk_init` positions the
  cursor at the first item, then each `rlp_walk_next` advances
  past exactly one item and reports its content bounds, so the
  decoder consumes fields 0..N-1 in N visits.

  Key invariant.  For every RLP item form, the content (payload)
  start pointer is recoverable from the two values `walk_next`
  returns -- the *advanced* cursor and the *content length*:

      content_ptr = advanced_cursor - content_length

  Verified per form (C = item-start cursor):
    * single byte  (<0x80)   : adv = C+1, len = 1     -> ptr = C
    * short string (0x80..b7): adv = C+1+len          -> ptr = C+1
    * long string  (b8..bf)  : adv = C+1+lol+len      -> ptr = C+1+lol
    * short list   (c0..f7)  : len = full span, ptr = C
    * long list    (f8..ff)  : len = full span, ptr = C

  This mirrors PR-K20's content semantics exactly: byte-string
  items are prefix-stripped, sub-list items are returned in full
  (so callers can recurse / store whole-encoded spans).

  No proofs yet -- these are codegen `String` defs only.  The
  verified cursor-advancing walker in `EvmAsm.Rv64.RLP` (e.g.
  `ValidatingFieldWalk.lean`) is the future verification target.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.RLP.ContentToU64Strict
import EvmAsm.Rv64.RLP.ContentToU256BeStrict
import EvmAsm.Rv64.RLP.Field0ToU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## rlp_walk_init -- position cursor at the first list item

    Skip the outer RLP list prefix (0xc0..0xff) so the cursor
    points at the first encoded child item.

    Calling convention:
      a0 (input)  : list bytes ptr (start of outer list prefix)
      a1 (input)  : total list byte length (full encoded item)
      ra (input)  : return
      a0 (output) : cursor (first child item, abs ptr)
      a1 (output) : end (list_ptr + list_len, exclusive)
      a2 (output) : status (0 ok; nonzero = malformed, distinct per reason):
                      1 not-a-list (prefix < 0xc0)
                      2 empty (list_len == 0)
                      3 short-list length mismatch (1 + (prefix-0xc0) != list_len)
                      4 long-list header truncated (1 + lol > list_len)
                      5 long-list length-field leading zero (len[0] == 0)
                      6 long-list non-minimal (decoded < 56)
                      7 long-list length mismatch (1 + lol + decoded != list_len)

    EXACT (execution-specs-equivalent): the list's self-declared length must
    equal `list_len` -- `1 + lol + decoded` (long) or `1 + (prefix-0xc0)` (short).
    Frameless leaf -- clobbers t0..t6, returns in a0/a1/a2.

    Emitted from the verified body `EvmAsm.Rv64.RLP.rlp_walk_init_prog` (proven
    correct by `rlp_walk_init_spec_within`); the rendered assembly is
    instruction-identical to the prior hand-written version (EEST 200/200 on spike). -/
def rlpWalkInitFunction : String :=
  "rlp_walk_init:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_walk_init_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    verified `rlp_walk_init_prog` rendered under its label, so any future
    hand-edit of `rlpWalkInitFunction` that diverges from the verified body
    fails to typecheck here. -/
theorem rlpWalkInitFunction_eq_verified_prog :
    rlpWalkInitFunction =
      "rlp_walk_init:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_walk_init_prog :=
  rfl

#guard rlpWalkInitFunction.startsWith "rlp_walk_init:\n"
#guard EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = 53

/-! ## rlp_walk_next -- advance cursor past one item (STRICT)

    #12021: recursive wrapper transcribed to Programs (356 B unconverted region).
    Core remains verified `rlp_walk_next_prog` (103 insn). Status 7 = recursively
    invalid list payload via `rlp_validate_payload`.
-/
def rlpWalkNext_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SUB .x5 .x11 .x10,
    .SLLI .x8 .x5 (1 : BitVec 6),
    .LI .x9 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next_shared (GuestAddrs.rlp_walk_next + 28)),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `rlpWalkNext_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpWalkNext_relocs : RelocTable :=
  [ (7, .jal .x1 "rlp_walk_next_shared") ]

def rlpWalkNextEntryFunction : String :=
  "rlp_walk_next:\n" ++ emitProgramR rlpWalkNext_prog rlpWalkNext_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpWalkNext_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpWalkNextEntryFunction_eq_prog :
    rlpWalkNextEntryFunction = "rlp_walk_next:\n" ++ emitProgramR rlpWalkNext_prog rlpWalkNext_relocs := rfl

#guard rlpWalkNextEntryFunction.startsWith "rlp_walk_next:\n"
#guard rlpWalkNext_prog.length = 13

def rlpWalkNextNested_prog : Program :=
  [ .JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared (GuestAddrs.rlp_walk_next_nested + 0)) ]

/-- Reloc side-table for `rlpWalkNextNested_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpWalkNextNested_relocs : RelocTable :=
  [ (0, .jal .x0 "rlp_walk_next_shared") ]

def rlpWalkNextNestedFunction : String :=
  "rlp_walk_next_nested:\n" ++ emitProgramR rlpWalkNextNested_prog rlpWalkNextNested_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpWalkNextNested_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpWalkNextNestedFunction_eq_prog :
    rlpWalkNextNestedFunction = "rlp_walk_next_nested:\n" ++ emitProgramR rlpWalkNextNested_prog rlpWalkNextNested_relocs := rfl

#guard rlpWalkNextNestedFunction.startsWith "rlp_walk_next_nested:\n"
#guard rlpWalkNextNested_prog.length = 1

def rlpWalkNextShared_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next_core (GuestAddrs.rlp_walk_next_shared + 16)),
    .SD .x2 .x10 (24 : BitVec 12),
    .SD .x2 .x11 (32 : BitVec 12),
    .SD .x2 .x12 (40 : BitVec 12),
    .BNE .x11 .x0 (152 : BitVec 13),
    .LI .x5 (2 : Word),
    .BLTU .x8 .x5 (128 : BitVec 13),
    .ADDI .x8 .x8 (-2 : BitVec 12),
    .LD .x5 .x2 (8 : BitVec 12),
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (192 : Word),
    .BLTU .x6 .x7 (124 : BitVec 13),
    .LI .x7 (1024 : Word),
    .BGEU .x9 .x7 (100 : BitVec 13),
    .ADDI .x9 .x9 (1 : BitVec 12),
    .LD .x11 .x2 (24 : BitVec 12),
    .LI .x7 (248 : Word),
    .BLTU .x6 .x7 (64 : BitVec 13),
    .LI .x7 (247 : Word),
    .SUB .x28 .x6 .x7,
    .MV .x13 .x28,
    .ADDI .x29 .x5 (1 : BitVec 12),
    .LI .x30 (0 : Word),
    .BEQ .x28 .x0 (28 : BitVec 13),
    .SLLI .x30 .x30 (8 : BitVec 6),
    .LBU .x31 .x29 (0 : BitVec 12),
    .OR .x30 .x30 .x31,
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x12 .x5 .x13,
    .ADDI .x12 .x12 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x12 .x5 (1 : BitVec 12),
    .MV .x10 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_validate_payload (GuestAddrs.rlp_walk_next_shared + 156)),
    .ADDI .x9 .x9 (-1 : BitVec 12),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .LD .x10 .x2 (8 : BitVec 12),
    .LI .x11 (7 : Word),
    .LI .x12 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LD .x10 .x2 (24 : BitVec 12),
    .LD .x11 .x2 (32 : BitVec 12),
    .LD .x12 .x2 (40 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `rlpWalkNextShared_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpWalkNextShared_relocs : RelocTable :=
  [ (4, .jal .x1 "rlp_walk_next_core"),
    (39, .jal .x1 "rlp_validate_payload") ]

def rlpWalkNextSharedFunction : String :=
  "rlp_walk_next_shared:\n" ++ emitProgramR rlpWalkNextShared_prog rlpWalkNextShared_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpWalkNextShared_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpWalkNextSharedFunction_eq_prog :
    rlpWalkNextSharedFunction = "rlp_walk_next_shared:\n" ++ emitProgramR rlpWalkNextShared_prog rlpWalkNextShared_relocs := rfl

#guard rlpWalkNextSharedFunction.startsWith "rlp_walk_next_shared:\n"
#guard rlpWalkNextShared_prog.length = 52

def rlpValidatePayload_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .LD .x10 .x2 (8 : BitVec 12),
    .LD .x5 .x2 (16 : BitVec 12),
    .MV .x11 .x5,
    .BEQ .x10 .x5 (32 : BitVec 13),
    .BLTU .x5 .x10 (44 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next_nested (GuestAddrs.rlp_validate_payload + 36)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .LD .x5 .x2 (16 : BitVec 12),
    .BLTU .x5 .x10 (28 : BitVec 13),
    .SD .x2 .x10 (8 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (7 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `rlpValidatePayload_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpValidatePayload_relocs : RelocTable :=
  [ (9, .jal .x1 "rlp_walk_next_nested") ]

def rlpValidatePayloadFunction : String :=
  "rlp_validate_payload:\n" ++ emitProgramR rlpValidatePayload_prog rlpValidatePayload_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpValidatePayload_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpValidatePayloadFunction_eq_prog :
    rlpValidatePayloadFunction = "rlp_validate_payload:\n" ++ emitProgramR rlpValidatePayload_prog rlpValidatePayload_relocs := rfl

#guard rlpValidatePayloadFunction.startsWith "rlp_validate_payload:\n"
#guard rlpValidatePayload_prog.length = 23

def rlpWalkNextCore_prog : Program :=
  [ .BGEU .x10 .x11 (brOff (GuestAddrs.rlp_walk_next_core + 352) (GuestAddrs.rlp_walk_next_core + 0)),
    .LBU .x5 .x10 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.rlp_walk_next_core + 300) (GuestAddrs.rlp_walk_next_core + 12)),
    .LI .x6 (184 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.rlp_walk_next_core + 248) (GuestAddrs.rlp_walk_next_core + 20)),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.rlp_walk_next_core + 148) (GuestAddrs.rlp_walk_next_core + 28)),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.rlp_walk_next_core + 316) (GuestAddrs.rlp_walk_next_core + 36)),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .ADDI .x6 .x7 (1 : BitVec 12),
    .ADD .x29 .x10 .x6,
    .BLTU .x11 .x29 (brOff (GuestAddrs.rlp_walk_next_core + 364) (GuestAddrs.rlp_walk_next_core + 56)),
    .ADDI .x30 .x10 (1 : BitVec 12),
    .LBU .x31 .x30 (0 : BitVec 12),
    .BEQ .x31 .x0 (brOff (GuestAddrs.rlp_walk_next_core + 388) (GuestAddrs.rlp_walk_next_core + 68)),
    .LI .x28 (0 : Word),
    .MV .x6 .x7,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x31 .x30 (0 : BitVec 12),
    .OR .x28 .x28 .x31,
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x6 (56 : Word),
    .BLTU .x28 .x6 (brOff (GuestAddrs.rlp_walk_next_core + 376) (GuestAddrs.rlp_walk_next_core + 112)),
    .ADD .x31 .x7 .x28,
    .ADDI .x31 .x31 (1 : BitVec 12),
    .SUB .x6 .x11 .x29,
    .BLTU .x6 .x28 (brOff (GuestAddrs.rlp_walk_next_core + 364) (GuestAddrs.rlp_walk_next_core + 128)),
    .ADD .x10 .x31 .x10,
    .MV .x12 .x31,
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (183 : Word),
    .SUB .x7 .x5 .x6,
    .ADDI .x6 .x7 (1 : BitVec 12),
    .ADD .x29 .x10 .x6,
    .BLTU .x11 .x29 (brOff (GuestAddrs.rlp_walk_next_core + 364) (GuestAddrs.rlp_walk_next_core + 164)),
    .ADDI .x30 .x10 (1 : BitVec 12),
    .LBU .x31 .x30 (0 : BitVec 12),
    .BEQ .x31 .x0 (brOff (GuestAddrs.rlp_walk_next_core + 388) (GuestAddrs.rlp_walk_next_core + 176)),
    .LI .x28 (0 : Word),
    .MV .x6 .x7,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x31 .x30 (0 : BitVec 12),
    .OR .x28 .x28 .x31,
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x6 (56 : Word),
    .BLTU .x28 .x6 (brOff (GuestAddrs.rlp_walk_next_core + 376) (GuestAddrs.rlp_walk_next_core + 220)),
    .SUB .x6 .x11 .x29,
    .BLTU .x6 .x28 (brOff (GuestAddrs.rlp_walk_next_core + 364) (GuestAddrs.rlp_walk_next_core + 228)),
    .ADD .x10 .x29 .x28,
    .MV .x12 .x28,
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .SUB .x12 .x5 .x6,
    .ADDI .x7 .x10 (1 : BitVec 12),
    .SUB .x28 .x11 .x10,
    .BGEU .x12 .x28 (brOff (GuestAddrs.rlp_walk_next_core + 364) (GuestAddrs.rlp_walk_next_core + 264)),
    .LI .x6 (1 : Word),
    .BNE .x12 .x6 (16 : BitVec 13),
    .LBU .x6 .x7 (0 : BitVec 12),
    .LI .x29 (128 : Word),
    .BLTU .x6 .x29 (brOff (GuestAddrs.rlp_walk_next_core + 400) (GuestAddrs.rlp_walk_next_core + 284)),
    .ADD .x10 .x7 .x12,
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .LI .x12 (1 : Word),
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .SUB .x31 .x5 .x6,
    .ADDI .x31 .x31 (1 : BitVec 12),
    .SUB .x6 .x11 .x10,
    .BLTU .x6 .x31 (32 : BitVec 13),
    .ADD .x10 .x31 .x10,
    .MV .x12 .x31,
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x11 (2 : Word),
    .LI .x12 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x11 (3 : Word),
    .LI .x12 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x11 (4 : Word),
    .LI .x12 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x11 (5 : Word),
    .LI .x12 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x11 (6 : Word),
    .LI .x12 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpWalkNextCoreFunction : String :=
  "rlp_walk_next_core:\n" ++ emitProgram rlpWalkNextCore_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpWalkNextCore_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpWalkNextCoreFunction_eq_prog :
    rlpWalkNextCoreFunction = "rlp_walk_next_core:\n" ++ emitProgram rlpWalkNextCore_prog := rfl

#guard rlpWalkNextCoreFunction.startsWith "rlp_walk_next_core:\n"
#guard rlpWalkNextCore_prog.length = 103

/-! **Guest-anchor tie for the verified core.**

    The semantic triple in `EvmAsm.Rv64.RLP.WalkNext` is parameterised by a
    code base and names `rlp_walk_next_code base`, while this Codegen module
    names the linked entry through `GuestAddrs.rlp_walk_next_core`. Keep the
    two program copies tied without pinning the numeric address: the only
    equality needed here is the program-body equality above, and the base is
    the symbolic GuestAddrs value. -/
theorem rlpWalkNextCoreCode_eq_verified :
    CodeReq.ofProg (GuestAddrs.rlp_walk_next_core : Word) rlpWalkNextCore_prog =
      EvmAsm.Rv64.RLP.rlp_walk_next_code
        (GuestAddrs.rlp_walk_next_core : Word) := by
  change CodeReq.ofProg (GuestAddrs.rlp_walk_next_core : Word) rlpWalkNextCore_prog =
    CodeReq.ofProg (GuestAddrs.rlp_walk_next_core : Word)
      EvmAsm.Rv64.RLP.rlp_walk_next_prog
  rw [show rlpWalkNextCore_prog = EvmAsm.Rv64.RLP.rlp_walk_next_prog from rfl]

/-- Concatenated emission used by Dispatch: entry+nested+shared+validate+core. -/
def rlpWalkNextFunction : String :=
  rlpWalkNextEntryFunction ++ "\n" ++
  rlpWalkNextNestedFunction ++ "\n" ++
  rlpWalkNextSharedFunction ++ "\n" ++
  rlpValidatePayloadFunction ++ "\n" ++
  rlpWalkNextCoreFunction

#guard rlpWalkNextFunction.startsWith "rlp_walk_next:\n"

/-! ## rlp_content_to_u64 -- big-endian content bytes -> u64

    Decode a big-endian byte string (the prefix-stripped payload
    of an RLP byte-string item, as reported by `rlp_walk_next`) as
    a u64.  This is the BE-decode half of PR-K34
    `rlp_field_to_u64`, taking an explicit (ptr, len) instead of
    re-walking the list.

    Emitted from the verified **lenient** body
    `EvmAsm.Rv64.RLP.rlp_content_to_u64_prog` (proven correct by the three-way
    dispatch theorem `rlp_content_to_u64_spec_within`, see
    `EvmAsm/Rv64/RLP/ContentToU64.lean`). Leading-zero scalar bytes are accepted,
    matching the guest's `int.from_bytes` semantics; only over-width content
    returns status `2`.

    Calling convention:
      a0 (input)  : content bytes ptr
      a1 (input)  : content byte length
      ra (input)  : return
      a0 (output) : u64 value (LE register form)
      a1 (output) : status (0 ok / 2 too long (> 8 bytes))

    Frameless leaf. -/
def rlpContentToU64Function : String :=
  "rlp_content_to_u64:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    verified `rlp_content_to_u64_prog` rendered under its label, so any
    future hand-edit of `rlpContentToU64Function` that diverges from the
    verified body fails to typecheck here. -/
theorem rlpContentToU64Function_eq_verified_prog :
    rlpContentToU64Function =
      "rlp_content_to_u64:\n" ++ emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u64_prog :=
  rfl

#guard rlpContentToU64Function.startsWith "rlp_content_to_u64:\n"
#guard EvmAsm.Rv64.RLP.rlp_content_to_u64_prog.length = 18

/-! ## rlp_content_to_u64_strict -- canonical scalar -> u64

    This is the typed-transaction / typed-withdrawal surface.  It is kept
    beside the lenient witness/account decoder because the two callers have
    different reference semantics: typed scalar decoding rejects a leading
    zero, while account and BAL state witnesses use `int.from_bytes`.

    The strict leaf returns status `3` for a nonempty payload whose first byte
    is zero, status `2` for a payload wider than eight bytes, and status `0`
    otherwise. -/
def rlpContentToU64StrictFunction : String :=
  "rlp_content_to_u64_strict:\n" ++
    emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog

theorem rlpContentToU64StrictFunction_eq_verified_prog :
    rlpContentToU64StrictFunction =
      "rlp_content_to_u64_strict:\n" ++
        emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog :=
  rfl

#guard rlpContentToU64StrictFunction.startsWith "rlp_content_to_u64_strict:\n"
#guard EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog.length = 22

/-! ## rlp_content_to_u256_be -- right-align content bytes -> u256 BE

    Right-align a big-endian byte string (the prefix-stripped
    payload of an RLP byte-string item) into a 32-byte BE u256
    buffer.  This is the copy half of PR-K35
    `rlp_field_to_u256_be`, taking an explicit (ptr, len, out)
    instead of re-walking the list.

    Emitted from the verified **lenient** body
    `EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog` (proven correct by the
    three-way dispatch theorem `rlp_content_to_u256_be_spec_within`, see
    `EvmAsm/Rv64/RLP/ContentToU256Be.lean`). Behavior difference from the
    prior hand-written body that matters for callers: leading-zero scalar bytes
    are accepted and right-aligned; only content wider than 32 bytes returns
    status `2`.

    Calling convention:
      a0 (input)  : content bytes ptr
      a1 (input)  : content byte length
      a2 (input)  : 32-byte u256 BE output ptr (right-aligned)
      ra (input)  : return
      a0 (output) : status
                      0 ok (len <= 32)
                      2 too long (len > 32)

    The output is always zeroed first, so fail / too-long
    paths leave a zero u256. Frameless leaf. -/
def rlpContentToU256BeFunction : String :=
  "rlp_content_to_u256_be:\n" ++
    emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    verified `rlp_content_to_u256_be_prog` rendered under its label, so any
    future hand-edit of `rlpContentToU256BeFunction` that diverges from the
    verified body fails to typecheck here. -/
theorem rlpContentToU256BeFunction_eq_verified_prog :
    rlpContentToU256BeFunction =
      "rlp_content_to_u256_be:\n" ++
        emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog :=
  rfl

#guard rlpContentToU256BeFunction.startsWith "rlp_content_to_u256_be:\n"
#guard EvmAsm.Rv64.RLP.rlp_content_to_u256_be_prog.length = 26

/-! ## rlp_content_to_u256_be_strict -- canonical scalar -> u256 BE

    The strict typed-scalar counterpart of the lenient state-witness helper.
    It uses the same output-buffer ABI and adds status `3` for a nonempty
    leading-zero payload. -/
def rlpContentToU256BeStrictFunction : String :=
  "rlp_content_to_u256_be_strict:\n" ++
    emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u256_be_strict_prog

theorem rlpContentToU256BeStrictFunction_eq_verified_prog :
    rlpContentToU256BeStrictFunction =
      "rlp_content_to_u256_be_strict:\n" ++
        emitProgram EvmAsm.Rv64.RLP.rlp_content_to_u256_be_strict_prog :=
  rfl

#guard rlpContentToU256BeStrictFunction.startsWith "rlp_content_to_u256_be_strict:\n"
#guard EvmAsm.Rv64.RLP.rlp_content_to_u256_be_strict_prog.length = 26

/-! ## rlp_field0_to_u64 -- fixed-offset first-field u64 wrapper

    Experimental verified-layout alternative to the index-based
    rlp_field_to_u64 helper for callers that only need field 0. The emitted
    image is the wrapper plus the verified walk/content callees, padded with
    NOPs so the wrapper's fixed PC-relative JAL offsets land at the proven
    callee entry points.

    The wrapper body is partially verified today: the shared parse-failure tail
    is proved by rlp_field0_to_u64_parse_fail_spec_within, and the successful
    content_to_u64 call composition is proved by
    rlp_field0_to_u64_content_call_success_spec_within. The remaining work is
    to compose walk_init and walk_next into the unified top theorem. -/
def rlpField0ToU64Function : String :=
  "rlp_field0_to_u64:\n" ++
    emitProgram EvmAsm.Rv64.RLP.rlp_field0_to_u64_full_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly the
    deployable fixed-offset image from EvmAsm.Rv64.RLP.Field0ToU64. -/
theorem rlpField0ToU64Function_eq_verified_prog :
    rlpField0ToU64Function =
      "rlp_field0_to_u64:\n" ++
        emitProgram EvmAsm.Rv64.RLP.rlp_field0_to_u64_full_prog :=
  rfl

#guard rlpField0ToU64Function.startsWith "rlp_field0_to_u64:\n"
#guard EvmAsm.Rv64.RLP.rlp_field0_to_u64_prog.length = 15
#guard EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = 53
#guard EvmAsm.Rv64.RLP.rlp_walk_next_prog.length = 103
#guard EvmAsm.Rv64.RLP.rlp_content_to_u64_prog.length = 18

/-! The cursor-walk primitives concatenated as a single helper block.

    Standalone debug probes that embed the tx/header decoders (which now use
    the single-pass cursor walker) must link these bodies too. Mirrors the
    index-based RLP primitives each such probe already bundles; centralised
    here so new probes don't hand-copy the six helper definitions (the documented closure-drift
    pattern, see `BlockVerdictV2.lean` ziskStatelessVerdictV2ProbeUnit). -/
def rlpWalkHelpersClosure : String :=
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  rlpContentToU64Function ++ "\n" ++
  rlpContentToU256BeFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpContentToU256BeStrictFunction

/-- Kernel-checked drift guard: the closure is exactly the concatenation of
    the six guarded helper definitions, so future edits cannot quietly
    bypass one of them (each helper is itself tied to its verified Rv64
    program by `rlpWalkInitFunction_eq_verified_prog`,
    `rlpWalkNextCoreFunction_eq_prog`,
    `rlpContentToU64Function_eq_verified_prog`, and
    `rlpContentToU256BeFunction_eq_verified_prog` and their strict counterparts). -/
theorem rlpWalkHelpersClosure_eq_helpers :
    rlpWalkHelpersClosure =
      rlpWalkInitFunction ++ "\n" ++
      rlpWalkNextFunction ++ "\n" ++
      rlpContentToU64Function ++ "\n" ++
      rlpContentToU256BeFunction ++ "\n" ++
      rlpContentToU64StrictFunction ++ "\n" ++
      rlpContentToU256BeStrictFunction :=
  rfl

end EvmAsm.Codegen
