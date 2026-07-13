/-
  EvmAsm.Codegen.Layout

  Asm program layout: the `_start` text-unit wrapper, halt stubs, and the
  `BuildUnit` glue that lets a verified `Program` body sit alongside raw
  asm text (prologue, epilogue, `.data` seeding) needed to run on
  `ziskemu`.

  Halt convention is parametric (see CODEGEN.md §"Locked decisions"):
    `.sp1`     — `ECALL` with `t0 = 0`, matches the verified
                 `step_ecall_halt` (`EvmAsm/Rv64/Execution.lean:611-615`).
                 `ziskemu` does NOT honor this (resolved 2026-05-18 — see
                 CODEGEN.md §Tricky bits #5).
    `.linux93` — `ECALL` with `a7 = 93`, matches Zisk's `simple_add`.
                 `ziskemu` halts cleanly. Default for codegen output.

  The halt stubs and any prologue/epilogue/.data are emitted as raw
  GNU-as text rather than as `Instr` values because they sit outside the
  verified body. This keeps `emitInstr` total over `Instr` without
  forcing M2+ wiring (write_output, data sections, `la` pseudo) into
  the verified core.
-/

import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Halt convention selected at codegen time. -/
inductive HaltConv where
  | sp1
  | linux93
  deriving DecidableEq, Repr

namespace HaltConv

def ofString? : String → Option HaltConv
  | "sp1"     => some .sp1
  | "linux93" => some .linux93
  | _         => none

def toString : HaltConv → String
  | .sp1     => "sp1"
  | .linux93 => "linux93"

instance : ToString HaltConv := ⟨HaltConv.toString⟩

end HaltConv

/-! ## Verified memory zones (mirror of `EvmAsm/Rv64/Basic.lean`)

    Post-#5164 the verified model recognises three disjoint zones;
    the codegen side carries the same constants so any address-bounds
    introspection downstream sees the same numeric values.
-/

/-- Inclusive lower bound of the legacy valid memory zone.
    Mirrors `MEM_START` at `EvmAsm/Rv64/Basic.lean`. -/
def MEM_START : Nat := 0x20

/-- Inclusive upper bound of the legacy valid memory zone. -/
def MEM_END : Nat := 0x78000000

/-- Lower bound of the input-buffer zone (matches `INPUT_ADDR`). -/
def INPUT_MEM_START : Nat := 0x40000000

/-- Upper bound of the input-buffer zone. -/
def INPUT_MEM_END : Nat := 0x40002000

/-- Lower bound of the writable-RAM zone (covers `.data`
    and `OUTPUT_ADDR`). -/
def RAM_MEM_START : Nat := 0xa0000000

/-- Upper bound of the writable-RAM zone. -/
def RAM_MEM_END : Nat := 0xc0000000

/-- A program-plus-wrapping that codegen knows how to turn into a single
    `.s` file: the verified RV64 body, optional raw-asm prologue and
    epilogue (e.g. data-pointer setup and `write_output`), and an
    optional `.data` section. -/
structure BuildUnit where
  /-- The verified body, rendered via `emitProgram`. -/
  body         : Program
  /-- Raw asm emitted after `_start:` and before `body` (e.g.
      `la x12, operands`). Empty string means "omit". -/
  prologueAsm  : String := ""
  /-- Raw asm emitted after `body` and before the halt stub (e.g.
      a `write_output` ecall sequence). Empty string means "omit". -/
  epilogueAsm  : String := ""
  /-- Raw asm for a `.data` section, including the `.section .data`
      header. Emitted after the halt stub. Empty string means "omit". -/
  dataAsm      : String := ""

/-- Halt stub emitted after the body + epilogue. -/
def emitHaltStub : HaltConv → String
  | .sp1 =>
      "  li x5, 0\n" ++
      "  ecall"
  | .linux93 =>
      "  li x17, 93\n" ++
      "  li x10, 0\n" ++
      "  ecall"

/-- Header preamble: disable RVC so every encoding is a 4-byte instruction
    (predictable PC arithmetic; required for the future binary encoder). -/
def textPreamble : String :=
  ".option norvc\n" ++
  ".section .text\n" ++
  ".globl _start\n" ++
  "_start:"

private def joinNonEmpty (xs : List String) : String :=
  String.intercalate "\n" (xs.filter (fun s => ¬ s.isEmpty))

/-! ## Zero-initialized data

    GNU `as` emits `.zero` inside a normal `.data` section as PROGBITS, which
    makes the file contain every byte of the guest's large scratch arenas.  The
    source generators intentionally keep labels, alignment, and nonzero tables
    interleaved, so the final data string is split here at the common
    `BuildUnit` boundary.  A zero item carries its immediately preceding
    alignment/label prefix with it; a following nonzero item switches back to
    `.data`.  This preserves every symbol's relative order within its new
    section while leaving the emitted instruction text untouched. -/

private inductive DataSection where
  | other
  | data
  | bss
  deriving DecidableEq

private def trimmed (line : String) : String := line.trimAscii.toString

private def isSection (name line : String) : Bool :=
  (trimmed line).startsWith (".section " ++ name)

private def isZeroDirective (line : String) : Bool :=
  let t := trimmed line
  t == ".zero" || t.startsWith ".zero " || t.startsWith ".zero\t" ||
    t.startsWith ".skip " || t.startsWith ".skip\t" ||
    t.startsWith ".space " || t.startsWith ".space\t"

private def isZeroPrefix (line : String) : Bool :=
  let t := trimmed line
  t.isEmpty || t.startsWith "#" || t.startsWith ".balign " ||
    (t.endsWith ":" && !t.startsWith ".")

private def isSectionDirective (line : String) : Bool :=
  (trimmed line).startsWith ".section "

private def isPushDataSection (line : String) : Bool :=
  (trimmed line).startsWith ".pushsection .data"

private def isPopSection (line : String) : Bool :=
  trimmed line == ".popsection"

private def flushPending (pending : List String) (outRev : List String) : List String :=
  pending.reverse.foldl (fun acc line => line :: acc) outRev

private def moveZeroDataLines
    (lines : List String) (sec : DataSection) (pending : List String)
    (outRev : List String) : List String :=
  match lines with
  | [] => flushPending pending outRev
  | line :: rest =>
      if isSectionDirective line then
        moveZeroDataLines rest
          (if isSection ".data" line then .data
           else if isSection ".bss" line then .bss else .other) []
          (line :: flushPending pending outRev)
      else if isPushDataSection line then
        moveZeroDataLines rest .data [] (line :: flushPending pending outRev)
      else if isPopSection line then
        moveZeroDataLines rest .other [] (line :: flushPending pending outRev)
      else if sec == .data && isZeroDirective line then
        moveZeroDataLines rest .bss []
          (line :: flushPending pending
            (".section .bss,\"aw\",@nobits" :: outRev))
      else if sec == .bss && isZeroDirective line then
        moveZeroDataLines rest .bss [] (line :: flushPending pending outRev)
      else if (sec == .data || sec == .bss) && isZeroPrefix line then
        moveZeroDataLines rest sec (line :: pending) outRev
      else if sec == .bss then
        moveZeroDataLines rest .data []
          (line :: flushPending pending (".section .data" :: outRev))
      else
        moveZeroDataLines rest sec [] (line :: flushPending pending outRev)

private def moveZeroDataToBss (asm : String) : String :=
  String.intercalate "\n"
    ((moveZeroDataLines (asm.splitOn "\n") .other [] []).reverse)

/-- Render a full `.s` file from a `BuildUnit` and halt convention. -/
def emitBuildUnit (hc : HaltConv) (u : BuildUnit) : String :=
  joinNonEmpty
    [ textPreamble
    , u.prologueAsm
    , emitProgram u.body
    , moveZeroDataToBss u.epilogueAsm
    , emitHaltStub hc
    , moveZeroDataToBss u.dataAsm
    , ""  -- trailing newline
    ]

/-- A `.dword 0x…` line for a 64-bit value. Two-space indent, lowercase hex. -/
def emitDword (n : UInt64) : String :=
  s!"  .dword 0x{natToHex n.toNat}"

/-- Build a `.data` section with a label and a list of 64-bit values
    (little-endian on disk because `.dword` emits LE on RV64). -/
def emitDataLabel (sectionName label : String) (values : List UInt64) : String :=
  joinNonEmpty
    ([ s!".section {sectionName}"
     , ".balign 8"
     , s!"{label}:" ]
     ++ values.map emitDword)

end EvmAsm.Codegen
