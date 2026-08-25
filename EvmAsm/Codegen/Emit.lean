/-
  EvmAsm.Codegen.Emit

  Pretty-print `Instr` and `Program` as GNU-as RV64IM mnemonics.

  Total over every `Instr` constructor in `EvmAsm/Rv64/Basic.lean:113-237`.

  Immediate rendering conventions:
    - `BitVec 12`, `BitVec 13`, `BitVec 21` → signed decimal (`.toInt`)
    - `BitVec 6` (shamt) → unsigned decimal (`.toNat`)
    - `BitVec 20` (LUI/AUIPC) → unsigned hex (`0x…`)
    - `Word` (LI) → signed 64-bit decimal (`.toInt`); `as` picks the
      `lui`/`addiw`/`slli`/`addi` expansion that materializes it

  Store instructions (SD/SW/SB/SH) carry `(rs1 rs2 : Reg)` in the Lean
  constructor (rs1 = base address register, rs2 = source data), but
  GNU-as syntax is `sX rs2, off(rs1)` — note the swap in `emitInstr`.

  Emission is a one-way output channel; it carries no proofs and is not
  part of the trusted kernel surface.
-/

module

public import EvmAsm.Rv64.Program
meta import EvmAsm.Rv64.Program

@[expose] public section

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Decimal digit as a one-character string.

    A literal table rather than `Char.ofNat (48 + d)`, so that reduction is a
    match on a `Nat` literal and never enters `Char`/`UInt32` — which would
    just trade one non-exposed dependency for another. -/
def digitStr : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

/-- Decimal rendering of a `Nat`, accumulating least-significant digit first.
    Structurally recursive on the fuel argument; `natStr` passes `n` itself,
    which is ample since the value divides by 10 each step. -/
def natStrAux : Nat → Nat → String → String
  | 0,      _, acc => acc
  | _ + 1,  0, acc => acc
  | f + 1,  n, acc => natStrAux f (n / 10) (digitStr (n % 10) ++ acc)

/-- Decimal rendering of a `Nat`.

    ⚠️ This exists instead of `toString`/`Nat.repr` because **`Nat.repr` is not
    exposed** under the module system, so every `rfl` example in this file that
    renders a number stops reducing:

        Note: The following definitions were not unfolded because their
        definition is not exposed:
          Nat.repr ↦ 3

    Reduction here is Nat literal arithmetic (`/`, `%`, which the kernel does on
    GMP integers) plus `String` literal append, both of which reduce fine. -/
def natStr (n : Nat) : String :=
  if n = 0 then "0" else natStrAux n n ""

/-- Decimal rendering of an `Int`, with a leading `-` for negatives. -/
def intStr (i : Int) : String :=
  if i < 0 then "-" ++ natStr i.natAbs else natStr i.natAbs

/-- Render a register as the canonical `xNN` mnemonic.

    Spelled out rather than `toString r`, so it does not route through the
    `ToString Reg` instance in `Rv64/Basic.lean` — whose body is `s!"x{r.toNat}"`
    and therefore reaches the non-exposed `Nat.repr`. -/
def emitReg (r : Reg) : String := "x" ++ natStr r.toNat

def natToHex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Render a signed branch/JAL offset as PC-relative: `.+N` or `.-N`.
    Plain integer operands to RV64 branches and JAL are interpreted by
    GNU-as as absolute target addresses (not relative offsets), which
    breaks at link time when text is loaded at e.g. `0x80000000`. The
    PC-relative form keeps the offset anchored at the current pc. -/
def emitBranchOff (n : Int) : String :=
  if n < 0 then s!".{intStr n}" else s!".+{intStr n}"

/-- Render a single RV64IM instruction as one GNU-as line. -/
def emitInstr : Instr → String
  -- RV64I ALU register-register
  | .ADD   rd rs1 rs2 => s!"add {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .SUB   rd rs1 rs2 => s!"sub {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .SLL   rd rs1 rs2 => s!"sll {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .SRL   rd rs1 rs2 => s!"srl {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .SRA   rd rs1 rs2 => s!"sra {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .AND   rd rs1 rs2 => s!"and {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .OR    rd rs1 rs2 => s!"or {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .XOR   rd rs1 rs2 => s!"xor {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .SLT   rd rs1 rs2 => s!"slt {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .SLTU  rd rs1 rs2 => s!"sltu {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  -- RV64I ALU immediate (signed 12-bit)
  | .ADDI  rd rs1 imm => s!"addi {emitReg rd}, {emitReg rs1}, {intStr imm.toInt}"
  | .ANDI  rd rs1 imm => s!"andi {emitReg rd}, {emitReg rs1}, {intStr imm.toInt}"
  | .ORI   rd rs1 imm => s!"ori {emitReg rd}, {emitReg rs1}, {intStr imm.toInt}"
  | .XORI  rd rs1 imm => s!"xori {emitReg rd}, {emitReg rs1}, {intStr imm.toInt}"
  | .SLTI  rd rs1 imm => s!"slti {emitReg rd}, {emitReg rs1}, {intStr imm.toInt}"
  | .SLTIU rd rs1 imm => s!"sltiu {emitReg rd}, {emitReg rs1}, {intStr imm.toInt}"
  -- RV64I shift-immediate (6-bit unsigned shamt)
  | .SLLI  rd rs1 sh  => s!"slli {emitReg rd}, {emitReg rs1}, {natStr sh.toNat}"
  | .SRLI  rd rs1 sh  => s!"srli {emitReg rd}, {emitReg rs1}, {natStr sh.toNat}"
  | .SRAI  rd rs1 sh  => s!"srai {emitReg rd}, {emitReg rs1}, {natStr sh.toNat}"
  -- RV64I upper-immediate (20-bit unsigned, hex)
  | .LUI   rd imm     => s!"lui {emitReg rd}, 0x{natToHex imm.toNat}"
  | .AUIPC rd imm     => s!"auipc {emitReg rd}, 0x{natToHex imm.toNat}"
  -- RV64I doubleword memory
  | .LD    rd rs1 off  => s!"ld {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  | .SD    rs1 rs2 off => s!"sd {emitReg rs2}, {intStr off.toInt}({emitReg rs1})"
  -- RV64I word memory
  | .LW    rd rs1 off  => s!"lw {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  | .LWU   rd rs1 off  => s!"lwu {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  | .SW    rs1 rs2 off => s!"sw {emitReg rs2}, {intStr off.toInt}({emitReg rs1})"
  -- RV64I sub-word memory
  | .LB    rd rs1 off  => s!"lb {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  | .LH    rd rs1 off  => s!"lh {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  | .LBU   rd rs1 off  => s!"lbu {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  | .LHU   rd rs1 off  => s!"lhu {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  | .SB    rs1 rs2 off => s!"sb {emitReg rs2}, {intStr off.toInt}({emitReg rs1})"
  | .SH    rs1 rs2 off => s!"sh {emitReg rs2}, {intStr off.toInt}({emitReg rs1})"
  -- RV64I branches (signed 13-bit byte offset, emitted as PC-relative)
  | .BEQ   rs1 rs2 off => s!"beq {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BNE   rs1 rs2 off => s!"bne {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BLT   rs1 rs2 off => s!"blt {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BGE   rs1 rs2 off => s!"bge {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BLTU  rs1 rs2 off => s!"bltu {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BGEU  rs1 rs2 off => s!"bgeu {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  -- RV64I jumps (JAL offset is PC-relative; JALR offset is register-indirect)
  | .JAL   rd off      => s!"jal {emitReg rd}, {emitBranchOff off.toInt}"
  | .JALR  rd rs1 off  => s!"jalr {emitReg rd}, {intStr off.toInt}({emitReg rs1})"
  -- RV64I pseudo-instructions
  | .MV    rd rs       => s!"mv {emitReg rd}, {emitReg rs}"
  | .LI    rd imm      => s!"li {emitReg rd}, {intStr imm.toInt}"
  | .NOP               => "nop"
  -- RV64I *W (word-size ops on lower 32 bits)
  | .ADDIW rd rs1 imm  => s!"addiw {emitReg rd}, {emitReg rs1}, {intStr imm.toInt}"
  -- RV64I system
  | .ECALL             => "ecall"
  | .FENCE             => "fence"
  | .EBREAK            => "ebreak"
  -- RV64M multiply
  | .MUL    rd rs1 rs2 => s!"mul {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .MULH   rd rs1 rs2 => s!"mulh {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .MULHSU rd rs1 rs2 => s!"mulhsu {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .MULHU  rd rs1 rs2 => s!"mulhu {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  -- RV64M divide
  | .DIV    rd rs1 rs2 => s!"div {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .DIVU   rd rs1 rs2 => s!"divu {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .REM    rd rs1 rs2 => s!"rem {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .REMU   rd rs1 rs2 => s!"remu {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  -- ZisK accelerator call: pre-encoded `csrrs x0, csr, rs1` so the plain
  -- rv64imac toolchain assembles it without Zicsr (the `.4byte` pattern
  -- used throughout Codegen/Programs)
  | .CSRS   csr rs1    =>
      s!".4byte {(csr.toNat <<< 20) ||| (rs1.toNat <<< 15) ||| 0x2073}"

-- The pre-encoded accelerator words match the hand-written guest literals
-- (`csrs 0x800, a0` / `csrs 0x802, t0` / `csrs 0x805, a0`).
example : emitInstr (.CSRS 0x800 .x10) = s!".4byte {0x80052073}" := rfl
example : emitInstr (.CSRS 0x802 .x5) = s!".4byte {0x8022a073}" := rfl
example : emitInstr (.CSRS 0x805 .x10) = s!".4byte {0x80552073}" := rfl
example : emitInstr (.CSRS 0x803 .x5) = s!".4byte {0x8032a073}" := rfl
example : emitInstr (.CSRS 0x804 .x5) = s!".4byte {0x8042a073}" := rfl
example : emitInstr (.CSRS 0x806 .x5) = s!".4byte {0x8062a073}" := rfl
example : emitInstr (.CSRS 0x807 .x5) = s!".4byte {0x8072a073}" := rfl
example : emitInstr (.CSRS 0x808 .x5) = s!".4byte {0x8082a073}" := rfl
example : emitInstr (.CSRS 0x809 .x5) = s!".4byte {0x8092a073}" := rfl
example : emitInstr (.CSRS 0x80A .x5) = s!".4byte {0x80a2a073}" := rfl
example : emitInstr (.CSRS 0x80B .x10) = s!".4byte {0x80b52073}" := rfl
example : emitInstr (.CSRS 0x80C .x10) = s!".4byte {0x80c52073}" := rfl
example : emitInstr (.CSRS 0x80D .x10) = s!".4byte {0x80d52073}" := rfl
example : emitInstr (.CSRS 0x80E .x10) = s!".4byte {0x80e52073}" := rfl
example : emitInstr (.CSRS 0x80F .x10) = s!".4byte {0x80f52073}" := rfl
example : emitInstr (.CSRS 0x810 .x10) = s!".4byte {0x81052073}" := rfl
example : emitInstr (.CSRS 0x819 .x10) = s!".4byte {0x81952073}" := rfl

/-- Join rendered lines with a newline.

    ⚠️ This exists instead of `String.intercalate` because core's
    `String.intercalate` is **not exposed** under the module system, so the
    kernel-checked `rfl` examples at the bottom of this file stop reducing
    through it:

        Note: The following definitions were not unfolded because their
        definition is not exposed:
          String.intercalate ↦ 3

    Those examples pin the exact emitted assembly text, and `emitProgramR`'s
    reloc branch has no other kernel-checked witness — the whole-guest
    byte-identity gate is skipped on some platforms, so a regression there
    could travel. `import all`, `with_unfolding_all rfl` and `decide` were all
    tried and none reaches a non-exposed body: non-exposure is an unfold
    *axiom*, not a visibility setting.

    Defined by structural recursion rather than well-founded recursion, because
    a well-founded definition does not reduce by `rfl` either — that would swap
    one blocker for another. Semantics match core's `intercalate` with a
    newline separator exactly, including on `[]` and on a singleton. -/
def joinLines : List String → String
  | [] => ""
  | [l] => l
  | l :: ls => l ++ "\n" ++ joinLines ls

/-- Render a `Program` as one mnemonic per line, each indented two spaces. -/
def emitProgram (p : Program) : String :=
  joinLines (p.map (fun i => "  " ++ emitInstr i))

/-- Which conditional branch a relaxed far-branch site came from. Typed rather
    than a bare mnemonic `String` because a typo would emit valid-looking asm
    that only the byte-identity gate could catch — and that gate is skipped on
    some platforms, so the mistake could travel. -/
inductive BrCond where
  | beq | bne | blt | bge | bltu | bgeu
  deriving Repr, DecidableEq

/-- The GNU-as mnemonic for a branch condition. -/
def emitBrCond : BrCond → String
  | .beq => "beq" | .bne => "bne" | .blt => "blt"
  | .bge => "bge" | .bltu => "bltu" | .bgeu => "bgeu"

/-- A relocatable (link-layout-dependent) operand that must be emitted
    *symbolically* so every image's linker resolves it against its own layout
    (bead evm-asm-4ch8f.9.3).  The Program stores the concrete guest-linked
    immediates (`AsmReloc.laHi`/`laLo`/`jalOff`) for the verification view; the
    emitted guest string keeps the symbolic form via `emitProgramR`. -/
inductive AsmSym where
  /-- `la reg, symbol` — a two-instruction `auipc`+`addi` pair (the marked
      index and the one after it) rendered as a single `la` line. -/
  | la  (reg : Reg) (symbol : String)
  /-- `jal rd, callee` — a cross-function jump rendered symbolically. -/
  | jal (rd : Reg) (callee : String)
  /-- `b<cond> rs1, rs2, symbol` — a **relaxed far branch** (GH #12204).

      A conditional branch to a target outside B-type's ±4 KiB reach does not
      survive assembly as one instruction: GNU-as rewrites it as the *inverted*
      condition skipping over an unconditional jump,

      ```
        beq  rs1, rs2, far          ⇒   bne rs1, rs2, .+8
                                        j   far
      ```

      so the linked image — and therefore any faithful `Program` — holds the
      **pair**. This reloc marks the inverted branch (the first of the two) and
      consumes the following `j`, rendering the one source line back. The
      recorded `cond` is the ORIGINAL condition, not the inverted one stored in
      the `Program`; `Rv64/BranchRelaxation.lean` proves the pair's semantics
      matches that original branch, with fall-through at `pc + 8`.

      Emitted in three-operand form (`bne rs, x0, sym` rather than
      `bnez rs, sym`); the two assemble identically, and the gate is byte
      identity of the assembled text, not string identity of the source.

      **Why only the relaxed form has a reloc kind.** Whether GNU-as relaxes
      depends on more than distance: for a symbol NOT defined in the assembly
      unit it relaxes *unconditionally*, because the distance is unknown until
      link time (measured with `riscv64-elf-as`; a branch to an undefined
      symbol emits `b<inv> .+8` + `j` with an `R_RISCV_JAL` on the jump). Only
      an in-unit target is decided by distance. The per-function byte-identity
      harness supplies cross-function targets as `--defsym` externals, so it
      sees the relaxed form either way — which means a single-instruction
      symbolic branch would be an encoding path the arbiter gate cannot check.
      `scripts/asm_to_program.py` therefore refuses an in-reach symbolic branch
      outright rather than emitting one unvalidated. -/
  | br  (cond : BrCond) (rs1 rs2 : Reg) (symbol : String)
  deriving Repr

/-- Reloc side-table: `(instruction index in the Program, symbolic form)`.
    An `la` entry additionally suppresses the following `addi` instruction. -/
abbrev RelocTable := List (Nat × AsmSym)

/-- Render a `Program` like `emitProgram`, except instructions covered by
    `relocs` are emitted **symbolically** (`la reg, sym` / `jal rd, callee`) so
    the string is image-agnostic — each linked image (guest, dispatcher, every
    `zisk_*` probe) relocates it against its own `.text`/`.data` layout.  The
    Program itself carries the concrete guest-linked immediates for proofs; this
    render is what lands in the emitted guest text, byte-identical to the
    hand-written `la`/`jal` in EVERY image.  An `la` entry consumes its `auipc`
    plus the following `addi` (one emitted line); a `br` entry likewise consumes
    the inverted branch plus the following `j` of a relaxed far branch. -/
def emitProgramR (p : Program) (relocs : RelocTable) : String :=
  let step : (List String × Nat) → (Instr × Nat) → (List String × Nat) :=
    fun (acc, skip) (instr, idx) =>
      if skip > 0 then (acc, skip - 1)
      else match relocs.lookup idx with
        | some (.la reg sym) => (s!"  la {emitReg reg}, {sym}" :: acc, 1)
        | some (.jal rd cal) => (s!"  jal {emitReg rd}, {cal}" :: acc, 0)
        | some (.br c a b sym) =>
            (s!"  {emitBrCond c} {emitReg a}, {emitReg b}, {sym}" :: acc, 1)
        | none               => (("  " ++ emitInstr instr) :: acc, 0)
  joinLines (p.zipIdx.foldl step ([], 0)).1.reverse

/-! ### `emitProgramR` on a relaxed far branch (GH #12204)

No converted routine carries a `.br` reloc yet, so the manifest's
byte-identity gate does not reach this branch of `emitProgramR`. These two
examples pin it directly: the reloc collapses the pair to the one source line
the author wrote and resumes at the instruction *after* the `j`, and the same
`Program` without the reloc renders both instructions — so the first example
is testing the reloc rather than an accident of the render.
`scripts/asm_to_program.py symbranch-self-test` pins the same round trip on the
converter's side. -/

example :
    emitProgramR
      [.BGEU .x7 .x6 (8 : BitVec 13),
       .JAL .x0 (0x23420 : BitVec 21),
       .ADDI .x5 .x5 (1 : BitVec 12)]
      [(0, .br .bltu .x7 .x6 ".exit_outofgas")] =
    "  bltu x7, x6, .exit_outofgas\n  addi x5, x5, 1" := rfl

-- Negative control: no reloc, so the relaxed pair renders as the two
-- instructions it literally is.
example :
    emitProgramR
      [.BGEU .x7 .x6 (8 : BitVec 13),
       .JAL .x0 (0x23420 : BitVec 21),
       .ADDI .x5 .x5 (1 : BitVec 12)]
      [] =
    "  bgeu x7, x6, .+8\n  jal x0, .+144416\n  addi x5, x5, 1" := rfl

/-! ### Parity with the core renderers this file had to stop using

    `natStr`, `intStr`, `joinLines` and `emitReg` exist only because their core
    equivalents are not exposed (see each one's docstring). Replacing a renderer
    in a *code generator* is only safe if it emits byte-identical text, so that
    is checked here directly against the core functions rather than argued.

    `#guard` evaluates at elaboration time, so these run on every build. They
    are deliberately stated as `ours == core`, not as pinned literals: a pinned
    literal would still pass if BOTH sides drifted. -/

-- Decimal rendering, over a dense low range and the boundaries that matter
-- (byte, 32-bit, 64-bit, and the `.+144416` offset from the examples below).
#guard (List.range 1000).all (fun n => natStr n == toString n)
#guard [0, 9, 10, 99, 100, 1023, 4096, 65535, 144416, 1000000,
        2147483647, 4294967295, 18446744073709551615].all
       (fun n => natStr n == toString n)

-- Signed rendering, across zero and at both 32-/64-bit magnitudes.
#guard ((List.range 400).map (fun n : Nat => (Int.ofNat n) - 200)).all
       (fun i => intStr i == toString i)
#guard [(-18446744073709551615 : Int), -2147483648, -1, 0, 1, 2147483647].all
       (fun i => intStr i == toString i)

-- Line joining, on every shape that differs: empty, singleton, an empty
-- element in the middle (which a naive `++`-with-separator gets wrong), and
-- the general case.
#guard joinLines [] == String.intercalate "\n" []
#guard joinLines ["a"] == String.intercalate "\n" ["a"]
#guard joinLines ["a","b"] == String.intercalate "\n" ["a","b"]
#guard joinLines ["a","","c"] == String.intercalate "\n" ["a","","c"]
#guard joinLines ["a","b","c","d"] == String.intercalate "\n" ["a","b","c","d"]

-- Register rendering, against the `ToString Reg` instance, on all 32.
#guard [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16, Reg.x17, Reg.x18, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.x31].all (fun r => emitReg r == toString r)

end EvmAsm.Codegen
