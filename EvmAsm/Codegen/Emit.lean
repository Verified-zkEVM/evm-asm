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

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Render a register as the canonical `xNN` mnemonic. -/
def emitReg (r : Reg) : String := toString r

def natToHex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Render a signed branch/JAL offset as PC-relative: `.+N` or `.-N`.
    Plain integer operands to RV64 branches and JAL are interpreted by
    GNU-as as absolute target addresses (not relative offsets), which
    breaks at link time when text is loaded at e.g. `0x80000000`. The
    PC-relative form keeps the offset anchored at the current pc. -/
def emitBranchOff (n : Int) : String :=
  if n < 0 then s!".{n}" else s!".+{n}"

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
  | .ADDI  rd rs1 imm => s!"addi {emitReg rd}, {emitReg rs1}, {imm.toInt}"
  | .ANDI  rd rs1 imm => s!"andi {emitReg rd}, {emitReg rs1}, {imm.toInt}"
  | .ORI   rd rs1 imm => s!"ori {emitReg rd}, {emitReg rs1}, {imm.toInt}"
  | .XORI  rd rs1 imm => s!"xori {emitReg rd}, {emitReg rs1}, {imm.toInt}"
  | .SLTI  rd rs1 imm => s!"slti {emitReg rd}, {emitReg rs1}, {imm.toInt}"
  | .SLTIU rd rs1 imm => s!"sltiu {emitReg rd}, {emitReg rs1}, {imm.toInt}"
  -- RV64I shift-immediate (6-bit unsigned shamt)
  | .SLLI  rd rs1 sh  => s!"slli {emitReg rd}, {emitReg rs1}, {sh.toNat}"
  | .SRLI  rd rs1 sh  => s!"srli {emitReg rd}, {emitReg rs1}, {sh.toNat}"
  | .SRAI  rd rs1 sh  => s!"srai {emitReg rd}, {emitReg rs1}, {sh.toNat}"
  -- RV64I upper-immediate (20-bit unsigned, hex)
  | .LUI   rd imm     => s!"lui {emitReg rd}, 0x{natToHex imm.toNat}"
  | .AUIPC rd imm     => s!"auipc {emitReg rd}, 0x{natToHex imm.toNat}"
  -- RV64I doubleword memory
  | .LD    rd rs1 off  => s!"ld {emitReg rd}, {off.toInt}({emitReg rs1})"
  | .SD    rs1 rs2 off => s!"sd {emitReg rs2}, {off.toInt}({emitReg rs1})"
  -- RV64I word memory
  | .LW    rd rs1 off  => s!"lw {emitReg rd}, {off.toInt}({emitReg rs1})"
  | .LWU   rd rs1 off  => s!"lwu {emitReg rd}, {off.toInt}({emitReg rs1})"
  | .SW    rs1 rs2 off => s!"sw {emitReg rs2}, {off.toInt}({emitReg rs1})"
  -- RV64I sub-word memory
  | .LB    rd rs1 off  => s!"lb {emitReg rd}, {off.toInt}({emitReg rs1})"
  | .LH    rd rs1 off  => s!"lh {emitReg rd}, {off.toInt}({emitReg rs1})"
  | .LBU   rd rs1 off  => s!"lbu {emitReg rd}, {off.toInt}({emitReg rs1})"
  | .LHU   rd rs1 off  => s!"lhu {emitReg rd}, {off.toInt}({emitReg rs1})"
  | .SB    rs1 rs2 off => s!"sb {emitReg rs2}, {off.toInt}({emitReg rs1})"
  | .SH    rs1 rs2 off => s!"sh {emitReg rs2}, {off.toInt}({emitReg rs1})"
  -- RV64I branches (signed 13-bit byte offset, emitted as PC-relative)
  | .BEQ   rs1 rs2 off => s!"beq {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BNE   rs1 rs2 off => s!"bne {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BLT   rs1 rs2 off => s!"blt {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BGE   rs1 rs2 off => s!"bge {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BLTU  rs1 rs2 off => s!"bltu {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  | .BGEU  rs1 rs2 off => s!"bgeu {emitReg rs1}, {emitReg rs2}, {emitBranchOff off.toInt}"
  -- RV64I jumps (JAL offset is PC-relative; JALR offset is register-indirect)
  | .JAL   rd off      => s!"jal {emitReg rd}, {emitBranchOff off.toInt}"
  | .JALR  rd rs1 off  => s!"jalr {emitReg rd}, {off.toInt}({emitReg rs1})"
  -- RV64I pseudo-instructions
  | .MV    rd rs       => s!"mv {emitReg rd}, {emitReg rs}"
  | .LI    rd imm      => s!"li {emitReg rd}, {imm.toInt}"
  | .NOP               => "nop"
  -- RV64I *W (word-size ops on lower 32 bits)
  | .ADDIW rd rs1 imm  => s!"addiw {emitReg rd}, {emitReg rs1}, {imm.toInt}"
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
example : emitInstr (.CSRS 0x80B .x10) = s!".4byte {0x80b52073}" := rfl
example : emitInstr (.CSRS 0x819 .x10) = s!".4byte {0x81952073}" := rfl

/-- Render a `Program` as one mnemonic per line, each indented two spaces. -/
def emitProgram (p : Program) : String :=
  String.intercalate "\n" (p.map (fun i => "  " ++ emitInstr i))

end EvmAsm.Codegen
