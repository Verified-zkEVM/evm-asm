/-
  EvmAsm.Rv64.SAsm.Sym

  The pure block engine for SAsm: forward symbolic execution of straight-line
  instruction blocks over the exposed register file.

  `aluSem` classifies each supported instruction as a destination register, a
  source list, and a result function of the register valuation, mirroring
  `execInstrBr` exactly.  `execInstrRF`/`execBlock` run that classification
  over a `RegFile`; `instrOk`/`blockOk` are the decidable supported-subset and
  exposure checks whose failure the VC generator surfaces as a labeled goal.

  Supported subset (docs/sasm-design.md §3.4): ALU reg/reg and reg/imm ops,
  constants (LI/LUI/MV/NOP), ADDIW, and the RV64M multiply/divide family.
  Memory, branches, jumps, and system instructions are not block leaves:
  branches/jumps are synthesized by the flattener, and memory ops arrive with
  region support (M5).
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SAsm.RegFile

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Read-only byte regions (docs/sasm-design.md §3.3)
-- ============================================================================

/-- A read-only byte buffer owned by an SAsm function: `bytes` live at the
    dword-aligned `base`.  The degenerate `Region.empty` is the default for
    functions that touch no memory. -/
structure Region where
  base : Word
  bytes : List (BitVec 8)

/-- The no-memory region (its assertion is `empAssertion`). -/
def Region.empty : Region := ⟨0, []⟩

/-- Read the byte at an absolute address (junk when out of range; the block
    VCs rule that out). -/
def Region.byteAt (reg : Region) (addr : Word) : BitVec 8 :=
  reg.bytes.getD (addr - reg.base).toNat 0

/-- Region well-formedness: dword-aligned base, no address wrap, and every
    byte within the machine's valid memory range.  Decidable for concrete
    regions (`decide`); `omega`/`bv_omega` for symbolic ones. -/
def Region.wf (reg : Region) : Prop :=
  reg.base.toNat % 8 = 0 ∧
  reg.base.toNat + reg.bytes.length < 2 ^ 64 ∧
  ∀ k, k < reg.bytes.length → isValidMemAddr (reg.base + BitVec.ofNat 64 k) = true

instance (reg : Region) : Decidable reg.wf := by
  unfold Region.wf
  infer_instance

/-- Classification of a supported straight-line instruction: destination,
    sources, and result as a function of the register valuation. -/
structure AluOp where
  rd : Reg
  srcs : List Reg
  f : (Reg → Word) → Word

/-- Classify an instruction.  The result functions mirror `execInstrBr`
    case-for-case; `none` means the instruction is not a supported SAsm
    block leaf. -/
def aluSem : Instr → Option AluOp
  -- ALU register-register
  | .ADD  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 + g rs2⟩
  | .SUB  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 - g rs2⟩
  | .SLL  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 <<< ((g rs2).toNat % 64)⟩
  | .SRL  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 >>> ((g rs2).toNat % 64)⟩
  | .SRA  rd rs1 rs2 => some ⟨rd, [rs1, rs2],
      fun g => BitVec.sshiftRight (g rs1) ((g rs2).toNat % 64)⟩
  | .AND  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 &&& g rs2⟩
  | .OR   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 ||| g rs2⟩
  | .XOR  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 ^^^ g rs2⟩
  | .SLT  rd rs1 rs2 => some ⟨rd, [rs1, rs2],
      fun g => if BitVec.slt (g rs1) (g rs2) then 1 else 0⟩
  | .SLTU rd rs1 rs2 => some ⟨rd, [rs1, rs2],
      fun g => if BitVec.ult (g rs1) (g rs2) then 1 else 0⟩
  -- ALU immediate
  | .ADDI  rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 + signExtend12 imm⟩
  | .ANDI  rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 &&& signExtend12 imm⟩
  | .ORI   rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 ||| signExtend12 imm⟩
  | .XORI  rd rs1 imm => some ⟨rd, [rs1], fun g => g rs1 ^^^ signExtend12 imm⟩
  | .SLTI  rd rs1 imm => some ⟨rd, [rs1],
      fun g => if BitVec.slt (g rs1) (signExtend12 imm) then 1 else 0⟩
  | .SLTIU rd rs1 imm => some ⟨rd, [rs1],
      fun g => if BitVec.ult (g rs1) (signExtend12 imm) then 1 else 0⟩
  | .SLLI  rd rs1 shamt => some ⟨rd, [rs1], fun g => g rs1 <<< shamt.toNat⟩
  | .SRLI  rd rs1 shamt => some ⟨rd, [rs1], fun g => g rs1 >>> shamt.toNat⟩
  | .SRAI  rd rs1 shamt => some ⟨rd, [rs1],
      fun g => BitVec.sshiftRight (g rs1) shamt.toNat⟩
  -- Upper immediate / constants / pseudo
  | .LUI rd imm => some ⟨rd, [],
      fun _ => ((imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64)⟩
  | .MV  rd rs  => some ⟨rd, [rs], fun g => g rs⟩
  | .LI  rd imm => some ⟨rd, [], fun _ => imm⟩
  | .NOP        => some ⟨.x0, [], fun _ => 0⟩
  -- *W
  | .ADDIW rd rs1 imm => some ⟨rd, [rs1],
      fun g => (((g rs1).truncate 32 + (signExtend12 imm).truncate 32 : BitVec 32).signExtend 64)⟩
  -- RV64M
  | .MUL    rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => g rs1 * g rs2⟩
  | .MULH   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_mulh (g rs1) (g rs2)⟩
  | .MULHSU rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_mulhsu (g rs1) (g rs2)⟩
  | .MULHU  rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_mulhu (g rs1) (g rs2)⟩
  | .DIV    rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_div (g rs1) (g rs2)⟩
  | .DIVU   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_divu (g rs1) (g rs2)⟩
  | .REM    rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_rem (g rs1) (g rs2)⟩
  | .REMU   rd rs1 rs2 => some ⟨rd, [rs1, rs2], fun g => rv64_remu (g rs1) (g rs2)⟩
  -- Everything else (memory, control flow, system) is not a block leaf.
  | _ => none

/-- Classification of a byte load from the function's read-only region:
    destination, address register, immediate offset, and how the byte
    extends to a word. -/
structure LoadOp where
  rd : Reg
  rs1 : Reg
  ofs : BitVec 12
  ext : BitVec 8 → Word

/-- Classify a byte load.  `LBU`/`LB` only in M5a; wider loads arrive with
    multi-byte region reads. -/
def loadSem : Instr → Option LoadOp
  | .LBU rd rs1 ofs => some ⟨rd, rs1, ofs, fun b => b.zeroExtend 64⟩
  | .LB  rd rs1 ofs => some ⟨rd, rs1, ofs, fun b => b.signExtend 64⟩
  | _ => none

/-- Symbolic execution of one instruction over the register file, reading
    byte loads from `reg`.  Unsupported instructions are the identity; they
    are ruled out by `instrOk`, which the VC generator enforces. -/
def execInstrRF (reg : Region) (rf : RegFile) (i : Instr) : RegFile :=
  match aluSem i with
  | some op => rf.set op.rd (op.f rf.get)
  | none =>
    match loadSem i with
    | some l => rf.set l.rd (l.ext (reg.byteAt (rf.get l.rs1 + signExtend12 l.ofs)))
    | none => rf

/-- Supported-and-exposed check for a block leaf instruction: the instruction
    is in the supported subset, writes an exposed register (or x0), and reads
    only exposed registers (or x0). -/
def instrOk (i : Instr) : Bool :=
  match aluSem i with
  | some op =>
      (Reg.isExposed op.rd || op.rd == .x0)
        && op.srcs.all (fun r => Reg.isExposed r || r == .x0)
  | none =>
    match loadSem i with
    | some l =>
        (Reg.isExposed l.rd || l.rd == .x0)
          && (Reg.isExposed l.rs1 || l.rs1 == .x0)
    | none => false

/-- Forward symbolic execution of a straight-line block. -/
def execBlock (reg : Region) (rf : RegFile) : List Instr → RegFile
  | [] => rf
  | i :: is => execBlock reg (execInstrRF reg rf i) is

/-- Every instruction of the block is a supported, exposure-respecting leaf. -/
def blockOk (instrs : List Instr) : Bool :=
  instrs.all instrOk

/-- Address side conditions of a block's loads, threaded through the
    symbolic execution: every load's effective address indexes into the
    region. -/
def blockVCs (reg : Region) (rf : RegFile) : List Instr → Prop
  | [] => True
  | i :: is =>
      (match loadSem i with
       | some l =>
           ((rf.get l.rs1 + signExtend12 l.ofs) - reg.base).toNat < reg.bytes.length
       | none => True)
      ∧ blockVCs reg (execInstrRF reg rf i) is

/-- Whether a block contains any load (decides whether a `.mem` VC is
    emitted at all). -/
def hasLoad (instrs : List Instr) : Bool :=
  instrs.any (fun i => (loadSem i).isSome)

/-- Blocks without loads have no memory side conditions. -/
theorem blockVCs_of_not_hasLoad (reg : Region) (rf : RegFile)
    (instrs : List Instr) (h : hasLoad instrs = false) :
    blockVCs reg rf instrs := by
  induction instrs generalizing rf with
  | nil => trivial
  | cons i is ih =>
      simp only [hasLoad, List.any_cons, Bool.or_eq_false_iff] at h
      refine ⟨?_, ih _ (by simp [hasLoad, h.2])⟩
      cases hl : loadSem i with
      | none => trivial
      | some l => simp [hl] at h

@[simp] theorem execBlock_nil (reg : Region) (rf : RegFile) :
    execBlock reg rf [] = rf := rfl

@[simp] theorem execBlock_cons (reg : Region) (rf : RegFile) (i : Instr)
    (is : List Instr) :
    execBlock reg rf (i :: is) = execBlock reg (execInstrRF reg rf i) is := rfl

end SAsm
end EvmAsm.Rv64
