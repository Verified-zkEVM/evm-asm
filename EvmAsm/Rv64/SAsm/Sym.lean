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
import EvmAsm.Rv64.ByteOps
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

/-- Read the little-endian 16-bit halfword at a 2-aligned absolute address. -/
def Region.half16At (reg : Region) (addr : Word) : BitVec 16 :=
  reg.byteAt (addr + 1) ++ reg.byteAt addr

/-- Read the little-endian 32-bit word at a 4-aligned absolute address. -/
def Region.word32At (reg : Region) (addr : Word) : BitVec 32 :=
  reg.byteAt (addr + 3) ++ reg.byteAt (addr + 2)
    ++ reg.byteAt (addr + 1) ++ reg.byteAt addr

/-- Read the dword (as its packed cell) at an 8-aligned absolute address. -/
def Region.dwordAt (reg : Region) (addr : Word) : Word :=
  packBytes ((reg.bytes.drop (addr - reg.base).toNat).take 8)

/-- Address side condition of an `n`-byte load: the index is `n`-aligned
    within the region and the whole access fits. -/
def Region.loadOk (reg : Region) (addr : Word) (n : Nat) : Prop :=
  n ∣ (addr - reg.base).toNat
    ∧ (addr - reg.base).toNat + n ≤ reg.bytes.length

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

-- ============================================================================
-- Writable byte regions (docs/sasm-design.md §3.3, M5b-2)
-- ============================================================================

/-- A writable byte region owned by an SAsm function: `len` bytes at the
    dword-aligned `base`.  Unlike the read-only `Region`, the *contents* are
    part of the symbolic state (`Reach`), not of the region descriptor.  The
    degenerate `RwRegion.empty` is the default for functions that write no
    memory. -/
structure RwRegion where
  base : Word
  len : Nat

/-- The no-writable-memory region. -/
def RwRegion.empty : RwRegion := ⟨0, 0⟩

/-- Writable-region well-formedness: dword-aligned base, no address wrap,
    every byte within the machine's valid memory range. -/
def RwRegion.wf (rw : RwRegion) : Prop :=
  rw.base.toNat % 8 = 0 ∧
  rw.base.toNat + rw.len < 2 ^ 64 ∧
  ∀ k, k < rw.len → isValidMemAddr (rw.base + BitVec.ofNat 64 k) = true

instance (rw : RwRegion) : Decidable rw.wf := by
  unfold RwRegion.wf
  infer_instance

theorem RwRegion.empty_wf : RwRegion.empty.wf := by decide

/-- Whether an `n`-byte access at `addr` falls entirely inside the writable
    region (current contents `ws`).  This is the load-routing condition: such
    accesses read the symbolic contents, everything else reads the read-only
    region. -/
def inRw (rwBase : Word) (ws : List (BitVec 8)) (addr : Word) (n : Nat) : Prop :=
  (addr - rwBase).toNat + n ≤ ws.length

instance (rwBase : Word) (ws : List (BitVec 8)) (addr : Word) (n : Nat) :
    Decidable (inRw rwBase ws addr n) := by
  unfold inRw
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

/-- Classification of a load from the function's read-only region:
    destination, address register, immediate offset, access width in bytes,
    and the loaded (extended) word as a function of region and address. -/
structure LoadOp where
  rd : Reg
  rs1 : Reg
  ofs : BitVec 12
  nbytes : Nat
  val : Region → Word → Word

/-- Classify a load.  Bytes, halfwords, 32-bit words, and dwords. -/
def loadSem : Instr → Option LoadOp
  | .LBU rd rs1 ofs => some ⟨rd, rs1, ofs, 1, fun reg a => (reg.byteAt a).zeroExtend 64⟩
  | .LB  rd rs1 ofs => some ⟨rd, rs1, ofs, 1, fun reg a => (reg.byteAt a).signExtend 64⟩
  | .LHU rd rs1 ofs => some ⟨rd, rs1, ofs, 2, fun reg a => (reg.half16At a).zeroExtend 64⟩
  | .LH  rd rs1 ofs => some ⟨rd, rs1, ofs, 2, fun reg a => (reg.half16At a).signExtend 64⟩
  | .LW  rd rs1 ofs => some ⟨rd, rs1, ofs, 4, fun reg a => (reg.word32At a).signExtend 64⟩
  | .LWU rd rs1 ofs => some ⟨rd, rs1, ofs, 4, fun reg a => (reg.word32At a).zeroExtend 64⟩
  | .LD  rd rs1 ofs => some ⟨rd, rs1, ofs, 8, fun reg a => reg.dwordAt a⟩
  | _ => none

/-- Symbolic execution of one instruction over the register file and the
    writable region's contents `ws`.  A load whose access falls entirely
    inside the writable region reads the symbolic contents; every other load
    reads the read-only region `ro`.  Unsupported instructions are the
    identity; they are ruled out by `instrOk`, which the VC generator
    enforces. -/
def execInstrRF (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Instr) : RegFile × List (BitVec 8) :=
  match aluSem i with
  | some op => (rf.set op.rd (op.f rf.get), ws)
  | none =>
    match loadSem i with
    | some l =>
        let a := rf.get l.rs1 + signExtend12 l.ofs
        ((if inRw rwBase ws a l.nbytes
          then rf.set l.rd (l.val ⟨rwBase, ws⟩ a)
          else rf.set l.rd (l.val ro a)), ws)
    | none => (rf, ws)

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
def execBlock (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) : List Instr → RegFile × List (BitVec 8)
  | [] => (rf, ws)
  | i :: is =>
      execBlock ro rwBase (execInstrRF ro rwBase rf ws i).1
        (execInstrRF ro rwBase rf ws i).2 is

/-- Every instruction of the block is a supported, exposure-respecting leaf. -/
def blockOk (instrs : List Instr) : Bool :=
  instrs.all instrOk

/-- Address side conditions of a block's loads, threaded through the
    symbolic execution: a load routed to the writable region must be aligned
    (it fits by the routing condition); every other load indexes into the
    read-only region. -/
def blockVCs (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) : List Instr → Prop
  | [] => True
  | i :: is =>
      (match loadSem i with
       | some l =>
           let a := rf.get l.rs1 + signExtend12 l.ofs
           if inRw rwBase ws a l.nbytes
           then (Region.mk rwBase ws).loadOk a l.nbytes
           else ro.loadOk a l.nbytes
       | none => True)
      ∧ blockVCs ro rwBase (execInstrRF ro rwBase rf ws i).1
          (execInstrRF ro rwBase rf ws i).2 is

/-- Whether a block contains any load (decides whether a `.mem` VC is
    emitted at all). -/
def hasLoad (instrs : List Instr) : Bool :=
  instrs.any (fun i => (loadSem i).isSome)

/-- Blocks without loads have no memory side conditions. -/
theorem blockVCs_of_not_hasLoad (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (instrs : List Instr) (h : hasLoad instrs = false) :
    blockVCs ro rwBase rf ws instrs := by
  induction instrs generalizing rf ws with
  | nil => trivial
  | cons i is ih =>
      simp only [hasLoad, List.any_cons, Bool.or_eq_false_iff] at h
      refine ⟨?_, ih _ _ (by simp [hasLoad, h.2])⟩
      cases hl : loadSem i with
      | none => trivial
      | some l => simp [hl] at h

/-- Every supported load moves at least one byte. -/
theorem loadSem_nbytes_pos {i : Instr} {l : LoadOp} (h : loadSem i = some l) :
    0 < l.nbytes := by
  cases i <;> simp only [loadSem, reduceCtorEq] at h <;>
    (injection h with h; subst h; simp)

/-- With no writable bytes, nothing routes to the writable region. -/
theorem not_inRw_nil {rwBase a : Word} {n : Nat} (hn : 0 < n) :
    ¬ inRw rwBase [] a n := by
  unfold inRw
  simp only [List.length_nil, Nat.le_zero]
  omega

/-- Routing `if` over an empty writable region collapses to the read-only
    branch (`hn` is discharged by `decide` for the engine's literal widths). -/
@[simp] theorem ite_inRw_nil {α : Sort u} (rwBase a : Word) {n : Nat}
    (hn : 0 < n) (X Y : α) :
    (if inRw rwBase [] a n then X else Y) = Y :=
  if_neg (not_inRw_nil hn)

/-- With no writable bytes, one engine step reads the read-only region:
    the `ws = []` reduction demos and read-only ports rewrite with. -/
@[simp] theorem execInstrRF_nil (ro : Region) (rwBase : Word) (rf : RegFile)
    (i : Instr) :
    execInstrRF ro rwBase rf [] i
      = (match aluSem i with
         | some op => (rf.set op.rd (op.f rf.get), [])
         | none =>
           match loadSem i with
           | some l =>
               (rf.set l.rd (l.val ro (rf.get l.rs1 + signExtend12 l.ofs)), [])
           | none => (rf, [])) := by
  unfold execInstrRF
  cases haluSem : aluSem i with
  | some op => rfl
  | none =>
      cases hload : loadSem i with
      | some l =>
          dsimp only
          rw [if_neg (not_inRw_nil (loadSem_nbytes_pos hload))]
      | none => rfl

/-- One instruction preserves the writable region's size. -/
@[simp] theorem execInstrRF_ws_length (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (i : Instr) :
    (execInstrRF ro rwBase rf ws i).2.length = ws.length := by
  unfold execInstrRF
  split
  · rfl
  · split
    · rfl
    · rfl

/-- A block preserves the writable region's size. -/
@[simp] theorem execBlock_ws_length (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (instrs : List Instr) :
    (execBlock ro rwBase rf ws instrs).2.length = ws.length := by
  induction instrs generalizing rf ws with
  | nil => rfl
  | cons i is ih =>
      show (execBlock ro rwBase _ _ is).2.length = _
      rw [ih, execInstrRF_ws_length]

@[simp] theorem execBlock_nil (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    execBlock ro rwBase rf ws [] = (rf, ws) := rfl

@[simp] theorem execBlock_cons (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Instr) (is : List Instr) :
    execBlock ro rwBase rf ws (i :: is)
      = execBlock ro rwBase (execInstrRF ro rwBase rf ws i).1
          (execInstrRF ro rwBase rf ws i).2 is := rfl

end SAsm
end EvmAsm.Rv64
