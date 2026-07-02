/-
  EvmAsm.Rv64.SAsm.Ast

  Abstract syntax for the SAsm structured-assembly DSL: branch conditions
  and structured statements over raw-instruction basic blocks.

  Design: docs/sasm-design.md §3.2.  Key points:
  - Leaves are `List Instr` (raw instructions from the supported subset).
  - Control flow is structured: `ite`, `when` (if without else), bounded
    `while` with an inline invariant, and `call` to a fixed entry address.
  - Annotations (loop invariants, optional `assert` mid-conditions) are pure
    predicates over the exposed register file; ghost data enters through
    ambient Lean binders of the enclosing definition.
  - Labels name the verification conditions generated from each node.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.SAsm.RegFile
import EvmAsm.Rv64.SAsm.Handle

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Branch conditions
-- ============================================================================

/-- Structured branch conditions: exactly the RV64 conditional branches,
    reading two registers. -/
inductive Cond where
  | beq  (rs1 rs2 : Reg)
  | bne  (rs1 rs2 : Reg)
  | blt  (rs1 rs2 : Reg)
  | bge  (rs1 rs2 : Reg)
  | bltu (rs1 rs2 : Reg)
  | bgeu (rs1 rs2 : Reg)
  deriving DecidableEq, Repr

namespace Cond

/-- Denotation over the exposed register file.  The `Bool = true` forms match
    the machine semantics (`execInstrBr`) and the `generic_b*_spec_within`
    postconditions. -/
def holds : Cond → RegFile → Prop
  | beq  rs1 rs2, rf => rf.get rs1 = rf.get rs2
  | bne  rs1 rs2, rf => rf.get rs1 ≠ rf.get rs2
  | blt  rs1 rs2, rf => BitVec.slt (rf.get rs1) (rf.get rs2) = true
  | bge  rs1 rs2, rf => ¬ (BitVec.slt (rf.get rs1) (rf.get rs2) = true)
  | bltu rs1 rs2, rf => BitVec.ult (rf.get rs1) (rf.get rs2) = true
  | bgeu rs1 rs2, rf => ¬ (BitVec.ult (rf.get rs1) (rf.get rs2) = true)

instance (c : Cond) (rf : RegFile) : Decidable (c.holds rf) := by
  cases c <;> simp only [holds] <;> infer_instance

/-- Logical negation, staying inside the branch-condition language
    (`beq ↔ bne`, `blt ↔ bge`, `bltu ↔ bgeu`). -/
def neg : Cond → Cond
  | beq  rs1 rs2 => bne  rs1 rs2
  | bne  rs1 rs2 => beq  rs1 rs2
  | blt  rs1 rs2 => bge  rs1 rs2
  | bge  rs1 rs2 => blt  rs1 rs2
  | bltu rs1 rs2 => bgeu rs1 rs2
  | bgeu rs1 rs2 => bltu rs1 rs2

@[simp] theorem neg_neg (c : Cond) : c.neg.neg = c := by
  cases c <;> rfl

theorem holds_neg (c : Cond) (rf : RegFile) :
    c.neg.holds rf ↔ ¬ c.holds rf := by
  cases c <;> simp [holds, neg]

/-- The machine branch instruction testing this condition, with the given
    byte offset. -/
def toInstr : Cond → BitVec 13 → Instr
  | beq  rs1 rs2, ofs => .BEQ  rs1 rs2 ofs
  | bne  rs1 rs2, ofs => .BNE  rs1 rs2 ofs
  | blt  rs1 rs2, ofs => .BLT  rs1 rs2 ofs
  | bge  rs1 rs2, ofs => .BGE  rs1 rs2 ofs
  | bltu rs1 rs2, ofs => .BLTU rs1 rs2 ofs
  | bgeu rs1 rs2, ofs => .BGEU rs1 rs2 ofs

/-- The registers a condition reads. -/
def regs : Cond → Reg × Reg
  | beq  rs1 rs2 | bne  rs1 rs2 | blt  rs1 rs2
  | bge  rs1 rs2 | bltu rs1 rs2 | bgeu rs1 rs2 => (rs1, rs2)

/-- A condition is well-formed when it only reads exposed registers or x0. -/
def wf (c : Cond) : Bool :=
  let (rs1, rs2) := c.regs
  (Reg.isExposed rs1 || rs1 == .x0) && (Reg.isExposed rs2 || rs2 == .x0)

end Cond

-- ============================================================================
-- Statements
-- ============================================================================

/-- Structured statements.  `label` fields name the verification conditions
    generated from the node; the VC generator prefixes them with the path, so
    they need not be globally unique. -/
inductive Stmt where
  /-- Straight-line block of raw instructions (supported subset; the block
      engine rejects unsupported instructions with a labeled VC). -/
  | block  (label : String) (instrs : List Instr)
  /-- Sequential composition. -/
  | seq    (a b : Stmt)
  /-- If-then-else on a branch condition. -/
  | ite    (label : String) (c : Cond) (thn els : Stmt)
  /-- If without else. -/
  | when   (label : String) (c : Cond) (body : Stmt)
  /-- Optional mid-condition: emits no code; generates one VC stating that
      every reachable register file satisfies `P`, and strengthens the
      reachable set with `P` downstream (a proof cut). -/
  | assert (label : String) (P : RegFile → List (BitVec 8) → Assertion → Prop)
  /-- Bounded loop: the body runs while `c` holds, at most `fuel` iterations.
      `inv i` must hold at the i-th evaluation of the header; the generator
      emits initialization, preservation, and fuel-exhaustion VCs. -/
  | «while»  (label : String) (c : Cond) (fuel : Nat)
           (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop) (body : Stmt)
  /-- Direct call (`jal ra, f.entry`) to a routine with a verified caller
      interface (docs/sasm-design.md §3.6).  The handle carries the callee's
      pre/post in the C-like ABI; the VC generator emits one `.pre`
      obligation per call site. -/
  | call   (label : String) (f : FnHandle)

namespace Stmt

/-- Sequential composition, right-associated. -/
scoped infixr:60 " ;;; " => Stmt.seq

/-- Number of machine instructions emitted for a statement, including
    synthesized branches and jumps (docs/sasm-design.md §3.7). -/
def size : Stmt → Nat
  | block _ is        => is.length
  | seq a b           => a.size + b.size
  | ite _ _ t e       => t.size + e.size + 2
  | when _ _ b        => b.size + 1
  | assert _ _        => 0
  | «while» _ _ _ _ b   => b.size + 2
  | call _ _          => 1

/-- All statement sizes are meaningful; `assert` is the only zero-size node. -/
@[simp] theorem size_seq (a b : Stmt) : (seq a b).size = a.size + b.size := rfl

/-- A statement makes no calls.  Call-free bodies get the stronger leaf
    soundness theorem (every non-exposed register, including `ra`, is left
    untouched and framed), which is what `Fn.toHandle` packages. -/
def callFree : Stmt → Bool
  | block _ _         => true
  | seq a b           => a.callFree && b.callFree
  | ite _ _ t e       => t.callFree && e.callFree
  | when _ _ b        => b.callFree
  | assert _ _        => true
  | «while» _ _ _ _ b => b.callFree
  | call _ _          => false

end Stmt

end SAsm
end EvmAsm.Rv64
