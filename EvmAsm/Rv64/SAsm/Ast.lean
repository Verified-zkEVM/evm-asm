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
  /-- Focus block: a straight-line block whose *writable window* is a
      `bytesRegion` at the address held in register `ptr`, opened out of
      the ambient assertion for the block's duration.  The annotation
      `winR` *relates* the entry state to the decomposition (window bytes,
      remainder assertion) — relational rather than functional so it can
      name existentially-quantified ghosts from the ambient invariant
      (zipper contexts, subtrees).  The generator emits a `.focus` VC
      demanding a related decomposition exist with
      `A = bytesRegion (rf.get ptr) win ** rest`.  The function's flat rw
      window is framed — inaccessible inside the block; the read-only
      region stays readable.  This is how SAsm code reads and writes
      pointer-owned memory (tree nodes, list cells) with pure VCs. -/
  | blockAt (label : String) (ptr : Reg)
            (winR : RegFile → List (BitVec 8) → Assertion →
              List (BitVec 8) → Assertion → Prop)
            (instrs : List Instr)
  /-- Read-focus block (the read-side mirror of `blockAt`): a straight-line
      block whose *read-only source* is a `bytesRegion` at the address held
      in register `ptr`, opened out of the ambient assertion for the block's
      duration.  The annotation `roR` *relates* the entry state to the
      decomposition (region bytes, remainder assertion) — relational so it
      can name existentially-quantified ghosts from the ambient invariant.
      The generator emits a `.focus` VC demanding a related decomposition
      exist with `A = bytesRegion (rf.get ptr) robytes ** rest`.  Inside the
      block, loads that miss the function's writable window read the focused
      region's bytes; the primary read-only region is framed — inaccessible.
      The writable window and the ambient assertion are untouched (the
      focused region is read-only, so its bytes never change).  This is how
      a multi-input routine reads from one of several independent external
      buffers (each an ambient `bytesRegion`) while still writing its result
      through the function's writable window (`bnfMulModP`/`secfMulModP`). -/
  | readAt (label : String) (ptr : Reg)
           (roR : RegFile → List (BitVec 8) → Assertion →
              List (BitVec 8) → Assertion → Prop)
           (instrs : List Instr)
  /-- Ghost step: emits no code; replaces the ambient assertion `A` by an
      `R`-related `A'`, justified by one VC producing such an `A'` with a
      pointwise entailment (and pc-freedom).  Relational rather than
      functional so the new assertion can be built from
      existentially-quantified ghosts.  The strongest postcondition also
      records satisfiability of the old `A` — the *harvest* by which pure
      facts trapped inside the assertion (`p = 0` at a leaf, …) reach the
      pure VCs.  This is how recursive predicates are folded/unfolded
      mid-body (open a tree node, push a zipper frame, …). -/
  | ghost  (label : String)
           (R : RegFile → List (BitVec 8) → Assertion → Assertion → Prop)
  /-- Bounded loop: the body runs while `c` holds, at most `fuel` iterations.
      `inv i` must hold at the i-th evaluation of the header; the generator
      emits initialization, preservation, and fuel-exhaustion VCs. -/
  | «while»  (label : String) (c : Cond) (fuel : Nat)
           (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop) (body : Stmt)
  /-- Bounded loop with an *entry-snapshot-parameterized* invariant
      (docs/sasm-design.md §3.10): `inv rf₀ ws₀ A₀ i` must hold at the i-th
      evaluation of the header, where `(rf₀, ws₀, A₀)` is the symbolic state
      at loop entry.  This is the classic loop rule with logical variables:
      the snapshot is the only channel by which facts of the *enclosing*
      context — in particular an outer loop's quantified index, held in a
      counter register — survive across the loop (`sp` forgets the entry
      reach).  Use for inner loops of nested scans; `while` is the special
      case of a snapshot-independent invariant.  Emits the same code and
      the same three VCs as `while`, with the snapshot universally
      quantified (constrained by the entry reach) in `inv_step` and
      `exhausted`, and existentially recorded in the exit `sp`. -/
  | «whileS» (label : String) (c : Cond) (fuel : Nat)
           (inv : RegFile → List (BitVec 8) → Assertion →
             Nat → RegFile → List (BitVec 8) → Assertion → Prop)
           (body : Stmt)
  /-- Bounded loop with a **mid-body early exit** (`break`).  The loop runs
      while `guard` holds, at most `fuel` iterations; each iteration runs
      `bodyBefore`, then — if `breakCond` holds — jumps out of the loop to
      `post` (the break), otherwise runs `bodyAfter` and takes the back-edge.
      Both the guard-fail exit and the break exit establish `post` directly.
      `inv i` must hold at the i-th header evaluation.  This is the structured
      form of the machine idiom "scan until a predicate holds" (a header
      guard plus a mid-loop conditional branch to the loop exit, past the
      back-edge — a shape the single-exit `«while»` cannot express).  The
      generator emits initialization, continue-preservation, fuel-exhaustion,
      guard-exit, and break VCs (docs/sasm-design.md §3.10). -/
  | «whileBreak» (label : String) (guard : Cond) (fuel : Nat)
           (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
           (post : RegFile → List (BitVec 8) → Assertion → Prop)
           (bodyBefore : Stmt) (breakCond : Cond) (bodyAfter : Stmt)
  /-- Bottom-entry loop with a **mid-body break** and no top guard.  Each
      iteration starts by running `bodyBefore`; if `breakCond` holds, the
      synthesized branch exits to `post`, otherwise `bodyAfter` runs and a
      synthesized `JAL x0` jumps back to the loop entry.  `inv i` holds at the
      i-th entry to `bodyBefore`.  This byte-matches loops whose only exit test
      is in the middle of the body, after required side effects such as stores. -/
  | «doWhileBreak» (label : String) (fuel : Nat)
           (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
           (post : RegFile → List (BitVec 8) → Assertion → Prop)
           (bodyBefore : Stmt) (breakCond : Cond) (bodyAfter : Stmt)
  /-- Bottom-test (`do`-`while`) loop: `body` runs unconditionally, then the
      trailing branch loops back to the body's start while `guard` holds, at
      most `fuel` iterations — the machine idiom `body ++ [B guard → Lbody]`
      with no header guard and no unconditional jump (the conditional branch
      itself *is* the back-edge).  `inv i` must hold immediately after the
      i-th run of the body (before the i-th guard test); the body always
      runs at least once.  The generator emits initialization (from the
      statement's entry reach, through one run of `body`), preservation
      (guard holds ⇒ another run of `body` reaches `inv (i+1)`), and
      fuel-exhaustion (`inv fuel` ⇒ `¬ guard`) VCs — the bottom-test sibling
      of `«while»` (docs/sasm-design.md §3.10). -/
  | «doWhile» (label : String) (guard : Cond) (fuel : Nat)
           (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop) (body : Stmt)
  /-- Bottom-test loop with an *entry-snapshot-parameterized* invariant
      (the `doWhile`-to-`whileS` analogue): `inv rf₀ ws₀ A₀ i` must hold
      immediately after the i-th run of `body`, where `(rf₀, ws₀, A₀)` is
      the symbolic state at loop entry — same channel `whileS` uses for an
      outer loop's quantified index to survive an inner loop (`sp` forgets
      the entry reach otherwise).  Same code as `doWhile` (`body.flatten ++
      [B guard → Lbody]`, no header, no `JAL`); same three VCs as
      `doWhile`, with the snapshot universally quantified in `inv_step`/
      `exhausted` and existentially recorded in the exit `sp` — e.g. a
      nested bottom-test scan whose outer loop rereads a register after
      the inner loop finishes (the BE↔LE field-element converters). -/
  | «doWhileS» (label : String) (guard : Cond) (fuel : Nat)
           (inv : RegFile → List (BitVec 8) → Assertion →
             Nat → RegFile → List (BitVec 8) → Assertion → Prop)
           (body : Stmt)
  /-- Bounded return-terminating loop with two distinct return tails.  The
      header exits to `guardTail` when `guard` fails; after `bodyBefore`,
      `breakCond` exits to `breakTail`; otherwise `bodyAfter` runs and the
      synthesized `JAL x0` jumps back to the header.  Both tails must be
      accepted by `retOffsetsOk`, so the whole statement exits through `ra`
      rather than through the legacy single-exit `Fn.Spec` path. -/
  | «retWhileBreak» (label : String) (guard : Cond) (fuel : Nat)
           (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
           (bodyBefore : Stmt) (breakCond : Cond) (bodyAfter : Stmt)
           (guardTail breakTail : Stmt)
  /-- Direct call (`jal ra, f.entry`) to a routine with a verified caller
      interface (docs/sasm-design.md §3.6).  The handle carries the callee's
      pre/post in the C-like ABI; the VC generator emits one `.pre`
      obligation per call site. -/
  | call   (label : String) (f : FnHandle)
  /-- Indirect call (`jalr ra, rs, 0`) through an exposed register, against
      a finite table of possible callees (docs/sasm-design.md §3.6.3).  The
      `.pre` VC demands the register hold the entry address of one of the
      handles whose precondition is met; the strongest postcondition is the
      disjunction of the handles' postconditions.  Per-branch correlation
      (which handler ran) is recovered by instantiating the handles' ghost
      contracts per call site. -/
  | callReg (label : String) (rs : Reg) (handles : List FnHandle)
  /-- Indirect call (`jalr ra, rs, 0`) against a finite table of
      *snapshot-parameterized* callees (docs/4ch8f-interp-strategy.md).
      Same code, same `.pre` VC shape as `callReg`; the strongest
      postcondition additionally records the call's entry state, so each
      handle's `post` may relate exit to entry.  This is the dispatch
      construct for state-transforming callees invoked repeatedly at one
      call site (the interpreter's opcode handlers). -/
  | callRegS (label : String) (rs : Reg) (handles : List FnHandleS)
  /-- Direct call with a **focused read-only region** (the callee analogue of
      `readAt`): `jal ra, f.entry` to a routine whose read-only `region` is
      NOT the enclosing function's `reg` but a `bytesRegion` atom carved out
      of the ambient assertion `A` for that one call.  The relation `roR`
      pins the decomposition `A = bytesRegion f.region.base f.region.bytes **
      rest`; the `.focus` VC forces the caller to own that atom, and the
      callee is run against it as its `region` while the enclosing `reg` and
      the remainder `rest` are framed.  The callee's writable window is the
      enclosing `rw` (as for a plain `call`); its ambient is empty (leaf
      callee).  Flattens to the same single `JAL` as `call` — byte-identical,
      no injected instructions.  This is how a multi-input routine calls one
      converter per external buffer (`bnfMulModP`: be→le a0; be→le a1;
      le→be dst, with a0/a1 arbitrary independent pointers). -/
  | callAt (label : String)
           (roR : RegFile → List (BitVec 8) → Assertion → Assertion → Prop)
           (f : FnHandle)
  /-- Return to `ra` (`JALR x0 x1 0`).  This node is intentionally rejected by
      the legacy single-exit `Stmt.sound` path; use the return-terminating
      soundness path for statements whose control flow exits through `ra`. -/
  | retJalr (label : String)
  /-- Branch to one of two return-terminated tail blocks, with no balancing
      `JAL` after either arm.  Layout: `B c -> then; else; then`, where both
      arms are checked by the return-terminating soundness path. -/
  | retIf  (label : String) (c : Cond) (thn els : Stmt)

namespace Stmt

/-- Return to `ra` (`JALR x0 x1 0`). -/
def ret (label : String) : Stmt := retJalr label

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
  | ghost _ _         => 0
  | blockAt _ _ _ is  => is.length
  | readAt _ _ _ is   => is.length
  | «while» _ _ _ _ b   => b.size + 2
  | «whileS» _ _ _ _ b  => b.size + 2
  | «whileBreak» _ _ _ _ _ bb _ ba => bb.size + ba.size + 3
  | «doWhileBreak» _ _ _ _ bb _ ba => bb.size + ba.size + 2
  | «doWhile» _ _ _ _ b => b.size + 1
  | «doWhileS» _ _ _ _ b => b.size + 1
  | «retWhileBreak» _ _ _ _ bb _ ba gt bt => bb.size + ba.size + gt.size + bt.size + 3
  | call _ _          => 1
  | callReg _ _ _     => 1
  | callRegS _ _ _    => 1
  | callAt _ _ _      => 1
  | retJalr _         => 1
  | retIf _ _ t e     => t.size + e.size + 1

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
  | ghost _ _         => true
  | blockAt _ _ _ _   => true
  | readAt _ _ _ _    => true
  | «while» _ _ _ _ b => b.callFree
  | «whileS» _ _ _ _ b => b.callFree
  | «whileBreak» _ _ _ _ _ bb _ ba => bb.callFree && ba.callFree
  | «doWhileBreak» _ _ _ _ bb _ ba => bb.callFree && ba.callFree
  | «doWhile» _ _ _ _ b => b.callFree
  | «doWhileS» _ _ _ _ b => b.callFree
  | «retWhileBreak» _ _ _ _ bb _ ba gt bt =>
      bb.callFree && ba.callFree && gt.callFree && bt.callFree
  | call _ _          => false
  | callReg _ _ _     => false
  | callRegS _ _ _    => false
  | callAt _ _ _      => false
  | retJalr _         => true
  | retIf _ _ t e     => t.callFree && e.callFree

end Stmt

end SAsm
end EvmAsm.Rv64
