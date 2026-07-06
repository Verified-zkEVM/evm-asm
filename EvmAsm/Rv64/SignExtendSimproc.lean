/-
  EvmAsm.Rv64.SignExtendSimproc

  Definitional simprocs that evaluate `signExtend12` / `signExtend13` /
  `signExtend21` applied to a *concrete* `BitVec` literal down to the
  corresponding `Word` (`BitVec 64`) constant, plus a `signext` closing
  tactic for the address-arithmetic goals that pervade the opcode specs.

  Motivation: before this file, every `addr + signExtend12 c = addr + K`
  obligation (and every standalone `signExtend1? c = K` grind-set fact) was
  discharged either by a hand-enumerated `@[grind =]` lemma per offset or by
  an ad-hoc `congr 1 <;> decide` / `rw [show … from by decide]` incantation
  (~150 sites). A simproc is the idiomatic tool for *reducing a function on
  literals* (cf. core `BitVec.reduceSignExtend`), and unlike the enumerated
  lemmas it handles ANY literal — including negative offsets such as
  `-32#12`, which the core `BitVec.reduceSignExtend` declines because the
  argument is `Neg.neg (…)` rather than a normalized literal (we `whnfR` the
  argument first to recover the value).

  These are `dsimproc`s: the rewrite is a *definitional* reduction, so no
  proof term is produced and nothing is added to the trusted base — fully
  kernel-checkable, consistent with the no-`bv_decide`/`native_decide` policy
  (see CLAUDE.md).
-/

import EvmAsm.Rv64.Instructions
import Lean

namespace EvmAsm.Rv64

open Lean Meta Simp

/-- Recover the concrete `BitVec` value of `arg`, seeing through a leading
    `Neg.neg` (negative offsets such as `-32#12` are written as
    `Neg.neg (32#12)`, which `getBitVecValue?` does not recognize directly). -/
private partial def bvLitValue? (arg : Expr) : SimpM (Option ((n : Nat) × BitVec n)) := do
  if let some r ← getBitVecValue? arg then
    return some r
  match_expr arg with
  | Neg.neg _ _ a =>
    match ← bvLitValue? a with
    | some ⟨n, v⟩ => return some ⟨n, -v⟩
    | none => return none
  | _ =>
    let arg' ← whnf arg
    if arg' == arg then return none else getBitVecValue? arg'

@[inline] private def reduceSignExtendCore (w : Nat) (arg : Expr) :
    SimpM DStep := do
  let some ⟨n, v⟩ ← bvLitValue? arg | return .continue
  if h : n = w then
    -- Emit a clean `BitVec.ofNat 64 <lit>` (defeq to `K#64` / `(K : Word)`),
    -- so the residual `K#64 = K` closes by `rfl` without deep unfolding.
    let val := ((h ▸ v : BitVec w).signExtend 64).toNat
    return .done (mkApp2 (.const ``BitVec.ofNat []) (toExpr (64 : Nat)) (toExpr val))
  else
    return .continue

/-- Evaluate `signExtend12 <literal>` to its `Word` constant. -/
dsimproc_decl reduceSignExtend12 (EvmAsm.Rv64.signExtend12 _) := fun e => do
  let_expr EvmAsm.Rv64.signExtend12 arg := e | return .continue
  reduceSignExtendCore 12 arg

/-- Evaluate `signExtend13 <literal>` to its `Word` constant. -/
dsimproc_decl reduceSignExtend13 (EvmAsm.Rv64.signExtend13 _) := fun e => do
  let_expr EvmAsm.Rv64.signExtend13 arg := e | return .continue
  reduceSignExtendCore 13 arg

/-- Evaluate `signExtend21 <literal>` to its `Word` constant. -/
dsimproc_decl reduceSignExtend21 (EvmAsm.Rv64.signExtend21 _) := fun e => do
  let_expr EvmAsm.Rv64.signExtend21 arg := e | return .continue
  reduceSignExtendCore 21 arg

/--
  `signext` — close a concrete address-arithmetic goal.

  Reduces every concrete `signExtend12/13/21` to its `Word` constant, then
  finishes the residual linear `BitVec` arithmetic. Handles the three shapes
  that dominate the opcode specs:
    * `addr + signExtend12 c = addr + K`
    * `(base + N) + M = base + K`     (pure address reassociation)
    * `signExtend12 c = K`            (standalone grind-set fact)
  Kernel-checkable (`bv_omega` is `omega` on `BitVec`; `decide`/`rfl` close
  the ground residuals).
-/
syntax "signext" : tactic
macro_rules
  | `(tactic| signext) =>
    `(tactic|
        (try simp only [reduceSignExtend12, reduceSignExtend13, reduceSignExtend21]
         all_goals first | bv_omega | rfl | decide))

end EvmAsm.Rv64
