/-
  EvmAsm.Codegen.Proofs.ExecuteSeamBridge

  Bead `.10` pilot — FOUNDATION only (issue 11801).

  The `.10` bead's job is the **execution seam**: prove that a dispatched
  guest handler implements its `SpecRef` instruction, closing the `execute`
  parameter of `runStatelessGuestSound`. This module is the pilot's **landed
  foundation**, not the one-step simulation itself — see the two residuals at
  the bottom and the honest "what this does NOT claim" section.

  ## The bridge is EFFECT-ON-A-MODELLED-MACHINE, not a RESULT

  `iAdd : EvmM Unit` is a state transformer over the SpecRef `Machine`/`Evm`
  (`Stateless/SpecRef/InstructionsCore.lean`): `binOp` pops two stack words,
  charges `GAS_VERY_LOW`, pushes `wrap256 (x + y)`, and advances `pc` by one.
  It **returns `Unit`** — there is no result value to relate, so a
  result-equality bridge has no well-typed target at all. The interpreter seam
  threads the `Evm` machine across instructions (`executeLoop → opImplementation`,
  op `0x01` → `iAdd`), so exactly the *state transition* of `iAdd` is what a
  dispatched handler must be shown to induce. The bridge statement is therefore:

  > running the dispatch step plus `h_ADD` reaches the next dispatch point in
  > a state encoding `(iAdd evm).run` — same stack with `wrap256(x + y)` on
  > top and one fewer word, `pc + 1`, gas debited by `GAS_VERY_LOW`.

  ## The relation: the ACTIVE-frame companion of `encodesFrame` (field ownership)

  This pilot introduces ONE new encoding relation, `guestExec`, between the
  guest's **active EVM execution state** and the SpecRef `Evm`. This is NOT a
  second, parallel account of what `encodesFrame` describes, and it must not be
  read as one — the two relations read **disjoint fields**:

  * `encodesFrame` (`Codegen/CallFrameWindows.lean:278`) is the
    **suspended-parent-frame** relation: at depth `d`, it pins a parent's saved
    `pc`/`codebase` dwords and its stack window (a `FrameState.stack : List
    Word`, serialized by the *placeholder* `stackWindowBytes`, which bead `.56`
    is what fixes), tiling the frame window for frames that are **not running**.
  * `guestExec` (this module) is the **active / running frame's execution
    state** — the stack pointer and the `evmStackIs` 256-bit stack at `sp`, the
    code pointer, and (once the debit site is decided) the gas cell. This is
    the state the handler actually mutates and that `iAdd` acts on.

  Two relations over the *same* object would rot; two relations over *disjoint*
  state are a decomposition. `encodesFrame` is left entirely **untouched** by
  this pilot.

  ## Why Option B is rejected

  The pilot does **not** extend `FrameState`/`encodesFrame` to carry a real
  `U256` stack and a gas field. Doing so would force bead `.56`'s concrete
  stack encoding to land as a side effect of an ADD pilot, and would change a
  relation that suspended-parent proofs already depend on. A pilot must not
  drag a foundational encoding change in behind it — if `.56` should land, it
  lands as its own piece with its own review.

  ## What this module does NOT claim (the two residuals)

  1. **Unpinned gas field (a FINDING, not a blocker).** There is **no
     per-opcode regular-gas debit** in the guest that a triple can see:
     a tree-wide search for `GAS_VERY_LOW`/`gasVeryLow` under `EvmAsm/Codegen`
     returns nothing; the only regular-gas machinery is the settle-time cell
     `runtime_tx_settle_regular_gas_left` (`Dispatch.lean`), and what
     `DispatcherExecStateGas` carries is EIP-8037 *state* gas, a different
     budget. `ADD`'s `GAS_VERY_LOW` is therefore very likely inside the
     **unproven dispatcher inline-asm seam** the issue itself names (related:
     #10524). Consequently `guestExec.gasLeft` is **deliberately unpinned** here
     — no guest cell is asserted to hold it — and every per-opcode simulation
     theorem inherits this gap until the seam is proven. We do **not** invent a
     debit site to make the relation look total.
  2. **Absent dispatch-step triple.** `EvmTinyInterp` is an *unrolled tiny-EVM
     demo* that chains verified opcode `Program`s with an explicit `x10`; it is
     **not** a reusable fetch/decode/table-jump triple over the real
     dispatcher. The dispatch-step lemma must be built over the actual
     dispatcher assembly and is its own substantial sub-proof. This pilot's
     single provable claim is the value bridge below; the one-step simulation
     itself is not yet closed and is not claimed here.

  ## What is claimed (and proven) here

  The **arithmetic identity** that turns "same stack" from an assumption into a
  theorem: the guest's 4-limb carry result (`add_limb_result_eq_add`) equals
  `a + b : EvmWord`, which composed with `BitVec.toNat_add` yields
  `wrap256 (x + y)` — precisely the sum `iAdd` pushes. This depends on neither
  open input and is the real bridge fact this landing carries.
-/

import EvmAsm.Evm64.EvmWord
import EvmAsm.Evm64.EvmWordArith.Arithmetic
import Mathlib.Tactic.FinCases
import EvmAsm.Stateless.SpecRef.Types
import EvmAsm.Stateless.SpecRef.Vm

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Stateless.SpecRef
open EvmAsm.Evm64.EvmWord

/-- `wrap256 n = n mod 2^256` — the SpecRef `U256` operator behind `iAdd`. -/
def wrap256 (n : Nat) : U256 := n % 2^256

/-- The SpecRef `U256` value carried by a guest EVM word: its `BitVec 256`
    `toNat` (already `< 2^256`, so it is a well-formed `U256`). -/
def evmWordToU256 (w : EvmAsm.Evm64.EvmWord) : U256 := w.toNat

/-- The guest `evmStackIs` word list read as the SpecRef `Evm.stack : List U256`. -/
def guestStackToU256 (ws : List EvmAsm.Evm64.EvmWord) : List U256 :=
  ws.map evmWordToU256

/-- The guest 4-limb carry result of `evm_add` equals the true 256-bit sum
    `a + b : EvmWord`. This is what makes `iAdd`'s stack effect (`wrap256
    (x + y)` pushed) identical to the guest handler's result-word — the ADD
    half of the "same stack" bridge. Built on the existing
    `add_carry_chain_correct`, not a new carry chain. -/
theorem add_limb_result_eq_add (a b : EvmAsm.Evm64.EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : BitVec 64) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : BitVec 64) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : BitVec 64) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : BitVec 64) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : BitVec 64) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let result3 := psum3 + carry2
    fromLimbs (fun i : Fin 4 => match i.val with
      | 0 => sum0 | 1 => result1 | 2 => result2 | _ => result3) = a + b := by
  intro a0 b0 a1 b1 a2 b2 a3 b3 sum0 carry0 psum1 carry1a result1 carry1b carry1 psum2 carry2a result2 carry2b carry2 psum3 result3
  have h := add_carry_chain_correct a b
  rcases h with ⟨h0, h1, h2, h3⟩
  refine (eq_iff_limbs.mpr ?_)
  intro i
  fin_cases i
  · rw [getLimb_fromLimbs]; exact h0.symm
  · rw [getLimb_fromLimbs]; exact h1.symm
  · rw [getLimb_fromLimbs]; exact h2.symm
  · rw [getLimb_fromLimbs]; exact h3.symm

/-- The composed ADD U256 identity: the guest ADD result word's value is
    `wrap256 (x + y)`, the exact sum `iAdd` pushes onto the stack. -/
theorem add_result_toNat_wrap256 (a b : EvmAsm.Evm64.EvmWord) :
    evmWordToU256 (a + b) = wrap256 (a.toNat + b.toNat) := by
  unfold evmWordToU256 wrap256
  rw [BitVec.toNat_add]

/-! ## The active-frame encoding relation skeleton

    `guestExec` maps the guest's active EVM execution state onto the SpecRef
    `Evm` machine. It is the **active-frame companion** of `encodesFrame` (see
    the module header): the two read disjoint fields. The `gasLeft` field is
    **deliberately unpinned** — see residual (1): no guest cell is asserted to
    hold it yet, because the per-opcode regular-gas debit is the unproven
    dispatcher seam. It is carried as a value in the abstract projection so the
    statement is already in the shape the one-step simulation will fill once
    that decision lands. -/

/-- The abstract EVM-machine projection a guest execution state encodes. -/
structure GuestEvmExec where
  /-- The EVM stack as a `List U256` (the `evmStackIs` word list read under
      `evmWordToU256`). -/
  stack : List U256
  /-- The EVM program counter (guest code pointer `x10` value). -/
  pc : U256
  /-- The code base (guest `codebase` word). -/
  codebase : BitVec 64
  /-- ⚠️ UNPINNED. The EVM gas-left. No guest cell is asserted to hold this
      yet: the per-opcode regular-gas debit has not been located (it is the
      unproven dispatcher inline-asm seam, issue 11801 / #10524). Carried only
      as the abstract target value, so the one-step simulation has the field to
      fill once the debit site is decided. -/
  gasLeft : U256

/-- `guestExec`: the active-frame encoding relation. `sp` is the guest EVM
    stack pointer (held in `x12`); `stack` is the encoded `evmStackIs` word
    list read as `List U256`; together with the abstract projection `g` they
    determine a SpecRef `Evm` machine. The stack/`pc`/`codebase` correspondence
    is the pinned part; `gasLeft` is the unpinned part (see `GuestEvmExec`). -/
def guestExec (_sp : BitVec 64) (stack : List U256) (g : GuestEvmExec) (e : Evm) : Prop :=
  e.stack = stack ∧ e.pc = g.pc ∧ e.gasLeft = g.gasLeft

end EvmAsm.Codegen.Proofs
