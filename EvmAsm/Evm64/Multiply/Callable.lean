/-
  EvmAsm.Evm64.Multiply.Callable

  LP64-callable shim around `evm_mul`.

  The base `evm_mul` program (`Multiply/Program.lean`) ends in an `ADDI` that
  advances the EVM stack pointer; it does not return to the caller. To invoke
  it via `JAL x1, …` from a non-leaf function (e.g. the upcoming EXP opcode
  per `docs/92-exp-survey.md` §6.1), we wrap it with the `cc_ret` snippet
  from `Evm64/CallingConvention.lean`:

      mul_callable := evm_mul ;; cc_ret

  The shim is 64 instructions = 256 bytes long. Calling `mul_callable`
  satisfies the LP64 contract:

    * Pre-call layout: as for `evm_mul` (a at sp..sp+24, b at sp+32..sp+56,
      x12 = sp), plus `(.x1 ↦ᵣ ra_val)` carrying the saved return address.
    * Post-call: `evmMulStackPost sp a b` (x12 = sp+32, a*b at sp+32) plus
      `(.x1 ↦ᵣ ra_val)` (preserved), with PC now at `ra_val &&& ~~~1`.

  Reference: GH #92 (parent evm-asm-20z6), beads slice evm-asm-pp56.
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Multiply.Spec
import EvmAsm.Evm64.CallingConvention

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Program
-- ============================================================================

/-- LP64-callable wrapper for `evm_mul`: append a `cc_ret` so callers using
    `JAL x1, mul_callable` get control back via `JALR x0, x1, 0`. -/
def mul_callable : Program := evm_mul ;; cc_ret

/-- 63 (`evm_mul`) + 1 (`cc_ret`) = 64 instructions. -/
example : mul_callable.length = 64 := by decide

-- ============================================================================
-- Code-region helper
-- ============================================================================

/-- CodeReq for the full callable shim: union of `evm_mul_code` at `base`
    with `cc_ret_code` at `base + 252` (the byte offset where `cc_ret`
    starts). -/
abbrev mul_callable_code (base : Word) : CodeReq :=
  CodeReq.union (evm_mul_code base) (cc_ret_code (base + 252))

-- ============================================================================
-- Disjointness — evm_mul_code base ∥ cc_ret_code (base + 252)
-- ============================================================================

private theorem mul_callable_codes_disjoint (base : Word) :
    (evm_mul_code base).Disjoint (cc_ret_code (base + 252)) := by
  unfold evm_mul_code mul_col0_code mul_col1_code mul_col2_code mul_col3_code
         cc_ret_code cc_ret
  unfold mul_col0 mul_col1 mul_col2 mul_col3
  crDisjoint

-- ============================================================================
-- Callable spec
-- ============================================================================

/-- Stack-level LP64-callable MUL. Same pre/post as
    `evm_mul_stack_spec_within`, augmented with an `(.x1 ↦ᵣ ra_val)` slot
    that carries the caller's return address through the `cc_ret`. The exit
    PC is `ra_val &&& ~~~1` (the standard JALR target masking).

    64 instructions, 256 bytes total. -/
theorem mul_callable_spec_within (sp base ra_val : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word) :
    cpsTripleWithin 64 base (ra_val &&& ~~~1) (mul_callable_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b ** (.x1 ↦ᵣ ra_val))
      (evmMulStackPost sp a b ** (.x1 ↦ᵣ ra_val)) := by
  -- pcFree witness for the irreducible postcondition.
  have hpcFreeMulPost : (evmMulStackPost sp a b).pcFree := by
    delta evmMulStackPost; pcFree
  -- Step 1: the bare evm_mul stack-level spec, framed with `(.x1 ↦ᵣ ra_val)`.
  have h_mul := evm_mul_stack_spec_within sp base a b v5 v6 v7 v10 v11
  have h_mul_framed :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ ra_val) (by pcFree) h_mul
  -- Step 2: cc_ret at base + 252, jumping to ra_val &&& ~~~1, framed with
  -- `evmMulStackPost sp a b` on the left.
  have h_ret := ret_spec_within' (base + 252) ra_val
  have h_ret_framed :=
    cpsTripleWithin_frameL (evmMulStackPost sp a b) hpcFreeMulPost h_ret
  -- Compose. `cpsTripleWithin_seq` yields code `cr1.union cr2`, which is
  -- defeq to `mul_callable_code base`. Bound: 63 + 1 = 64.
  have hd := mul_callable_codes_disjoint base
  have h_seq := cpsTripleWithin_seq hd h_mul_framed h_ret_framed
  -- Align pre-condition associativity (the goal's right-leaning shape vs
  -- the framed `(… ) ** (.x1 ↦ᵣ ra_val)` left-leaning shape).
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => hp)
    h_seq

end EvmAsm.Evm64
