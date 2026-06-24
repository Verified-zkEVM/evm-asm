/-
  EvmAsm.Evm64.MulMod.ReduceOuterInduction

  Eight-limb induction for the MULMOD 512-bit reducer outer loop. The outer
  loop walks the eight 64-bit product limbs from high to low (`x16` starts at
  the top limb and decreases by 8 each iteration), folding each into the
  running remainder via the inner bit loop. Unlike the inner loop — whose
  product word is carried in a register and shifted — the outer loop's limbs
  live in memory, so the induction threads a *window* of the not-yet-processed
  limbs (`limbChain`) as a frame across iterations.

  This file builds that window primitive; the induction over
  `evm_mulmod_reduce512_loop_body_loop_path` / `_done_path` follows.
-/

import EvmAsm.Evm64.MulMod.ReduceOuterLoop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The product-limb memory window: `m` consecutive 64-bit limbs in memory,
    the first at `ptr`, each subsequent one 8 bytes lower (`ptr - 8`, matching
    the outer loop's `ADDI x16, x16, -8` stride). `limbs i` is the value at
    `ptr - 8 * i`; `limbs 0` is the limb the next iteration consumes. The empty
    window (`m = 0`) owns no memory. -/
def limbChain (ptr : Word) (limbs : Nat → Word) : Nat → Assertion
  | 0 => empAssertion
  | m + 1 =>
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) **
    limbChain (ptr + signExtend12 (4088 : BitVec 12)) (fun i => limbs (i + 1)) m

@[simp] theorem limbChain_zero (ptr : Word) (limbs : Nat → Word) :
    limbChain ptr limbs 0 = empAssertion := rfl

/-- Peel the head limb off the window: the limb at `ptr` (the next to be
    consumed) splits off, leaving the remaining `m` limbs as a window starting
    8 bytes lower. This is the step the eight-limb induction takes each
    iteration — the body folds `limbs 0`, then the tail becomes the next
    iteration's window. -/
theorem limbChain_succ (ptr : Word) (limbs : Nat → Word) (m : Nat) :
    limbChain ptr limbs (m + 1) =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) **
        limbChain (ptr + signExtend12 (4088 : BitVec 12)) (fun i => limbs (i + 1)) m) :=
  rfl

end EvmAsm.Evm64
