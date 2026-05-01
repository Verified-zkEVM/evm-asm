/-
  EvmAsm.Evm64.Memory

  Separation logic model for EVM memory (byte-addressable, zero-initialized,
  dynamically expandable) stored in RV64IM doubleword-aligned memory cells.

  Slice 1 (issue #99): defines the core `evmMemIs` assertion at dword-cell
  granularity plus the zero-initialized form `evmMemZero`. Subsequent slices
  add high-water-mark / expansion tracking (slice 2), MLOAD/MSTORE/MSTORE8
  specs (slices 3-5) and MSIZE (slice 6).

  Design choices (kept minimal for this slice):

  * EVM memory is modelled as a sequence of 64-bit cells, each owning eight
    consecutive bytes. Byte-level access (MSTORE8 / MLOAD at unaligned
    offsets) will be lifted on top of `evmMemIs` in later slices via the
    `ByteOps.lean` LBU/SB byte-level specs, which already operate on the
    underlying `↦ₘ` dword cells.
  * `numCells` is the dword (8-byte) count. The corresponding EVM byte size
    is `8 * numCells`. EVM memory expansion in the spec is in 32-byte words,
    which is a constraint enforced by the consumers (MSTORE/MLOAD specs),
    not by `evmMemIs` itself.
  * `contents : Nat → Word` is a pure function rather than a `ByteArray`
    so the assertion is total in `Nat` index — out-of-range indices simply
    have no cell asserted (they sit outside the sepConj chain). This
    matches how `evmStackIs` uses a `List EvmWord`.
-/

import EvmAsm.Evm64.Basic
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `evmMemIs base numCells contents` asserts that `numCells` consecutive
    8-byte memory cells starting at `base` hold the values `contents 0 ..
    contents (numCells-1)`. The cells are stored at byte offsets
    `base + 0, base + 8, ..., base + 8*(numCells-1)`.

    This is the dword-cell view of EVM memory. Byte-level reads/writes are
    lifted on top via the `ByteOps.lean` LBU/SB specs in later slices. -/
def evmMemIs (base : Word) (numCells : Nat) (contents : Nat → Word) : Assertion :=
  match numCells with
  | 0     => empAssertion
  | n + 1 =>
      evmMemIs base n contents ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ contents n)

/-- The zero-initialized EVM memory region: `numCells` dword cells, all 0.
    Models the EVM-spec invariant that unwritten memory reads as zero. -/
def evmMemZero (base : Word) (numCells : Nat) : Assertion :=
  evmMemIs base numCells (fun _ => 0)

@[simp] theorem evmMemIs_zero {base : Word} {contents : Nat → Word} :
    evmMemIs base 0 contents = empAssertion := rfl

theorem evmMemIs_succ {base : Word} {n : Nat} {contents : Nat → Word} :
    evmMemIs base (n + 1) contents =
      (evmMemIs base n contents ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ contents n)) := rfl

@[simp] theorem evmMemZero_zero {base : Word} :
    evmMemZero base 0 = empAssertion := rfl

theorem evmMemZero_succ {base : Word} {n : Nat} :
    evmMemZero base (n + 1) =
      (evmMemZero base n ** ((base + (BitVec.ofNat 64 (8 * n))) ↦ₘ 0)) := rfl

/-! ## pcFree -/

theorem pcFree_evmMemIs {base : Word} {n : Nat} {contents : Nat → Word} :
    (evmMemIs base n contents).pcFree := by
  induction n with
  | zero => exact pcFree_emp
  | succ k ih =>
      rw [evmMemIs_succ]
      exact pcFree_sepConj ih pcFree_memIs

theorem pcFree_evmMemZero {base : Word} {n : Nat} :
    (evmMemZero base n).pcFree := by
  unfold evmMemZero; exact pcFree_evmMemIs

instance (base : Word) (n : Nat) (contents : Nat → Word) :
    Assertion.PCFree (evmMemIs base n contents) := ⟨pcFree_evmMemIs⟩

instance (base : Word) (n : Nat) : Assertion.PCFree (evmMemZero base n) :=
  ⟨pcFree_evmMemZero⟩

end EvmAsm.Evm64
