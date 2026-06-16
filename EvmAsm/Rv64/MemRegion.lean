/-
  EvmAsm.Rv64.MemRegion

  A contiguous multi-dword **byte region** in RISC-V memory: a `List (BitVec 8)`
  stored little-endian across consecutive 8-byte dwords, each named by `↦ₘ` with
  value `packBytes`. This is the separation-logic resource the RLP list decoder
  needs to read a payload spanning more than one dword — the existing decoder
  (`Phase2LongLoopGeneral`) reads only within a single dword.

  The base address is assumed dword-aligned (a payload at an unaligned pointer is
  read as a byte offset into a region whose base is the aligned input buffer).
-/

import EvmAsm.Rv64.ByteOps

namespace EvmAsm.Rv64

/-- Assert `n` consecutive 8-byte dwords starting at `base`, holding `bs`
    little-endian (`packBytes` per chunk). -/
def bytesRegionAux (base : Word) : Nat → List (BitVec 8) → Assertion
  | 0, _ => empAssertion
  | n + 1, bs => (base ↦ₘ packBytes (bs.take 8)) ** bytesRegionAux (base + 8) n (bs.drop 8)

/-- A contiguous byte region: `bs` stored in `⌈|bs|/8⌉` consecutive dwords from
    the (dword-aligned) `base`. -/
def bytesRegion (base : Word) (bs : List (BitVec 8)) : Assertion :=
  bytesRegionAux base ((bs.length + 7) / 8) bs

@[simp] theorem bytesRegion_nil (base : Word) : bytesRegion base [] = empAssertion := rfl

/-- Peel the first dword (8 bytes) off a nonempty region. -/
theorem bytesRegion_eq_cons (base : Word) (bs : List (BitVec 8)) (h : bs ≠ []) :
    bytesRegion base bs
      = ((base ↦ₘ packBytes (bs.take 8)) ** bytesRegion (base + 8) (bs.drop 8)) := by
  have hlen : 0 < bs.length := List.length_pos_of_ne_nil h
  have hchunks : (bs.length + 7) / 8 = ((bs.drop 8).length + 7) / 8 + 1 := by
    rw [List.length_drop]; omega
  unfold bytesRegion
  rw [hchunks]
  rfl

theorem bytesRegionAux_pcFree (n : Nat) (base : Word) (bs : List (BitVec 8)) :
    (bytesRegionAux base n bs).pcFree := by
  induction n generalizing base bs with
  | zero => exact pcFree_emp
  | succ k ih => exact pcFree_sepConj pcFree_memIs (ih _ _)

theorem bytesRegion_pcFree (base : Word) (bs : List (BitVec 8)) :
    (bytesRegion base bs).pcFree :=
  bytesRegionAux_pcFree _ base bs

end EvmAsm.Rv64

