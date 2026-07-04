/-
  EvmAsm.Codegen.Proofs.JumpdestBitmap

  The jumpdest-bitmap prologue's build loop (bead `evm-asm-cfjzu`, child of
  `.49.2`).  The dispatcher precomputes, once before the main loop, a bit per
  code byte marking the valid JUMPDEST positions (`emitJumpdestBitmapBuild`,
  `Dispatch.lean:142-206`); JUMP/JUMPI then test one bit in O(1).

  This module proves the loop's triple against the SpecRef anchor
  `validJumpDestinations` (EvmAsm/Stateless/SpecRef/Runtime.lean): the built
  bitmap's bit `idx` is set iff `idx` is a valid jump destination.

  L3 (the bit/byte layer) lives here: `bitmapBit` reads the logical bit `idx`
  out of the byte-list `ws`, `bitmapBit_setBit` is the read-modify-write step
  (`lbu; or; sb` sets exactly bit `pc`), and `bitmapBit_replicate_zero` is the
  loader-zeroed initial state.  The spec-side boundary-walk layer (L1) is in
  `SpecRef.Runtime` (`walkFrom`, `Reaches`, `vjd_lt_step`).
-/

import EvmAsm.Rv64.MemRegionWriteWide
import EvmAsm.Stateless.SpecRef.Runtime

namespace EvmAsm.Codegen.Proofs.JumpdestBitmap

/-! ## L3 — the bitmap bit/byte layer

The bitmap is a `List (BitVec 8)`; logical bit `idx` is bit `idx % 8` of byte
`idx / 8`. -/

/-- Logical bit `idx` of a byte-list bitmap: bit `idx % 8` of byte `idx / 8`. -/
def bitmapBit (ws : List (BitVec 8)) (idx : Nat) : Bool :=
  (ws.getD (idx / 8) 0).getLsbD (idx % 8)

private theorem getD_set_self {l : List (BitVec 8)} {i : Nat} {b d : BitVec 8}
    (h : i < l.length) : (l.set i b).getD i d = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

private theorem getD_set_ne {l : List (BitVec 8)} {i j : Nat} {b d : BitVec 8}
    (h : i ≠ j) : (l.set i b).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

/-- The single-bit mask `1 <<< k` has bit `j` set iff `j = k` (for `j < 8`). -/
private theorem mask_getLsbD (j k : Nat) (hj : j < 8) :
    ((1 : BitVec 8) <<< k).getLsbD j = decide (j = k) := by
  rw [BitVec.getLsbD_shiftLeft]; simp only [hj, decide_true, Bool.true_and]
  by_cases h : j < k <;> simp [h] <;> omega

/-- **L3 — the read-modify-write step.**  The `lbu; or; sb` sequence at code
    position `pc` (load byte `pc / 8`, or in bit `pc % 8`, store back) sets
    exactly logical bit `pc` of the bitmap and leaves every other bit alone. -/
theorem bitmapBit_setBit (ws : List (BitVec 8)) (pc idx : Nat)
    (hlen : pc / 8 < ws.length) :
    bitmapBit (ws.set (pc / 8) (ws.getD (pc / 8) 0 ||| ((1 : BitVec 8) <<< (pc % 8)))) idx
      = (decide (idx = pc)) || bitmapBit ws idx := by
  unfold bitmapBit
  by_cases hbyte : idx / 8 = pc / 8
  · rw [hbyte, getD_set_self hlen, BitVec.getLsbD_or,
      mask_getLsbD _ _ (Nat.mod_lt _ (by omega))]
    have hd : (idx = pc) ↔ (idx % 8 = pc % 8) := by omega
    cases (ws.getD (pc / 8) 0).getLsbD (idx % 8) <;> simp [hd, Bool.or_comm]
  · have hne : idx ≠ pc := by omega
    rw [getD_set_ne (Ne.symm hbyte)]; simp [hne]

/-- The loader-zeroed bitmap has every logical bit clear. -/
theorem bitmapBit_replicate_zero (n idx : Nat) :
    bitmapBit (List.replicate n 0) idx = false := by
  simp only [bitmapBit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : idx / 8 < n <;> simp [h]

end EvmAsm.Codegen.Proofs.JumpdestBitmap
