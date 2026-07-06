/-
  EvmAsm.Rv64.CodeReqExtents

  Generic composition of an image-level `CodeReq` from a list of
  `(base, Program)` entries with ascending, non-overlapping extents
  (bead evm-asm-4ch8f.63).

  The guest image is `CodeReq.unionAll` over hundreds of per-function
  `CodeReq.ofProg` blocks.  A per-function triple proved against its own
  block lifts to the whole image via `cpsTripleWithin_extend_code` /
  `cpsHaltTripleWithin_extend_code`, whose monotonicity witness
  (`∀ a i, cr a = some i → cr' a = some i`) is what
  `ofProg_sub_unionAll_of_extentsOk` provides — with the entire
  384-block disjointness discharged by ONE decidable extent check
  (`extentsOkFrom`), never a per-block case split (the standing
  compose-don't-enumerate rule).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemSat

namespace EvmAsm.Rv64.CodeReq

/-- Extent sanity of `(base, prog)` entries: starting at or after `lo`,
    each entry's byte extent `[base, base + 4·|prog|)` begins at or after
    the previous entry's end, and the final end is ≤ `hi`.  One Boolean
    fold — `by decide` checks a whole image table. -/
def extentsOkFrom (lo hi : Nat) : List (Nat × Program) → Bool
  | [] => decide (lo ≤ hi)
  | e :: rest =>
      decide (lo ≤ e.1) && extentsOkFrom (e.1 + 4 * e.2.length) hi rest

theorem extentsOkFrom_le {lo hi : Nat} {es : List (Nat × Program)}
    (h : extentsOkFrom lo hi es = true) : lo ≤ hi := by
  induction es generalizing lo with
  | nil => simpa [extentsOkFrom] using h
  | cons e rest ih =>
    simp only [extentsOkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    have := ih h.2
    omega

/-- Every entry of an extent-checked list lies inside `[lo, hi]`. -/
theorem extentsOkFrom_mem {lo hi : Nat} {es : List (Nat × Program)}
    (h : extentsOkFrom lo hi es = true) :
    ∀ e ∈ es, lo ≤ e.1 ∧ e.1 + 4 * e.2.length ≤ hi := by
  induction es generalizing lo with
  | nil => intro e he; cases he
  | cons e0 rest ih =>
    simp only [extentsOkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    intro e he
    cases he with
    | head => exact ⟨h.1, extentsOkFrom_le h.2⟩
    | tail _ hmem =>
      have := ih h.2 e hmem
      omega

/-- The image `CodeReq` of an entry list. -/
def ofEntries (es : List (Nat × Program)) : CodeReq :=
  CodeReq.unionAll (es.map fun e => CodeReq.ofProg (BitVec.ofNat 64 e.1) e.2)

/-- **The image-composition workhorse**: under one decidable extent check,
    every entry's `ofProg` block is subsumed by the image union — the
    monotonicity witness `cpsTripleWithin_extend_code` and
    `cpsHaltTripleWithin_extend_code` consume.  No per-entry disjointness
    obligations survive: ascending extents make every earlier block miss
    the addresses of a later one. -/
theorem ofProg_sub_ofEntries_of_extentsOk {lo hi : Nat}
    {es : List (Nat × Program)}
    (hok : extentsOkFrom lo hi es = true) (hhi : hi < 2 ^ 64) :
    ∀ e ∈ es, ∀ a i,
      (CodeReq.ofProg (BitVec.ofNat 64 e.1) e.2) a = some i →
      ofEntries es a = some i := by
  induction es generalizing lo with
  | nil => intro e he; cases he
  | cons e0 rest ih =>
    simp only [extentsOkFrom, Bool.and_eq_true, decide_eq_true_eq] at hok
    intro e he a i hai
    simp only [ofEntries, List.map_cons, CodeReq.unionAll_cons]
    cases he with
    | head => exact CodeReq.union_hit hai
    | tail _ hmem =>
      -- `a` lies in `e`'s extent, which starts at or after `e0`'s end,
      -- so the `e0` block misses it and the union falls through.
      have hbounds := extentsOkFrom_mem hok.2 e hmem
      obtain ⟨k, hk, hae⟩ := CodeReq.ofProg_some_range _ _ _ _ hai
      have he0hi : e0.1 + 4 * e0.2.length ≤ hi :=
        Nat.le_trans hbounds.1 (by omega)
      have hatoNat : a.toNat = e.1 + 4 * k := by
        rw [hae, toNat_add_ofNat_of_le]
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
      have hne : CodeReq.ofProg (BitVec.ofNat 64 e0.1) e0.2 a = none := by
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have : a.toNat = e0.1 + 4 * k' := by
          rw [heq, toNat_add_ofNat_of_le]
          · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            omega
        omega
      exact CodeReq.union_skip hne (ih hok.2 e hmem a i hai)

end EvmAsm.Rv64.CodeReq
