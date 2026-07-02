/-
  EvmAsm.Rv64.SAsm.MultiDword

  Reusable algebra for multi-dword focus windows (docs/sasm-howto.md,
  "Multi-dword focus blocks"): a window that is a concatenation of dword
  cells (`dwordBytes a ++ (dwordBytes b ++ …)`), read and written at
  literal offsets 0, 8, 16, ….

  - The slice lemmas reduce `((win.drop k).take 8)` to the k/8-th cell,
    feeding `execInstrRF_ld_dword`'s `hslice`.
  - The splice lemmas push `setBytes` through `++`, so a dword store into
    such a window rewrites to the same concatenation with one cell
    replaced (`execInstrRF_sd_dword` + `setBytes_append_* ` +
    `setBytes_dword_full`).

  The worked example is `revCellFn` in ExamplesVc.lean.
-/

import EvmAsm.Rv64.SAsm.RaSpill

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Slices of dword-concatenation windows (for loads)
-- ============================================================================

/-- The head cell of a dword-concatenation window. -/
theorem take8_dword_append (v : Word) (rest : List (BitVec 8)) :
    (dwordBytes v ++ rest).take 8 = dwordBytes v := by
  rw [List.take_append_of_le_length (by rw [length_dwordBytes]),
    List.take_of_length_le (by rw [length_dwordBytes])]

/-- Step past the head cell of a dword-concatenation window. -/
theorem drop8_dword_append (v : Word) (rest : List (BitVec 8)) (k : Nat) :
    (dwordBytes v ++ rest).drop (8 + k) = rest.drop k := by
  rw [show 8 + k = (dwordBytes v).length + k from by rw [length_dwordBytes],
    List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left]

/-- A full-dword store replaces the window (the generic multi-dword
    splice building block). -/
theorem setBytes_dword_full (ws : List (BitVec 8)) (v : Word)
    (h : ws.length = 8) : setBytes ws 0 (dwordBytes v) = dwordBytes v := by
  have h1 := setBytes_slot ws (dwordBytes v) 0 (by rw [length_dwordBytes]; omega)
  rwa [List.drop_zero, length_dwordBytes,
    List.take_of_length_le (by rw [length_setBytes]; omega)] at h1

/-- The head cell, packed (feeds `execInstrRF_ld_dword`'s `hslice`). -/
theorem packDword_at0 (v : Word) (rest : List (BitVec 8)) :
    packBytes (((dwordBytes v ++ rest).drop 0).take 8) = v := by
  rw [List.drop_zero, take8_dword_append, packBytes_dwordBytes]

-- ============================================================================
-- Splices into dword-concatenation windows (for stores)
-- ============================================================================

/-- A splice entirely inside the left part of `a ++ b` stays left. -/
theorem setBytes_append_left (a b ns : List (BitVec 8)) (i : Nat)
    (h : i + ns.length ≤ a.length) :
    setBytes (a ++ b) i ns = setBytes a i ns ++ b := by
  induction ns generalizing a i with
  | nil => rfl
  | cons n rest ih =>
      simp only [setBytes_cons]
      rw [List.set_append_left _ _ (by
        simp only [List.length_cons] at h
        omega),
        ih _ _ (by
          simp only [List.length_cons] at h
          simp only [List.length_set]
          omega)]

/-- A splice entirely inside the right part of `a ++ b` stays right. -/
theorem setBytes_append_right (a b ns : List (BitVec 8)) (i : Nat)
    (h : a.length ≤ i) :
    setBytes (a ++ b) i ns = a ++ setBytes b (i - a.length) ns := by
  induction ns generalizing b i with
  | nil => rfl
  | cons n rest ih =>
      simp only [setBytes_cons]
      rw [List.set_append_right _ _ (by omega),
        ih _ _ (by omega),
        show i + 1 - a.length = i - a.length + 1 from by omega]

/-- Overwrite the head cell of a dword-concatenation window. -/
theorem setBytes_dword_at0 (v w : Word) (rest : List (BitVec 8)) :
    setBytes (dwordBytes v ++ rest) 0 (dwordBytes w) = dwordBytes w ++ rest := by
  rw [setBytes_append_left _ _ _ _ (by rw [length_dwordBytes, length_dwordBytes]),
    setBytes_dword_full _ _ (length_dwordBytes v)]

-- ============================================================================
-- Byte-granularity windows (docs/sasm-howto.md, "Byte-granularity focus
-- blocks"): with `execInstrRF_lbu_byte`/`execInstrRF_sb_byte` (Sym.lean),
-- a byte store is a plain `List.set` and a byte load round-trips through
-- the zero-extension.  For FIXED-SIZE windows, explode the byte list into
-- cons cells (`w = [b0, …, bN]`) and `List.set`/`getD`/`reverse` all
-- reduce definitionally — no take/drop invariants needed for unrolled
-- code.  Worked example: `rev4Fn` in ExamplesVc.lean.
-- ============================================================================

/-- A one-byte splice is a plain `List.set`. -/
theorem setBytes_singleton (ws : List (BitVec 8)) (k : Nat) (b : BitVec 8) :
    setBytes ws k [b] = ws.set k b := rfl

/-- A byte loaded zero-extended (`LBU`) and stored truncated (`SB`)
    round-trips. -/
theorem truncate_zeroExtend_byte (b : BitVec 8) :
    ((b.zeroExtend 64).truncate 8) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp

/-- Step a splice past the head cell of a dword-concatenation window. -/
theorem setBytes_dword_past (v : Word) (rest ns : List (BitVec 8)) (k : Nat) :
    setBytes (dwordBytes v ++ rest) (8 + k) ns
      = dwordBytes v ++ setBytes rest k ns := by
  rw [setBytes_append_right _ _ _ _ (by rw [length_dwordBytes]; omega),
    length_dwordBytes, show 8 + k - 8 = k from by omega]

end SAsm
end EvmAsm.Rv64
