/-
  EvmAsm.Rv64.MemRegionWrite

  Writing into a `bytesRegion`: the byte-store counterpart to `bytesRegion_lbu_within`.
  An `SB` to byte `i` of a region turns `bytesRegion regionBase bs` into
  `bytesRegion regionBase (bs.set i b)`. The destination resource a byte-array copy
  loop needs (RLP address / hash fields → output struct).

  The algebraic core is `packBytes_set`: replacing byte `k` of a packed dword equals
  packing the byte list with position `k` set. Proved via byte-wise extensionality
  of dwords (`eq_of_forall_extractByte`).
-/

import EvmAsm.Rv64.ByteOps

namespace EvmAsm.Rv64

/-- `interval_cases`-over-8-bits closer for concrete `extractByte`/`replaceByte` goals. -/
local macro "byte_algebra" : tactic =>
  `(tactic| (ext i (hi : i < 8); simp [BitVec.truncate, BitVec.zeroExtend];
             try { interval_cases i <;> simp_all }))

/-- Replacing byte `k` then reading byte `j ≠ k` is unchanged. -/
theorem extractByte_replaceByte_diff (w : Word) (b : BitVec 8) {j k : Nat}
    (hj : j < 8) (hk : k < 8) (hne : j ≠ k) :
    extractByte (replaceByte w k b) j = extractByte w j := by
  interval_cases j <;> interval_cases k <;>
    first
      | exact absurd rfl hne
      | (simp only [extractByte, replaceByte]; byte_algebra)

/-- Reading byte `j` of a packed byte list is the (zero-padded) `j`-th byte. -/
theorem extractByte_packBytes_total (bytes : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (packBytes bytes) j = getByteAt bytes j := by
  rw [show j = (⟨j, hj⟩ : Fin 8).val from rfl, packBytes, extractByte_packDword]

/-- A dword is determined by its eight bytes. -/
theorem eq_of_forall_extractByte {w1 w2 : Word}
    (h : ∀ j, j < 8 → extractByte w1 j = extractByte w2 j) : w1 = w2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hmod : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : p / 8 * 8 + p % 8 = p := by omega
  have hbit := congrArg (fun bb => bb.getLsbD (p % 8)) (h (p / 8) (by omega))
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h2, hmod,
    decide_true, Bool.true_and] at hbit
  exact hbit

/-- Reading byte `j` of `bytes.set k b`: `b` at `k` (when in range), else `bytes`'s byte. -/
theorem getByteAt_set (bytes : List (BitVec 8)) (k : Nat) (b : BitVec 8) (j : Nat)
    (hk : k < bytes.length) :
    getByteAt (bytes.set k b) j = if j = k then b else getByteAt bytes j := by
  unfold getByteAt
  by_cases hjk : j = k
  · subst hjk
    simp [List.length_set, List.getElem_set_self, hk]
  · have hkj : k ≠ j := Ne.symm hjk
    by_cases hj : j < bytes.length <;>
      simp [List.length_set, List.getElem_set_ne, hj, hjk, hkj]

/-- **`replaceByte` of a packed dword = packing with the byte set.** The algebraic
    core of writing into a `bytesRegion`. -/
theorem packBytes_set (chunk : List (BitVec 8)) (k : Nat) (b : BitVec 8)
    (hk8 : k < 8) (hklen : k < chunk.length) :
    replaceByte (packBytes chunk) k b = packBytes (chunk.set k b) := by
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes_total _ j hj, getByteAt_set chunk k b j hklen]
  by_cases hjk : j = k
  · rw [if_pos hjk, hjk]
    exact extractByte_replaceByte_same (packBytes chunk) ⟨k, hk8⟩ b
  · rw [if_neg hjk, extractByte_replaceByte_diff _ _ hj hk8 hjk, extractByte_packBytes_total _ j hj]

end EvmAsm.Rv64
