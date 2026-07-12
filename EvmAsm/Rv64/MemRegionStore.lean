/-
  EvmAsm.Rv64.MemRegionStore

  Writing a byte into a `bytesRegion`: `bytesRegion_sb_within`, the `SB` counterpart
  to `bytesRegion_lbu_within`. Storing byte `i` (`SB`) turns `bytesRegion regionBase bs`
  into `bytesRegion regionBase (bs.set i b)` — the writable destination a byte-array
  copy loop needs.

  The structural core is `bytesRegion_dword_at_set`: a single induction that frames the
  `i`-th dword for BOTH `bs` and `bs.set i b` with the SAME surrounding `front`/`rest`,
  so the `SB` (which updates only that dword, via `packBytes_set`) lands exactly on the
  `bs.set i b` region.
-/

import EvmAsm.Rv64.MemRegionWrite
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Rv64

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-- Frame the `q`-th dword of a region for both `bs` and `bs.set (8q+r) b`, with shared
    `front`/`rest`. The store-side analog of `bytesRegion_dword_at`. -/
theorem bytesRegion_dword_at_set (regionBase : Word) (bs : List (BitVec 8)) (q r : Nat)
    (b : BitVec 8) (hr : r < 8) (hi : 8 * q + r < bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegion regionBase bs
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * q)) ↦ₘ
            packBytes ((bs.drop (8 * q)).take 8)) ** rest))
      ∧ bytesRegion regionBase (bs.set (8 * q + r) b)
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * q)) ↦ₘ
            packBytes (((bs.drop (8 * q)).take 8).set r b)) ** rest)) := by
  induction q generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hi
    have hbspos : 0 < bs.length := List.length_pos_of_ne_nil hne
    refine ⟨empAssertion, bytesRegion (regionBase + 8) (bs.drop 8), pcFree_emp,
      bytesRegion_pcFree _ _, ?_, ?_⟩
    · rw [bytesRegion_eq_cons regionBase bs hne,
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, List.drop_zero, sepConj_emp_left']
    · have hset_ne : bs.set (8 * 0 + r) b ≠ [] :=
        List.ne_nil_of_length_pos (by rw [List.length_set]; exact hbspos)
      rw [bytesRegion_eq_cons regionBase (bs.set (8 * 0 + r) b) hset_ne]
      have htake : (bs.set (8 * 0 + r) b).take 8 = (bs.take 8).set (8 * 0 + r) b := List.take_set
      have hdrop : (bs.set (8 * 0 + r) b).drop 8 = bs.drop 8 := by
        rw [List.drop_set]; simp only [if_pos (show 8 * 0 + r < 8 from by omega)]
      rw [htake, hdrop,
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, Nat.zero_add, List.drop_zero, sepConj_emp_left']
  | succ k ih =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hi
    have hi' : 8 * k + r < (bs.drop 8).length := by
      rw [List.length_drop]; omega
    obtain ⟨front', rest', hf', hr', heq', heqset'⟩ := ih (regionBase + 8) (bs.drop 8) hi'
    have haddr : (regionBase + 8) + BitVec.ofNat 64 (8 * k)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]; omega
    have hdrop : (bs.drop 8).drop (8 * k) = bs.drop (8 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    have htake_first : (bs.set (8 * (k + 1) + r) b).take 8 = bs.take 8 := by
      rw [List.take_set, List.set_eq_of_length_le (by rw [List.length_take]; omega)]
    have hdrop_first : (bs.set (8 * (k + 1) + r) b).drop 8 = (bs.drop 8).set (8 * k + r) b := by
      rw [List.drop_set]; simp only [show ¬ (8 * (k + 1) + r < 8) from by omega, if_false]
      congr 1; omega
    refine ⟨(regionBase ↦ₘ packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIs hf', hr', ?_, ?_⟩
    · rw [bytesRegion_eq_cons regionBase bs hne, heq', haddr, hdrop, ← sepConj_assoc_eq]
    · have hset_ne : bs.set (8 * (k + 1) + r) b ≠ [] :=
        List.ne_nil_of_length_pos (by rw [List.length_set]; exact List.length_pos_of_ne_nil hne)
      rw [bytesRegion_eq_cons regionBase (bs.set (8 * (k + 1) + r) b) hset_ne,
        htake_first, hdrop_first, heqset', haddr, hdrop, ← sepConj_assoc_eq]

/-- **`SB` writes byte `i` of the region.** Storing the low byte of `rs2` at
    `regionBase + i` (`i < bs.length`, base dword-aligned, no overflow) turns
    `bytesRegion regionBase bs` into `bytesRegion regionBase (bs.set i (v_data.truncate 8))`
    — the multi-dword byte store the single-`dwordAddr` `SB` spec could not express, the
    write analog of `bytesRegion_lbu_within`. -/
theorem bytesRegion_sb_within (rs1 rs2 : Reg) (regionBase v_data : Word) (base : Word)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data) **
       bytesRegion regionBase (bs.set i (v_data.truncate 8))) := by
  have hr : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hi_eq : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegion_dword_at_set regionBase bs (i / 8) (i % 8) (v_data.truncate 8) hr (by omega)
  rw [hi_eq] at heqset
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have hptr_eq : (regionBase + BitVec.ofNat 64 i) + signExtend12 (0 : BitVec 12)
      = regionBase + BitVec.ofNat 64 i := by show _ + (0 : Word) = _; bv_omega
  have halign' :
      alignToDword ((regionBase + BitVec.ofNat 64 i) + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [hptr_eq]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' :
      isValidByteAccess ((regionBase + BitVec.ofNat 64 i) + signExtend12 (0 : BitVec 12)) = true := by
    rw [hptr_eq]; exact hvalid
  have sb := generic_sb_spec_within rs1 rs2 (regionBase + BitVec.ofNat 64 i) v_data 0 base
    dwordAddr wordVal halign' hvalid'
  rw [hptr_eq] at sb
  have hbo : byteOffset (regionBase + BitVec.ofNat 64 i) = i % 8 :=
    byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : i % 8 < ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, packBytes_set _ (i % 8) (v_data.truncate 8) hr hchunk_len] at sb
  rw [heq, heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sb)

end EvmAsm.Rv64
