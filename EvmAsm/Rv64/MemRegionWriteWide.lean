/-
  EvmAsm.Rv64.MemRegionWriteWide

  Multi-byte writes into a `bytesRegion`: the SH/SW/SD counterparts of
  `packBytes_set` / `bytesRegion_dword_at_set` (MemRegionWrite/MemRegionStore).

  - `setBytes` splices a little-endian store payload into a region's byte list.
  - `packBytes_setBytes_halfword` / `_word32` / `_dword`: replacing an aligned
    halfword / 32-bit word / whole cell of a packed dword equals packing the
    byte list with the payload spliced in — the algebraic core of `SH`/`SW`/`SD`
    into a byte region.
  - `bytesRegion_dword_at_setBytes` frames the `q`-th dword for BOTH `bs` and
    `setBytes bs (8q+r) ns` with the SAME `front`/`rest` (the multi-byte
    generalization of `bytesRegion_dword_at_set`), so an aligned store lands
    exactly on the spliced region.

  All payloads stay within one dword cell (`r + ns.length ≤ 8`), which the
  n-alignment of machine store addresses guarantees.
-/

import EvmAsm.Rv64.MemRegionStore

namespace EvmAsm.Rv64

-- ============================================================================
-- Splicing a store payload into a byte list
-- ============================================================================

/-- Splice the byte list `ns` into `bs` starting at index `i` (a little-endian
    store payload).  Out-of-range positions are dropped (`List.set` semantics);
    store side conditions keep everything in range. -/
def setBytes (bs : List (BitVec 8)) (i : Nat) : List (BitVec 8) → List (BitVec 8)
  | [] => bs
  | b :: rest => setBytes (bs.set i b) (i + 1) rest

@[simp] theorem setBytes_nil (bs : List (BitVec 8)) (i : Nat) :
    setBytes bs i [] = bs := rfl

@[simp] theorem setBytes_cons (bs : List (BitVec 8)) (i : Nat) (b : BitVec 8)
    (rest : List (BitVec 8)) :
    setBytes bs i (b :: rest) = setBytes (bs.set i b) (i + 1) rest := rfl

@[simp] theorem length_setBytes (ns bs : List (BitVec 8)) (i : Nat) :
    (setBytes bs i ns).length = bs.length := by
  induction ns generalizing bs i with
  | nil => rfl
  | cons b rest ih => simp [ih]

@[simp] theorem setBytes_nil_left (i : Nat) (ns : List (BitVec 8)) :
    setBytes [] i ns = [] := by
  induction ns generalizing i with
  | nil => rfl
  | cons b rest ih => simp [ih]

/-- Reading byte `j` of a spliced list: the payload byte inside the spliced
    window, the original byte outside. -/
theorem getByteAt_setBytes (ns bs : List (BitVec 8)) (i j : Nat)
    (hin : i + ns.length ≤ bs.length) :
    getByteAt (setBytes bs i ns) j
      = if i ≤ j ∧ j < i + ns.length then getByteAt ns (j - i)
        else getByteAt bs j := by
  induction ns generalizing bs i with
  | nil =>
      simp only [setBytes_nil, List.length_nil, Nat.add_zero]
      rw [if_neg (by omega)]
  | cons b rest ih =>
      simp only [List.length_cons] at hin
      simp only [setBytes_cons]
      rw [ih _ (i + 1) (by rw [List.length_set]; omega)]
      by_cases h1 : i + 1 ≤ j ∧ j < i + 1 + rest.length
      · rw [if_pos h1, if_pos (by simp only [List.length_cons]; omega)]
        have hj : j - i = (j - (i + 1)) + 1 := by omega
        rw [hj]
        show getByteAt rest _ = getByteAt (b :: rest) _
        unfold getByteAt
        by_cases hr : j - (i + 1) < rest.length
        · rw [dif_pos hr, dif_pos (by simp only [List.length_cons]; omega)]
          simp
        · rw [dif_neg hr, dif_neg (by simp only [List.length_cons]; omega)]
      · rw [if_neg h1, getByteAt_set bs i b j (by omega)]
        by_cases h2 : j = i
        · subst h2
          rw [if_pos rfl, if_pos (by simp only [List.length_cons]; omega)]
          simp [getByteAt]
        · rw [if_neg h2, if_neg (by simp only [List.length_cons]; omega)]

-- ============================================================================
-- setBytes / take / drop commutation (for the region split induction)
-- ============================================================================

theorem setBytes_take_of_le (ns bs : List (BitVec 8)) (i n : Nat)
    (h : i + ns.length ≤ n) :
    (setBytes bs i ns).take n = setBytes (bs.take n) i ns := by
  induction ns generalizing bs i with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.length_cons] at h
      simp only [setBytes_cons]
      rw [ih _ (i + 1) (by omega), List.take_set]

theorem setBytes_drop_of_le (ns bs : List (BitVec 8)) (i n : Nat)
    (h : i + ns.length ≤ n) :
    (setBytes bs i ns).drop n = bs.drop n := by
  induction ns generalizing bs i with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.length_cons] at h
      simp only [setBytes_cons]
      rw [ih _ (i + 1) (by omega), List.drop_set,
        if_pos (show i < n from by omega)]

theorem setBytes_take_of_ge (ns bs : List (BitVec 8)) (i n : Nat)
    (h : n ≤ i) :
    (setBytes bs i ns).take n = bs.take n := by
  induction ns generalizing bs i with
  | nil => rfl
  | cons b rest ih =>
      simp only [setBytes_cons]
      rw [ih _ (i + 1) (by omega), List.take_set,
        List.set_eq_of_length_le (by rw [List.length_take]; omega)]

theorem setBytes_drop_of_ge (ns bs : List (BitVec 8)) (i n : Nat)
    (h : n ≤ i) :
    (setBytes bs i ns).drop n = setBytes (bs.drop n) (i - n) ns := by
  induction ns generalizing bs i with
  | nil => rfl
  | cons b rest ih =>
      simp only [setBytes_cons]
      rw [ih _ (i + 1) (by omega), List.drop_set,
        if_neg (show ¬ i < n from by omega),
        show i + 1 - n = i - n + 1 from by omega]

-- ============================================================================
-- Byte-level reads of replaceHalfword / replaceWord32
-- ============================================================================

/-- `interval_cases`-over-8-bits closer for concrete byte-of-dword goals. -/
local macro "byte_algebra" : tactic =>
  `(tactic| (ext i (hi : i < 8); simp [BitVec.truncate, BitVec.zeroExtend];
             try { interval_cases i <;> simp_all }))

/-- Byte `j` of `replaceHalfword w pos h`: the payload's bytes inside the
    replaced halfword, `w`'s bytes outside. -/
theorem extractByte_replaceHalfword (w : Word) (h : BitVec 16) {pos j : Nat}
    (hpos : pos < 4) (hj : j < 8) :
    extractByte (replaceHalfword w pos h) j
      = if j = 2 * pos then h.truncate 8
        else if j = 2 * pos + 1 then (h >>> 8).truncate 8
        else extractByte w j := by
  interval_cases pos <;> interval_cases j <;>
    simp only [replaceHalfword, extractByte, Nat.reduceMul, Nat.reduceAdd,
      reduceIte, Nat.zero_ne_add_one, Nat.add_one_ne_zero] <;>
    byte_algebra

/-- Byte `j` of `replaceWord32 w pos v`: the payload's bytes inside the
    replaced 32-bit word, `w`'s bytes outside. -/
theorem extractByte_replaceWord32 (w : Word) (v : BitVec 32) {pos j : Nat}
    (hpos : pos < 2) (hj : j < 8) :
    extractByte (replaceWord32 w pos v) j
      = if j = 4 * pos then v.truncate 8
        else if j = 4 * pos + 1 then (v >>> 8).truncate 8
        else if j = 4 * pos + 2 then (v >>> 16).truncate 8
        else if j = 4 * pos + 3 then (v >>> 24).truncate 8
        else extractByte w j := by
  interval_cases pos <;> interval_cases j <;>
    simp only [replaceWord32, extractByte, Nat.reduceMul, Nat.reduceAdd,
      reduceIte, Nat.zero_ne_add_one, Nat.add_one_ne_zero] <;>
    byte_algebra

-- ============================================================================
-- packBytes over spliced payloads (the SH/SW/SD algebraic cores)
-- ============================================================================

/-- The little-endian payload of an `SH` (the two bytes of `h`). -/
def halfwordBytes (h : BitVec 16) : List (BitVec 8) :=
  [h.truncate 8, (h >>> 8).truncate 8]

/-- The little-endian payload of an `SW` (the four bytes of `v`). -/
def word32Bytes (v : BitVec 32) : List (BitVec 8) :=
  [v.truncate 8, (v >>> 8).truncate 8, (v >>> 16).truncate 8, (v >>> 24).truncate 8]

/-- The little-endian payload of an `SD` (the eight bytes of `v`). -/
def dwordBytes (v : Word) : List (BitVec 8) :=
  [extractByte v 0, extractByte v 1, extractByte v 2, extractByte v 3,
   extractByte v 4, extractByte v 5, extractByte v 6, extractByte v 7]

@[simp] theorem length_halfwordBytes (h : BitVec 16) :
    (halfwordBytes h).length = 2 := rfl

@[simp] theorem length_word32Bytes (v : BitVec 32) :
    (word32Bytes v).length = 4 := rfl

@[simp] theorem length_dwordBytes (v : Word) :
    (dwordBytes v).length = 8 := rfl

/-- **`replaceHalfword` of a packed dword = packing with the payload spliced.** -/
theorem packBytes_setBytes_halfword (chunk : List (BitVec 8)) (r : Nat)
    (h : BitVec 16) (hr2 : 2 ∣ r) (hr8 : r + 2 ≤ 8) (hlen : r + 2 ≤ chunk.length) :
    replaceHalfword (packBytes chunk) (r / 2) h
      = packBytes (setBytes chunk r (halfwordBytes h)) := by
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_replaceHalfword _ _ (by omega) hj,
    show extractByte (packBytes (setBytes chunk r (halfwordBytes h))) j
      = getByteAt (setBytes chunk r (halfwordBytes h)) j
      from extractByte_packBytes_total _ j hj,
    getByteAt_setBytes _ _ _ _ (by simpa using hlen)]
  obtain ⟨m, rfl⟩ := hr2
  rw [show 2 * m / 2 = m from by omega]
  by_cases h0 : j = 2 * m
  · rw [if_pos h0, if_pos (by simp only [length_halfwordBytes]; omega)]
    subst h0
    simp [halfwordBytes, getByteAt]
  · rw [if_neg h0]
    by_cases h1 : j = 2 * m + 1
    · rw [if_pos h1, if_pos (by simp only [length_halfwordBytes]; omega)]
      subst h1
      simp [halfwordBytes, getByteAt]
    · rw [if_neg h1, if_neg (by simp only [length_halfwordBytes]; omega),
        extractByte_packBytes_total _ j hj]

/-- **`replaceWord32` of a packed dword = packing with the payload spliced.** -/
theorem packBytes_setBytes_word32 (chunk : List (BitVec 8)) (r : Nat)
    (v : BitVec 32) (hr4 : 4 ∣ r) (hr8 : r + 4 ≤ 8) (hlen : r + 4 ≤ chunk.length) :
    replaceWord32 (packBytes chunk) (r / 4) v
      = packBytes (setBytes chunk r (word32Bytes v)) := by
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_replaceWord32 _ _ (by omega) hj,
    show extractByte (packBytes (setBytes chunk r (word32Bytes v))) j
      = getByteAt (setBytes chunk r (word32Bytes v)) j
      from extractByte_packBytes_total _ j hj,
    getByteAt_setBytes _ _ _ _ (by simpa using hlen)]
  obtain ⟨m, rfl⟩ := hr4
  rw [show 4 * m / 4 = m from by omega]
  by_cases h0 : j = 4 * m
  · rw [if_pos h0, if_pos (by simp only [length_word32Bytes]; omega)]
    subst h0
    simp [word32Bytes, getByteAt]
  · rw [if_neg h0]
    by_cases h1 : j = 4 * m + 1
    · rw [if_pos h1, if_pos (by simp only [length_word32Bytes]; omega)]
      subst h1
      simp [word32Bytes, getByteAt]
    · rw [if_neg h1]
      by_cases h2 : j = 4 * m + 2
      · rw [if_pos h2, if_pos (by simp only [length_word32Bytes]; omega)]
        subst h2
        simp [word32Bytes, getByteAt]
      · rw [if_neg h2]
        by_cases h3 : j = 4 * m + 3
        · rw [if_pos h3, if_pos (by simp only [length_word32Bytes]; omega)]
          subst h3
          simp [word32Bytes, getByteAt]
        · rw [if_neg h3, if_neg (by simp only [length_word32Bytes]; omega),
            extractByte_packBytes_total _ j hj]

/-- **A stored dword = packing its own payload** (the `SD` core: the whole
    cell is replaced, so no read-modify-write is involved). -/
theorem packBytes_setBytes_dword (chunk : List (BitVec 8)) (v : Word)
    (hlen : 8 ≤ chunk.length) :
    v = packBytes (setBytes chunk 0 (dwordBytes v)) := by
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes_total _ j hj,
    getByteAt_setBytes _ _ _ _ (by simpa using hlen),
    if_pos (by simp only [length_dwordBytes]; omega)]
  interval_cases j <;> simp [dwordBytes, getByteAt]

-- ============================================================================
-- The paired region split for a spliced payload
-- ============================================================================

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-- Frame the `q`-th dword of a region for both `bs` and
    `setBytes bs (8q+r) ns`, with shared `front`/`rest` — the multi-byte
    generalization of `bytesRegion_dword_at_set`.  The payload stays within
    the cell (`r + ns.length ≤ 8`). -/
theorem bytesRegion_dword_at_setBytes (regionBase : Word)
    (bs ns : List (BitVec 8)) (q r : Nat)
    (hns : ns ≠ []) (hr : r + ns.length ≤ 8)
    (hi : 8 * q + r + ns.length ≤ bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegion regionBase bs
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * q)) ↦ₘ
            packBytes ((bs.drop (8 * q)).take 8)) ** rest))
      ∧ bytesRegion regionBase (setBytes bs (8 * q + r) ns)
        = (front ** (((regionBase + BitVec.ofNat 64 (8 * q)) ↦ₘ
            packBytes (setBytes ((bs.drop (8 * q)).take 8) r ns)) ** rest)) := by
  have hnslen : 0 < ns.length := List.length_pos_of_ne_nil hns
  induction q generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by
      intro h; subst h; simp only [List.length_nil] at hi; omega
    refine ⟨empAssertion, bytesRegion (regionBase + 8) (bs.drop 8), pcFree_emp,
      bytesRegion_pcFree _ _, ?_, ?_⟩
    · rw [bytesRegion_eq_cons regionBase bs hne,
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, List.drop_zero, sepConj_emp_left']
    · have hset_ne : setBytes bs (8 * 0 + r) ns ≠ [] :=
        List.ne_nil_of_length_pos
          (by rw [length_setBytes]; exact List.length_pos_of_ne_nil hne)
      rw [bytesRegion_eq_cons regionBase (setBytes bs (8 * 0 + r) ns) hset_ne]
      rw [setBytes_take_of_le ns bs (8 * 0 + r) 8 (by omega),
        setBytes_drop_of_le ns bs (8 * 0 + r) 8 (by omega),
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, Nat.zero_add, List.drop_zero, sepConj_emp_left']
  | succ k ih =>
    have hne : bs ≠ [] := by
      intro h; subst h; simp only [List.length_nil] at hi; omega
    have hi' : 8 * k + r + ns.length ≤ (bs.drop 8).length := by
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
    have htake_first : (setBytes bs (8 * (k + 1) + r) ns).take 8 = bs.take 8 :=
      setBytes_take_of_ge ns bs _ 8 (by omega)
    have hdrop_first : (setBytes bs (8 * (k + 1) + r) ns).drop 8
        = setBytes (bs.drop 8) (8 * k + r) ns := by
      rw [setBytes_drop_of_ge ns bs _ 8 (by omega)]
      congr 1
      omega
    refine ⟨(regionBase ↦ₘ packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIs hf', hr', ?_, ?_⟩
    · rw [bytesRegion_eq_cons regionBase bs hne, heq', haddr, hdrop, ← sepConj_assoc_eq]
    · have hset_ne : setBytes bs (8 * (k + 1) + r) ns ≠ [] :=
        List.ne_nil_of_length_pos
          (by rw [length_setBytes]; exact List.length_pos_of_ne_nil hne)
      rw [bytesRegion_eq_cons regionBase (setBytes bs (8 * (k + 1) + r) ns) hset_ne,
        htake_first, hdrop_first, heqset', haddr, hdrop, ← sepConj_assoc_eq]

end EvmAsm.Rv64
