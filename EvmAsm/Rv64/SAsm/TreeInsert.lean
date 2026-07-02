/-
  EvmAsm.Rv64.SAsm.TreeInsert

  Sorted-BST insertion (Assertion-state milestone, stage 5b) — the
  slot-based formulation.

  A *slot* is an 8-byte pointer cell.  The tree hangs from a root slot
  (`Tree **root` in C terms); a node at `p` is a key cell at `p` plus two
  child slots at `p+8`/`p+16`.  The walk keeps the address of the current
  slot in a register and computes the next slot (`cur+8`/`cur+16`) — no
  parent tracking, and the terminal insert is one uniform store through
  the hole slot, with no top-vs-interior case split.

  Duplicates are excluded by the precondition (`x ∉ t0.keys`), so a
  two-way comparison suffices.
-/

import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.TreeDemo

namespace EvmAsm.Rv64
namespace SAsm

open Stmt

-- ============================================================================
-- Pure helpers
-- ============================================================================

namespace Tree

/-- Tree height. -/
def depth : Tree → Nat
  | .leaf => 0
  | .node _ l r => max l.depth r.depth + 1

end Tree

theorem insert_go_left {x k : Word} {l r : Tree} (h : BitVec.ult x k) :
    (Tree.node k l r).insert x = .node k (l.insert x) r := by
  simp [Tree.insert, h]

theorem insert_go_right {x k : Word} {l r : Tree}
    (hk : ¬ BitVec.ult x k) (hne : x ≠ k) :
    (Tree.node k l r).insert x = .node k l (r.insert x) := by
  have hkx : BitVec.ult k x := by
    simp only [BitVec.ult] at hk ⊢
    have : k.toNat ≠ x.toNat := fun hh => hne (BitVec.eq_of_toNat_eq hh).symm
    simp only [decide_eq_true_eq] at hk ⊢
    omega
  simp [Tree.insert, hk, hkx]

theorem not_mem_keys_left {x k : Word} {l r : Tree}
    (h : x ∉ (Tree.node k l r).keys) : x ∉ l.keys := by
  simp only [Tree.keys, List.mem_cons, List.mem_append] at h
  exact fun hl => h (Or.inr (Or.inl hl))

theorem not_mem_keys_right {x k : Word} {l r : Tree}
    (h : x ∉ (Tree.node k l r).keys) : x ∉ r.keys := by
  simp only [Tree.keys, List.mem_cons, List.mem_append] at h
  exact fun hr => h (Or.inr (Or.inr hr))

theorem ne_key_of_not_mem {x k : Word} {l r : Tree}
    (h : x ∉ (Tree.node k l r).keys) : x ≠ k := by
  simp only [Tree.keys, List.mem_cons] at h
  exact fun he => h (Or.inl he)

/-- The right-pointer dword of a node's byte image. -/
theorem nodeBytes_right (k pl pr : Word) :
    ((nodeBytes k pl pr).drop 16).take 8 = dwordBytes pr := by
  rw [show (16 : Nat) = 8 + 8 from rfl, ← List.drop_drop, nodeBytes,
    List.drop_append_of_le_length (by rw [length_dwordBytes]),
    List.drop_eq_nil_of_le (as := dwordBytes k) (by rw [length_dwordBytes]),
    List.nil_append,
    List.drop_append_of_le_length (by rw [length_dwordBytes]),
    List.drop_eq_nil_of_le (as := dwordBytes pl) (by rw [length_dwordBytes]),
    List.nil_append,
    List.take_of_length_le (by rw [length_dwordBytes])]

/-- The tail of a node's byte image is its right-pointer dword. -/
theorem nodeBytes_drop16 (k pl pr : Word) :
    (nodeBytes k pl pr).drop 16 = dwordBytes pr := by
  have h := nodeBytes_right k pl pr
  rwa [List.take_of_length_le (by
    simp only [List.length_drop, length_nodeBytes]
    omega)] at h

-- ============================================================================
-- Well-formedness helpers
-- ============================================================================

/-- Every valid address is nonzero (all machine ranges start at ≥ 0x20). -/
theorem RwRegion.wf_base_ne_zero {s : Word} {n : Nat} (h : RwRegion.wf ⟨s, n⟩)
    (hn : 0 < n) : s ≠ 0 := by
  intro h0
  subst h0
  have hv : isValidMemAddr ((0 : Word) + BitVec.ofNat 64 0) = true := h.2.2 0 hn
  rw [show ((0 : Word) + BitVec.ofNat 64 0) = 0 from by decide] at hv
  exact absurd hv (by decide)

/-- Split a 24-byte region's well-formedness into its three dword cells. -/
theorem wf24_split {q : Word} (h : RwRegion.wf ⟨q, 24⟩) :
    RwRegion.wf ⟨q, 8⟩ ∧ RwRegion.wf ⟨q + 8, 8⟩ ∧ RwRegion.wf ⟨q + 16, 8⟩ := by
  have hal : q.toNat % 8 = 0 := h.1
  have hov : q.toNat + 24 < 2 ^ 64 := h.2.1
  have hval : ∀ k, k < 24 → isValidMemAddr (q + BitVec.ofNat 64 k) = true :=
    fun k hk => h.2.2 k hk
  have h8 : (q + 8).toNat = q.toNat + 8 := by bv_omega
  have h16 : (q + 16).toNat = q.toNat + 16 := by bv_omega
  refine ⟨⟨hal, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · show q.toNat + 8 < 2 ^ 64
    omega
  · intro k hk
    have hk' : k < 8 := hk
    exact hval k (by omega)
  · show (q + 8).toNat % 8 = 0
    omega
  · show (q + 8).toNat + 8 < 2 ^ 64
    omega
  · intro k hk
    have hk' : k < 8 := hk
    rw [show (q + 8) + BitVec.ofNat 64 k = q + BitVec.ofNat 64 (8 + k) from by
      bv_omega]
    exact hval (8 + k) (by omega)
  · show (q + 16).toNat % 8 = 0
    omega
  · show (q + 16).toNat + 8 < 2 ^ 64
    omega
  · intro k hk
    have hk' : k < 8 := hk
    rw [show (q + 16) + BitVec.ofNat 64 k = q + BitVec.ofNat 64 (16 + k) from by
      bv_omega]
    exact hval (16 + k) (by omega)

/-- A provable pure assertion is `emp`. -/
theorem pure_true_eq_emp {P : Prop} (h : P) : ⌜P⌝ = empAssertion :=
  funext fun _hp => propext ⟨fun ⟨he, _⟩ => he, fun he => ⟨he, h⟩⟩

-- ============================================================================
-- Byte-level cell algebra
-- ============================================================================

/-- A single-dword region is one memory cell. -/
theorem bytesRegion_dword_eq (b v : Word) :
    bytesRegion b (dwordBytes v) = ((b ↦ₘ v) ** empAssertion) := by
  rw [bytesRegion_eq_cons b (dwordBytes v) (by simp [dwordBytes]),
    List.take_of_length_le (by rw [length_dwordBytes]),
    packBytes_dwordBytes,
    List.drop_eq_nil_of_le (by rw [length_dwordBytes]),
    bytesRegion_nil]

/-- A node's 24-byte region splits into three dword-cell regions. -/
theorem bytesRegion_node_split (q k a b : Word) :
    bytesRegion q (nodeBytes k a b)
      = ((bytesRegion q (dwordBytes k)) **
         ((bytesRegion (q + 8) (dwordBytes a)) **
          bytesRegion (q + 16) (dwordBytes b))) := by
  rw [bytesRegion_eq_cons q (nodeBytes k a b) (by simp [nodeBytes, dwordBytes]),
    show (nodeBytes k a b).take 8 = dwordBytes k from by
      have := nodeBytes_key k a b
      rwa [List.drop_zero] at this,
    packBytes_dwordBytes,
    bytesRegion_eq_cons (q + 8) ((nodeBytes k a b).drop 8) (by
      simp [nodeBytes, dwordBytes]),
    show ((nodeBytes k a b).drop 8).take 8 = dwordBytes a from
      nodeBytes_left k a b,
    packBytes_dwordBytes,
    show ((nodeBytes k a b).drop 8).drop 8 = (nodeBytes k a b).drop 16 from by
      rw [List.drop_drop],
    show bytesRegion ((q + 8) + 8) ((nodeBytes k a b).drop 16)
        = bytesRegion (q + 16) (dwordBytes b) from by
      rw [show ((q + 8) + 8 : Word) = q + 16 from by bv_omega,
        show (nodeBytes k a b).drop 16 = dwordBytes b from by
          have := nodeBytes_right k a b
          rwa [List.take_of_length_le (by
            simp [nodeBytes, dwordBytes])] at this],
    bytesRegion_dword_eq q k, bytesRegion_dword_eq (q + 8) a]
  rw [sepConj_assoc', sepConj_emp_left']
  rw [sepConj_assoc', sepConj_emp_left']

/-- A full-dword store replaces the window. -/
theorem setBytes_dword_full (ws : List (BitVec 8)) (v : Word)
    (h : ws.length = 8) : setBytes ws 0 (dwordBytes v) = dwordBytes v := by
  have h1 := setBytes_slot ws (dwordBytes v) 0 (by rw [length_dwordBytes]; omega)
  rwa [List.drop_zero, length_dwordBytes,
    List.take_of_length_le (by rw [length_setBytes]; omega)] at h1

/-- `getByteAt` through `drop`. -/
theorem getByteAt_drop (l : List (BitVec 8)) (n m : Nat)
    (h : n + m < l.length) :
    getByteAt (l.drop n) m = getByteAt l (n + m) := by
  unfold getByteAt
  rw [dif_pos (by rw [List.length_drop]; omega), dif_pos h]
  exact List.getElem_drop ..

/-- `getByteAt` through `take`. -/
theorem getByteAt_take_eq (l : List (BitVec 8)) (n m : Nat) (hm : m < n)
    (h : m < l.length) :
    getByteAt (l.take n) m = getByteAt l m := by
  unfold getByteAt
  rw [dif_pos (by rw [List.length_take]; omega), dif_pos h]
  exact List.getElem_take ..

/-- Writing key and nil children over 24 junk bytes yields a fresh node. -/
theorem setBytes_junk_node (junk : List (BitVec 8)) (x : Word)
    (h24 : junk.length = 24) :
    setBytes (setBytes (setBytes junk 0 (dwordBytes x)) 8 (dwordBytes 0))
        16 (dwordBytes 0)
      = nodeBytes x 0 0 := by
  apply List.ext_getElem
  · simp [h24, nodeBytes, dwordBytes]
  · intro j hj1 hj2
    have hj24 : j < 24 := by
      simpa [length_setBytes, h24] using hj1
    have hget : ∀ (bs : List (BitVec 8)) (i : Nat) (h : i < bs.length),
        bs[i] = getByteAt bs i := fun bs i h => by
      unfold getByteAt
      rw [dif_pos h]
    rw [hget _ j hj1, hget _ j hj2]
    rw [getByteAt_setBytes _ _ _ _ (by
        simp only [length_setBytes, h24, length_dwordBytes]
        omega),
      getByteAt_setBytes _ _ _ _ (by
        simp only [length_setBytes, h24, length_dwordBytes]
        omega),
      getByteAt_setBytes _ _ _ _ (by
        simp only [h24, length_dwordBytes]
        omega)]
    simp only [length_dwordBytes]
    by_cases hc16 : 16 ≤ j
    · rw [if_pos ⟨hc16, by omega⟩]
      have h1 : getByteAt (nodeBytes x 0 0) j
          = getByteAt (dwordBytes (0 : Word)) (j - 16) := by
        have hd := getByteAt_drop (nodeBytes x 0 0) 16 (j - 16)
          (by rw [length_nodeBytes]; omega)
        rw [show 16 + (j - 16) = j from by omega] at hd
        rw [← hd, nodeBytes_drop16]
      rw [h1]
    · rw [if_neg (fun hh => hc16 hh.1)]
      by_cases hc8 : 8 ≤ j
      · rw [if_pos ⟨hc8, by omega⟩]
        have h1 : getByteAt (nodeBytes x 0 0) j
            = getByteAt (dwordBytes (0 : Word)) (j - 8) := by
          have hd := getByteAt_drop (nodeBytes x 0 0) 8 (j - 8)
            (by rw [length_nodeBytes]; omega)
          rw [show 8 + (j - 8) = j from by omega] at hd
          have ht := getByteAt_take_eq ((nodeBytes x 0 0).drop 8) 8 (j - 8)
            (by omega)
            (by rw [List.length_drop, length_nodeBytes]; omega)
          rw [← hd, ← ht, nodeBytes_left]
        rw [h1]
      · rw [if_neg (fun hh => hc8 hh.1), if_pos ⟨by omega, by omega⟩]
        have h1 : getByteAt (nodeBytes x 0 0) j = getByteAt (dwordBytes x) j := by
          have ht := getByteAt_take_eq (nodeBytes x 0 0) 8 j (by omega)
            (by rw [length_nodeBytes]; omega)
          rw [← ht, show (nodeBytes x 0 0).take 8 = dwordBytes x from by
            have h := nodeBytes_key x 0 0
            rwa [List.drop_zero] at h]
        rw [h1, Nat.sub_zero]

-- ============================================================================
-- Slot-based tree predicates
-- ============================================================================

/-- An 8-byte pointer cell at `s` holding `p`. -/
def slotCell (s p : Word) : Assertion :=
  ⌜RwRegion.wf ⟨s, 8⟩⌝ ** bytesRegion s (dwordBytes p)

/-- The key cell of a node. -/
def keyCell (p k : Word) : Assertion :=
  ⌜RwRegion.wf ⟨p, 8⟩⌝ ** bytesRegion p (dwordBytes k)

theorem pcFree_slotCell (s p : Word) : (slotCell s p).pcFree :=
  pcFree_sepConj pcFree_pure (bytesRegion_pcFree _ _)

theorem pcFree_keyCell (p k : Word) : (keyCell p k).pcFree :=
  pcFree_sepConj pcFree_pure (bytesRegion_pcFree _ _)

/-- The tree `t` at node address `p`, slot-based: key cell plus two child
    slots (nil = 0). -/
def treeAtS : Word → Tree → Assertion
  | p, .leaf => ⌜p = 0⌝
  | p, .node k l r => fun h => ∃ pl pr,
      ((keyCell p k) **
        ((slotCell (p + 8) pl ** treeAtS pl l) **
         (slotCell (p + 16) pr ** treeAtS pr r))) h

/-- The tree hanging from the slot at `s`. -/
def treeFrom (s : Word) (t : Tree) : Assertion :=
  fun h => ∃ p, ((slotCell s p) ** treeAtS p t) h

theorem pcFree_treeAtS (p : Word) (t : Tree) : (treeAtS p t).pcFree := by
  induction t generalizing p with
  | leaf => exact pcFree_pure
  | node k l r ihl ihr =>
      intro h hp
      obtain ⟨pl, pr, hh⟩ := hp
      exact pcFree_sepConj (pcFree_keyCell _ _)
        (pcFree_sepConj (pcFree_sepConj (pcFree_slotCell _ _) (ihl pl))
          (pcFree_sepConj (pcFree_slotCell _ _) (ihr pr))) h hh

theorem pcFree_treeFrom (s : Word) (t : Tree) : (treeFrom s t).pcFree := by
  intro h hp
  obtain ⟨p, hh⟩ := hp
  exact pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _) h hh

/-- Node addresses are nonzero (baked well-formedness). -/
theorem treeAtS_sat_node {p k : Word} {l r : Tree} {hp : PartialState}
    (h : treeAtS p (.node k l r) hp) :
    p ≠ 0 ∧ RwRegion.wf ⟨p, 8⟩ := by
  obtain ⟨pl, pr, h1, h2, hd, hu, hkey, hch⟩ := h
  have hwf := ((sepConj_pure_left h1).mp hkey).1
  exact ⟨RwRegion.wf_base_ne_zero hwf (by omega), hwf⟩

/-- The nil shadow on satisfying states. -/
theorem treeAtS_sat_shadow {p : Word} {t : Tree} {hp : PartialState}
    (h : treeAtS p t hp) : p = 0 ↔ t = .leaf := by
  cases t with
  | leaf => exact ⟨fun _ => rfl, fun _ => h.2⟩
  | node k l r =>
      exact ⟨fun h0 => absurd h0 (treeAtS_sat_node h).1,
        fun hleaf => nomatch hleaf⟩

-- ============================================================================
-- The slot zipper
-- ============================================================================

/-- Tree-with-a-hole over slots: `ctxS c s0 s` is the structure from the
    root slot `s0` down to (excluding) the subtree hanging from slot `s`. -/
def ctxS : Tree.Ctx → Word → Word → Assertion
  | .top, s0, s => ⌜s0 = s⌝
  | .left k r c, s0, s => fun h => ∃ sp pn pr,
      (⌜s = pn + 8⌝ **
        ((ctxS c s0 sp) **
          ((slotCell sp pn) **
            ((keyCell pn k) ** (slotCell (pn + 16) pr ** treeAtS pr r))))) h
  | .right k l c, s0, s => fun h => ∃ sp pn pl,
      (⌜s = pn + 16⌝ **
        ((ctxS c s0 sp) **
          ((slotCell sp pn) **
            ((keyCell pn k) ** (slotCell (pn + 8) pl ** treeAtS pl l))))) h

theorem pcFree_ctxS (c : Tree.Ctx) (s0 s : Word) : (ctxS c s0 s).pcFree := by
  induction c generalizing s with
  | top => exact pcFree_pure
  | left k r c ih =>
      intro h hp
      obtain ⟨sp, pn, pr, hh⟩ := hp
      exact pcFree_sepConj pcFree_pure
        (pcFree_sepConj (ih sp)
          (pcFree_sepConj (pcFree_slotCell _ _)
            (pcFree_sepConj (pcFree_keyCell _ _)
              (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _)))))
        h hh
  | right k l c ih =>
      intro h hp
      obtain ⟨sp, pn, pl, hh⟩ := hp
      exact pcFree_sepConj pcFree_pure
        (pcFree_sepConj (ih sp)
          (pcFree_sepConj (pcFree_slotCell _ _)
            (pcFree_sepConj (pcFree_keyCell _ _)
              (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _)))))
        h hh

/-- The zipper fold over slots. -/
theorem ctxS_zip_fold (c : Tree.Ctx) (s0 : Word) :
    ∀ (s p : Word) (t : Tree) hp,
      ((ctxS c s0 s) ** ((slotCell s p) ** treeAtS p t)) hp →
      treeFrom s0 (c.zip t) hp := by
  induction c with
  | top =>
      intro s p t hp hh
      obtain ⟨hs0, ht⟩ := (sepConj_pure_left hp).mp hh
      subst hs0
      exact ⟨p, ht⟩
  | left k r c ih =>
      rintro s p t hp ⟨h1, h2, hd, hu, ⟨sp, pn, pr, hctx⟩, ht⟩
      have hh' : ((⌜s = pn + 8⌝ **
          ((ctxS c s0 sp) **
            ((slotCell sp pn) **
              ((keyCell pn k) ** (slotCell (pn + 16) pr ** treeAtS pr r)))))
          ** ((slotCell s p) ** treeAtS p t)) hp :=
        ⟨h1, h2, hd, hu, hctx, ht⟩
      rw [sepConj_assoc'] at hh'
      obtain ⟨heq, hh''⟩ := (sepConj_pure_left hp).mp hh'
      subst heq
      have hfin : ((ctxS c s0 sp) **
          ((slotCell sp pn) ** treeAtS pn (.node k t r))) hp := by
        have hshaped : ((ctxS c s0 sp) **
            ((slotCell sp pn) **
              ((keyCell pn k) **
                ((slotCell (pn + 8) p ** treeAtS p t) **
                 (slotCell (pn + 16) pr ** treeAtS pr r))))) hp := by
          xperm_hyp hh''
        exact sepConj_mono_right (fun hq hx =>
          sepConj_mono_right (fun hv hy => ⟨p, pr, hy⟩) hq hx) hp hshaped
      exact ih sp pn (.node k t r) hp hfin
  | right k l c ih =>
      rintro s p t hp ⟨h1, h2, hd, hu, ⟨sp, pn, pl, hctx⟩, ht⟩
      have hh' : ((⌜s = pn + 16⌝ **
          ((ctxS c s0 sp) **
            ((slotCell sp pn) **
              ((keyCell pn k) ** (slotCell (pn + 8) pl ** treeAtS pl l)))))
          ** ((slotCell s p) ** treeAtS p t)) hp :=
        ⟨h1, h2, hd, hu, hctx, ht⟩
      rw [sepConj_assoc'] at hh'
      obtain ⟨heq, hh''⟩ := (sepConj_pure_left hp).mp hh'
      subst heq
      have hfin : ((ctxS c s0 sp) **
          ((slotCell sp pn) ** treeAtS pn (.node k l t))) hp := by
        have hshaped : ((ctxS c s0 sp) **
            ((slotCell sp pn) **
              ((keyCell pn k) **
                ((slotCell (pn + 8) pl ** treeAtS pl l) **
                 (slotCell (pn + 16) p ** treeAtS p t))))) hp := by
          xperm_hyp hh''
        exact sepConj_mono_right (fun hq hx =>
          sepConj_mono_right (fun hv hy => ⟨pl, p, hy⟩) hq hx) hp hshaped
      exact ih sp pn (.node k l t) hp hfin

/-- Descend left: push a zipper frame around the opened node. -/
theorem ctxS_push_left (c : Tree.Ctx) (s0 s p k : Word) (l r : Tree) :
    ∀ hp, ((ctxS c s0 s) **
        ((slotCell s p) **
          ((keyCell p k) **
            ((treeFrom (p + 8) l) ** (treeFrom (p + 16) r))))) hp →
      ((ctxS (.left k r c) s0 (p + 8)) ** treeFrom (p + 8) l) hp := by
  intro hp hh
  -- open the right child's slot existential at this state
  obtain ⟨h1, h2, hd, hu, hctx, h3, h4, hd2, hu2, hslot, h5, h6, hd3, hu3,
    hkey, h7, h8, hd4, hu4, htl, ⟨pr, htr⟩⟩ := hh
  have hh' : ((ctxS c s0 s) **
      ((slotCell s p) **
        ((keyCell p k) **
          ((treeFrom (p + 8) l) **
            ((slotCell (p + 16) pr) ** treeAtS pr r))))) hp :=
    ⟨h1, h2, hd, hu, hctx, h3, h4, hd2, hu2, hslot, h5, h6, hd3, hu3,
      hkey, h7, h8, hd4, hu4, htl, htr⟩
  have hshaped : (((ctxS c s0 s) **
      ((slotCell s p) **
        ((keyCell p k) ** ((slotCell (p + 16) pr) ** treeAtS pr r)))) **
      treeFrom (p + 8) l) hp := by
    xperm_hyp hh'
  exact sepConj_mono_left (fun hq hx =>
    ⟨s, p, pr, (sepConj_pure_left hq).mpr ⟨rfl, hx⟩⟩) hp hshaped

/-- Descend right: push a zipper frame around the opened node. -/
theorem ctxS_push_right (c : Tree.Ctx) (s0 s p k : Word) (l r : Tree) :
    ∀ hp, ((ctxS c s0 s) **
        ((slotCell s p) **
          ((keyCell p k) **
            ((treeFrom (p + 8) l) ** (treeFrom (p + 16) r))))) hp →
      ((ctxS (.right k l c) s0 (p + 16)) ** treeFrom (p + 16) r) hp := by
  intro hp hh
  obtain ⟨h1, h2, hd, hu, hctx, h3, h4, hd2, hu2, hslot, h5, h6, hd3, hu3,
    hkey, h7, h8, hd4, hu4, ⟨pl, htl⟩, htr⟩ := hh
  have hh' : ((ctxS c s0 s) **
      ((slotCell s p) **
        ((keyCell p k) **
          (((slotCell (p + 8) pl) ** treeAtS pl l) **
            (treeFrom (p + 16) r))))) hp :=
    ⟨h1, h2, hd, hu, hctx, h3, h4, hd2, hu2, hslot, h5, h6, hd3, hu3,
      hkey, h7, h8, hd4, hu4, htl, htr⟩
  have hshaped : (((ctxS c s0 s) **
      ((slotCell s p) **
        ((keyCell p k) ** ((slotCell (p + 8) pl) ** treeAtS pl l)))) **
      treeFrom (p + 16) r) hp := by
    xperm_hyp hh'
  exact sepConj_mono_left (fun hq hx =>
    ⟨s, p, pl, (sepConj_pure_left hq).mpr ⟨rfl, hx⟩⟩) hp hshaped

-- ============================================================================
-- The free node
-- ============================================================================

/-- The 24-byte free node at `q` (contents junk until the terminal fill). -/
def junkAt (q : Word) (junk : List (BitVec 8)) : Assertion :=
  ⌜RwRegion.wf ⟨q, 24⟩⌝ ** bytesRegion q junk

theorem pcFree_junkAt (q : Word) (junk : List (BitVec 8)) :
    (junkAt q junk).pcFree :=
  pcFree_sepConj pcFree_pure (bytesRegion_pcFree _ _)

/-- The well-formedness a slot cell bakes in. -/
theorem slotCell_wf {s p : Word} {hp : PartialState} (h : slotCell s p hp) :
    RwRegion.wf ⟨s, 8⟩ :=
  ((sepConj_pure_left hp).mp h).1

-- ============================================================================
-- The annotations
-- ============================================================================

/-- Focus annotation of the root-slot load: the window is the root slot's
    pointer cell; the remainder is its well-formedness, the free node, and
    the tree hanging from the loaded pointer. -/
def treeInsLoad0R (q : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest => ∃ p : Word,
    win = dwordBytes p
    ∧ rest = (⌜RwRegion.wf ⟨rf.get .x10, 8⟩⌝ **
        ((junkAt q junk) ** treeAtS p t0))

/-- The enter ghost: reseal the root slot around the loaded pointer, open
    the trivial zipper, and harvest the nil-pointer shadow. -/
def treeInsEnterR (s0 q : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion → Assertion → Prop :=
  fun rf _ _ A' =>
    A' = ((junkAt q junk) **
      ((ctxS .top s0 (rf.get .x10)) **
        ((slotCell (rf.get .x10) (rf.get .x12)) ** treeAtS (rf.get .x12) t0)))
    ∧ (rf.get .x12 = 0 ↔ t0 = .leaf)

/-- The loop invariant of the insertion walk: a slot zipper and the current
    subtree (both ghost), the insertion-image plug identity, freshness of
    the key below the hole, the nil-pointer shadow, the counter-register
    tie, the remaining-depth bound, and the pinned argument registers. -/
def treeInsInv (s0 x q : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A => ∃ (c : Tree.Ctx) (t' : Tree),
    A = ((junkAt q junk) **
      ((ctxS c s0 (rf.get .x10)) **
        ((slotCell (rf.get .x10) (rf.get .x12)) ** treeAtS (rf.get .x12) t')))
    ∧ c.zip (t'.insert x) = t0.insert x
    ∧ x ∉ t'.keys
    ∧ (rf.get .x12 = 0 ↔ t' = .leaf)
    ∧ rf.get .x15 = BitVec.ofNat 64 i
    ∧ t'.depth + i ≤ t0.depth
    ∧ rf.get .x11 = x
    ∧ rf.get .x14 = q

/-- Focus annotation of the node-key load: the window is the current node's
    key cell; the remainder is everything else, with the node opened into
    its key-cell well-formedness and two child slots. -/
def treeInsKeyR (s0 x q : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    ∃ (c : Tree.Ctx) (k : Word) (l r : Tree) (pl pr : Word),
    win = dwordBytes k
    ∧ rest = (⌜RwRegion.wf ⟨rf.get .x12, 8⟩⌝ **
        ((junkAt q junk) **
          ((ctxS c s0 (rf.get .x10)) **
            ((slotCell (rf.get .x10) (rf.get .x12)) **
              (((slotCell (rf.get .x12 + 8) pl) ** treeAtS pl l) **
               ((slotCell (rf.get .x12 + 16) pr) ** treeAtS pr r))))))
    ∧ c.zip ((Tree.node k l r).insert x) = t0.insert x
    ∧ x ∉ (Tree.node k l r).keys
    ∧ (Tree.node k l r).depth + (rf.get .x15).toNat ≤ t0.depth

/-- The descend ghost (shared by both branches): after `cur := p+8`/`p+16`
    the ambient is a pushed zipper frame plus the chosen child's slot-tree.
    The context existential hides which direction was taken. -/
def treeInsDescendR (s0 x q : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion → Assertion → Prop :=
  fun rf _ _ A' => ∃ (c' : Tree.Ctx) (t' : Tree),
    A' = ((junkAt q junk) **
      ((ctxS c' s0 (rf.get .x10)) ** treeFrom (rf.get .x10) t'))
    ∧ c'.zip (t'.insert x) = t0.insert x
    ∧ x ∉ t'.keys
    ∧ t'.depth + (rf.get .x15).toNat ≤ t0.depth

/-- Focus annotation of the next-slot load: the window is the current
    slot's pointer cell. -/
def treeInsSlotR (s0 x q : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest => ∃ (c' : Tree.Ctx) (p' : Word) (t' : Tree),
    win = dwordBytes p'
    ∧ rest = (⌜RwRegion.wf ⟨rf.get .x10, 8⟩⌝ **
        ((junkAt q junk) **
          ((ctxS c' s0 (rf.get .x10)) ** treeAtS p' t')))
    ∧ c'.zip (t'.insert x) = t0.insert x
    ∧ x ∉ t'.keys
    ∧ t'.depth + (rf.get .x15).toNat ≤ t0.depth

/-- The step ghost: reseal the slot around the loaded pointer and harvest
    the child's nil-pointer shadow — the invariant shape at `i+1`. -/
def treeInsStepR (s0 x q : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion → Assertion → Prop :=
  fun rf _ _ A' => ∃ (c' : Tree.Ctx) (t' : Tree),
    A' = ((junkAt q junk) **
      ((ctxS c' s0 (rf.get .x10)) **
        ((slotCell (rf.get .x10) (rf.get .x12)) ** treeAtS (rf.get .x12) t')))
    ∧ c'.zip (t'.insert x) = t0.insert x
    ∧ x ∉ t'.keys
    ∧ (rf.get .x12 = 0 ↔ t' = .leaf)
    ∧ t'.depth + (rf.get .x15).toNat ≤ t0.depth

/-- Focus annotation of the terminal fill: the window is the free node's
    24 junk bytes; the loop has exited, so the hole subtree is a leaf. -/
def treeInsFillR (s0 x : Word) (junk : List (BitVec 8)) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest => ∃ (c : Tree.Ctx),
    win = junk
    ∧ rest = (⌜RwRegion.wf ⟨rf.get .x14, 24⟩⌝ **
        ((ctxS c s0 (rf.get .x10)) **
          ((slotCell (rf.get .x10) (rf.get .x12)) **
            treeAtS (rf.get .x12) .leaf)))
    ∧ c.zip (Tree.leaf.insert x) = t0.insert x

/-- The mknode ghost: the filled bytes are a fresh singleton node. -/
def treeInsMkR (s0 x : Word) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion → Assertion → Prop :=
  fun rf _ _ A' => ∃ (c : Tree.Ctx),
    A' = ((ctxS c s0 (rf.get .x10)) **
      ((slotCell (rf.get .x10) (rf.get .x12)) **
        treeAtS (rf.get .x14) (.node x .leaf .leaf)))
    ∧ c.zip (Tree.leaf.insert x) = t0.insert x

/-- Focus annotation of the terminal store: the window is the hole slot's
    pointer cell (still nil). -/
def treeInsStoreR (s0 x : Word) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest => ∃ (c : Tree.Ctx),
    win = dwordBytes (rf.get .x12)
    ∧ rest = (⌜RwRegion.wf ⟨rf.get .x10, 8⟩⌝ **
        ((ctxS c s0 (rf.get .x10)) **
          treeAtS (rf.get .x14) (.node x .leaf .leaf)))
    ∧ c.zip (Tree.leaf.insert x) = t0.insert x

-- ============================================================================
-- The function
-- ============================================================================

/-- Sorted-BST insertion, slot-based: walk the pointer-cell addresses to
    the nil slot where `x` belongs (duplicates excluded by precondition),
    fill the free node at `a4` with `(x, nil, nil)`, and store its address
    through the hole slot.  `a0` = root slot, `a1` = key, `a4` = free node;
    ghosts: the tree `t0`, the free node's junk bytes. -/
def treeInsertFn (s0 x q : Word) (junk : List (BitVec 8)) (t0 : Tree) : Fn where
  name := "treeInsert"
  pre := fun rf _ A => rf.get .x10 = s0 ∧ rf.get .x11 = x ∧ rf.get .x14 = q
    ∧ A = ((junkAt q junk) ** treeFrom s0 t0)
  post := fun _ _ A => A = treeFrom s0 (t0.insert x)
  body :=
    .block "init" [.LI .x15 0] ;;;
    .blockAt "load0" .x10 (treeInsLoad0R q junk t0) [.LD .x12 .x10 0] ;;;
    .ghost "enter" (treeInsEnterR s0 q junk t0) ;;;
    .«while» "walk" (.bne .x12 .x0) t0.depth (treeInsInv s0 x q junk t0)
      (.blockAt "node" .x12 (treeInsKeyR s0 x q junk t0)
          [.LD .x13 .x12 0, .ADDI .x15 .x15 1] ;;;
       .ite "cmp" (.bltu .x11 .x13)
         (.block "goL" [.ADDI .x10 .x12 8] ;;;
          .ghost "stepL" (treeInsDescendR s0 x q junk t0))
         (.block "goR" [.ADDI .x10 .x12 16] ;;;
          .ghost "stepR" (treeInsDescendR s0 x q junk t0)) ;;;
       .blockAt "load" .x10 (treeInsSlotR s0 x q junk t0) [.LD .x12 .x10 0] ;;;
       .ghost "step" (treeInsStepR s0 x q junk t0)) ;;;
    .blockAt "fill" .x14 (treeInsFillR s0 x junk t0)
      [.SD .x14 .x11 0, .SD .x14 .x0 8, .SD .x14 .x0 16] ;;;
    .ghost "mknode" (treeInsMkR s0 x t0) ;;;
    .blockAt "store" .x10 (treeInsStoreR s0 x t0) [.SD .x10 .x14 0] ;;;
    .ghost "fold" (fun _ _ _ A' => A' = treeFrom s0 (t0.insert x))

-- ============================================================================
-- The block engines
-- ============================================================================

private theorem treeIns_li_engine (reg : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    (execBlock reg b rf ws [.LI .x15 0]).1 = rf.set .x15 0 := by
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]

private theorem treeIns_addi_engine (reg : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (ofs : BitVec 12) :
    (execBlock reg b rf ws [.ADDI .x10 .x12 ofs]).1
      = rf.set .x10 (rf.get .x12 + signExtend12 ofs) := by
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]

/-- The slot-load block: `a2 := *(a0)` with the slot cell as the window. -/
private theorem treeIns_load_engine (reg : Region) (rf : RegFile) (p : Word) :
    (execBlock reg (rf.get .x10) rf (dwordBytes p) [.LD .x12 .x10 0]).1
        = rf.set .x12 p
    ∧ (execBlock reg (rf.get .x10) rf (dwordBytes p) [.LD .x12 .x10 0]).2
        = dwordBytes p := by
  have h0 : ((rf.get .x10 + signExtend12 (0 : BitVec 12))
      - rf.get .x10).toNat = 0 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem]
  rw [if_pos (show inRw (rf.get .x10) (dwordBytes p)
      (rf.get .x10 + signExtend12 0) 8 from by
    unfold inRw
    rw [h0, length_dwordBytes])]
  refine ⟨?_, trivial⟩
  show rf.set .x12 (Region.dwordAt ⟨rf.get .x10, dwordBytes p⟩ _) = _
  unfold Region.dwordAt
  rw [show ((rf.get .x10 + signExtend12 0)
      - (⟨rf.get .x10, dwordBytes p⟩ : Region).base).toNat = 0 from h0,
    List.drop_zero, List.take_of_length_le (by rw [length_dwordBytes]),
    packBytes_dwordBytes]

/-- The node-visit block: `a3 := *(a2)`, bump the counter. -/
private theorem treeIns_node_engine (reg : Region) (rf : RegFile) (k : Word) :
    (execBlock reg (rf.get .x12) rf (dwordBytes k)
        [.LD .x13 .x12 0, .ADDI .x15 .x15 1]).1
      = (rf.set .x13 k).set .x15 (rf.get .x15 + 1)
    ∧ (execBlock reg (rf.get .x12) rf (dwordBytes k)
        [.LD .x13 .x12 0, .ADDI .x15 .x15 1]).2
      = dwordBytes k := by
  have h0 : ((rf.get .x12 + signExtend12 (0 : BitVec 12))
      - rf.get .x12).toNat = 0 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  have hv : Region.dwordAt ⟨rf.get .x12, dwordBytes k⟩
      (rf.get .x12 + signExtend12 0) = k := by
    unfold Region.dwordAt
    rw [show ((rf.get .x12 + signExtend12 0)
        - (⟨rf.get .x12, dwordBytes k⟩ : Region).base).toNat = 0 from h0,
      List.drop_zero, List.take_of_length_le (by rw [length_dwordBytes]),
      packBytes_dwordBytes]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem]
  rw [if_pos (show inRw (rf.get .x12) (dwordBytes k)
      (rf.get .x12 + signExtend12 0) 8 from by
    unfold inRw
    rw [h0, length_dwordBytes])]
  rw [hv, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    RegFile.get_set_ne _ .x13 .x15 _ (by decide)]
  exact ⟨rfl, trivial⟩

/-- The fill block: write key and nil children over the free node's junk. -/
private theorem treeIns_fill_engine (reg : Region) (rf : RegFile)
    (junk : List (BitVec 8)) (h24 : junk.length = 24) :
    (execBlock reg (rf.get .x14) rf junk
        [.SD .x14 .x11 0, .SD .x14 .x0 8, .SD .x14 .x0 16]).1 = rf
    ∧ (execBlock reg (rf.get .x14) rf junk
        [.SD .x14 .x11 0, .SD .x14 .x0 8, .SD .x14 .x0 16]).2
      = nodeBytes (rf.get .x11) 0 0 := by
  have h0 : ((rf.get .x14 + signExtend12 (0 : BitVec 12))
      - rf.get .x14).toNat = 0 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  have h8 : ((rf.get .x14 + signExtend12 (8 : BitVec 12))
      - rf.get .x14).toNat = 8 := by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
    bv_omega
  have h16 : ((rf.get .x14 + signExtend12 (16 : BitVec 12))
      - rf.get .x14).toNat = 16 := by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
    bv_omega
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem,
    storeSem, RegFile.get_x0]
  rw [h0, h8, h16]
  exact ⟨trivial, setBytes_junk_node junk (rf.get .x11) h24⟩

/-- The terminal store: `*(a0) := a4`, replacing the hole slot's content. -/
private theorem treeIns_store_engine (reg : Region) (rf : RegFile)
    (p0 : Word) :
    (execBlock reg (rf.get .x10) rf (dwordBytes p0) [.SD .x10 .x14 0]).1 = rf
    ∧ (execBlock reg (rf.get .x10) rf (dwordBytes p0) [.SD .x10 .x14 0]).2
      = dwordBytes (rf.get .x14) := by
  have h0 : ((rf.get .x10 + signExtend12 (0 : BitVec 12))
      - rf.get .x10).toNat = 0 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem,
    storeSem]
  rw [h0]
  exact ⟨trivial, setBytes_dword_full (dwordBytes p0) (rf.get .x14)
    (length_dwordBytes p0)⟩

-- ============================================================================
-- The spec
-- ============================================================================

theorem treeInsertFn_spec (s0 x q : Word) (junk : List (BitVec 8)) (t0 : Tree)
    (h24 : junk.length = 24) (hmem : x ∉ t0.keys)
    (hdep : t0.depth < 2 ^ 64 - 1) (base : Word) :
    (treeInsertFn s0 x q junk t0).Spec base := by
  vcgen
  case treeInsert.load0.focus =>
    rintro rf ws A ⟨rf₀, ws₀, -, ⟨hx10, hx11, hx14, hA⟩, rfl, rfl⟩ hApc hp hhp
    rw [treeIns_li_engine]
    have hx10' : (rf₀.set .x15 0).get .x10 = s0 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide), hx10]
    rw [hA] at hhp
    obtain ⟨h1, h2, hd, hu, hjunk, p, h3, h4, hd2, hu2, hsc, htree⟩ := hhp
    have hwf := slotCell_wf hsc
    refine ⟨dwordBytes p, _, ⟨p, rfl, rfl⟩, ?_, ?_, ?_⟩
    · rw [hx10']
      have hall : ((junkAt q junk) **
          ((⌜RwRegion.wf ⟨s0, 8⟩⌝ ** bytesRegion s0 (dwordBytes p)) **
            treeAtS p t0)) hp :=
        ⟨h1, h2, hd, hu, hjunk, h3, h4, hd2, hu2, hsc, htree⟩
      xperm_hyp hall
    · exact pcFree_sepConj pcFree_pure
        (pcFree_sepConj (pcFree_junkAt _ _) (pcFree_treeAtS _ _))
    · rw [length_dwordBytes, hx10']
      exact hwf
  case treeInsert.load0.mem =>
    rintro rf ws A win rest - - ⟨p, rfl, rfl⟩ -
    have h0 : ((rf.get .x10 + signExtend12 (0 : BitVec 12))
        - rf.get .x10).toNat = 0 := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hc : inRw (rf.get .x10) (dwordBytes p)
        (rf.get .x10 + signExtend12 0) 8 := by
      unfold inRw
      rw [h0, length_dwordBytes]
    simp only [blockVCs, loadSem, Region.loadOk, length_dwordBytes,
      if_pos hc, h0]
    and_intros <;> trivial
  case treeInsert.enter =>
    rintro rf ws A ⟨rf₁, A₀, win, rest, -,
      ⟨rf₀, ws₀, -, ⟨hx10, hx11, hx14, hA⟩, rfl, rfl⟩, -, ⟨p, rfl, rfl⟩,
      rfl, rfl⟩ hApc hsat
    rw [treeIns_li_engine] at hsat ⊢
    obtain ⟨hld1, hld2⟩ := treeIns_load_engine
      ((treeInsertFn s0 x q junk t0).region) (rf₀.set .x15 0) p
    rw [hld2] at hsat
    rw [hld1, hld2]
    have hx10₁ : (rf₀.set .x15 0).get .x10 = s0 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide), hx10]
    have hx10v : ((rf₀.set .x15 0).set .x12 p).get .x10 = s0 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx10₁
    have hx12v : ((rf₀.set .x15 0).set .x12 p).get .x12 = p :=
      RegFile.get_set_self _ _ _ (by decide)
    obtain ⟨hp0, hhp0⟩ := hsat
    obtain ⟨_, hs1⟩ := sepConj_sat_right hhp0
    obtain ⟨_, hs2⟩ := sepConj_sat_right hs1
    obtain ⟨_, hs3⟩ := sepConj_sat_right hs2
    have hshadow := treeAtS_sat_shadow hs3
    refine ⟨_, ⟨rfl, ?_⟩, ?_, ?_⟩
    · rw [hx12v]
      exact hshadow
    · intro hq hh
      rw [hx10₁] at hh
      rw [hx10v, hx12v,
        show ctxS Tree.Ctx.top s0 s0 = ⌜s0 = s0⌝ from rfl,
        pure_true_eq_emp rfl, sepConj_emp_left',
        show slotCell s0 p
          = (⌜RwRegion.wf ⟨s0, 8⟩⌝ ** bytesRegion s0 (dwordBytes p)) from rfl]
      xperm_hyp hh
    · exact pcFree_sepConj (pcFree_junkAt _ _)
        (pcFree_sepConj (pcFree_ctxS _ _ _)
          (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _)))
  case treeInsert.walk.inv_init =>
    rintro rf ws A ⟨A₁, ⟨rf₁, A₀, win, rest, -,
      ⟨rf₀, ws₀, -, ⟨hx10, hx11, hx14, hA⟩, rfl, rfl⟩, -, ⟨p, rfl, rfl⟩,
      rfl, rfl⟩, -, rfl, hshadow⟩
    rw [treeIns_li_engine] at hshadow ⊢
    obtain ⟨hld1, -⟩ := treeIns_load_engine
      ((treeInsertFn s0 x q junk t0).region) (rf₀.set .x15 0) p
    rw [hld1] at hshadow ⊢
    refine ⟨.top, t0, rfl, rfl, hmem, hshadow, ?_, by omega, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      decide
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide), hx14]
  case treeInsert.walk.body.node.focus =>
    rintro rf ws A ⟨i, hi, ⟨c, t', hAeq, hzip, hkeys, hshadow, hx15, hd,
      hx11, hx14⟩, hcond⟩ hApc hp hhp
    have hne : rf.get .x12 ≠ 0 := by
      simp only [Cond.holds, ne_eq] at hcond
      simpa using hcond
    obtain ⟨k, l, r, rfl⟩ : ∃ k l r, t' = Tree.node k l r := by
      cases t' with
      | leaf => exact absurd (hshadow.mpr rfl) hne
      | node k l r => exact ⟨k, l, r, rfl⟩
    rw [hAeq] at hhp
    obtain ⟨h1, h2, hd12, hu12, hjunk, h3, h4, hd34, hu34, hctx,
      h5, h6, hd56, hu56, hslot, htree⟩ := hhp
    obtain ⟨pl, pr, htree'⟩ := htree
    have hwf8 : RwRegion.wf ⟨rf.get .x12, 8⟩ :=
      (treeAtS_sat_node (⟨pl, pr, htree'⟩ :
        treeAtS (rf.get .x12) (.node k l r) h6)).2
    have hti : (rf.get .x15).toNat = i := by
      rw [hx15, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨dwordBytes k, _, ⟨c, k, l, r, pl, pr, rfl, rfl, hzip, hkeys, ?_⟩,
      ?_, ?_, ?_⟩
    · rw [hti]
      exact hd
    · have hall : ((junkAt q junk) ** ((ctxS c s0 (rf.get .x10)) **
          ((slotCell (rf.get .x10) (rf.get .x12)) **
            ((⌜RwRegion.wf ⟨rf.get .x12, 8⟩⌝ **
                bytesRegion (rf.get .x12) (dwordBytes k)) **
              (((slotCell (rf.get .x12 + 8) pl) ** treeAtS pl l) **
               ((slotCell (rf.get .x12 + 16) pr) ** treeAtS pr r)))))) hp :=
        ⟨h1, h2, hd12, hu12, hjunk, h3, h4, hd34, hu34, hctx,
          h5, h6, hd56, hu56, hslot, htree'⟩
      xperm_hyp hall
    · exact pcFree_sepConj pcFree_pure (pcFree_sepConj (pcFree_junkAt _ _)
        (pcFree_sepConj (pcFree_ctxS _ _ _)
          (pcFree_sepConj (pcFree_slotCell _ _)
            (pcFree_sepConj
              (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _))
              (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _))))))
    · rw [length_dwordBytes]
      exact hwf8
  case treeInsert.walk.body.node.mem =>
    rintro rf ws A win rest - - ⟨c, k, l, r, pl, pr, rfl, rfl, -, -, -⟩ -
    have h0 : ((rf.get .x12 + signExtend12 (0 : BitVec 12))
        - rf.get .x12).toNat = 0 := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hc : inRw (rf.get .x12) (dwordBytes k)
        (rf.get .x12 + signExtend12 0) 8 := by
      unfold inRw
      rw [h0, length_dwordBytes]
    simp only [blockVCs, loadSem, storeSem, Region.loadOk,
      length_dwordBytes, if_pos hc, h0]
    and_intros <;> trivial
  case treeInsert.walk.body.cmp.t.stepL =>
    rintro rf ws A ⟨rf₂, ws₂, -, ⟨⟨rf₀, A₀, win, rest, -,
      ⟨i, hi, ⟨c₀, t₀', hAeq₀, hzip₀, hkeys₀, hshadow₀, hx15₀, hd₀,
        hx11₀, hx14₀⟩, hcond⟩, -,
      ⟨c, k, l, r, pl, pr, rfl, rfl, hzip, hkeys, hdp⟩, rfl, rfl⟩,
      hcmp⟩, rfl, rfl⟩ hApc hsat
    obtain ⟨hn1, hn2⟩ := treeIns_node_engine
      ((treeInsertFn s0 x q junk t0).region) rf₀ k
    rw [hn1] at hcmp ⊢
    rw [hn2, treeIns_addi_engine]
    have hx12₂ : ((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).get .x12
        = rf₀.get .x12 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
    have hx10v : (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).set .x10
        (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).get .x12
          + signExtend12 8)).get .x10 = rf₀.get .x12 + 8 := by
      rw [RegFile.get_set_self _ _ _ (by decide), hx12₂,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
    have hx15v : (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).set .x10
        (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).get .x12
          + signExtend12 8)).get .x15 = rf₀.get .x15 + 1 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    simp only [Cond.holds] at hcmp
    rw [RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide), hx11₀,
      RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide)] at hcmp
    have hti : (rf₀.get .x15 + 1).toNat = i + 1 := by
      rw [hx15₀]
      have h1 : i + 1 < 2 ^ 64 := by omega
      bv_omega
    refine ⟨_, ⟨Tree.Ctx.left k r c, l, rfl, ?_, not_mem_keys_left hkeys, ?_⟩,
      ?_, ?_⟩
    · show Tree.Ctx.zip (.left k r c) (l.insert x) = t0.insert x
      rw [show Tree.Ctx.zip (.left k r c) (l.insert x)
          = c.zip (.node k (l.insert x) r) from rfl, ← insert_go_left hcmp]
      exact hzip
    · rw [hx15v, hti]
      have hti₀ : (rf₀.get .x15).toNat = i := by
        rw [hx15₀, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hti₀] at hdp
      have hle := Nat.le_max_left l.depth r.depth
      simp only [Tree.depth] at hdp
      omega
    · intro hq hh
      have hshaped : ((junkAt q junk) **
          ((ctxS c s0 (rf₀.get .x10)) **
            ((slotCell (rf₀.get .x10) (rf₀.get .x12)) **
              ((keyCell (rf₀.get .x12) k) **
                (((slotCell (rf₀.get .x12 + 8) pl) ** treeAtS pl l) **
                 ((slotCell (rf₀.get .x12 + 16) pr) ** treeAtS pr r)))))) hq := by
        rw [show keyCell (rf₀.get .x12) k
            = (⌜RwRegion.wf ⟨rf₀.get .x12, 8⟩⌝ **
                bytesRegion (rf₀.get .x12) (dwordBytes k)) from rfl]
        xperm_hyp hh
      rw [hx10v]
      exact sepConj_mono_right (fun hv hy =>
        ctxS_push_left c s0 (rf₀.get .x10) (rf₀.get .x12) k l r hv
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (fun _ h1 => ⟨pl, h1⟩) (fun _ h2 => ⟨pr, h2⟩))))
            hv hy)) hq hshaped
    · exact pcFree_sepConj (pcFree_junkAt _ _)
        (pcFree_sepConj (pcFree_ctxS _ _ _) (pcFree_treeFrom _ _))
  case treeInsert.walk.body.cmp.e.stepR =>
    rintro rf ws A ⟨rf₂, ws₂, -, ⟨⟨rf₀, A₀, win, rest, -,
      ⟨i, hi, ⟨c₀, t₀', hAeq₀, hzip₀, hkeys₀, hshadow₀, hx15₀, hd₀,
        hx11₀, hx14₀⟩, hcond⟩, -,
      ⟨c, k, l, r, pl, pr, rfl, rfl, hzip, hkeys, hdp⟩, rfl, rfl⟩,
      hcmp⟩, rfl, rfl⟩ hApc hsat
    obtain ⟨hn1, hn2⟩ := treeIns_node_engine
      ((treeInsertFn s0 x q junk t0).region) rf₀ k
    rw [hn1] at hcmp ⊢
    rw [hn2, treeIns_addi_engine]
    have hx12₂ : ((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).get .x12
        = rf₀.get .x12 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
    have hx10v : (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).set .x10
        (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).get .x12
          + signExtend12 16)).get .x10 = rf₀.get .x12 + 16 := by
      rw [RegFile.get_set_self _ _ _ (by decide), hx12₂,
        show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
    have hx15v : (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).set .x10
        (((rf₀.set .x13 k).set .x15 (rf₀.get .x15 + 1)).get .x12
          + signExtend12 16)).get .x15 = rf₀.get .x15 + 1 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    simp only [Cond.holds] at hcmp
    rw [RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide), hx11₀,
      RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide)] at hcmp
    have hti : (rf₀.get .x15 + 1).toNat = i + 1 := by
      rw [hx15₀]
      have h1 : i + 1 < 2 ^ 64 := by omega
      bv_omega
    refine ⟨_, ⟨Tree.Ctx.right k l c, r, rfl, ?_, not_mem_keys_right hkeys, ?_⟩,
      ?_, ?_⟩
    · show Tree.Ctx.zip (.right k l c) (r.insert x) = t0.insert x
      rw [show Tree.Ctx.zip (.right k l c) (r.insert x)
          = c.zip (.node k l (r.insert x)) from rfl,
        ← insert_go_right hcmp (ne_key_of_not_mem hkeys)]
      exact hzip
    · rw [hx15v, hti]
      have hti₀ : (rf₀.get .x15).toNat = i := by
        rw [hx15₀, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hti₀] at hdp
      have hle := Nat.le_max_right l.depth r.depth
      simp only [Tree.depth] at hdp
      omega
    · intro hq hh
      have hshaped : ((junkAt q junk) **
          ((ctxS c s0 (rf₀.get .x10)) **
            ((slotCell (rf₀.get .x10) (rf₀.get .x12)) **
              ((keyCell (rf₀.get .x12) k) **
                (((slotCell (rf₀.get .x12 + 8) pl) ** treeAtS pl l) **
                 ((slotCell (rf₀.get .x12 + 16) pr) ** treeAtS pr r)))))) hq := by
        rw [show keyCell (rf₀.get .x12) k
            = (⌜RwRegion.wf ⟨rf₀.get .x12, 8⟩⌝ **
                bytesRegion (rf₀.get .x12) (dwordBytes k)) from rfl]
        xperm_hyp hh
      rw [hx10v]
      exact sepConj_mono_right (fun hv hy =>
        ctxS_push_right c s0 (rf₀.get .x10) (rf₀.get .x12) k l r hv
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (fun _ h1 => ⟨pl, h1⟩) (fun _ h2 => ⟨pr, h2⟩))))
            hv hy)) hq hshaped
    · exact pcFree_sepConj (pcFree_junkAt _ _)
        (pcFree_sepConj (pcFree_ctxS _ _ _) (pcFree_treeFrom _ _))
  case treeInsert.walk.body.load.focus =>
    rintro rf ws A (⟨A₀, -, -, ⟨c', t', rfl, hzip, hkeys, hdp⟩⟩ |
      ⟨A₀, -, -, ⟨c', t', rfl, hzip, hkeys, hdp⟩⟩) hApc hp hhp <;>
    · obtain ⟨h1, h2, hd12, hu12, hjunk, h3, h4, hd34, hu34, hctx,
        p', h5, h6, hd56, hu56, hslot, htree⟩ := hhp
      have hwf := slotCell_wf hslot
      refine ⟨dwordBytes p', _, ⟨c', p', t', rfl, rfl, hzip, hkeys, hdp⟩,
        ?_, ?_, ?_⟩
      · have hall : ((junkAt q junk) ** ((ctxS c' s0 (rf.get .x10)) **
            ((⌜RwRegion.wf ⟨rf.get .x10, 8⟩⌝ **
              bytesRegion (rf.get .x10) (dwordBytes p')) ** treeAtS p' t'))) hp :=
          ⟨h1, h2, hd12, hu12, hjunk, h3, h4, hd34, hu34, hctx,
            h5, h6, hd56, hu56, hslot, htree⟩
        xperm_hyp hall
      · exact pcFree_sepConj pcFree_pure (pcFree_sepConj (pcFree_junkAt _ _)
          (pcFree_sepConj (pcFree_ctxS _ _ _) (pcFree_treeAtS _ _)))
      · rw [length_dwordBytes]
        exact hwf
  case treeInsert.walk.body.load.mem =>
    rintro rf ws A win rest - - ⟨c', p', t', rfl, rfl, -, -, -⟩ -
    have h0 : ((rf.get .x10 + signExtend12 (0 : BitVec 12))
        - rf.get .x10).toNat = 0 := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hc : inRw (rf.get .x10) (dwordBytes p')
        (rf.get .x10 + signExtend12 0) 8 := by
      unfold inRw
      rw [h0, length_dwordBytes]
    simp only [blockVCs, loadSem, Region.loadOk, length_dwordBytes,
      if_pos hc, h0]
    and_intros <;> trivial
  case treeInsert.walk.body.step =>
    rintro rf ws A ⟨rf₃, A₀, win, rest, -, -, -,
      ⟨c', p', t', rfl, rfl, hzip, hkeys, hdp⟩, rfl, rfl⟩ hApc hsat
    obtain ⟨hld1, hld2⟩ := treeIns_load_engine
      ((treeInsertFn s0 x q junk t0).region) rf₃ p'
    rw [hld1, hld2]
    have hx10v : (rf₃.set .x12 p').get .x10 = rf₃.get .x10 :=
      RegFile.get_set_ne _ _ _ _ (by decide)
    have hx12v : (rf₃.set .x12 p').get .x12 = p' :=
      RegFile.get_set_self _ _ _ (by decide)
    have hx15v : (rf₃.set .x12 p').get .x15 = rf₃.get .x15 :=
      RegFile.get_set_ne _ _ _ _ (by decide)
    obtain ⟨hp0, hhp0⟩ := hsat
    obtain ⟨_, hs1⟩ := sepConj_sat_right hhp0
    obtain ⟨_, hs2⟩ := sepConj_sat_right hs1
    obtain ⟨_, hs3⟩ := sepConj_sat_right hs2
    obtain ⟨_, hs4⟩ := sepConj_sat_right hs3
    have hshadow := treeAtS_sat_shadow hs4
    refine ⟨_, ⟨c', t', rfl, hzip, hkeys, ?_, ?_⟩, ?_, ?_⟩
    · rw [hx12v]
      exact hshadow
    · rw [hx15v]
      exact hdp
    · intro hq hh
      rw [hx10v, hx12v,
        show slotCell (rf₃.get .x10) p'
          = (⌜RwRegion.wf ⟨rf₃.get .x10, 8⟩⌝ **
            bytesRegion (rf₃.get .x10) (dwordBytes p')) from rfl]
      xperm_hyp hh
    · exact pcFree_sepConj (pcFree_junkAt _ _)
        (pcFree_sepConj (pcFree_ctxS _ _ _)
          (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _)))
  case treeInsert.walk.inv_step =>
    rintro i hi rf ws A ⟨A₁, ⟨rf₃, A₀, win, rest, -, hite, -,
      ⟨c₃, p₃, t₃, rfl, -, -, -, -⟩, rfl, rfl⟩, -,
      ⟨c'', t'', rfl, hzip'', hkeys'', hshadow'', hdp''⟩⟩
    rcases hite with ⟨A₂, ⟨rf₂, ws₂, -, ⟨⟨rf₀, A₃, win₃, rest₃, -,
        ⟨⟨c₀, t₀', -, -, -, -, hx15₀, -, hx11₀, hx14₀⟩, -⟩, -,
        ⟨ck, kk, ll, rr, pll, prr, rfl, -, -, -, -⟩, rfl, rfl⟩, -⟩,
        rfl, rfl⟩, -, -⟩ |
      ⟨A₂, ⟨rf₂, ws₂, -, ⟨⟨rf₀, A₃, win₃, rest₃, -,
        ⟨⟨c₀, t₀', -, -, -, -, hx15₀, -, hx11₀, hx14₀⟩, -⟩, -,
        ⟨ck, kk, ll, rr, pll, prr, rfl, -, -, -, -⟩, rfl, rfl⟩, -⟩,
        rfl, rfl⟩, -, -⟩ <;>
    · obtain ⟨hn1, -⟩ := treeIns_node_engine
        ((treeInsertFn s0 x q junk t0).region) rf₀ kk
      refine ⟨c'', t'', rfl, hzip'', hkeys'', hshadow'', ?_, ?_, ?_, ?_⟩
      · rw [(treeIns_load_engine _ _ p₃).1,
          RegFile.get_set_ne _ _ _ _ (by decide), treeIns_addi_engine,
          RegFile.get_set_ne _ _ _ _ (by decide), hn1,
          RegFile.get_set_self _ _ _ (by decide), hx15₀,
          show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
      · rw [(treeIns_load_engine _ _ p₃).1,
          RegFile.get_set_ne _ _ _ _ (by decide), treeIns_addi_engine,
          RegFile.get_set_ne _ _ _ _ (by decide), hn1,
          RegFile.get_set_self _ _ _ (by decide), hx15₀] at hdp''
        have h1 : i + 1 < 2 ^ 64 := by omega
        have hti : ((BitVec.ofNat 64 i : Word) + 1).toNat = i + 1 := by
          bv_omega
        rw [hti] at hdp''
        exact hdp''
      · rw [(treeIns_load_engine _ _ p₃).1,
          RegFile.get_set_ne _ _ _ _ (by decide), treeIns_addi_engine,
          RegFile.get_set_ne _ _ _ _ (by decide), hn1,
          RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide)]
        exact hx11₀
      · rw [(treeIns_load_engine _ _ p₃).1,
          RegFile.get_set_ne _ _ _ _ (by decide), treeIns_addi_engine,
          RegFile.get_set_ne _ _ _ _ (by decide), hn1,
          RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide)]
        exact hx14₀
  case treeInsert.walk.exhausted =>
    rintro rf ws A ⟨c, t', -, -, -, hshadow, -, hd, -, -⟩
    have ht' : t' = .leaf := by
      cases t' with
      | leaf => rfl
      | node k l r => exact absurd hd (by simp only [Tree.depth]; omega)
    have h0 : rf.get .x12 = 0 := hshadow.mpr ht'
    simp only [Cond.holds]
    rw [h0]
    simp
  case treeInsert.fill.focus =>
    rintro rf ws A ⟨⟨i, -, ⟨c, t', hAeq, hzip, -, hshadow, -, -, hx11, hx14⟩⟩,
      hncond⟩ hApc hp hhp
    have h0 : rf.get .x12 = 0 := by
      simp only [Cond.holds, ne_eq] at hncond
      simpa using hncond
    have ht' : t' = .leaf := hshadow.mp h0
    subst ht'
    rw [hAeq] at hhp
    obtain ⟨h1, h2, hd12, hu12, hjunk, hrest2⟩ := hhp
    have hwf24 : RwRegion.wf ⟨q, 24⟩ := ((sepConj_pure_left h1).mp hjunk).1
    refine ⟨junk, _, ⟨c, rfl, rfl, hzip⟩, ?_, ?_, ?_⟩
    · rw [hx14]
      have hall : ((⌜RwRegion.wf ⟨q, 24⟩⌝ ** bytesRegion q junk) **
          ((ctxS c s0 (rf.get .x10)) **
            ((slotCell (rf.get .x10) (rf.get .x12)) **
              treeAtS (rf.get .x12) Tree.leaf))) hp :=
        ⟨h1, h2, hd12, hu12, hjunk, hrest2⟩
      xperm_hyp hall
    · exact pcFree_sepConj pcFree_pure
        (pcFree_sepConj (pcFree_ctxS _ _ _)
          (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _)))
    · rw [h24, hx14]
      exact hwf24
  case treeInsert.fill.mem =>
    rintro rf ws A win rest - - ⟨c, rfl, rfl, -⟩ -
    have h0 : ((rf.get .x14 + signExtend12 (0 : BitVec 12))
        - rf.get .x14).toNat = 0 := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have h8 : ((rf.get .x14 + signExtend12 (8 : BitVec 12))
        - rf.get .x14).toNat = 8 := by
      rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    have h16 : ((rf.get .x14 + signExtend12 (16 : BitVec 12))
        - rf.get .x14).toNat = 16 := by
      rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
      bv_omega
    simp only [blockVCs, loadSem, aluSem, storeSem, execInstrRF, inRw,
      length_setBytes, h0, h8, h16, h24]
    and_intros <;> trivial
  case treeInsert.mknode =>
    rintro rf ws A ⟨rf₀, A₀, win, rest, -,
      ⟨⟨i, -, ⟨c₀, t₀', -, -, -, hshadow₀, -, -, hx11₀, hx14₀⟩⟩, hncond⟩, -,
      ⟨c, rfl, rfl, hzip⟩, rfl, rfl⟩ hApc hsat
    obtain ⟨-, hf2⟩ := treeIns_fill_engine
      ((treeInsertFn s0 x q win t0).region) rf win h24
    rw [hf2, hx11₀]
    refine ⟨_, ⟨c, rfl, hzip⟩, ?_, ?_⟩
    · intro hq hh
      obtain ⟨h1, h2, hd12, hu12, hbytes, hrest⟩ := hh
      have hwf24 : RwRegion.wf ⟨rf.get .x14, 24⟩ :=
        ((sepConj_pure_left h2).mp hrest).1
      have hrest' := ((sepConj_pure_left h2).mp hrest).2
      obtain ⟨hwfk, hwf8, hwf16⟩ := wf24_split hwf24
      rw [bytesRegion_node_split] at hbytes
      have htree : treeAtS (rf.get .x14) (.node x .leaf .leaf) h1 := by
        refine ⟨0, 0, ?_⟩
        have hcells : ((keyCell (rf.get .x14) x) **
            (((slotCell (rf.get .x14 + 8) (0 : Word)) **
                treeAtS (0 : Word) .leaf) **
             ((slotCell (rf.get .x14 + 16) (0 : Word)) **
                treeAtS (0 : Word) .leaf)))
            = ((bytesRegion (rf.get .x14) (dwordBytes x)) **
              ((bytesRegion (rf.get .x14 + 8) (dwordBytes (0 : Word))) **
                bytesRegion (rf.get .x14 + 16) (dwordBytes (0 : Word)))) := by
          rw [show keyCell (rf.get .x14) x
              = (⌜RwRegion.wf ⟨rf.get .x14, 8⟩⌝ **
                bytesRegion (rf.get .x14) (dwordBytes x)) from rfl,
            show slotCell (rf.get .x14 + 8) (0 : Word)
              = (⌜RwRegion.wf ⟨rf.get .x14 + 8, 8⟩⌝ **
                bytesRegion (rf.get .x14 + 8) (dwordBytes 0)) from rfl,
            show slotCell (rf.get .x14 + 16) (0 : Word)
              = (⌜RwRegion.wf ⟨rf.get .x14 + 16, 8⟩⌝ **
                bytesRegion (rf.get .x14 + 16) (dwordBytes 0)) from rfl,
            show treeAtS (0 : Word) Tree.leaf = ⌜(0 : Word) = 0⌝ from rfl,
            pure_true_eq_emp hwfk, pure_true_eq_emp hwf8,
            pure_true_eq_emp hwf16, pure_true_eq_emp rfl,
            sepConj_emp_left', sepConj_emp_left', sepConj_emp_left',
            sepConj_emp_right', sepConj_emp_right']
        rw [hcells]
        exact hbytes
      have hrest'' : ((ctxS c s0 (rf.get .x10)) **
          slotCell (rf.get .x10) (rf.get .x12)) h2 :=
        sepConj_mono_right (fun hv hy =>
          ((sepConj_pure_right hv).mp hy).1) h2 hrest'
      have hall : ((treeAtS (rf.get .x14) (Tree.node x Tree.leaf Tree.leaf)) **
          ((ctxS c s0 (rf.get .x10)) **
            slotCell (rf.get .x10) (rf.get .x12))) hq :=
        ⟨h1, h2, hd12, hu12, htree, hrest''⟩
      xperm_hyp hall
    · exact pcFree_sepConj (pcFree_ctxS _ _ _)
        (pcFree_sepConj (pcFree_slotCell _ _) (pcFree_treeAtS _ _))
  case treeInsert.store.focus =>
    rintro rf ws A ⟨A₀, -, -, ⟨c, rfl, hzip⟩⟩ hApc hp hhp
    obtain ⟨h1, h2, hd12, hu12, hctx, h3, h4, hd34, hu34, hslot, htree⟩ := hhp
    have hwf := slotCell_wf hslot
    refine ⟨dwordBytes (rf.get .x12), _, ⟨c, rfl, rfl, hzip⟩, ?_, ?_, ?_⟩
    · have hall : ((ctxS c s0 (rf.get .x10)) **
          ((⌜RwRegion.wf ⟨rf.get .x10, 8⟩⌝ **
            bytesRegion (rf.get .x10) (dwordBytes (rf.get .x12))) **
            treeAtS (rf.get .x14) (Tree.node x Tree.leaf Tree.leaf))) hp :=
        ⟨h1, h2, hd12, hu12, hctx, h3, h4, hd34, hu34, hslot, htree⟩
      xperm_hyp hall
    · exact pcFree_sepConj pcFree_pure
        (pcFree_sepConj (pcFree_ctxS _ _ _) (pcFree_treeAtS _ _))
    · rw [length_dwordBytes]
      exact hwf
  case treeInsert.store.mem =>
    rintro rf ws A win rest - - ⟨c, rfl, rfl, -⟩ -
    have h0 : ((rf.get .x10 + signExtend12 (0 : BitVec 12))
        - rf.get .x10).toNat = 0 := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    simp only [blockVCs, loadSem, storeSem, inRw, length_dwordBytes, h0]
    and_intros <;> trivial
  case treeInsert.fold =>
    rintro rf ws A ⟨rf₀, A₀, win, rest, -, ⟨A₁, -, -, ⟨c, rfl, hzip⟩⟩, -,
      ⟨c₂, hwin, rfl, hzip₂⟩, rfl, rfl⟩ hApc hsat
    subst hwin
    obtain ⟨-, hs2⟩ := treeIns_store_engine
      ((treeInsertFn s0 x q junk t0).region) rf (rf.get .x12)
    rw [hs2]
    refine ⟨treeFrom s0 (t0.insert x), rfl, ?_, pcFree_treeFrom _ _⟩
    intro hq hh
    have hshaped : ((ctxS c₂ s0 (rf.get .x10)) **
        ((slotCell (rf.get .x10) (rf.get .x14)) **
          treeAtS (rf.get .x14) (Tree.node x Tree.leaf Tree.leaf))) hq := by
      rw [show slotCell (rf.get .x10) (rf.get .x14)
          = (⌜RwRegion.wf ⟨rf.get .x10, 8⟩⌝ **
            bytesRegion (rf.get .x10) (dwordBytes (rf.get .x14))) from rfl]
      xperm_hyp hh
    have hfolded := ctxS_zip_fold c₂ s0 (rf.get .x10) (rf.get .x14)
      (.node x .leaf .leaf) hq hshaped
    rw [show Tree.Ctx.zip c₂ (Tree.node x Tree.leaf Tree.leaf)
        = c₂.zip (Tree.leaf.insert x) from rfl, hzip₂] at hfolded
    exact hfolded
  case treeInsert.post =>
    rintro rf ws A ⟨A₀, -, -, rfl⟩
    rfl

end SAsm
end EvmAsm.Rv64
