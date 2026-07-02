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

end SAsm
end EvmAsm.Rv64
