/-
  EvmAsm.Rv64.SAsm.TreeSep

  A binary search tree as a recursive separation-logic predicate over the
  SAsm ambient assertion (docs/sasm-design.md; Assertion-state milestone,
  stage 4).

  Layout: a node is 3 consecutive dwords at a dword-aligned, nonzero
  address `p` — key at `p`, left-child pointer at `p+8`, right-child
  pointer at `p+16`; the nil pointer is `0`.  `treeAt p t` bakes the
  machine-level well-formedness (`RwRegion.wf ⟨p, 24⟩`) into every node so
  focus blocks (`.blockAt`) can open nodes without extra side conditions.

  The zipper (`TreeCtx`/`ctxAt`) is the loop-invariant shape for iterative
  tree walks: `ctxAt c root p ** treeAt p t` — a tree-with-hole rooted at
  `root` whose hole is the current subtree at `p` — folds back to
  `treeAt root (c.zip t)` (`ctxAt_zip_fold`).

  The pure model (`Tree.insert`, `Tree.Sorted`, `insert_sorted`) is what
  demo specs relate the memory shape to.
-/

import EvmAsm.Rv64.SAsm.AssertionSpec

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- The pure model
-- ============================================================================

/-- A binary tree of 64-bit keys. -/
inductive Tree where
  | leaf
  | node (k : Word) (l r : Tree)
deriving Repr

namespace Tree

/-- The keys of a tree. -/
def keys : Tree → List Word
  | .leaf => []
  | .node k l r => k :: (l.keys ++ r.keys)

/-- BST insertion by unsigned comparison (idempotent on duplicates). -/
def insert (x : Word) : Tree → Tree
  | .leaf => .node x .leaf .leaf
  | .node k l r =>
      if BitVec.ult x k then .node k (insert x l) r
      else if BitVec.ult k x then .node k l (insert x r)
      else .node k l r

/-- The BST invariant (strict, by unsigned comparison). -/
def Sorted : Tree → Prop
  | .leaf => True
  | .node k l r => Sorted l ∧ Sorted r
      ∧ (∀ k' ∈ l.keys, BitVec.ult k' k) ∧ (∀ k' ∈ r.keys, BitVec.ult k k')

theorem mem_keys_insert {x k' : Word} {t : Tree}
    (h : k' ∈ (t.insert x).keys) : k' = x ∨ k' ∈ t.keys := by
  induction t with
  | leaf =>
      simp only [insert, keys, List.mem_cons, List.append_nil] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact absurd h (List.not_mem_nil)
  | node k l r ihl ihr =>
      simp only [insert] at h
      by_cases hxk : BitVec.ult x k
      · rw [if_pos hxk] at h
        simp only [keys, List.mem_cons, List.mem_append] at h ⊢
        rcases h with rfl | h | h
        · exact Or.inr (Or.inl rfl)
        · rcases ihl h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rw [if_neg hxk] at h
        by_cases hkx : BitVec.ult k x
        · rw [if_pos hkx] at h
          simp only [keys, List.mem_cons, List.mem_append] at h ⊢
          rcases h with rfl | h | h
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl h))
          · rcases ihr h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inr h))
        · rw [if_neg hkx] at h
          exact Or.inr h

/-- Insertion preserves the BST invariant. -/
theorem insert_sorted {x : Word} {t : Tree} (h : t.Sorted) :
    (t.insert x).Sorted := by
  induction t with
  | leaf =>
      exact ⟨trivial, trivial,
        fun k' hk' => absurd hk' (List.not_mem_nil),
        fun k' hk' => absurd hk' (List.not_mem_nil)⟩
  | node k l r ihl ihr =>
      obtain ⟨hl, hr, hlt, hgt⟩ := h
      simp only [insert]
      by_cases hxk : BitVec.ult x k
      · rw [if_pos hxk]
        refine ⟨ihl hl, hr, ?_, hgt⟩
        intro k' hk'
        rcases mem_keys_insert hk' with rfl | hk'
        · exact hxk
        · exact hlt k' hk'
      · rw [if_neg hxk]
        by_cases hkx : BitVec.ult k x
        · rw [if_pos hkx]
          refine ⟨hl, ihr hr, hlt, ?_⟩
          intro k' hk'
          rcases mem_keys_insert hk' with rfl | hk'
          · exact hkx
          · exact hgt k' hk'
        · rw [if_neg hkx]
          exact ⟨hl, hr, hlt, hgt⟩

/-- A zipper context: a tree with a hole, innermost frame first. -/
inductive Ctx where
  | top
  | left  (k : Word) (r : Tree) (parent : Ctx)
  | right (k : Word) (l : Tree) (parent : Ctx)

/-- Plug a subtree into the hole. -/
def Ctx.zip : Ctx → Tree → Tree
  | .top, t => t
  | .left k r c, t => c.zip (.node k t r)
  | .right k l c, t => c.zip (.node k l t)

end Tree

-- ============================================================================
-- The memory shape
-- ============================================================================

/-- The 24 bytes of a node: key, left pointer, right pointer (little-endian
    dwords). -/
def nodeBytes (k pl pr : Word) : List (BitVec 8) :=
  dwordBytes k ++ (dwordBytes pl ++ dwordBytes pr)

@[simp] theorem length_nodeBytes (k pl pr : Word) :
    (nodeBytes k pl pr).length = 24 := by
  simp [nodeBytes]

/-- One tree node at `p`: nonzero dword-aligned valid address, 24 bytes. -/
def nodeAt (p k pl pr : Word) : Assertion :=
  ⌜p ≠ 0 ∧ RwRegion.wf ⟨p, 24⟩⌝ ** bytesRegion p (nodeBytes k pl pr)

theorem pcFree_nodeAt (p k pl pr : Word) : (nodeAt p k pl pr).pcFree :=
  pcFree_sepConj pcFree_pure (bytesRegion_pcFree _ _)

/-- The tree `t` laid out in memory at `p` (`p = 0` iff `t` is a leaf). -/
def treeAt : Word → Tree → Assertion
  | p, .leaf => ⌜p = 0⌝
  | p, .node k l r => fun h => ∃ pl pr,
      ((nodeAt p k pl pr) ** (treeAt pl l ** treeAt pr r)) h

theorem pcFree_treeAt (p : Word) (t : Tree) : (treeAt p t).pcFree := by
  induction t generalizing p with
  | leaf => exact pcFree_pure
  | node k l r ihl ihr =>
      intro h hp
      obtain ⟨pl, pr, hh⟩ := hp
      exact pcFree_sepConj (pcFree_nodeAt _ _ _ _)
        (pcFree_sepConj (ihl pl) (ihr pr)) h hh

/-- Unfolding a node (for `.ghost`/`.focus` reasoning). -/
theorem treeAt_node (p k : Word) (l r : Tree) :
    treeAt p (.node k l r)
      = fun h => ∃ pl pr,
          ((nodeAt p k pl pr) ** (treeAt pl l ** treeAt pr r)) h := rfl

/-- Folding a node from its pieces. -/
theorem treeAt_fold (p k pl pr : Word) (l r : Tree) :
    ∀ hp, ((nodeAt p k pl pr) ** (treeAt pl l ** treeAt pr r)) hp →
      treeAt p (.node k l r) hp :=
  fun _ hh => ⟨pl, pr, hh⟩

/-- A leaf is the nil pointer. -/
theorem treeAt_leaf_iff (p : Word) : ∀ hp, treeAt p .leaf hp ↔ ⌜p = 0⌝ hp :=
  fun _ => Iff.rfl

/-- The tree-with-hole: the path context `c` laid out in memory, rooted at
    `root`, with the hole at `hole` (the address the innermost frame's
    child pointer stores). -/
def ctxAt : Tree.Ctx → Word → Word → Assertion
  | .top, root, hole => ⌜root = hole⌝
  | .left k r c, root, hole => fun h => ∃ pn pr,
      ((ctxAt c root pn) ** ((nodeAt pn k hole pr) ** (treeAt pr r))) h
  | .right k l c, root, hole => fun h => ∃ pn pl,
      ((ctxAt c root pn) ** ((nodeAt pn k pl hole) ** (treeAt pl l))) h

theorem pcFree_ctxAt (c : Tree.Ctx) (root hole : Word) :
    (ctxAt c root hole).pcFree := by
  induction c generalizing hole with
  | top => exact pcFree_pure
  | left k r c ih =>
      intro h hp
      obtain ⟨pn, pr, hh⟩ := hp
      exact pcFree_sepConj (ih pn)
        (pcFree_sepConj (pcFree_nodeAt _ _ _ _) (pcFree_treeAt _ _)) h hh
  | right k l c ih =>
      intro h hp
      obtain ⟨pn, pl, hh⟩ := hp
      exact pcFree_sepConj (ih pn)
        (pcFree_sepConj (pcFree_nodeAt _ _ _ _) (pcFree_treeAt _ _)) h hh

/-- **The zipper fold**: a context plus the subtree in its hole is the
    plugged tree.  This is what reseals `treeAt root (c.zip t)` at the end
    of an iterative walk. -/
theorem ctxAt_zip_fold (c : Tree.Ctx) (root : Word) :
    ∀ (p : Word) (t : Tree) hp,
      ((ctxAt c root p) ** treeAt p t) hp → treeAt root (c.zip t) hp := by
  induction c with
  | top =>
      intro p t hp hh
      obtain ⟨hroot, ht⟩ := (sepConj_pure_left hp).mp hh
      subst hroot
      exact ht
  | left k r c ih =>
      rintro p t hp ⟨h1, h2, hd, hu, ⟨pn, pr, hctx⟩, ht⟩
      have hh' : (((ctxAt c root pn) ** ((nodeAt pn k p pr) ** treeAt pr r))
          ** treeAt p t) hp := ⟨h1, h2, hd, hu, hctx, ht⟩
      rw [sepConj_assoc', sepConj_assoc',
        sepConj_comm' (treeAt pr r) (treeAt p t)] at hh'
      exact ih pn (.node k t r) hp
        (sepConj_mono_right (fun hq hx => ⟨p, pr, hx⟩) hp hh')
  | right k l c ih =>
      rintro p t hp ⟨h1, h2, hd, hu, ⟨pn, pl, hctx⟩, ht⟩
      have hh' : (((ctxAt c root pn) ** ((nodeAt pn k pl p) ** treeAt pl l))
          ** treeAt p t) hp := ⟨h1, h2, hd, hu, hctx, ht⟩
      rw [sepConj_assoc', sepConj_assoc'] at hh'
      exact ih pn (.node k l t) hp
        (sepConj_mono_right (fun hq hx => ⟨pl, p, hx⟩) hp hh')

/-- Descend left: open the node at the hole and push a zipper frame. -/
theorem ctxAt_push_left (c : Tree.Ctx) (root p k pl pr : Word) (l r : Tree) :
    ∀ hp, ((ctxAt c root p) **
        ((nodeAt p k pl pr) ** (treeAt pl l ** treeAt pr r))) hp →
      ((ctxAt (.left k r c) root pl) ** treeAt pl l) hp := by
  intro hp hh
  rw [show ctxAt (.left k r c) root pl
      = fun h => ∃ pn pr', ((ctxAt c root pn)
          ** ((nodeAt pn k pl pr') ** (treeAt pr' r))) h from rfl]
  -- reassociate: (C ** (N ** (L ** R))) → ((C ** (N ** R)) ** L)
  rw [sepConj_left_comm (nodeAt p k pl pr) (treeAt pl l) (treeAt pr r),
    sepConj_left_comm (ctxAt c root p) (treeAt pl l)] at hh
  -- hh : (L ** (C ** (N ** R)))
  rw [sepConj_comm'] at hh
  -- hh : ((C ** (N ** R)) ** L)
  exact sepConj_mono_left (fun hq hx => ⟨p, pr, hx⟩) hp hh

/-- Descend right: open the node at the hole and push a zipper frame. -/
theorem ctxAt_push_right (c : Tree.Ctx) (root p k pl pr : Word) (l r : Tree) :
    ∀ hp, ((ctxAt c root p) **
        ((nodeAt p k pl pr) ** (treeAt pl l ** treeAt pr r))) hp →
      ((ctxAt (.right k l c) root pr) ** treeAt pr r) hp := by
  intro hp hh
  rw [show ctxAt (.right k l c) root pr
      = fun h => ∃ pn pl', ((ctxAt c root pn)
          ** ((nodeAt pn k pl' pr) ** (treeAt pl' l))) h from rfl]
  -- reassociate: (C ** (N ** (L ** R))) → ((C ** (N ** L)) ** R)
  rw [sepConj_comm' (treeAt pl l) (treeAt pr r),
    sepConj_left_comm (nodeAt p k pl pr) (treeAt pr r) (treeAt pl l),
    sepConj_left_comm (ctxAt c root p) (treeAt pr r)] at hh
  -- hh : (R ** (C ** (N ** L)))
  rw [sepConj_comm'] at hh
  exact sepConj_mono_left (fun hq hx => ⟨p, pl, hx⟩) hp hh

-- ============================================================================
-- Satisfiability shadows (what harvest steps extract)
-- ============================================================================

/-- Satisfiability of a conjunct, from satisfiability of the whole. -/
theorem sepConj_sat_left {A B : Assertion} {hp : PartialState}
    (h : (A ** B) hp) : ∃ hq, A hq := by
  obtain ⟨h1, h2, -, -, ha, -⟩ := h
  exact ⟨h1, ha⟩

/-- Satisfiability of a conjunct, from satisfiability of the whole. -/
theorem sepConj_sat_right {A B : Assertion} {hp : PartialState}
    (h : (A ** B) hp) : ∃ hq, B hq := by
  obtain ⟨h1, h2, -, -, -, hb⟩ := h
  exact ⟨h2, hb⟩

/-- On a satisfying state, a node's address is nonzero and well-formed —
    what a `.focus` VC extracts before opening the node. -/
theorem treeAt_sat_node {p k : Word} {l r : Tree} {hp : PartialState}
    (h : treeAt p (.node k l r) hp) :
    p ≠ 0 ∧ RwRegion.wf ⟨p, 24⟩ := by
  obtain ⟨pl, pr, hh⟩ := h
  obtain ⟨h1, h2, hd, hu, hnode, hch⟩ := hh
  exact ((sepConj_pure_left h1).mp hnode).1

/-- The nil-pointer shadow: on any satisfying state, the pointer is nil
    exactly when the tree is a leaf.  This is the pure fact tree walks
    harvest at ghost steps for their loop-exit reasoning. -/
theorem treeAt_sat_shadow {p : Word} {t : Tree} {hp : PartialState}
    (h : treeAt p t hp) : p = 0 ↔ t = .leaf := by
  cases t with
  | leaf => exact ⟨fun _ => rfl, fun _ => h.2⟩
  | node k l r =>
      have hne := (treeAt_sat_node h).1
      exact ⟨fun h0 => absurd h0 hne, fun hleaf => nomatch hleaf⟩

end SAsm
end EvmAsm.Rv64
