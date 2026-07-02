/-
  EvmAsm.Rv64.SAsm.TreeDemo

  The tree-walk integration demo (Assertion-state milestone, stage 5):
  `treeMinFn` walks a `treeAt`-owned binary tree to its leftmost key,
  exercising every mechanism at once — a `while` loop whose invariant
  carries existentially-quantified zipper ghosts, focus blocks opening
  nodes at a register-held pointer, ghost descend steps
  (`ctxAt_push_left`), the satisfiability harvest (nil-pointer shadows),
  and the post-loop reseal (`ctxAt_zip_fold`).

  The loop-index bridge: annotation relations (`winR`, ghost `R`) cannot
  mention the loop index `i`, so the code maintains a counter register
  (`t2 := i`) and the invariant ties it (`rf.get .x13 = ofNat i`) —
  registers are the shared channel between reach-level and
  annotation-level facts.
-/

import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.TreeSep
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm

open Stmt

-- ============================================================================
-- Pure helpers
-- ============================================================================

namespace Tree

/-- Depth of the leftmost path. -/
def lDepth : Tree → Nat
  | .leaf => 0
  | .node _ l _ => l.lDepth + 1

/-- The leftmost key, with default `d` for the empty tree. -/
def leftmost (d : Word) : Tree → Word
  | .leaf => d
  | .node k l _ => l.leftmost k

end Tree

/-- The key dword of a node's byte image. -/
theorem nodeBytes_key (k pl pr : Word) :
    ((nodeBytes k pl pr).drop 0).take 8 = dwordBytes k := by
  rw [List.drop_zero, nodeBytes,
    List.take_append_of_le_length (by rw [length_dwordBytes]),
    List.take_of_length_le (by rw [length_dwordBytes])]

/-- The left-pointer dword of a node's byte image. -/
theorem nodeBytes_left (k pl pr : Word) :
    ((nodeBytes k pl pr).drop 8).take 8 = dwordBytes pl := by
  rw [nodeBytes, List.drop_append_of_le_length (by rw [length_dwordBytes]),
    List.drop_eq_nil_of_le (by rw [length_dwordBytes]), List.nil_append,
    List.take_append_of_le_length (by rw [length_dwordBytes]),
    List.take_of_length_le (by rw [length_dwordBytes])]

-- ============================================================================
-- The walk
-- ============================================================================

/-- The node-visit block: key into `a2`, bump the counter, left child
    into `a0` (overwriting the node pointer last). -/
def treeMinBlock : List Instr :=
  [.LD .x12 .x10 0, .ADDI .x13 .x13 1, .LD .x10 .x10 8]

/-- The loop invariant of the leftmost-key walk: a zipper context and the
    current subtree (both ghost), the plug identity, the nil-pointer
    shadow, the answer-so-far relation, the counter-register tie, and the
    exact remaining left-depth. -/
def treeMinInv (root d0 : Word) (t0 : Tree) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A => ∃ (c : Tree.Ctx) (t' : Tree),
    A = ((ctxAt c root (rf.get .x10)) ** treeAt (rf.get .x10) t')
    ∧ c.zip t' = t0
    ∧ (rf.get .x10 = 0 ↔ t' = .leaf)
    ∧ t0.leftmost d0 = t'.leftmost (rf.get .x12)
    ∧ rf.get .x13 = BitVec.ofNat 64 i
    ∧ t'.lDepth + i = t0.lDepth

/-- The focus annotation: the window is the current node's bytes; the
    remainder is its pure facts, the children, and the context.  The
    relation restates the structural ghosts (annotations cannot see the
    invariant's own existentials) and carries the loop-index-dependent
    depth fact through the counter register. -/
def treeMinWinR (root d0 : Word) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    ∃ (c : Tree.Ctx) (k : Word) (l r : Tree) (pl pr : Word),
    win = nodeBytes k pl pr
    ∧ rest = (⌜rf.get .x10 ≠ 0 ∧ RwRegion.wf ⟨rf.get .x10, 24⟩⌝ **
        ((treeAt pl l ** treeAt pr r) ** ctxAt c root (rf.get .x10)))
    ∧ c.zip (.node k l r) = t0
    ∧ t0.leftmost d0 = (Tree.node k l r).leftmost (rf.get .x12)
    ∧ (Tree.node k l r).lDepth + (rf.get .x13).toNat = t0.lDepth

/-- The descend annotation: after the visit block, `a0` holds the left
    child, `a2` the node's key, `t2` the incremented counter; the new
    ambient is the pushed context plus the left subtree. -/
def treeMinStepR (root d0 : Word) (t0 : Tree) :
    RegFile → List (BitVec 8) → Assertion → Assertion → Prop :=
  fun rf _ _ A' => ∃ (c : Tree.Ctx) (k : Word) (r l : Tree),
    A' = ((ctxAt (Tree.Ctx.left k r c) root (rf.get .x10)) **
      treeAt (rf.get .x10) l)
    ∧ (Tree.Ctx.left k r c).zip l = t0
    ∧ (rf.get .x10 = 0 ↔ l = .leaf)
    ∧ t0.leftmost d0 = l.leftmost (rf.get .x12)
    ∧ l.lDepth + (rf.get .x13).toNat = t0.lDepth

/-- Walk to the leftmost key: `a2 := leftmost of the tree at a0`
    (defaulting to the entry `a2`), preserving the tree.  Ghosts: the
    tree `t0`, its root address, the default. -/
def treeMinFn (root d0 : Word) (t0 : Tree) : Fn where
  name := "treeMin"
  pre := fun rf _ A => rf.get .x10 = root ∧ rf.get .x12 = d0
    ∧ A = treeAt root t0
  post := fun rf _ A => rf.get .x12 = t0.leftmost d0 ∧ A = treeAt root t0
  body :=
    .block "init" [.LI .x13 0] ;;;
    .ghost "enter" (fun _ _ _ A' =>
      A' = ((ctxAt Tree.Ctx.top root root) ** treeAt root t0)
      ∧ (root = 0 ↔ t0 = .leaf)) ;;;
    .«while» "walk" (.bne .x10 .x0) t0.lDepth (treeMinInv root d0 t0)
      (.blockAt "node" .x10 (treeMinWinR root d0 t0) treeMinBlock ;;;
       .ghost "step" (treeMinStepR root d0 t0)) ;;;
    .ghost "fold" (fun _ _ _ A' => A' = treeAt root t0)

/-- The visit block's register effect (the routing conditions discharge
    against the 24-byte window). -/
private theorem treeMin_engine (reg : Region) (rf₀ : RegFile) (k pl pr : Word) :
    (execBlock reg (rf₀.get .x10) rf₀ (nodeBytes k pl pr) treeMinBlock).1.get .x10
        = pl
    ∧ (execBlock reg (rf₀.get .x10) rf₀ (nodeBytes k pl pr) treeMinBlock).1.get .x12
        = k
    ∧ (execBlock reg (rf₀.get .x10) rf₀ (nodeBytes k pl pr) treeMinBlock).1.get .x13
        = rf₀.get .x13 + 1 := by
  have h0 : ((rf₀.get .x10 + signExtend12 (0 : BitVec 12))
      - rf₀.get .x10).toNat = 0 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  have h8 : ((rf₀.get .x10 + signExtend12 (8 : BitVec 12))
      - rf₀.get .x10).toNat = 8 := by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
    bv_omega
  have hg10 : ∀ v w : Word,
      ((rf₀.set .x12 v).set .x13 w).get .x10 = rf₀.get .x10 := fun v w => by
    rw [RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide)]
  have hg13 : ∀ v : Word, (rf₀.set .x12 v).get .x13 = rf₀.get .x13 := fun v => by
    rw [RegFile.get_set_ne _ _ _ _ (by decide)]
  simp only [treeMinBlock, execBlock_cons, execBlock_nil, execInstrRF,
    loadSem, aluSem]
  rw [if_pos (show inRw (rf₀.get .x10) (nodeBytes k pl pr)
      (rf₀.get .x10 + signExtend12 0) 8 from by
    unfold inRw
    rw [h0, length_nodeBytes]
    omega)]
  simp only [hg10, hg13]
  rw [if_pos (show inRw (rf₀.get .x10) (nodeBytes k pl pr)
      (rf₀.get .x10 + signExtend12 8) 8 from by
    unfold inRw
    rw [h8, length_nodeBytes]
    omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [RegFile.get_set_self _ _ _ (by decide)]
    show Region.dwordAt ⟨rf₀.get .x10, nodeBytes k pl pr⟩ _ = pl
    unfold Region.dwordAt
    rw [show ((rf₀.get .x10 + signExtend12 8)
        - (⟨rf₀.get .x10, nodeBytes k pl pr⟩ : Region).base).toNat = 8 from h8,
      nodeBytes_left]
    exact packBytes_dwordBytes pl
  · rw [RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide)]
    show Region.dwordAt ⟨rf₀.get .x10, nodeBytes k pl pr⟩ _ = k
    unfold Region.dwordAt
    rw [show ((rf₀.get .x10 + signExtend12 0)
        - (⟨rf₀.get .x10, nodeBytes k pl pr⟩ : Region).base).toNat = 0 from h0,
      nodeBytes_key]
    exact packBytes_dwordBytes k
  · rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide)]

theorem treeMinFn_spec (root d0 : Word) (t0 : Tree)
    (hdep : t0.lDepth < 2 ^ 64 - 1) (base : Word) :
    (treeMinFn root d0 t0).Spec base := by
  vcgen
  case treeMin.enter =>
    rintro rf ws A ⟨rf₀, ws₀, -, ⟨hx10, hx12, hA⟩, rfl, rfl⟩ hApc hsat
    obtain ⟨hp, hhp⟩ := hsat
    rw [hA] at hhp
    have hshadow := treeAt_sat_shadow hhp
    refine ⟨_, ⟨rfl, hshadow⟩, ?_,
      pcFree_sepConj (pcFree_ctxAt _ _ _) (pcFree_treeAt _ _)⟩
    intro hq hh
    rw [hA] at hh
    exact (sepConj_pure_left hq).mpr ⟨rfl, hh⟩
  case treeMin.walk.inv_init =>
    rintro rf ws A ⟨A₀, ⟨rf₀, ws₀, -, ⟨hx10, hx12, hA⟩, rfl, rfl⟩, hsat, rfl, hshadow⟩
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨.top, t0, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ .x13 .x10 _ (by decide), hx10]
    · rw [RegFile.get_set_ne _ .x13 .x10 _ (by decide), hx10]
      exact hshadow
    · rw [RegFile.get_set_ne _ .x13 .x12 _ (by decide), hx12]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · omega
  case treeMin.walk.body.node.focus =>
    rintro rf ws A ⟨i, hi, ⟨c, t', hAeq, hzip, hshadow, hlm, hx13, hd⟩, hcond⟩
      hApc hp hhp
    have hne : rf.get .x10 ≠ 0 := by
      simp only [Cond.holds, ne_eq] at hcond
      simpa using hcond
    obtain ⟨k, l, r, rfl⟩ : ∃ k l r, t' = Tree.node k l r := by
      cases t' with
      | leaf => exact absurd (hshadow.mpr rfl) hne
      | node k l r => exact ⟨k, l, r, rfl⟩
    rw [hAeq] at hhp
    obtain ⟨h1, h2, hd12, hu12, hctx, htree⟩ := hhp
    obtain ⟨pl, pr, htree'⟩ := htree
    have hwfp := treeAt_sat_node (⟨pl, pr, htree'⟩ :
      treeAt (rf.get .x10) (.node k l r) h2)
    refine ⟨nodeBytes k pl pr,
      ⌜rf.get .x10 ≠ 0 ∧ RwRegion.wf ⟨rf.get .x10, 24⟩⌝ **
        ((treeAt pl l ** treeAt pr r) ** ctxAt c root (rf.get .x10)),
      ⟨c, k, l, r, pl, pr, rfl, rfl, hzip, hlm, ?_⟩, ?_, ?_, ?_⟩
    · rw [hx13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hd
    · have hall : ((ctxAt c root (rf.get .x10)) **
          ((nodeAt (rf.get .x10) k pl pr) **
            (treeAt pl l ** treeAt pr r))) hp :=
        ⟨h1, h2, hd12, hu12, hctx, htree'⟩
      rw [show nodeAt (rf.get .x10) k pl pr
          = (⌜rf.get .x10 ≠ 0 ∧ RwRegion.wf ⟨rf.get .x10, 24⟩⌝ **
            bytesRegion (rf.get .x10) (nodeBytes k pl pr)) from rfl] at hall
      xperm_hyp hall
    · exact pcFree_sepConj pcFree_pure
        (pcFree_sepConj (pcFree_sepConj (pcFree_treeAt _ _) (pcFree_treeAt _ _))
          (pcFree_ctxAt _ _ _))
    · rw [length_nodeBytes]
      exact hwfp.2
  case treeMin.walk.body.node.mem =>
    rintro rf ws A win rest hws hreach
      ⟨c, k, l, r, pl, pr, rfl, hrest, hzip, hlm, hdep'⟩ hsat
    have h0 : ((rf.get .x10 + signExtend12 (0 : BitVec 12))
        - rf.get .x10).toNat = 0 := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have h8 : ((rf.get .x10 + signExtend12 (8 : BitVec 12))
        - rf.get .x10).toNat = 8 := by
      rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    have hg10 : ∀ v w : Word,
        ((rf.set .x12 v).set .x13 w).get .x10 = rf.get .x10 := fun v w => by
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
    have hc1 : inRw (rf.get .x10) (nodeBytes k pl pr)
        (rf.get .x10 + signExtend12 0) 8 := by
      unfold inRw
      rw [h0, length_nodeBytes]
      omega
    have hc2 : inRw (rf.get .x10) (nodeBytes k pl pr)
        (rf.get .x10 + signExtend12 8) 8 := by
      unfold inRw
      rw [h8, length_nodeBytes]
      omega
    simp only [treeMinBlock, blockVCs, loadSem, aluSem, storeSem, execInstrRF,
      Region.loadOk, length_nodeBytes, if_pos hc1, hg10]
    simp only [if_pos hc2]
    simp only [h0, h8]
    and_intros <;> trivial
  case treeMin.walk.body.step =>
    rintro rf ws A ⟨rf₀, A₀, win, rest, hws,
      ⟨i, hi, ⟨c₀, t', hAeq, hzip₀, hshadow₀, hlm₀, hx13₀, hd₀⟩, hcond⟩, hsatp,
      ⟨c, k, l, r, pl, pr, rfl, rfl, hzip, hlm, hdep'⟩, rfl, rfl⟩ hApc hsat
    obtain ⟨hx10v, hx12v, hx13v⟩ := treeMin_engine
      (treeMinFn root d0 t0).region rf₀ k pl pr
    -- harvest the child's nil shadow
    have hchild : pl = 0 ↔ l = .leaf := by
      obtain ⟨hp, hhp⟩ := hsat
      obtain ⟨hq, hql⟩ := sepConj_sat_right hhp
      obtain ⟨hq2, hql2⟩ := sepConj_sat_right hql
      obtain ⟨hq3, hql3⟩ := sepConj_sat_left hql2
      obtain ⟨hq4, hql4⟩ := sepConj_sat_left hql3
      exact treeAt_sat_shadow hql4
    refine ⟨((ctxAt (Tree.Ctx.left k r c) root pl) ** treeAt pl l),
      ⟨c, k, r, l, by rw [hx10v], by rw [← hzip]; rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hx10v]
      exact hchild
    · rw [hx12v]
      exact hlm
    · rw [hx13v]
      simp only [Tree.lDepth] at hdep'
      have h1 : (rf₀.get .x13).toNat + 1 < 2 ^ 64 := by omega
      have h2 : (rf₀.get .x13 + 1).toNat = (rf₀.get .x13).toNat + 1 := by
        bv_omega
      rw [h2]
      omega
    · intro hq hh
      rw [show (execBlock (treeMinFn root d0 t0).region (rf₀.get .x10) rf₀
          (nodeBytes k pl pr) treeMinBlock).2 = nodeBytes k pl pr from rfl] at hh
      have hshaped : ((ctxAt c root (rf₀.get .x10)) **
          ((nodeAt (rf₀.get .x10) k pl pr) **
            (treeAt pl l ** treeAt pr r))) hq := by
        rw [show nodeAt (rf₀.get .x10) k pl pr
            = (⌜rf₀.get .x10 ≠ 0 ∧ RwRegion.wf ⟨rf₀.get .x10, 24⟩⌝ **
              bytesRegion (rf₀.get .x10) (nodeBytes k pl pr)) from rfl]
        xperm_hyp hh
      exact ctxAt_push_left c root (rf₀.get .x10) k pl pr l r hq hshaped
    · exact pcFree_sepConj (pcFree_ctxAt _ _ _) (pcFree_treeAt _ _)
  case treeMin.walk.inv_step =>
    rintro i hi rf' ws' A' ⟨A, ⟨rf₀, A₀, win, rest, hws,
      ⟨⟨c₀, t', hAeq, hzip₀, hshadow₀, hlm₀, hx13₀, hd₀⟩, hcond⟩, hsatp,
      ⟨c, k, l, r, pl, pr, rfl, rfl, hzip, hlm, hdep'⟩, rfl, rfl⟩, hsat,
      ⟨c₁, k₁, r₁, l₁, hA'eq, hzip₁, hshadow₁, hlm₁, hdep₁⟩⟩
    obtain ⟨hx10v, hx12v, hx13v⟩ := treeMin_engine
      (treeMinFn root d0 t0).region rf₀ k pl pr
    refine ⟨Tree.Ctx.left k₁ r₁ c₁, l₁, hA'eq, hzip₁, hshadow₁, hlm₁, ?_, ?_⟩
    · rw [hx13v, hx13₀, show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) from by
        rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]]
    · have htn : ((execBlock (treeMinFn root d0 t0).region (rf₀.get .x10) rf₀
          (nodeBytes k pl pr) treeMinBlock).1.get .x13).toNat = i + 1 := by
        rw [hx13v, hx13₀]
        have h1 : i + 1 < 2 ^ 64 := by omega
        bv_omega
      rw [htn] at hdep₁
      omega
  case treeMin.walk.exhausted =>
    rintro rf ws A ⟨c, t', hAeq, hzip, hshadow, hlm, hx13, hd⟩
    have ht' : t' = .leaf := by
      cases t' with
      | leaf => rfl
      | node k l r =>
          exact absurd hd (by simp only [Tree.lDepth]; omega)
    have h0 : rf.get .x10 = 0 := hshadow.mpr ht'
    simp only [Cond.holds]
    rw [h0]
    simp
  case treeMin.fold =>
    rintro rf ws A ⟨⟨i, hile, c, t', hAeq, hzip, hshadow, hlm, hx13, hd⟩,
      hncond⟩ hApc hsat
    refine ⟨_, rfl, ?_, pcFree_treeAt _ _⟩
    intro hq hh
    rw [hAeq] at hh
    rw [← hzip]
    exact ctxAt_zip_fold c root _ t' hq hh
  case treeMin.post =>
    rintro rf ws A ⟨A₁, ⟨⟨i, hile, c, t', hAeq, hzip, hshadow, hlm, hx13, hd⟩,
      hncond⟩, hsat, rfl⟩
    have h0 : rf.get .x10 = 0 := by
      simp only [Cond.holds, ne_eq] at hncond
      simpa using hncond
    have ht' : t' = .leaf := hshadow.mp h0
    subst ht'
    exact ⟨hlm.symm, rfl⟩

end SAsm
end EvmAsm.Rv64
