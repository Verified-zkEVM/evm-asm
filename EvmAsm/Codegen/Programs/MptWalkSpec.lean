/-
  EvmAsm.Codegen.Programs.MptWalkSpec

  Spec scaffolding for `mpt_walk` (obligation #10 / #11799).

  Pure hop lemmas live in `EvmAsm.Evm64.MptCorrespondence`
  (`mpt_walk_hop_extension` / `mpt_walk_hop_branch` + coverRef).
  This module packages the **loop-invariant ghost** the machine triple
  will carry and shows the pure hop preserves SpecRef alignment — the
  inductive step content, still free of RISC-V. The machine body
  (314-insn frame + Resolve replacement + kind dispatch) is follow-on.

  ## Domain gate (`.conditional` — named, not silent)

  * `MptNode` v1 hash-or-empty children only. **Inlined sub-32-byte
    children** (`mpt_branch_child` status 2 / guest path that folds a
    child offset into the parent buffer) are **excluded by this gate**,
    not merely unhandled.
  * Every node on the walk is `n.WF` and `rlpToMutableNode n.rlp` succeeds
    (hence equals `alpha_node n` by `rlpToMutableNode_rlp`).
  * Resolve (`nodeDbLookupSpec`) answers every taken hashed child; miss
    is the walk's fail arm, not a hop.
  * Residual path fuel exceeds the remaining nibble suffix.

  ## Loop invariant — six facts

  Material:
  1. NODE REF — current `(ptr,len)` owns `mptNodeIs ptr n` (REPLACED on
     hop by Resolve result; not a cursor advance inside the parent).
  2. PATH SUFFIX — ghost `pos` with residual `nibbles.drop pos`; hop
     advances `+1` (branch) or `+segLen` (extension).
  3. DB — `nodeDbIs` / lookup coherence; unchanged on pure read.
  4. FUEL — residual path length countdown (matches `trieLookupAux`).

  Ghosts (the correspondence content):
  5. SHALLOW ALPHA — `rlpToMutableNode n.rlp = some (alpha_node n)`.
  6. SPEC ALIGNMENT — `trieLookupAux fuel (some deep_n) nibbles pos`
     where `deep_n` is the parent with the taken child already substituted
     by `alpha_node child` (the form `trieLookupAux_*_hop` consumes).

  coverRef: `mpt_walk_hop_precondition_reachable` (two-node ext→leaf hop).
-/

import EvmAsm.Evm64.MptCorrespondence

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Evm64
open EvmAsm.Stateless.SpecRef (MutableNode trieLookupAux)

/-- Pure loop-invariant ghost package at one hop site (no memory).
    Machine layer will pair this with `mptNodeIs` / `nodeDbIs`. -/
structure WalkGhost where
  /-- Current guest node (hash-or-empty children only). -/
  node : MptNode
  /-- Well-formedness (v1 vocabulary). -/
  wf : node.WF
  /-- Path position into `nibbles`. -/
  pos : Nat
  /-- Full nibble path. -/
  nibbles : List (BitVec 8)
  /-- Residual fuel for `trieLookupAux` (`fuel = f+1` before a hop). -/
  fuel : Nat
  /-- Shallow alpha succeeds. -/
  alpha_ok : rlpToMutableNode node.rlp = some (alpha_node node)

/-- Child ghost after an extension hop of segment length `segLen`. -/
def WalkGhost.afterExt (g : WalkGhost) (child : MptNode) (hwf : child.WF)
    (segLen : Nat) (_hfuel : ∃ f, g.fuel = f + 1) : WalkGhost where
  node := child
  wf := hwf
  pos := g.pos + segLen
  nibbles := g.nibbles
  fuel := g.fuel - 1
  alpha_ok := rlpToMutableNode_rlp child hwf

/-- Child ghost after a branch hop (advance path by 1). -/
def WalkGhost.afterBranch (g : WalkGhost) (child : MptNode) (hwf : child.WF)
    (_hfuel : ∃ f, g.fuel = f + 1) : WalkGhost where
  node := child
  wf := hwf
  pos := g.pos + 1
  nibbles := g.nibbles
  fuel := g.fuel - 1
  alpha_ok := rlpToMutableNode_rlp child hwf

/-- Extension hop preserves SpecRef alignment on the substituted deep
    tree (ghost 6 inductive step). -/
theorem walkGhost_extension_hop
    (g : WalkGhost)
    (path childHash : List (BitVec 8))
    (child : MptNode) (hwf_child : child.WF)
    (nodes : List (List (BitVec 8)))
    (hn : g.node = .extension path childHash)
    (hlookup : nodeDbLookupSpec nodes childHash = some child.rlp)
    (h_prefix : (g.nibbles.drop g.pos).take path.length = path)
    (h_fuel : ∃ f, g.fuel = f + 1) :
    let g' := g.afterExt child hwf_child path.length h_fuel
    trieLookupAux g.fuel
        (some (.extension path (alpha_node child))) g.nibbles g.pos =
      trieLookupAux g'.fuel (some (alpha_node child)) g'.nibbles g'.pos := by
  intro g'
  obtain ⟨f, hf⟩ := h_fuel
  have hwf_ext : (MptNode.extension path childHash).WF := by
    rw [← hn]; exact g.wf
  have hop := (mpt_walk_hop_extension path childHash child nodes
    g.nibbles g.pos f hwf_ext hwf_child hlookup h_prefix).2.2
  -- g.fuel = f+1, g'.fuel = (f+1)-1 = f
  simp only [WalkGhost.afterExt, g', hf, Nat.add_sub_cancel] at hop ⊢
  exact hop

/-- Branch hop preserves SpecRef alignment after substituting the resolved
    child at the selected hash slot. Inlined / empty slots are outside
    this theorem (domain gate / terminal miss). -/
theorem walkGhost_branch_hop
    (g : WalkGhost)
    (cs : List (List (BitVec 8))) (value childHash : List (BitVec 8))
    (child : MptNode) (hwf_child : child.WF)
    (nodes : List (List (BitVec 8)))
    (hn : g.node = .branch cs value)
    (h_more : g.pos < g.nibbles.length)
    (h_idx_bound : (g.nibbles.getD g.pos 0).toNat < cs.length)
    (h_slot : cs.getD (g.nibbles.getD g.pos 0).toNat [] = childHash)
    (h_hash : childHash.length = 32)
    (hlookup : nodeDbLookupSpec nodes childHash = some child.rlp)
    (h_fuel : ∃ f, g.fuel = f + 1) :
    let idx := (g.nibbles.getD g.pos 0).toNat
    let children := cs.map fun c =>
      if c = [] then none else some (MutableNode.hashed c)
    let children' := children.set idx (some (alpha_node child))
    let g' := g.afterBranch child hwf_child h_fuel
    trieLookupAux g.fuel (some (.branch children' value)) g.nibbles g.pos =
      trieLookupAux g'.fuel (some (alpha_node child)) g'.nibbles g'.pos := by
  intro idx children children' g'
  obtain ⟨f, hf⟩ := h_fuel
  have hwf_br : (MptNode.branch cs value).WF := by
    rw [← hn]; exact g.wf
  have hop := (mpt_walk_hop_branch cs value childHash child nodes
    g.nibbles g.pos f hwf_br hwf_child h_more h_idx_bound h_slot h_hash
    hlookup).2.2
  simp only [WalkGhost.afterBranch, g', hf, Nat.add_sub_cancel,
    idx, children, children'] at hop ⊢
  exact hop

/-- coverRef re-export for the machine registry row. -/
theorem mpt_walk_precondition_reachable :
    ∃ (path childHash : List (BitVec 8)) (child : MptNode)
      (nodes : List (List (BitVec 8))) (nibbles : List (BitVec 8))
      (pos : Nat),
      (MptNode.extension path childHash).WF ∧
      child.WF ∧
      nodeDbLookupSpec nodes childHash = some child.rlp ∧
      (nibbles.drop pos).take path.length = path ∧
      0 < path.length :=
  mpt_walk_hop_precondition_reachable

end EvmAsm.Codegen.MptWalkSpec
