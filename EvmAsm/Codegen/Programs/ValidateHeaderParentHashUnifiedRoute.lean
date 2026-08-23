/-
  Caller-side plumbing for the unified parent-hash contract (#12346 item 8).

  The parent-hash call is made after the validate-header prologue has
  installed the parent RLP pointer in x20.  The continuation ambient therefore
  owns the child-frame stack and scratch/BSS regions, but deliberately leaves
  x20 to the route's post-prologue register assertion.  This prevents the
  ambient from claiming an entry-time x20 that the caller does not provide.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderParentHashAdapter

namespace EvmAsm.Codegen.ValidateHeaderCompose

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderParentHashCorrespondence
open EvmAsm.Codegen.HeaderValidateParentHashSpec

noncomputable section

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_regOwns _)

/-- The unified continuation ambient after the caller has supplied x20.

`hvphSuccKeccakAmb` also owns x20.  At the H+244 call seam that cell is
already produced by `postMerge_status0_to_parent_hash_args`, so this residual
form is what can actually be framed through that caller route. -/
def hvphSuccKeccakTail
    (spC : Word) (os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  stackFree spC 4 **
  regOwns [.x14, .x15, .x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F

theorem hvphSuccKeccakTail_pcFree
    (spC : Word) (os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) : (hvphSuccKeccakTail spC os out0 F).pcFree := by
  unfold hvphSuccKeccakTail
  pcf
  exact hF

/-! ## The real H+196 → H+248 caller seam

The theorem below is intentionally a direct consumer of
`validate_header_parent_hash_unified_call_spec_within`.  The route carries the
physical claimed/computed/zk3 resources and child-frame stack from the
post-prologue seam; it does not replace them by an unconstrained `G`.
-/

set_option maxRecDepth 8000 in
theorem postMerge_status0_to_parent_hash_unified_call
    {cr calleeCode : CodeReq} {n : Nat}
    (spC childSp header headerLen s4 s5 oldRa : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hchild : childSp = spC + signExtend12 (-32 : BitVec 12))
    (hvals8 : vals .x8 = header)
    (hvals9 : vals .x9 = headerLen)
    (hvals18 : vals .x18 = s4)
    (hdisj : (CodeReq.singleton
      ValidateHeaderParentHashCorrespondence.A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)))).Disjoint calleeCode)
    (hcallerDisj : parentHashRouteFrameCaller.Disjoint calleeCode)
    (hcode : ∀ a i, (parentHashRouteFrameCaller.union calleeCode) a = some i →
      cr a = some i)
    (hcallee : cpsTripleWithin n
      ValidateHeaderParentHashCorrespondence.Callee
      ValidateHeaderParentHashCorrespondence.Ret calleeCode
      ((.x1 ↦ᵣ ValidateHeaderParentHashCorrespondence.Ret) **
        ValidateHeaderParentHashCorrespondence.hvphEntryRest
          spC header headerLen s4 s5 vals thisBytes parentBytes **
        claimedOwn C0 **
        hvphSuccKeccakAmb childSp s4 os (List.replicate 32 0) G)
      (hvphUnifiedPost spC childSp
        ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
        thisBytes parentBytes C0 N rem os G)) :
    cpsTripleWithin (5 + (1 + n))
      (parentHashRouteFrameH + 196)
      ValidateHeaderParentHashCorrespondence.Ret cr
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)) **
        parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes **
        claimedOwn C0 **
        hvphSuccKeccakTail childSp os (List.replicate 32 0) G)
      ((.x21 ↦ᵣ s5) **
        hvphUnifiedPost spC childSp
          ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
          thisBytes parentBytes C0 N rem os G) := by
  let tail := hvphSuccKeccakTail childSp os (List.replicate 32 0) G
  let F := parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes **
    claimedOwn C0 ** tail
  have hF : F.pcFree := by
    dsimp [F, tail]
    pcf
    exact hG
  have hroute := postMerge_status0_to_parent_hash_args
    (header := header) (headerLen := headerLen) (s4 := s4) (s5 := s5)
    (F := F) hF
  have hcallerCode : ∀ a i, parentHashRouteFrameCaller a = some i → cr a = some i := by
    intro a i hi
    exact hcode a i (CodeReq.union_mono_left a i hi)
  have hrouteC := cpsTripleWithin_extend_code hcallerCode hroute
  have hcall :=
    validate_header_parent_hash_unified_call_spec_within
      (cr := cr) (calleeCode := calleeCode) (n := n)
      spC childSp header headerLen s4 s5 oldRa vals
      thisBytes parentBytes C0 N rem os s4 G hG
      hdisj hcallerDisj hcode hcallee
  have hx21 : ((.x21 ↦ᵣ s5) : Assertion).pcFree := pcFree_regIs
  have hcallF := cpsTripleWithin_frameR ((.x21 ↦ᵣ s5) : Assertion) hx21 hcall
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold F tail hvphSuccKeccakTail at hp
      unfold parentHashRouteFrame at hp
      unfold ValidateHeaderParentHashCorrespondence.hvphEntryRest
        hvphSuccKeccakAmb
      have hneg : signExtend12 (-32 : BitVec 12) =
          signExtend12 (BitVec.ofNat 12 4064) := by decide
      have hbase : spC + signExtend12 (-32 : BitVec 12) =
          spC + signExtend12 (BitVec.ofNat 12 4064) := by rw [hneg]
      rw [hchild] at hp
      rw [hchild] at ⊢
      rw [hbase] at ⊢
      rw [hbase] at hp
      rw [hvals18] at hp
      simp [hvals8, hvals9, hvals18,
        ValidateHeaderParentHashCorrespondence.hvphSavedFrame,
        EvmAsm.Rv64.SAsm.regsAt, EvmAsm.Rv64.SAsm.regOwns,
        HeaderValidateParentHashSpec.Computed, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp)
    hrouteC hcallF
  refine cpsTripleWithin_weaken
    (fun _ hp => by simpa [F, tail, sepConj_assoc'] using hp)
    (fun _ hq => by xperm_hyp hq)
    hseq

end

end EvmAsm.Codegen.ValidateHeaderCompose
