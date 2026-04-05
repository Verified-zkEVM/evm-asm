/-
  EvmAsm.Evm64.DivMod.LoopBody

  Hierarchical composition of the 114-instruction Knuth Algorithm D main loop body.
  Composes sub-specs from LimbSpec.lean into a single cpsBranch for one iteration,
  then proves the inductive loop spec via cpsTriple_loop_with_perm.

  Issue #87: DIV/MOD loop body composition.
-/

import EvmAsm.Evm64.DivMod.Compose

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 1: CodeReq subsumption infrastructure for loop body instructions
-- ============================================================================

/-- The loopBody ofProg (block 8) is subsumed by divCode. -/
private theorem divK_loopBody_ofProg_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 448) (divK_loopBody 556 7740)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: singleton at index k of divK_loopBody ⊆ divCode base. -/
private theorem lb_sub (base : Word) (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 556 7740).length)
    (h_addr : addr = (base + 448) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 556 7740).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (divCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_divCode base a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + 448) (divK_loopBody 556 7740) k hk (by native_decide)) a i h)

/-- Helper: combine two subsumption proofs over a union. -/
private theorem CodeReq_union_sub {cr1 cr2 target : CodeReq}
    (h1 : ∀ a i, cr1 a = some i → target a = some i)
    (h2 : ∀ a i, cr2 a = some i → target a = some i) :
    ∀ a i, (cr1.union cr2) a = some i → target a = some i := by
  intro a i h
  simp only [CodeReq.union] at h
  cases h1a : cr1 a with
  | some j => rw [h1a] at h; simp at h; exact h ▸ h1 a j h1a
  | none => rw [h1a] at h; simp at h; exact h2 a i h

-- ============================================================================
-- Section 2: Address normalization lemmas
-- Loop body base = base + 448.
-- Instruction [k] is at base + 448 + 4*k.
-- ============================================================================

-- Mulsub limb base addresses (instrs [22]-[65])
private theorem lb_ms0 (base : Word) : (base + 448 : Word) + 88 = base + 536 := by bv_addr
private theorem lb_ms1 (base : Word) : (base + 536 : Word) + 44 = base + 580 := by bv_addr
private theorem lb_ms2 (base : Word) : (base + 580 : Word) + 44 = base + 624 := by bv_addr
private theorem lb_ms3 (base : Word) : (base + 624 : Word) + 44 = base + 668 := by bv_addr
private theorem lb_ms_end (base : Word) : (base + 668 : Word) + 44 = base + 712 := by bv_addr

-- ============================================================================
-- Section 3: Mulsub 4-limbs composition
-- Composes 4 × divK_mulsub_limb_spec using seqFrame for automatic framing.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Multiply-subtract all 4 limbs: u[j+k] -= q_hat * v[k] for k=0..3 with carry chain.
    44 instructions, loop body indices [22]-[65].
    Entry: base+536, Exit: base+712, CodeReq: divCode base. -/
theorem divK_mulsub_4limbs_spec
    (sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (v5_init v7_init v2_init : Word)
    (base : Word)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess (u_base + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess (u_base + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess (u_base + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess (u_base + signExtend12 4072) = true) :
    -- Limb 0 intermediates
    let p0_lo := q_hat * v0
    let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0
    let c0 := pc0 + bs0
    -- Limb 1 intermediates
    let p1_lo := q_hat * v1
    let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1
    let c1 := pc1 + bs1
    -- Limb 2 intermediates
    let p2_lo := q_hat * v2
    let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2
    let c2 := pc2 + bs2
    -- Limb 3 intermediates
    let p3_lo := q_hat * v3
    let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3
    let c3 := pc3 + bs3
    cpsTriple (base + 536) (base + 712) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ (signExtend12 0 : Word)) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ v5_init) ** (.x7 ↦ᵣ v7_init) **
       (.x2 ↦ᵣ v2_init) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) ** (.x10 ↦ᵣ c3) **
       (.x6 ↦ᵣ u_base) ** (.x5 ↦ᵣ bs3) ** (.x7 ↦ᵣ fs3) **
       (.x2 ↦ᵣ un3) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3)) := by
  intro p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3
  -- Limb 0: instrs [22]-[32] at base+536
  have L0 := divK_mulsub_limb_spec sp u_base q_hat (signExtend12 0 : Word)
    v5_init v7_init v2_init v0 u0 32 0 (base + 536)
    hv_v0 hv_u0
  rw [lb_ms1] at L0
  have L0e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 22 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 23 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 24 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 25 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 26 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 27 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 28 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 29 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 30 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 31 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 32 _ _ (by native_decide) (by bv_addr) (by native_decide))))))))))))
    L0
  -- Limb 1: instrs [33]-[43] at base+580
  have L1 := divK_mulsub_limb_spec sp u_base q_hat c0
    bs0 fs0 un0 v1 u1 40 4088 (base + 580)
    hv_v1 hv_u1
  rw [lb_ms2] at L1
  have L1e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 33 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 34 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 35 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 36 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 37 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 38 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 39 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 40 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 41 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 42 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 43 _ _ (by native_decide) (by bv_addr) (by native_decide))))))))))))
    L1
  -- Frame L0 with memory for limbs 1-3 (so seqFrame can find L1's precondition atoms)
  have L0f := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3))
    (by pcFree) L0e
  -- Compose L0 + L1
  seqFrame L0f L1e
  -- Limb 2: instrs [44]-[54] at base+624
  have L2 := divK_mulsub_limb_spec sp u_base q_hat c1
    bs1 fs1 un1 v2 u2 48 4080 (base + 624)
    hv_v2 hv_u2
  rw [lb_ms3] at L2
  have L2e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 44 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 45 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 46 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 47 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 48 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 49 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 50 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 51 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 52 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 53 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 54 _ _ (by native_decide) (by bv_addr) (by native_decide))))))))))))
    L2
  -- Compose (L0+L1) + L2
  seqFrame L0fL1e L2e
  -- Limb 3: instrs [55]-[65] at base+668
  have L3 := divK_mulsub_limb_spec sp u_base q_hat c2
    bs2 fs2 un2 v3 u3 56 4072 (base + 668)
    hv_v3 hv_u3
  rw [lb_ms_end] at L3
  have L3e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 55 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 56 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 57 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 58 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 59 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 60 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 61 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 62 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 63 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 64 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 65 _ _ (by native_decide) (by bv_addr) (by native_decide))))))))))))
    L3
  -- Compose (L0+L1+L2) + L3
  seqFrame L0fL1eL2e L3e
  -- Final permutation to match goal pre/postcondition order
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    L0fL1eL2eL3e

-- ============================================================================
-- Section 4: Addback full composition
-- Composes addback_init + 4 × addback_limb + addback_final.
-- 37 instructions at loop body indices [71]-[107].
-- Entry: base+732, Exit: base+880, CodeReq: divCode base.
-- ============================================================================

-- Addback base addresses (instrs [71]-[107])
private theorem lb_ab_init (base : Word) : (base + 448 : Word) + 284 = base + 732 := by bv_addr
private theorem lb_ab0 (base : Word) : (base + 732 : Word) + 4 = base + 736 := by bv_addr
private theorem lb_ab0_end (base : Word) : (base + 736 : Word) + 32 = base + 768 := by bv_addr
private theorem lb_ab1_end (base : Word) : (base + 768 : Word) + 32 = base + 800 := by bv_addr
private theorem lb_ab2_end (base : Word) : (base + 800 : Word) + 32 = base + 832 := by bv_addr
private theorem lb_ab3_end (base : Word) : (base + 832 : Word) + 32 = base + 864 := by bv_addr
private theorem lb_abf_end (base : Word) : (base + 864 : Word) + 16 = base + 880 := by bv_addr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Full add-back correction: init carry + 4 limb corrections + final u[j+4] adjust + q_hat--.
    37 instructions, loop body indices [71]-[107].
    Entry: base+732, Exit: base+880, CodeReq: divCode base. -/
theorem divK_addback_full_spec
    (sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess (u_base + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess (u_base + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess (u_base + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess (u_base + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess (u_base + signExtend12 4064) = true) :
    -- Limb 0 addback intermediates
    let upc0 := u0 + (signExtend12 0 : Word)
    let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0 := upc0 + v0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let aco0 := ac1_0 ||| ac2_0
    -- Limb 1 addback intermediates
    let upc1 := u1 + aco0
    let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
    let aun1 := upc1 + v1
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let aco1 := ac1_1 ||| ac2_1
    -- Limb 2 addback intermediates
    let upc2 := u2 + aco1
    let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
    let aun2 := upc2 + v2
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let aco2 := ac1_2 ||| ac2_2
    -- Limb 3 addback intermediates
    let upc3 := u3 + aco2
    let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
    let aun3 := upc3 + v3
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let aco3 := ac1_3 ||| ac2_3
    -- Final: u4 + carry, q_hat--
    let aun4 := u4 + aco3
    let q_hat' := q_hat + signExtend12 4095
    cpsTriple (base + 732) (base + 880) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ v7_init) **
       (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_init) ** (.x2 ↦ᵣ v2_init) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ aco3) **
       (.x11 ↦ᵣ q_hat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4)) := by
  intro upc0 ac1_0 aun0 ac2_0 aco0
        upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2
        upc3 ac1_3 aun3 ac2_3 aco3
        aun4 q_hat'
  -- Init: instr [71] at base+732
  have I := divK_addback_init_spec v7_init (base + 732)
  rw [lb_ab0] at I
  have Ie := cpsTriple_extend_code (hmono := by
    exact lb_sub base 71 _ _ (by native_decide) (by bv_addr) (by native_decide)) I
  -- Frame init with all addback state
  have If := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x11 ↦ᵣ q_hat) **
     (.x5 ↦ᵣ v5_init) ** (.x2 ↦ᵣ v2_init) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u4))
    (by pcFree) Ie
  -- Limb 0: instrs [72]-[79] at base+736
  have A0 := divK_addback_limb_spec sp u_base (signExtend12 0 : Word)
    v5_init v2_init v0 u0 32 0 (base + 736) hv_v0 hv_u0
  rw [lb_ab0_end] at A0
  have A0e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 72 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 73 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 74 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 75 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 76 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 77 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 78 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 79 _ _ (by native_decide) (by bv_addr) (by native_decide)))))))))
    A0
  -- Compose init + limb 0
  seqFrame If A0e
  -- Limb 1: instrs [80]-[87] at base+768
  have A1 := divK_addback_limb_spec sp u_base aco0
    ac2_0 aun0 v1 u1 40 4088 (base + 768) hv_v1 hv_u1
  rw [lb_ab1_end] at A1
  have A1e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 80 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 81 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 82 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 83 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 84 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 85 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 86 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 87 _ _ (by native_decide) (by bv_addr) (by native_decide)))))))))
    A1
  seqFrame IfA0e A1e
  -- Limb 2: instrs [88]-[95] at base+800
  have A2 := divK_addback_limb_spec sp u_base aco1
    ac2_1 aun1 v2 u2 48 4080 (base + 800) hv_v2 hv_u2
  rw [lb_ab2_end] at A2
  have A2e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 88 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 89 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 90 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 91 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 92 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 93 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 94 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 95 _ _ (by native_decide) (by bv_addr) (by native_decide)))))))))
    A2
  seqFrame IfA0eA1e A2e
  -- Limb 3: instrs [96]-[103] at base+832
  have A3 := divK_addback_limb_spec sp u_base aco2
    ac2_2 aun2 v3 u3 56 4072 (base + 832) hv_v3 hv_u3
  rw [lb_ab3_end] at A3
  have A3e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 96 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 97 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 98 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 99 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 100 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 101 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 102 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 103 _ _ (by native_decide) (by bv_addr) (by native_decide)))))))))
    A3
  seqFrame IfA0eA1eA2e A3e
  -- Final: instrs [104]-[107] at base+864
  have AF := divK_addback_final_spec u_base aco3 q_hat ac2_3 u4 4064 (base + 864) hv_u4
  rw [lb_abf_end] at AF
  have AFe := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 104 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 105 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 106 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 107 _ _ (by native_decide) (by bv_addr) (by native_decide)))))
    AF
  seqFrame IfA0eA1eA2eA3e AFe
  -- Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IfA0eA1eA2eA3eAFe

-- ============================================================================
-- Section 5: Mulsub full composition (setup + 4limbs + sub_carry)
-- Instrs [17]-[69] at base+516 → base+728.
-- ============================================================================

-- Address normalization for mulsub_setup
private theorem lb_ms_setup (base : Word) : (base + 516 : Word) + 20 = base + 536 := by bv_addr

-- Address normalization for sub_carry
private theorem lb_sc (base : Word) : (base + 712 : Word) + 16 = base + 728 := by bv_addr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Mulsub full: setup + 4-limb multiply-subtract + carry subtraction from u[j+4].
    53 instructions, loop body indices [17]-[69].
    Entry: base+516, Exit: base+728, CodeReq: divCode base. -/
theorem divK_mulsub_full_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- Mulsub intermediates (same as mulsub_4limbs_spec)
    let p0_lo := q_hat * v0
    let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0
    let c0 := pc0 + bs0
    let p1_lo := q_hat * v1
    let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1
    let c1 := pc1 + bs1
    let p2_lo := q_hat * v2
    let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2
    let c2 := pc2 + bs2
    let p3_lo := q_hat * v3
    let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3
    let c3 := pc3 + bs3
    -- Sub-carry intermediates
    let borrow := if BitVec.ult u_top c3 then (1 : Word) else 0
    let u4_new := u_top - c3
    cpsTriple (base + 516) (base + 728) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x2 ↦ᵣ v2_old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ borrow) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
       ((u_base + signExtend12 4064) ↦ₘ u4_new)) := by
  intro u_base
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3
        borrow u4_new
  -- 1. Mulsub setup: instrs [17]-[21] at base+516
  have S := divK_mulsub_setup_spec sp q_hat j v1_old v5_old v6_old v10_old (base + 516) hv_j
  rw [lb_ms_setup] at S
  have Se := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 17 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 18 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 19 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 20 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 21 _ _ (by native_decide) (by bv_addr) (by native_decide)))))) S
  -- Frame setup with all memory + x7/x2 for mulsub
  have Sf := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ v7_old) ** (.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u_top))
    (by pcFree) Se
  -- 2. Mulsub 4 limbs: instrs [22]-[65] at base+536
  have M := divK_mulsub_4limbs_spec sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3
    (j <<< (3 : BitVec 6).toNat) v7_old v2_old base hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3
  intro_lets at M
  -- Compose setup + mulsub
  seqFrame Sf M
  -- 3. Sub-carry: instrs [66]-[69] at base+712
  have SC := divK_sub_carry_spec u_base c3 bs3 fs3 u_top 4064 (base + 712) hv_u4
  rw [lb_sc] at SC
  have SCe := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 66 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 67 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 68 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 69 _ _ (by native_decide) (by bv_addr) (by native_decide))))) SC
  -- Compose (setup+mulsub) + sub_carry
  seqFrame SfM SCe
  -- Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SfMSCe

-- ============================================================================
-- Section 6: Correction branch address normalization
-- BEQ at instr [70] (base+728): taken → base+880, not-taken → base+732.
-- ============================================================================

private theorem lb_beq_taken (base : Word) : (base + 728 : Word) + signExtend13 (152 : BitVec 13) = base + 880 := by
  have : signExtend13 (152 : BitVec 13) = (152 : Word) := by native_decide
  rw [this]; bv_addr

private theorem lb_beq_ntaken (base : Word) : (base + 728 : Word) + 4 = base + 732 := by bv_addr

-- ============================================================================
-- Section 6a: Correction skip spec (borrow = 0)
-- BEQ taken → skip addback. 1 instruction at base+728 → base+880.
-- ============================================================================

/-- Correction skip: when borrow=0, BEQ taken → jump to base+880. No addback.
    1 instruction. All registers and memory unchanged. -/
theorem divK_correction_skip_spec
    (sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5_old v2_old : Word) (base : Word) :
    cpsTriple (base + 728) (base + 880) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u4)) := by
  -- BEQ x7 x0 152 at base+728 with x7=0, x0=0
  have hbeq := beq_spec_gen .x7 .x0 (152 : BitVec 13) (0 : Word) 0 (base + 728)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 70 _ _ (by native_decide) (by bv_addr) (by native_decide)) hbeq
  -- Eliminate not-taken path (⌜0 ≠ 0⌝ is False)
  have skip := cpsBranch_elim_taken _ _ _ _ _ _ _ hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  -- Strip pure fact from taken postcondition
  have skip_clean : cpsTriple (base + 728) (base + 880) (divCode base)
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      skip
  -- Frame with all other state and permute
  have skip_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) **
     (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u4))
    (by pcFree) skip_clean
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    skip_framed

-- ============================================================================
-- Section 6b: Correction addback spec (borrow ≠ 0)
-- BEQ not-taken → run addback. 38 instrs at base+728 → base+880.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Correction with addback: when borrow≠0, BEQ not-taken → addback_full.
    38 instructions. Modifies u values and decrements q_hat. -/
theorem divK_correction_addback_spec
    (sp u_base borrow q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5_old v2_old : Word) (base : Word)
    (hb : borrow ≠ (0 : Word))
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess (u_base + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess (u_base + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess (u_base + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess (u_base + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess (u_base + signExtend12 4064) = true) :
    -- Addback intermediates
    let upc0 := u0 + (signExtend12 0 : Word)
    let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0 := upc0 + v0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let aco0 := ac1_0 ||| ac2_0
    let upc1 := u1 + aco0
    let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
    let aun1 := upc1 + v1
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let aco1 := ac1_1 ||| ac2_1
    let upc2 := u2 + aco1
    let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
    let aun2 := upc2 + v2
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let aco2 := ac1_2 ||| ac2_2
    let upc3 := u3 + aco2
    let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
    let aun3 := upc3 + v3
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let aco3 := ac1_3 ||| ac2_3
    let aun4 := u4 + aco3
    let q_hat' := q_hat + signExtend12 4095
    cpsTriple (base + 728) (base + 880) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ borrow) **
       (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ aco3) **
       (.x11 ↦ᵣ q_hat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4)) := by
  intro upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 q_hat'
  -- BEQ x7 x0 152 at base+728
  have hbeq := beq_spec_gen .x7 .x0 (152 : BitVec 13) borrow 0 (base + 728)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 70 _ _ (by native_decide) (by bv_addr) (by native_decide)) hbeq
  -- Eliminate taken path (⌜borrow = 0⌝ contradicts hb)
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hb hpure)
  -- Strip pure fact from not-taken postcondition
  have ntaken_clean : cpsTriple (base + 728) (base + 732) (divCode base)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      ntaken
  -- Frame ntaken with all addback state
  have ntaken_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) **
     (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u4))
    (by pcFree) ntaken_clean
  -- Compose with addback_full (base+732 → base+880)
  have AB := divK_addback_full_spec sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4
    borrow v5_old v2_old base hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  dsimp only [] at AB
  seqFrame ntaken_framed AB
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    ntaken_framedAB

-- ============================================================================
-- Section 7: Save j + trial load composition
-- Instrs [0]-[12] at base+448 → base+500.
-- ============================================================================

private theorem lb_save_j (base : Word) : (base + 448 : Word) + 4 = base + 452 := by bv_addr
private theorem lb_trial_load (base : Word) : (base + 452 : Word) + 48 = base + 500 := by bv_addr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Save j + trial load: save j to memory, then load u_hi, u_lo, v_top for trial quotient.
    13 instructions, loop body indices [0]-[12].
    Entry: base+448, Exit: base+500, CodeReq: divCode base. -/
theorem divK_save_trial_load_spec
    (sp j n j_old v5_old v6_old v7_old v10_old u_hi u_lo v_top : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 500) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3976 ↦ₘ j_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtop_base) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro u_addr vtop_base
  -- 1. Save j: instr [0] at base+448
  have SJ := divK_save_j_spec sp j j_old (base + 448) hv_j
  rw [lb_save_j] at SJ
  have SJe := cpsTriple_extend_code (hmono :=
    lb_sub base 0 _ _ (by native_decide) (by bv_addr) (by native_decide)) SJ
  -- Frame save_j with trial_load state
  have SJf := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
     (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
     (vtop_base + signExtend12 32 ↦ₘ v_top))
    (by pcFree) SJe
  -- 2. Trial load: instrs [1]-[12] at base+452
  have TL := divK_trial_load_spec sp j n v5_old v6_old v7_old v10_old u_hi u_lo v_top
    (base + 452) hv_n1 hv_uhi hv_ulo hv_vtop
  dsimp only [] at TL
  rw [lb_trial_load] at TL
  have TLe := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 1 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 2 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 3 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 4 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 5 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 6 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 7 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 8 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 9 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 10 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 11 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 12 _ _ (by native_decide) (by bv_addr) (by native_decide))))))))))))) TL
  -- 3. Compose save_j + trial_load
  seqFrame SJf TLe
  -- Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

-- ============================================================================
-- Section 8: Trial quotient BLTU branch + div128/max composition
-- After trial_load (base+500): x7=u_hi, x10=v_top, x5=u_lo.
-- BLTU x7 x10 12 at base+500:
--   Taken (u_hi < v_top) → base+512: JAL x2 556 → div128 → base+516, x11=q
--   Not-taken (u_hi >= v_top) → base+504: ADDI x11 x0 4095 + JAL x0 8 → base+516
-- ============================================================================

-- Address normalization for trial quotient
private theorem lb_bltu_taken (base : Word) : (base + 500 : Word) + signExtend13 (12 : BitVec 13) = base + 512 := by
  have : signExtend13 (12 : BitVec 13) = (12 : Word) := by native_decide
  rw [this]; bv_addr
private theorem lb_bltu_ntaken (base : Word) : (base + 500 : Word) + 4 = base + 504 := by bv_addr
private theorem lb_trial_max_end (base : Word) : (base + 504 : Word) + 12 = base + 516 := by bv_addr
private theorem lb_jal_target (base : Word) : (base + 512 : Word) + signExtend21 (556 : BitVec 21) = base + 1068 := by
  have : signExtend21 (556 : BitVec 21) = (556 : Word) := by native_decide
  rw [this]; bv_addr
private theorem lb_jal_ret (base : Word) : (base + 512 : Word) + 4 = base + 516 := by bv_addr

-- ============================================================================
-- Section 8a: Trial quotient NOT-TAKEN path (u_hi >= v_top)
-- Instrs [14]-[15] at base+504: ADDI x11 x0 4095 + JAL x0 8 → base+516.
-- ============================================================================

/-- Trial quotient MAX path: q_hat = MAX64, skip div128 call.
    2 instructions at base+504. Entry: base+504, Exit: base+516. -/
private theorem divK_trial_max_extended (v11_old : Word) (base : Word) :
    cpsTriple (base + 504) (base + 516) (divCode base)
      ((.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ 0))
      ((.x11 ↦ᵣ signExtend12 4095) ** (.x0 ↦ᵣ 0)) := by
  have TM := divK_trial_max_spec v11_old (base + 504)
  dsimp only [] at TM
  rw [lb_trial_max_end] at TM
  exact cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 14 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 15 _ _ (by native_decide) (by bv_addr) (by native_decide))) TM

-- ============================================================================
-- Section 8b: Trial quotient TAKEN path (u_hi < v_top)
-- Instr [16] JAL x2 556 at base+512 → div128 at base+1068 → returns to base+516.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Trial call path: JAL x2 556 (instr [16]) + div128 subroutine.
    Entry: base+512, Exit: base+516, CodeReq: divCode base.
    Computes q_hat = div128(u_hi, u_lo, v_top). -/
theorem divK_trial_call_path_spec
    (sp j u_lo u_hi v_top vtop_base : Word) (base : Word)
    (v2_old v11_old : Word)
    (ret_mem d_mem dlo_mem un0_mem : Word)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516) :
    -- div128 intermediates (same as div128_spec)
    let d_hi := v_top >>> (32 : BitVec 6).toNat
    let d_lo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTriple (base + 512) (base + 516) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtop_base) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (.x2 ↦ᵣ v2_old) ** (.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ rhat2_un0) **
       (.x5 ↦ᵣ q0') ** (.x6 ↦ᵣ d_hi) **
       (.x7 ↦ᵣ q0_dlo) ** (.x10 ↦ᵣ q1') **
       (.x2 ↦ᵣ (base + 516)) ** (.x11 ↦ᵣ q) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro d_hi d_lo un1 un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q
  -- 1. JAL x2 556 at base+512: x2 ← base+516, PC → base+1068
  have J := jal_spec .x2 v2_old (556 : BitVec 21) (base + 512) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTriple_extend_code (hmono :=
    lb_sub base 16 _ _ (by native_decide) (by bv_addr) (by native_decide)) J
  -- 2. div128 subroutine: base+1068 → base+516
  have D := div128_spec sp (base + 516) v_top u_lo u_hi base
    j vtop_base v11_old ret_mem d_mem dlo_mem un0_mem
    hv_ret hv_d hv_dlo hv_un0 halign
  dsimp only [] at D
  -- 3. Frame JAL with all registers/memory for div128
  have Jf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
     (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtop_base) **
     (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
     (.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) **
     (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) **
     (sp + signExtend12 3944 ↦ₘ un0_mem))
    (by pcFree) Je
  -- 4. Compose JAL + div128
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) Jf D
  -- 5. Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

-- ============================================================================
-- Section 9: Store q[j] + loop control
-- Store q[j] at instrs [108]-[111] (base+880→base+896).
-- Loop control at instrs [112]-[113] (base+896): j--, BGE back to base+448 or exit base+904.
-- ============================================================================

-- Address normalization for store_qj and loop control
private theorem lb_sqj (base : Word) : (base + 880 : Word) + 16 = base + 896 := by bv_addr
private theorem lb_lc_taken (base : Word) :
    (base + 896 : Word) + 4 + signExtend13 (7740 : BitVec 13) = base + 448 := by
  have : signExtend13 (7740 : BitVec 13) = (18446744073709551164 : Word) := by native_decide
  rw [this]; bv_addr
private theorem lb_lc_exit (base : Word) : (base + 896 : Word) + 8 = base + 904 := by bv_addr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Store q[j] + loop control: store quotient digit, decrement j, branch back or exit.
    6 instructions, loop body indices [108]-[113].
    Entry: base+880. Taken exit: base+448 (loop back). Not-taken exit: base+904 (exit loop).
    CodeReq: divCode base. -/
theorem divK_store_loop_spec
    (sp j q_hat v5_old v7_old q_old : Word)
    (base : Word)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - j_x8
    let j' := j + signExtend12 4095
    cpsBranch (base + 880) (divCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (q_addr ↦ₘ q_old))
      (base + 448)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) ** (.x0 ↦ᵣ (0 : Word)) **
       (q_addr ↦ₘ q_hat))
      (base + 904)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) ** (.x0 ↦ᵣ (0 : Word)) **
       (q_addr ↦ₘ q_hat)) := by
  intro j_x8 q_addr j'
  -- 1. Store q[j]: instrs [108]-[111] at base+880
  have SQ := divK_store_qj_spec sp j q_hat v5_old v7_old q_old (base + 880) hv_q
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 108 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 109 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (lb_sub base 110 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 111 _ _ (by native_decide) (by bv_addr) (by native_decide))))) SQ
  -- 2. Loop control: instrs [112]-[113] at base+896
  have LC := divK_loop_control_spec j (7740 : BitVec 13) (base + 896)
  dsimp only [] at LC
  rw [lb_lc_taken, lb_lc_exit] at LC
  have LCe := cpsBranch_extend_code (hmono := by
    exact CodeReq_union_sub (lb_sub base 112 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (lb_sub base 113 _ _ (by native_decide) (by bv_addr) (by native_decide))) LC
  -- 3. Add x0 to store_qj via frame, then reshape via consequence
  have SQx0 : cpsTriple (base + 880) (base + 896) (divCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) ** (q_addr ↦ₘ q_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) ** (.x0 ↦ᵣ (0 : Word)) ** (q_addr ↦ₘ q_hat)) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frame_left _ _ _ _ _ (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  -- 4. Frame loop_control with store_qj postcondition atoms, then reshape
  have LCp : cpsBranch (base + 896) (divCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) ** (.x0 ↦ᵣ (0 : Word)) ** (q_addr ↦ₘ q_hat))
      (base + 448)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) ** (.x0 ↦ᵣ (0 : Word)) ** (q_addr ↦ₘ q_hat))
      (base + 904)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) ** (.x0 ↦ᵣ (0 : Word)) ** (q_addr ↦ₘ q_hat)) :=
    cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frame_left _ _ _ _ _ _ _
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
         (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ q_addr) **
         (q_addr ↦ₘ q_hat))
        (by pcFree) LCe)
  -- 5. Compose store_qj(+x0) → loop_control(reshaped)
  exact cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => hp) SQx0 LCp

-- ============================================================================
-- Section 10: Mulsub + correction_skip composition (borrow = 0 path)
-- Takes borrow as an explicit parameter (not let-bound) to enable rw.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
/-- Mulsub + correction skip: when mulsub produces borrow=0, skip addback.
    Takes borrow as explicit parameter to avoid let-binding expansion issues.
    Entry: base+516, Exit: base+880, CodeReq: divCode base. -/
theorem divK_mulsub_correction_skip_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- Mulsub intermediates
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    -- Hypothesis: mulsub borrow = 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 516) (base + 880) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x2 ↦ᵣ v2_old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
       ((u_base + signExtend12 4064) ↦ₘ u4_new)) := by
  intro u_base
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        hborrow
  -- 1. Mulsub full (base+516 → base+728)
  have MS := divK_mulsub_full_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    v1_old v5_old v6_old v7_old v10_old v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  dsimp only [] at MS hborrow
  -- 2. Rewrite borrow to 0 in mulsub postcondition
  rw [hborrow] at MS
  -- 3. Correction skip (base+728 → base+880)
  have CS := divK_correction_skip_spec sp u_base q_hat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base
  -- 4. Compose mulsub(borrow=0) + correction_skip
  seqFrame MS CS
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    MSCS

-- ============================================================================
-- Section 10b: Mulsub + correction_addback composition (borrow ≠ 0 path)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
/-- Mulsub + correction addback: when mulsub produces borrow≠0, run addback.
    Entry: base+516, Exit: base+880, CodeReq: divCode base. -/
theorem divK_mulsub_correction_addback_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- Mulsub intermediates
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    -- Addback intermediates
    let upc0 := un0 + (signExtend12 0 : Word)
    let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0 := upc0 + v0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let aco0 := ac1_0 ||| ac2_0
    let upc1 := un1 + aco0
    let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
    let aun1 := upc1 + v1
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let aco1 := ac1_1 ||| ac2_1
    let upc2 := un2 + aco1
    let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
    let aun2 := upc2 + v2
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let aco2 := ac1_2 ||| ac2_2
    let upc3 := un3 + aco2
    let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
    let aun3 := upc3 + v3
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let aco3 := ac1_3 ||| ac2_3
    let aun4 := u4_new + aco3
    let q_hat' := q_hat + signExtend12 4095
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 516) (base + 880) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x1 ↦ᵣ v1_old) ** (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x2 ↦ᵣ v2_old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat') **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ aun4) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ aco3) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4)) := by
  intro u_base
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 q_hat'
        hborrow
  -- 1. Mulsub full (base+516 → base+728)
  have MS := divK_mulsub_full_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    v1_old v5_old v6_old v7_old v10_old v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  dsimp only [] at MS hborrow
  -- 2. Correction addback (base+728 → base+880) with borrow ≠ 0
  have CA := divK_correction_addback_spec sp u_base
    (if BitVec.ult u_top c3 then (1 : Word) else 0)
    q_hat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base hborrow
    hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  dsimp only [] at CA
  -- 3. Compose mulsub + correction_addback
  seqFrame MS CA
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    MSCA

-- ============================================================================
-- Section 11: Trial quotient max path (BLTU not-taken)
-- Composes: save_trial_load → BLTU ntaken → trial_max.
-- Entry: base+448, Exit: base+516 with x11 = MAX64.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Trial quotient max path: save j + load + BLTU not-taken + trial_max.
    When u_hi >= v_top, sets q_hat = MAX64 without calling div128.
    Entry: base+448, Exit: base+516, CodeReq: divCode base. -/
theorem divK_trial_max_full_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old u_hi u_lo v_top : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hbltu : ¬BitVec.ult u_hi v_top) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 516) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtop_base) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) ** (.x11 ↦ᵣ signExtend12 4095) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top)) := by
  intro u_addr vtop_base
  -- 1. Save j + trial load (base+448 → base+500)
  have STL := divK_save_trial_load_spec sp j n j_old v5_old v6_old v7_old v10_old u_hi u_lo v_top
    base hv_j hv_n1 hv_uhi hv_ulo hv_vtop
  dsimp only [] at STL
  -- 2. BLTU x7 x10 12 at base+500
  have hbltu_raw := bltu_spec_gen .x7 .x10 (12 : BitVec 13) u_hi v_top (base + 500)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 13 _ _ (by native_decide) (by bv_addr) (by native_decide)) hbltu_raw
  -- Eliminate taken path (⌜BitVec.ult u_hi v_top⌝ contradicts hbltu)
  have ntaken := cpsBranch_elim_ntaken _ _ _ _ _ _ _ hbltu_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hbltu hpure)
  -- Strip pure fact
  have ntaken_clean := cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp) ntaken
  -- 3. Trial max (base+504 → base+516)
  have TM := divK_trial_max_extended v11_old base
  -- 4. Frame save_trial_load with x11 + x0, compose with BLTU ntaken
  have STLf := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) STL
  seqFrame STLf ntaken_clean
  -- 5. Frame BLTU ntaken result with x0 + memory, compose with trial_max
  seqFrame STLfntaken_clean TM
  -- 6. Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    STLfntaken_cleanTM

-- ============================================================================
-- Section 11b: Trial quotient call path (BLTU taken): save + load + BLTU + JAL + div128
-- When u_hi < v_top, calls div128 to compute the trial quotient.
-- Entry: base+448, Exit: base+516, CodeReq: divCode base.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
/-- Trial quotient call path: save j + load + BLTU taken + JAL + div128.
    When u_hi < v_top, computes q_hat = div128(u_hi, u_lo, v_top).
    Entry: base+448, Exit: base+516, CodeReq: divCode base. -/
theorem divK_trial_call_full_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old u_hi u_lo v_top : Word)
    (ret_mem d_mem dlo_mem un0_mem : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u_hi v_top) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let d_hi := v_top >>> (32 : BitVec 6).toNat
    let d_lo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0_div := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0_div
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTriple (base + 448) (base + 516) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ rhat2_un0) **
       (.x5 ↦ᵣ q0') ** (.x6 ↦ᵣ d_hi) **
       (.x7 ↦ᵣ q0_dlo) ** (.x10 ↦ᵣ q1') ** (.x11 ↦ᵣ q) **
       (.x2 ↦ᵣ (base + 516)) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ un0_div)) := by
  intro u_addr vtop_base
        d_hi d_lo un1 un0_div q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q
  -- 1. Save j + trial load (base+448 → base+500)
  have STL := divK_save_trial_load_spec sp j n j_old v5_old v6_old v7_old v10_old u_hi u_lo v_top
    base hv_j hv_n1 hv_uhi hv_ulo hv_vtop
  dsimp only [] at STL
  -- 2. BLTU x7 x10 12 at base+500
  have hbltu_raw := bltu_spec_gen .x7 .x10 (12 : BitVec 13) u_hi v_top (base + 500)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 13 _ _ (by native_decide) (by bv_addr) (by native_decide)) hbltu_raw
  -- Eliminate ntaken path (⌜¬BitVec.ult u_hi v_top⌝ contradicts hbltu)
  have taken := cpsBranch_elim_taken _ _ _ _ _ _ _ hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  -- Strip pure fact from taken postcondition
  have taken_clean := cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp) taken
  -- 3. Trial call path (base+512 → base+516)
  have TCP := divK_trial_call_path_spec sp j u_lo u_hi v_top vtop_base base
    v2_old v11_old ret_mem d_mem dlo_mem un0_mem
    hv_ret hv_d hv_dlo hv_un0 halign
  dsimp only [] at TCP
  -- 4. Frame save_trial_load with x2, x11, x0, scratch memory
  have STLf := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11_old) ** (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) **
     (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) **
     (sp + signExtend12 3944 ↦ₘ un0_mem))
    (by pcFree) STL
  -- 5. Compose save_trial_load + BLTU taken
  seqFrame STLf taken_clean
  -- 6. Compose (save_trial_load + BLTU) + trial_call_path
  seqFrame STLftaken_clean TCP
  -- 7. Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    STLftaken_cleanTCP

-- ============================================================================
-- Section 12: Full loop body cpsBranch (BLTU not-taken, BEQ skip path)
-- Uses intro_lets instead of dsimp to preserve let-bound abbreviations.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU ntaken + BEQ skip): trial quotient MAX path + mulsub (no addback)
    + store q[j] + loop control. Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_max_skip_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old
     u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u_hi v_top) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let q_hat := signExtend12 4095  -- MAX64
    -- Mulsub intermediates
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) = (0 : Word) →
    cpsBranch (base + 448) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      -- Taken exit: loop back to base+448
      (base + 448)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat) **
       (.x2 ↦ᵣ un3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
       ((u_base + signExtend12 4064) ↦ₘ u4_new) **
       (q_addr ↦ₘ q_hat))
      -- Not-taken exit: exit loop to base+904
      (base + 904)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat) **
       (.x2 ↦ᵣ un3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
       ((u_base + signExtend12 4064) ↦ₘ u4_new) **
       (q_addr ↦ₘ q_hat)) := by
  intro u_addr vtop_base u_base q_hat
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        j' q_addr hborrow
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec sp j n j_old v5_old v6_old v7_old v10_old v11_old u_hi u_lo v_top
    base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  intro_lets at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    j u_lo vtop_base u_hi v_top v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store loop cpsBranch (base+880 → base+448/904)
  have SL := divK_store_loop_spec sp j q_hat u4_new (0 : Word) q_old base hv_q
  intro_lets at SL
  -- 4. Frame TF with mulsub memory + x2
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. TFfMCS0 already contains trial_load memory (from TF postcondition).
  -- No additional framing needed. Use TFfMCS0 directly as pre_store.
  let pre_store := TFfMCS0
  -- 7. Frame store_loop with ALL remaining atoms
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
     (vtop_base + signExtend12 32 ↦ₘ v_top))
    (by pcFree) SL
  -- 8. Compose pre_store (cpsTriple) with SLf (cpsBranch)
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) pre_store SLf
  -- 9. Permute final cpsBranch to match target
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 13: Full loop body cpsBranch (BLTU not-taken, BEQ addback path)
-- Same as Section 12 but uses mulsub_correction_addback instead of _skip.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU ntaken + BEQ addback): trial MAX + mulsub + addback
    + store q[j] + loop control. Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_max_addback_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old
     u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u_hi v_top) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let q_hat := signExtend12 4095
    -- Mulsub intermediates
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    -- Addback intermediates
    let upc0 := un0 + (signExtend12 0 : Word)
    let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0 := upc0 + v0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let aco0 := ac1_0 ||| ac2_0
    let upc1 := un1 + aco0
    let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
    let aun1 := upc1 + v1
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let aco1 := ac1_1 ||| ac2_1
    let upc2 := un2 + aco1
    let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
    let aun2 := upc2 + v2
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let aco2 := ac1_2 ||| ac2_2
    let upc3 := un3 + aco2
    let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
    let aun3 := upc3 + v3
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let aco3 := ac1_3 ||| ac2_3
    let aun4 := u4_new + aco3
    let q_hat' := q_hat + signExtend12 4095
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranch (base + 448) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (base + 448)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat') **
       (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4) **
       (q_addr ↦ₘ q_hat'))
      (base + 904)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat') **
       (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4) **
       (q_addr ↦ₘ q_hat')) := by
  intro u_addr vtop_base u_base q_hat
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 q_hat'
        j' q_addr hborrow
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec sp j n j_old v5_old v6_old v7_old v10_old v11_old u_hi u_lo v_top
    base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  intro_lets at TF
  -- 2. Mulsub + correction addback (base+516 → base+880)
  have MCA := divK_mulsub_correction_addback_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    j u_lo vtop_base u_hi v_top v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  -- 3. Store loop cpsBranch (base+880 → base+448/904)
  have SL := divK_store_loop_spec sp j q_hat' aun4 aco3 q_old base hv_q
  intro_lets at SL
  -- 4. Frame TF with mulsub+addback memory + x2
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. TFfMCA0 already contains trial_load memory — use directly
  let pre_store := TFfMCA0
  -- 7. Frame store_loop with ALL remaining atoms
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
     (vtop_base + signExtend12 32 ↦ₘ v_top))
    (by pcFree) SL
  -- 8. Compose pre_store + SLf
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) pre_store SLf
  -- 9. Permute final cpsBranch to match target
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 14: Full loop body cpsBranch (BLTU taken, BEQ skip path)
-- Trial quotient via div128 call, mulsub with no addback.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU taken + BEQ skip): trial quotient call path + mulsub (no addback)
    + store q[j] + loop control. Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_call_skip_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old
     u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u_hi v_top) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let d_hi := v_top >>> (32 : BitVec 6).toNat
    let d_lo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u_lo >>> (32 : BitVec 6).toNat
    let div_un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    -- Mulsub intermediates
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) = (0 : Word) →
    cpsBranch (base + 448) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      -- Taken exit: loop back to base+448
      (base + 448)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat) **
       (.x2 ↦ᵣ un3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
       ((u_base + signExtend12 4064) ↦ₘ u4_new) **
       (q_addr ↦ₘ q_hat) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      -- Not-taken exit: exit loop to base+904
      (base + 904)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat) **
       (.x2 ↦ᵣ un3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
       ((u_base + signExtend12 4064) ↦ₘ u4_new) **
       (q_addr ↦ₘ q_hat) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro u_addr vtop_base u_base
        d_hi d_lo div_un1 div_un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q_hat
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        j' q_addr hborrow
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_hi u_lo v_top ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  intro_lets at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516 : Word) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store loop cpsBranch (base+880 → base+448/904)
  have SL := divK_store_loop_spec sp j q_hat u4_new (0 : Word) q_old base hv_q
  intro_lets at SL
  -- 4. Frame TF with mulsub memory + q_addr
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Use composed result directly as pre_store
  let pre_store := TFfMCS0
  -- 7. Frame store_loop with ALL remaining atoms
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
     (vtop_base + signExtend12 32 ↦ₘ v_top) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v_top) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  -- 8. Compose pre_store (cpsTriple) with SLf (cpsBranch)
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) pre_store SLf
  -- 9. Permute final cpsBranch to match target
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 15: Full loop body cpsBranch (BLTU taken, BEQ addback path)
-- Trial quotient via div128 call, mulsub with addback correction.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU taken + BEQ addback): trial quotient call path + mulsub + addback
    + store q[j] + loop control. Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_call_addback_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old
     u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u_hi v_top) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let d_hi := v_top >>> (32 : BitVec 6).toNat
    let d_lo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u_lo >>> (32 : BitVec 6).toNat
    let div_un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    -- Mulsub intermediates
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    -- Addback intermediates
    let upc0 := un0 + (signExtend12 0 : Word)
    let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0 := upc0 + v0
    let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
    let aco0 := ac1_0 ||| ac2_0
    let upc1 := un1 + aco0
    let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
    let aun1 := upc1 + v1
    let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
    let aco1 := ac1_1 ||| ac2_1
    let upc2 := un2 + aco1
    let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
    let aun2 := upc2 + v2
    let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
    let aco2 := ac1_2 ||| ac2_2
    let upc3 := un3 + aco2
    let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
    let aun3 := upc3 + v3
    let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
    let aco3 := ac1_3 ||| ac2_3
    let aun4 := u4_new + aco3
    let q_hat' := q_hat + signExtend12 4095
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranch (base + 448) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (base + 448)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat') **
       (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4) **
       (q_addr ↦ₘ q_hat') **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      (base + 904)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
       (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_hat') **
       (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4) **
       (q_addr ↦ₘ q_hat') **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro u_addr vtop_base u_base
        d_hi d_lo div_un1 div_un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q_hat
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3 u4_new
        upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 q_hat'
        j' q_addr hborrow
  -- 1. Trial call full (base+448 → base+516)
  have TF := divK_trial_call_full_spec sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u_hi u_lo v_top ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  intro_lets at TF
  -- 2. Mulsub + correction addback (base+516 → base+880)
  have MCA := divK_mulsub_correction_addback_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516 : Word) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  -- 3. Store loop cpsBranch (base+880 → base+448/904)
  have SL := divK_store_loop_spec sp j q_hat' aun4 aco3 q_old base hv_q
  intro_lets at SL
  -- 4. Frame TF with mulsub+addback memory + q_addr
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCA0
  seqFrame TFf MCA0
  -- 6. Use composed result directly as pre_store
  let pre_store := TFfMCA0
  -- 7. Frame store_loop with ALL remaining atoms
  have SLf := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
     (vtop_base + signExtend12 32 ↦ₘ v_top) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v_top) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  -- 8. Compose pre_store + SLf
  have full := cpsTriple_seq_cpsBranch_with_perm_same_cr _ _ _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) pre_store SLf
  -- 9. Permute final cpsBranch to match target
  exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- Section 16: Combined loop body cpsBranch (all 4 paths unified)
-- Existentially quantifies over path-dependent outputs.
-- ============================================================================

/-- The postcondition of one loop body iteration: registers and memory
    after processing iteration j, with path-dependent values existentially quantified.
    Both cpsBranch exits share this postcondition (BGE only affects the target PC). -/
private def loopBodyPost
    (sp j n v0 v1 v2 v3 v_top u_hi u_lo : Word) : Assertion :=
  fun h =>
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    ∃ (x2v x10v x11v : Word)
      (un0v un1v un2v un3v u4v qv : Word)
      (retv dv dlov sunv : Word),
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
     (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
     (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
     (.x2 ↦ᵣ x2v) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
     (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
     (vtop_base + signExtend12 32 ↦ₘ v_top) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0v) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1v) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2v) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3v) **
     ((u_base + signExtend12 4064) ↦ₘ u4v) **
     (q_addr ↦ₘ qv) **
     (sp + signExtend12 3968 ↦ₘ retv) **
     (sp + signExtend12 3960 ↦ₘ dv) **
     (sp + signExtend12 3952 ↦ₘ dlov) **
     (sp + signExtend12 3944 ↦ₘ sunv)) h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Combined loop body: one iteration at base+448 with any trial quotient path
    and any correction path. Entry: base+448, cpsBranch to base+448/904.
    No case hypotheses needed — all paths handled internally.
    Both exits have the same postcondition (existentially quantified). -/
theorem divK_loop_body_combined_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old
     u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true) :
    let u_addr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtop_base := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsBranch (base + 448) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (u_addr ↦ₘ u_hi) ** ((u_addr + 8) ↦ₘ u_lo) **
       (vtop_base + signExtend12 32 ↦ₘ v_top) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (base + 448)
      (loopBodyPost sp j n v0 v1 v2 v3 v_top u_hi u_lo)
      (base + 904)
      (loopBodyPost sp j n v0 v1 v2 v3 v_top u_hi u_lo) := by
  intro u_addr vtop_base u_base q_addr
  by_cases hbltu : BitVec.ult u_hi v_top
  · -- BLTU taken: div128 call path
    -- Compute all div128 intermediates (determined by u_hi, u_lo, v_top)
    let d_hi := v_top >>> (32 : BitVec 6).toNat
    let d_lo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u_lo >>> (32 : BitVec 6).toNat
    let div_un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    -- Compute mulsub intermediates
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    let borrow := if BitVec.ult u_top c3 then (1 : Word) else 0
    by_cases hborrow : borrow = (0 : Word)
    · -- Call + skip (borrow = 0)
      have HS := divK_loop_body_call_skip_spec sp j n j_old v5_old v6_old v7_old v10_old
        v11_old v2_old u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old
        ret_mem d_mem dlo_mem scratch_un0 base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
        hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
      dsimp only [] at HS
      have HS0 := HS hborrow
      exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
        (fun h hp => by xperm_hyp hp)
        (fun h hp => ⟨un3, c3, q_hat, un0, un1, un2, un3, u4_new, q_hat,
          base + 516, v_top, d_lo, div_un0, by xperm_hyp hp⟩)
        (fun h hp => ⟨un3, c3, q_hat, un0, un1, un2, un3, u4_new, q_hat,
          base + 516, v_top, d_lo, div_un0, by xperm_hyp hp⟩)
        HS0
    · -- Call + addback (borrow ≠ 0)
      -- Addback intermediates
      let upc0 := un0 + (signExtend12 0 : Word)
      let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
      let aun0 := upc0 + v0
      let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
      let aco0 := ac1_0 ||| ac2_0
      let upc1 := un1 + aco0
      let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
      let aun1 := upc1 + v1
      let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
      let aco1 := ac1_1 ||| ac2_1
      let upc2 := un2 + aco1
      let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
      let aun2 := upc2 + v2
      let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
      let aco2 := ac1_2 ||| ac2_2
      let upc3 := un3 + aco2
      let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
      let aun3 := upc3 + v3
      let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
      let aco3 := ac1_3 ||| ac2_3
      let aun4 := u4_new + aco3
      let q_hat' := q_hat + signExtend12 4095
      have HA := divK_loop_body_call_addback_spec sp j n j_old v5_old v6_old v7_old v10_old
        v11_old v2_old u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old
        ret_mem d_mem dlo_mem scratch_un0 base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
        hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
      dsimp only [] at HA
      have HA0 := HA hborrow
      exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
        (fun h hp => by xperm_hyp hp)
        (fun h hp => ⟨aun3, c3, q_hat', aun0, aun1, aun2, aun3, aun4, q_hat',
          base + 516, v_top, d_lo, div_un0, by xperm_hyp hp⟩)
        (fun h hp => ⟨aun3, c3, q_hat', aun0, aun1, aun2, aun3, aun4, q_hat',
          base + 516, v_top, d_lo, div_un0, by xperm_hyp hp⟩)
        HA0
  · -- BLTU not taken: max path
    let q_hat := signExtend12 (4095 : BitVec 12)
    -- Compute mulsub intermediates with q_hat = MAX64
    let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0; let c0 := pc0 + bs0
    let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1; let c1 := pc1 + bs1
    let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2; let c2 := pc2 + bs2
    let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3; let c3 := pc3 + bs3
    let u4_new := u_top - c3
    let borrow := if BitVec.ult u_top c3 then (1 : Word) else 0
    by_cases hborrow : borrow = (0 : Word)
    · -- Max + skip (borrow = 0)
      have HS := divK_loop_body_max_skip_spec sp j n j_old v5_old v6_old v7_old v10_old
        v11_old v2_old u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop
        hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
      dsimp only [] at HS
      have HS0 := HS hborrow
      -- Frame with scratch memory (max path doesn't include it)
      have HSf := cpsBranch_frame_left _ _ _ _ _ _ _
        ((sp + signExtend12 3968 ↦ₘ ret_mem) **
         (sp + signExtend12 3960 ↦ₘ d_mem) **
         (sp + signExtend12 3952 ↦ₘ dlo_mem) **
         (sp + signExtend12 3944 ↦ₘ scratch_un0))
        (by pcFree) HS0
      exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
        (fun h hp => by xperm_hyp hp)
        (fun h hp => ⟨un3, c3, q_hat, un0, un1, un2, un3, u4_new, q_hat,
          ret_mem, d_mem, dlo_mem, scratch_un0, by xperm_hyp hp⟩)
        (fun h hp => ⟨un3, c3, q_hat, un0, un1, un2, un3, u4_new, q_hat,
          ret_mem, d_mem, dlo_mem, scratch_un0, by xperm_hyp hp⟩)
        HSf
    · -- Max + addback (borrow ≠ 0)
      let upc0 := un0 + (signExtend12 0 : Word)
      let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
      let aun0 := upc0 + v0
      let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
      let aco0 := ac1_0 ||| ac2_0
      let upc1 := un1 + aco0
      let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
      let aun1 := upc1 + v1
      let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
      let aco1 := ac1_1 ||| ac2_1
      let upc2 := un2 + aco1
      let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
      let aun2 := upc2 + v2
      let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
      let aco2 := ac1_2 ||| ac2_2
      let upc3 := un3 + aco2
      let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
      let aun3 := upc3 + v3
      let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
      let aco3 := ac1_3 ||| ac2_3
      let aun4 := u4_new + aco3
      let q_hat' := q_hat + signExtend12 4095
      have HA := divK_loop_body_max_addback_spec sp j n j_old v5_old v6_old v7_old v10_old
        v11_old v2_old u_hi u_lo v_top v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
        hv_j hv_n1 hv_uhi hv_ulo hv_vtop
        hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
      dsimp only [] at HA
      have HA0 := HA hborrow
      have HAf := cpsBranch_frame_left _ _ _ _ _ _ _
        ((sp + signExtend12 3968 ↦ₘ ret_mem) **
         (sp + signExtend12 3960 ↦ₘ d_mem) **
         (sp + signExtend12 3952 ↦ₘ dlo_mem) **
         (sp + signExtend12 3944 ↦ₘ scratch_un0))
        (by pcFree) HA0
      exact cpsBranch_consequence _ _ _ _ _ _ _ _ _ _
        (fun h hp => by xperm_hyp hp)
        (fun h hp => ⟨aun3, c3, q_hat', aun0, aun1, aun2, aun3, aun4, q_hat',
          ret_mem, d_mem, dlo_mem, scratch_un0, by xperm_hyp hp⟩)
        (fun h hp => ⟨aun3, c3, q_hat', aun0, aun1, aun2, aun3, aun4, q_hat',
          ret_mem, d_mem, dlo_mem, scratch_un0, by xperm_hyp hp⟩)
        HAf

end EvmAsm.Rv64
