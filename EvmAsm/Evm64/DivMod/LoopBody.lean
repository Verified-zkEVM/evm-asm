-- file-size-exception: tracked by issues #283/#266 (skip/addback unification + DIV/MOD loop factoring). Grandfathered pending consolidation.
/-
  EvmAsm.Evm64.DivMod.LoopBody

  Hierarchical composition of the 114-instruction Knuth Algorithm D main loop body.
  Composes sub-specs from LimbSpec.lean into a single cpsBranch for one iteration,
  then proves the inductive loop spec via cpsTriple_loop_with_perm.

  Issue #87: DIV/MOD loop body composition.
-/

import EvmAsm.Evm64.DivMod.Compose
import EvmAsm.Evm64.DivMod.LoopDefs
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se13_12 se13_156 se13_7736 se13_8044 se21_560)

-- ============================================================================
-- Section 1: CodeReq subsumption infrastructure for loop body instructions
-- ============================================================================

/-- The loopBody ofProg (block 8) is subsumed by sharedDivModCode. -/
private theorem divK_loopBody_ofProg_sub_sharedCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (sharedDivModCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: singleton at index k of divK_loopBody ⊆ sharedDivModCode base. -/
private theorem lb_sub (base : Word) (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 560 7736).length)
    (h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_sharedCode base a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + loopBodyOff) (divK_loopBody 560 7736) k hk (by decide)) a i h)

/-- Helper: combine two subsumption proofs over a union. -/
-- `CodeReq.union_sub` — use `CodeReq.union_sub` from `Rv64/SepLogic.lean` (shared).

-- ============================================================================
-- Section 2: Address normalization lemmas
-- Loop body base = base + loopBodyOff.
-- Instruction [k] is at base + loopBodyOff + 4*k.
-- ============================================================================

-- Mulsub limb base addresses (instrs [22]-[65])
private theorem lb_ms1 (base : Word) : (base + 536 : Word) + 44 = base + 580 := by bv_addr
private theorem lb_ms2 (base : Word) : (base + 580 : Word) + 44 = base + 624 := by bv_addr
private theorem lb_ms3 (base : Word) : (base + 624 : Word) + 44 = base + 668 := by bv_addr
private theorem lb_ms_end (base : Word) : (base + 668 : Word) + 44 = base + 712 := by bv_addr

-- ============================================================================
-- Section 3: Mulsub 4-limbs composition
-- Composes 4 × divK_mulsub_limb_spec using seqFrame for automatic framing.
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Multiply-subtract all 4 limbs: u[j+k] -= q_hat * v[k] for k=0..3 with carry chain.
    44 instructions, loop body indices [22]-[65].
    Entry: base+536, Exit: base+712, CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_4limbs_spec
    (sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (v5_init v7_init v2_init : Word)
    (base : Word) :
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
    cpsTriple (base + 536) (base + 712) (sharedDivModCode base)
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

  rw [lb_ms1] at L0
  have L0e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 22 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 23 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 24 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 25 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 26 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 27 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 28 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 29 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 30 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 31 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 32 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L0
  -- Limb 1: instrs [33]-[43] at base+580
  have L1 := divK_mulsub_limb_spec sp u_base q_hat c0
    bs0 fs0 un0 v1 u1 40 4088 (base + 580)

  rw [lb_ms2] at L1
  have L1e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 33 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 34 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 35 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 36 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 37 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 38 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 39 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 40 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 41 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 42 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 43 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L1
  -- Frame L0 with memory for limbs 1-3 (so seqFrame can find L1's precondition atoms)
  have L0f := cpsTriple_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3))
    (by pcFree) L0e
  -- Compose L0 + L1
  seqFrame L0f L1e
  -- Limb 2: instrs [44]-[54] at base+624
  have L2 := divK_mulsub_limb_spec sp u_base q_hat c1
    bs1 fs1 un1 v2 u2 48 4080 (base + 624)

  rw [lb_ms3] at L2
  have L2e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 44 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 45 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 46 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 47 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 48 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 49 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 50 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 51 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 52 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 53 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 54 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L2
  -- Compose (L0+L1) + L2
  seqFrame L0fL1e L2e
  -- Limb 3: instrs [55]-[65] at base+668
  have L3 := divK_mulsub_limb_spec sp u_base q_hat c2
    bs2 fs2 un2 v3 u3 56 4072 (base + 668)

  rw [lb_ms_end] at L3
  have L3e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 55 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 56 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 57 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 58 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 59 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 60 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 61 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 62 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 63 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 64 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 65 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L3
  -- Compose (L0+L1+L2) + L3
  seqFrame L0fL1eL2e L3e
  -- Final permutation to match goal pre/postcondition order
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    L0fL1eL2eL3e

-- ============================================================================
-- Section 4: Addback full composition
-- Composes addback_init + 4 × addback_limb + addback_final.
-- 37 instructions at loop body indices [71]-[107].
-- Entry: base+732, Exit: base+880, CodeReq: sharedDivModCode base.
-- ============================================================================

-- Addback base addresses (instrs [71]-[107])
private theorem lb_ab0 (base : Word) : (base + 732 : Word) + 4 = base + 736 := by bv_addr
private theorem lb_ab0_end (base : Word) : (base + 736 : Word) + 32 = base + 768 := by bv_addr
private theorem lb_ab1_end (base : Word) : (base + 768 : Word) + 32 = base + 800 := by bv_addr
private theorem lb_ab2_end (base : Word) : (base + 800 : Word) + 32 = base + 832 := by bv_addr
private theorem lb_ab3_end (base : Word) : (base + 832 : Word) + 32 = base + 864 := by bv_addr
private theorem lb_abf_end (base : Word) : (base + 864 : Word) + 16 = base + 880 := by bv_addr

set_option maxRecDepth 4096 in
/-- Full add-back correction: init carry + 4 limb corrections + final u[j+4] adjust + q_hat--.
    37 instructions, loop body indices [71]-[107].
    Entry: base+732, Exit: base+880, CodeReq: sharedDivModCode base. -/
theorem divK_addback_full_spec
    (sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word) :
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
    cpsTriple (base + 732) (base + 880) (sharedDivModCode base)
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
    exact lb_sub base 71 _ _ (by decide) (by bv_addr) (by decide)) I
  -- Frame init with all addback state
  have If := cpsTriple_frameR
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
    v5_init v2_init v0 u0 32 0 (base + 736)
  rw [lb_ab0_end] at A0
  have A0e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 72 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 73 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 74 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 75 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 76 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 77 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 78 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 79 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A0
  -- Compose init + limb 0
  seqFrame If A0e
  -- Limb 1: instrs [80]-[87] at base+768
  have A1 := divK_addback_limb_spec sp u_base aco0
    ac2_0 aun0 v1 u1 40 4088 (base + 768)
  rw [lb_ab1_end] at A1
  have A1e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 80 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 81 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 82 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 83 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 84 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 85 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 86 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 87 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A1
  seqFrame IfA0e A1e
  -- Limb 2: instrs [88]-[95] at base+800
  have A2 := divK_addback_limb_spec sp u_base aco1
    ac2_1 aun1 v2 u2 48 4080 (base + 800)
  rw [lb_ab2_end] at A2
  have A2e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 88 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 89 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 90 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 91 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 92 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 93 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 94 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 95 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A2
  seqFrame IfA0eA1e A2e
  -- Limb 3: instrs [96]-[103] at base+832
  have A3 := divK_addback_limb_spec sp u_base aco2
    ac2_2 aun2 v3 u3 56 4072 (base + 832)
  rw [lb_ab3_end] at A3
  have A3e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 96 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 97 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 98 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 99 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 100 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 101 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 102 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 103 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A3
  seqFrame IfA0eA1eA2e A3e
  -- Final: instrs [104]-[107] at base+864
  have AF := divK_addback_final_spec u_base aco3 q_hat ac2_3 u4 4064 (base + 864)
  rw [lb_abf_end] at AF
  have AFe := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 104 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 105 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 106 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 107 _ _ (by decide) (by bv_addr) (by decide)))))
    AF
  seqFrame IfA0eA1eA2eA3e AFe
  -- Final permutation
  exact cpsTriple_weaken
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
/-- Mulsub full: setup + 4-limb multiply-subtract + carry subtraction from u[j+4].
    53 instructions, loop body indices [17]-[69].
    Entry: base+516, Exit: base+728, CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_full_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word) :
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
    cpsTriple (base + 516) (base + 728) (sharedDivModCode base)
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
  have S := divK_mulsub_setup_spec sp q_hat j v1_old v5_old v6_old v10_old (base + 516)
  rw [lb_ms_setup] at S
  have Se := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 17 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 18 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 19 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 20 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 21 _ _ (by decide) (by bv_addr) (by decide)))))) S
  -- Frame setup with all memory + x7/x2 for mulsub
  have Sf := cpsTriple_frameR
    ((.x7 ↦ᵣ v7_old) ** (.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u_top))
    (by pcFree) Se
  -- 2. Mulsub 4 limbs: instrs [22]-[65] at base+536
  have M := divK_mulsub_4limbs_spec sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3
    (j <<< (3 : BitVec 6).toNat) v7_old v2_old base
  intro_lets at M
  -- Compose setup + mulsub
  seqFrame Sf M
  -- 3. Sub-carry: instrs [66]-[69] at base+712
  have SC := divK_sub_carry_spec u_base c3 bs3 fs3 u_top 4064 (base + 712)
  rw [lb_sc] at SC
  have SCe := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 66 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 67 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 68 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 69 _ _ (by decide) (by bv_addr) (by decide))))) SC
  -- Compose (setup+mulsub) + sub_carry
  seqFrame SfM SCe
  -- Final permutation
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SfMSCe

-- ============================================================================
-- Section 6: Correction branch address normalization
-- BEQ at instr [70] (base+728): taken → base+884, not-taken → base+732.
-- ============================================================================

private theorem lb_beq_taken (base : Word) : (base + 728 : Word) + signExtend13 (156 : BitVec 13) = base + 884 := by
  rw [se13_156]; bv_addr

private theorem lb_beq_ntaken (base : Word) : (base + 728 : Word) + 4 = base + 732 := by bv_addr

-- ============================================================================
-- Section 6a: Correction skip spec (borrow = 0)
-- BEQ taken → skip addback. 1 instruction at base+728 → base+884.
-- ============================================================================

/-- Correction skip: when borrow=0, BEQ taken → jump to base+884. No addback.
    1 instruction. All registers and memory unchanged. -/
theorem divK_correction_skip_spec
    (sp u_base q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5_old v2_old : Word) (base : Word) :
    cpsTriple (base + 728) (base + 884) (sharedDivModCode base)
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
  -- BEQ x7 x0 156 at base+728 with x7=0, x0=0
  have hbeq := beq_spec_gen .x7 .x0 (156 : BitVec 13) (0 : Word) 0 (base + 728)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  -- Eliminate not-taken path (⌜0 ≠ 0⌝ is False)
  have skip := cpsBranch_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  -- Strip pure fact from taken postcondition
  have skip_clean : cpsTriple (base + 728) (base + 884) (sharedDivModCode base)
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      skip
  -- Frame with all other state and permute
  have skip_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) **
     (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((u_base + signExtend12 4064) ↦ₘ u4))
    (by pcFree) skip_clean
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    skip_framed

-- ============================================================================
-- Section 6b: Correction addback spec (borrow ≠ 0)
-- BEQ not-taken → run addback. 38 instrs at base+728 → base+880.
-- ============================================================================

/-- Correction with addback: when borrow≠0, BEQ not-taken → addback_full.
    38 instructions. Modifies u values and decrements q_hat. -/
theorem divK_correction_addback_spec
    (sp u_base borrow q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5_old v2_old : Word) (base : Word)
    (hb : borrow ≠ (0 : Word)) :
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
    cpsTriple (base + 728) (base + 880) (sharedDivModCode base)
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
  -- BEQ x7 x0 156 at base+728
  have hbeq := beq_spec_gen .x7 .x0 (156 : BitVec 13) borrow 0 (base + 728)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  -- Eliminate taken path (⌜borrow = 0⌝ contradicts hb)
  have ntaken := cpsBranch_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hb hpure)
  -- Strip pure fact from not-taken postcondition
  have ntaken_clean : cpsTriple (base + 728) (base + 732) (sharedDivModCode base)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      ntaken
  -- Frame ntaken with all addback state
  have ntaken_framed := cpsTriple_frameR
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
    borrow v5_old v2_old base
  dsimp only [] at AB
  seqFrame ntaken_framed AB
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    ntaken_framedAB

/-- Variant of correction_addback_spec with addbackN4/addbackN4_carry in postcondition.
    Same proof via cpsTriple_consequence (definitional equality). -/
theorem divK_correction_addback_named_spec
    (sp u_base borrow q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5_old v2_old : Word) (base : Word)
    (hb : borrow ≠ (0 : Word)) :
    let ab := addbackN4 u0 u1 u2 u3 u4 v0 v1 v2 v3
    let q_hat' := q_hat + signExtend12 4095
    cpsTriple (base + 728) (base + 880) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ borrow) **
       (.x11 ↦ᵣ q_hat) ** (.x5 ↦ᵣ v5_old) ** (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ addbackN4_carry u0 u1 u2 u3 v0 v1 v2 v3) **
       (.x11 ↦ᵣ q_hat') ** (.x5 ↦ᵣ ab.2.2.2.2) ** (.x2 ↦ᵣ ab.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ ab.1) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ ab.2.1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ ab.2.2.1) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ ab.2.2.2.1) **
       ((u_base + signExtend12 4064) ↦ₘ ab.2.2.2.2)) := by
  intro ab q_hat'
  exact divK_correction_addback_spec sp u_base borrow q_hat v0 v1 v2 v3 u0 u1 u2 u3 u4
    v5_old v2_old base hb

-- ============================================================================
-- Section 7: Save j + trial load composition
-- Instrs [0]-[12] at base+448 → base+500.
-- ============================================================================

private theorem lb_save_j (base : Word) : (base + loopBodyOff : Word) + 4 = base + 452 := by bv_addr
private theorem lb_trial_load (base : Word) : (base + 452 : Word) + 48 = base + 500 := by bv_addr

/-- Save j + trial load: save j to memory, then load u_hi, u_lo, v_top for trial quotient.
    13 instructions, loop body indices [0]-[12].
    Entry: base+448, Exit: base+500, CodeReq: sharedDivModCode base. -/
theorem divK_save_trial_load_spec
    (sp j n j_old v5_old v6_old v7_old v10_old u_hi u_lo v_top : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + 500) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
       (sp + signExtend12 3976 ↦ₘ j_old) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top)) := by
  intro uAddr vtopBase
  -- 1. Save j: instr [0] at base+448
  have SJ := divK_save_j_spec sp j j_old (base + loopBodyOff)
  rw [lb_save_j] at SJ
  have SJe := cpsTriple_extend_code (hmono :=
    lb_sub base 0 _ _ (by decide) (by bv_addr) (by decide)) SJ
  -- Frame save_j with trial_load state
  have SJf := cpsTriple_frameR
    ((.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
     (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
     (vtopBase + signExtend12 32 ↦ₘ v_top))
    (by pcFree) SJe
  -- 2. Trial load: instrs [1]-[12] at base+452
  have TL := divK_trial_load_spec sp j n v5_old v6_old v7_old v10_old u_hi u_lo v_top
    (base + 452)
  dsimp only [] at TL
  rw [lb_trial_load] at TL
  have TLe := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 8 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 9 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 11 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 12 _ _ (by decide) (by bv_addr) (by decide))))))))))))) TL
  -- 3. Compose save_j + trial_load
  seqFrame SJf TLe
  -- Final permutation
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

-- ============================================================================
-- Section 8: Trial quotient BLTU branch + div128/max composition
-- After trial_load (base+500): x7=u_hi, x10=v_top, x5=u_lo.
-- BLTU x7 x10 12 at base+500:
--   Taken (u_hi < v_top) → base+512: JAL x2 560 → div128 → base+516, x11=q
--   Not-taken (u_hi >= v_top) → base+504: ADDI x11 x0 4095 + JAL x0 8 → base+516
-- ============================================================================

-- Address normalization for trial quotient
private theorem lb_bltu_taken (base : Word) : (base + 500 : Word) + signExtend13 (12 : BitVec 13) = base + 512 := by
  rw [se13_12]; bv_addr
private theorem lb_bltu_ntaken (base : Word) : (base + 500 : Word) + 4 = base + 504 := by bv_addr
private theorem lb_trial_max_end (base : Word) : (base + 504 : Word) + 12 = base + 516 := by bv_addr
private theorem lb_jal_target (base : Word) : (base + 512 : Word) + signExtend21 (560 : BitVec 21) = base + div128Off := by
  rw [se21_560]; bv_addr
private theorem lb_jal_ret (base : Word) : (base + 512 : Word) + 4 = base + 516 := by bv_addr

-- ============================================================================
-- Section 8a: Trial quotient NOT-TAKEN path (u_hi >= v_top)
-- Instrs [14]-[15] at base+504: ADDI x11 x0 4095 + JAL x0 8 → base+516.
-- ============================================================================

/-- Trial quotient MAX path: q_hat = MAX64, skip div128 call.
    2 instructions at base+504. Entry: base+504, Exit: base+516. -/
private theorem divK_trial_max_extended (v11_old : Word) (base : Word) :
    cpsTriple (base + 504) (base + 516) (sharedDivModCode base)
      ((.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ 0))
      ((.x11 ↦ᵣ signExtend12 4095) ** (.x0 ↦ᵣ 0)) := by
  have TM := divK_trial_max_spec v11_old (base + 504)
  dsimp only [] at TM
  rw [lb_trial_max_end] at TM
  exact cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 14 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 15 _ _ (by decide) (by bv_addr) (by decide))) TM

-- ============================================================================
-- Section 8b: Trial quotient TAKEN path (u_hi < v_top)
-- Instr [16] JAL x2 560 at base+512 → div128 at base+1072 → returns to base+516.
-- ============================================================================

/-- Trial call path: JAL x2 560 (instr [16]) + div128 subroutine.
    Entry: base+512, Exit: base+516, CodeReq: sharedDivModCode base.
    Computes q_hat = div128(u_hi, u_lo, v_top). -/
theorem divK_trial_call_path_spec
    (sp j u_lo u_hi v_top vtopBase : Word) (base : Word)
    (v2_old v11_old : Word)
    (ret_mem d_mem dlo_mem un0_mem : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516) :
    -- div128 intermediates (same as div128_spec)
    let dHi := v_top >>> (32 : BitVec 6).toNat
    let dLo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_hi dHi
    let rhat := u_hi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q_dlo := q1c * dLo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0_dlo := q0c * dLo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTriple (base + 512) (base + 516) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
       (.x2 ↦ᵣ v2_old) ** (.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ rhat2_un0) **
       (.x5 ↦ᵣ q0') ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ q0_dlo) ** (.x10 ↦ᵣ q1') **
       (.x2 ↦ᵣ (base + 516)) ** (.x11 ↦ᵣ q) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro dHi dLo un1 un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q
  -- 1. JAL x2 560 at base+512: x2 ← base+516, PC → base+1072
  have J := jal_spec .x2 v2_old (560 : BitVec 21) (base + 512) (by nofun)
  rw [lb_jal_target, lb_jal_ret] at J
  have Je := cpsTriple_extend_code (hmono :=
    lb_sub base 16 _ _ (by decide) (by bv_addr) (by decide)) J
  -- 2. div128 subroutine: base+1072 → base+516
  have D := div128_spec sp (base + 516) v_top u_lo u_hi base
    j vtopBase v11_old ret_mem d_mem dlo_mem un0_mem
    halign
  dsimp only [] at D
  -- 3. Frame JAL with all registers/memory for div128
  have Jf := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
     (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) **
     (.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) **
     (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) **
     (sp + signExtend12 3944 ↦ₘ un0_mem))
    (by pcFree) Je
  -- 4. Compose JAL + div128
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) Jf D
  -- 5. Final permutation
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

-- ============================================================================
-- Section 9: Store q[j] + loop control
-- Store q[j] at instrs [109]-[112] (base+884→base+900).
-- Loop control at instrs [113]-[114] (base+900): j--, BGE back to base+448 or exit base+908.
-- ============================================================================

-- Address normalization for store_qj and loop control
private theorem lb_sqj (base : Word) : (base + 884 : Word) + 16 = base + 900 := by bv_addr
private theorem lb_lc_taken (base : Word) :
    (base + 900 : Word) + 4 + signExtend13 (7736 : BitVec 13) = base + loopBodyOff := by
  rw [se13_7736]; bv_addr
private theorem lb_lc_exit (base : Word) : (base + 900 : Word) + 8 = base + denormOff := by bv_addr

private theorem lb_beq_back_ntaken (base : Word) : (base + 880 : Word) + 4 = base + 884 := by bv_addr

/-- BEQ passthrough at [108]: when carry (x7) ≠ 0, BEQ falls through from base+880 to base+884.
    Used to bridge addback exit (base+880) to store_loop entry (base+884). -/
theorem divK_beq_passthrough (carry : Word) (base : Word) (hne : carry ≠ 0) :
    cpsTriple (base + 880) (base + 884) (sharedDivModCode base)
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen .x7 .x0 (8044 : BitVec 13) carry 0 (base + 880)
  rw [lb_beq_back_ntaken] at hbeq
  have hbeq_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranch_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hne hpure)
  exact cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    ntaken

-- Address normalization for BEQ taken (double-addback backward branch)
private theorem lb_beq_back_taken (base : Word) :
    (base + 880 : Word) + signExtend13 (8044 : BitVec 13) = base + 732 := by
  rw [se13_8044]
  bv_addr

/-- Double-addback path at [108]: when first addback carry (x7) = 0, BEQ jumps back to [71]
    for a second addback pass. The second addback always produces carry ≠ 0, so BEQ at [108]
    then falls through to base+884.
    Entry: base+880 (after first addback), x7 = 0.
    Exit: base+884 (store entry), with double-addback results. -/
theorem divK_double_addback_beq_spec
    (sp u_base q_hat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word)
    (base : Word)
    (hcarry2_nz : addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3 ≠ 0) :
    -- Second addback intermediates (same chain as addbackN4 applied to first addback results)
    let upc0' := aun0 + (signExtend12 0 : Word)
    let ac1_0' := if BitVec.ult upc0' (signExtend12 0 : Word) then (1 : Word) else 0
    let aun0' := upc0' + v0
    let ac2_0' := if BitVec.ult aun0' v0 then (1 : Word) else 0
    let aco0' := ac1_0' ||| ac2_0'
    let upc1' := aun1 + aco0'
    let ac1_1' := if BitVec.ult upc1' aco0' then (1 : Word) else 0
    let aun1' := upc1' + v1
    let ac2_1' := if BitVec.ult aun1' v1 then (1 : Word) else 0
    let aco1' := ac1_1' ||| ac2_1'
    let upc2' := aun2 + aco1'
    let ac1_2' := if BitVec.ult upc2' aco1' then (1 : Word) else 0
    let aun2' := upc2' + v2
    let ac2_2' := if BitVec.ult aun2' v2 then (1 : Word) else 0
    let aco2' := ac1_2' ||| ac2_2'
    let upc3' := aun3 + aco2'
    let ac1_3' := if BitVec.ult upc3' aco2' then (1 : Word) else 0
    let aun3' := upc3' + v3
    let ac2_3' := if BitVec.ult aun3' v3 then (1 : Word) else 0
    let aco3' := ac1_3' ||| ac2_3'
    let aun4' := aun4 + aco3'
    let q_hat'' := q_hat' + signExtend12 4095
    cpsTriple (base + 880) (base + 884) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ q_hat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ aco3') **
       (.x11 ↦ᵣ q_hat'') ** (.x5 ↦ᵣ aun4') ** (.x2 ↦ᵣ aun3') ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0') **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1') **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2') **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3') **
       ((u_base + signExtend12 4064) ↦ₘ aun4')) := by
  intro upc0' ac1_0' aun0' ac2_0' aco0' upc1' ac1_1' aun1' ac2_1' aco1'
        upc2' ac1_2' aun2' ac2_2' aco2' upc3' ac1_3' aun3' ac2_3' aco3' aun4' q_hat''
  -- 1. BEQ at [108] taken (carry = 0, x7 = 0 = x0) → base+732
  have hbeq := beq_spec_gen .x7 .x0 (8044 : BitVec 13) (0 : Word) 0 (base + 880)
  rw [lb_beq_back_taken, lb_beq_back_ntaken] at hbeq
  have hbeq_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  -- Eliminate not-taken path (⌜0 ≠ 0⌝ is absurd)
  have beq_taken := cpsBranch_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  -- Strip pure fact from taken postcondition
  have beq_taken' := cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    beq_taken
  -- 2. Second addback (base+732 → base+880)
  have AB2 := divK_addback_full_spec sp u_base q_hat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4
    (0 : Word) aun4 aun3 base

  intro_lets at AB2
  -- 3. BEQ at [108] not taken (carry2 ≠ 0) → base+884
  have haco3_nz : aco3' ≠ 0 := by
    unfold addbackN4_carry at hcarry2_nz
    simp only [] at hcarry2_nz
    exact hcarry2_nz
  have BPT := divK_beq_passthrough aco3' base haco3_nz
  -- 4. Compose: BEQ taken (→732) + addback2 (732→880) + BEQ ntaken (880→884)
  -- Frame BEQ with addback atoms
  have beq_f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) **
     (.x11 ↦ᵣ q_hat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4))
    (by pcFree) beq_taken'
  -- Compose BEQ → addback2
  have beq_ab2 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) beq_f AB2
  -- Frame BEQ passthrough with addback2 postcondition atoms
  have BPTf := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) **
     (.x11 ↦ᵣ q_hat'') ** (.x5 ↦ᵣ aun4') ** (.x2 ↦ᵣ aun3') **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0') **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1') **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2') **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3') **
     ((u_base + signExtend12 4064) ↦ₘ aun4'))
    (by pcFree) BPT
  -- Compose (BEQ+addback2) → BEQ passthrough
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) beq_ab2 BPTf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

/-- Named variant of double_addback_beq_spec with addbackN4 projections in postcondition. -/
theorem divK_double_addback_beq_named_spec
    (sp u_base q_hat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word)
    (base : Word)
    (hcarry2_nz : addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3 ≠ 0) :
    let ab' := addbackN4 aun0 aun1 aun2 aun3 aun4 v0 v1 v2 v3
    let q_hat'' := q_hat' + signExtend12 4095
    cpsTriple (base + 880) (base + 884) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ q_hat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
       ((u_base + signExtend12 4064) ↦ₘ aun4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3) **
       (.x11 ↦ᵣ q_hat'') ** (.x5 ↦ᵣ ab'.2.2.2.2) ** (.x2 ↦ᵣ ab'.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ ab'.1) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ ab'.2.1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ ab'.2.2.1) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ ab'.2.2.2.1) **
       ((u_base + signExtend12 4064) ↦ₘ ab'.2.2.2.2)) := by
  intro ab' q_hat''
  exact divK_double_addback_beq_spec sp u_base q_hat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4
    base hcarry2_nz

/-- Double-addback BEQ check + store q[j] + loop control.
    7 instructions, loop body indices [108]-[114].
    The BEQ at [108] checks if addback carry (x7) = 0.
    When x7 ≠ 0 (single addback sufficient), BEQ falls through to store+loop.
    Entry: base+880. Taken exit: base+448 (loop back). Not-taken exit: base+908 (exit loop).
    CodeReq: sharedDivModCode base. -/
theorem divK_store_loop_spec
    (sp j q_hat v5_old v7_old q_old : Word)
    (base : Word) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j_x8
    let j' := j + signExtend12 4095
    cpsBranch (base + 884) (sharedDivModCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ q_old))
      (base + loopBodyOff)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ q_hat))
      (base + denormOff)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ q_hat)) := by
  intro j_x8 qAddr j'
  -- 1. Store q[j]: instrs [109]-[112] at base+884
  have SQ := divK_store_qj_spec sp j q_hat v5_old v7_old q_old (base + 884)
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 109 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 110 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 111 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 112 _ _ (by decide) (by bv_addr) (by decide))))) SQ
  -- 2. Loop control: instrs [113]-[114] at base+900
  have LC := divK_loop_control_spec j (7736 : BitVec 13) (base + 900)
  dsimp only [] at LC
  rw [lb_lc_taken, lb_lc_exit] at LC
  have LCe := cpsBranch_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 113 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 114 _ _ (by decide) (by bv_addr) (by decide))) LC
  -- 3. Add x0 to store_qj via frame, then reshape via consequence
  have SQx0 : cpsTriple (base + 884) (base + 900) (sharedDivModCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_hat)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  -- 4. Frame loop_control with store_qj postcondition atoms, then reshape
  have LCp : cpsBranch (base + 900) (sharedDivModCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_hat))
      (base + loopBodyOff)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_hat))
      (base + denormOff)
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_hat)) :=
    cpsBranch_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frameR
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
         (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) **
         (qAddr ↦ₘ q_hat))
        (by pcFree) LCe)
  -- 5. Compose store_qj(+x0) → loop_control(reshaped)
  exact cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => hp) SQx0 LCp

-- ============================================================================
-- Section 9b: Store + loop exit for j=0 (cpsTriple, BGE eliminated)
-- For j=0, j' = -1 < 0, so BGE is not taken → always exits to base+908.
-- ============================================================================

/-- For j=0, j' = signExtend12 4095, and slt j' 0 is true (j' < 0 signed). -/
private theorem j0_slt_zero :
    BitVec.slt ((0 : Word) + signExtend12 4095) 0 = true := by decide

/-- Store q[0] + loop exit at j=0. Since j' = -1 < 0, BGE is not taken,
    so this is a cpsTriple (not cpsBranch) to base+908. -/
theorem divK_store_loop_j0_spec
    (sp q_hat v5_old v7_old q_old : Word)
    (base : Word) :
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    let j' := (0 : Word) + signExtend12 4095
    cpsTriple (base + 884) (base + denormOff) (sharedDivModCode base)
      ((.x1 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ q_old))
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ q_hat)) := by
  intro qAddr j'
  -- 1. Store q[j]: instrs [109]-[112] at base+884
  have SQ := divK_store_qj_spec sp (0 : Word) q_hat v5_old v7_old q_old (base + 884)
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 109 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 110 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 111 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 112 _ _ (by decide) (by bv_addr) (by decide))))) SQ
  -- 2. ADDI x1 x1 4095 at base+900 (instr [113])
  have haddi := addi_spec_gen_same .x1 (0 : Word) 4095 (base + 900) (by nofun)
  rw [show (base + 900 : Word) + 4 = base + 904 from by bv_addr] at haddi
  have haddi_e := cpsTriple_extend_code (hmono := by
    exact lb_sub base 113 _ _ (by decide) (by bv_addr) (by decide)) haddi
  -- 3. BGE x1 x0 7736 at base+904 (instr [114])
  have hbge_raw := bge_spec_gen .x1 .x0 (7736 : BitVec 13) j' (0 : Word) (base + 904)
  rw [show (base + 904 : Word) + signExtend13 (7736 : BitVec 13) = base + loopBodyOff from by
        rw [se13_7736]
        bv_addr,
      show (base + 904 : Word) + 4 = base + denormOff from by bv_addr] at hbge_raw
  have hbge_ext := cpsBranch_extend_code (hmono := by
    exact lb_sub base 114 _ _ (by decide) (by bv_addr) (by decide)) hbge_raw
  -- 4. Eliminate taken branch: j' = -1 < 0, so BGE is not taken
  have hbge_exit_raw := cpsBranch_ntakenPath hbge_ext
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
      exact hpure j0_slt_zero)
  -- Strip pure fact from not-taken postcondition
  have hbge_exit := cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    hbge_exit_raw
  -- 5. Build store_qj + x0 frame → base+900
  have SQx0 : cpsTriple (base + 884) (base + 900) (sharedDivModCode base)
      ((.x1 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_old))
      ((.x1 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) **
       (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_hat)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  -- 6. Frame ADDI with x0 (BGE needs x0), then frame both with remaining atoms
  have haddi_x0 := cpsTriple_frameR
      (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_e
  -- Compose ADDI+x0 → BGE exit (both have x1 ** x0)
  have addi_bge := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddi_x0 hbge_exit
  -- Frame with remaining atoms
  have addi_bge_framed := cpsTriple_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) **
       (qAddr ↦ₘ q_hat))
      (by pcFree) addi_bge
  -- 7. Compose: store_qj → (ADDI → BGE exit)
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) SQx0 addi_bge_framed
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

-- ============================================================================
-- Section 9c: Store + loop continue for j > 0 (cpsTriple, BGE eliminated)
-- For j > 0, j' = j-1 ≥ 0, so BGE is taken → always loops back to base+448.
-- ============================================================================

/-- Store q[j] + loop back at j > 0. Since j' = j-1 ≥ 0 (signed), BGE is taken,
    so this is a cpsTriple (not cpsBranch) to base+448. -/
theorem divK_store_loop_jgt0_spec
    (sp j q_hat v5_old v7_old q_old : Word)
    (base : Word)
    (hj_pos : BitVec.slt (j + signExtend12 4095) 0 = false) :
    let j_x8 := j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j_x8
    let j' := j + signExtend12 4095
    cpsTriple (base + 884) (base + loopBodyOff) (sharedDivModCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ q_old))
      ((.x1 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ q_hat)) := by
  intro j_x8 qAddr j'
  -- 1. Store q[j]: instrs [109]-[112] at base+884
  have SQ := divK_store_qj_spec sp j q_hat v5_old v7_old q_old (base + 884)
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub base 109 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 110 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub base 111 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub base 112 _ _ (by decide) (by bv_addr) (by decide))))) SQ
  -- 2. ADDI x1 x1 4095 at base+900 (instr [113])
  have haddi := addi_spec_gen_same .x1 j 4095 (base + 900) (by nofun)
  rw [show (base + 900 : Word) + 4 = base + 904 from by bv_addr] at haddi
  have haddi_e := cpsTriple_extend_code (hmono := by
    exact lb_sub base 113 _ _ (by decide) (by bv_addr) (by decide)) haddi
  -- 3. BGE x1 x0 7736 at base+904 (instr [114])
  have hbge_raw := bge_spec_gen .x1 .x0 (7736 : BitVec 13) j' (0 : Word) (base + 904)
  rw [show (base + 904 : Word) + signExtend13 (7736 : BitVec 13) = base + loopBodyOff from by
        rw [se13_7736]
        bv_addr,
      show (base + 904 : Word) + 4 = base + denormOff from by bv_addr] at hbge_raw
  have hbge_ext := cpsBranch_extend_code (hmono := by
    exact lb_sub base 114 _ _ (by decide) (by bv_addr) (by decide)) hbge_raw
  -- 4. Eliminate not-taken branch: j' = j-1 ≥ 0, so BGE is taken
  have hbge_exit_raw := cpsBranch_takenPath hbge_ext
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
      exact absurd hpure (by rw [hj_pos]; exact Bool.false_ne_true))
  -- Strip pure fact from taken postcondition
  have hbge_exit := cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
    hbge_exit_raw
  -- 5. Build store_qj + x0 frame → base+900
  have SQx0 : cpsTriple (base + 884) (base + 900) (sharedDivModCode base)
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ v5_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_old))
      ((.x1 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ q_hat)) :=
    cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  -- 6. Frame ADDI with x0, then frame both with remaining atoms
  have haddi_x0 := cpsTriple_frameR
      (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_e
  -- Compose ADDI+x0 → BGE exit (both have x1 ** x0)
  have addi_bge := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddi_x0 hbge_exit
  -- Frame with remaining atoms
  have addi_bge_framed := cpsTriple_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat) **
       (.x5 ↦ᵣ j_x8) ** (.x7 ↦ᵣ qAddr) **
       (qAddr ↦ₘ q_hat))
      (by pcFree) addi_bge
  -- 7. Compose: store_qj → (ADDI → BGE exit)
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) SQx0 addi_bge_framed
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

-- ============================================================================
-- Section 10: Mulsub + correction_skip composition (borrow = 0 path)
-- Takes borrow as an explicit parameter (not let-bound) to enable rw.
-- ============================================================================

/-- Mulsub + correction skip: when mulsub produces borrow=0, skip addback.
    Takes borrow as explicit parameter to avoid let-binding expansion issues.
    Entry: base+516, Exit: base+880, CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_correction_skip_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word) :
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
    cpsTriple (base + 516) (base + 884) (sharedDivModCode base)
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

  dsimp only [] at MS hborrow
  -- 2. Rewrite borrow to 0 in mulsub postcondition
  rw [hborrow] at MS
  -- 3. Correction skip (base+728 → base+884)
  have CS := divK_correction_skip_spec sp u_base q_hat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base
  -- 4. Compose mulsub(borrow=0) + correction_skip
  seqFrame MS CS
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    MSCS

-- ============================================================================
-- Section 10b: Mulsub + correction_addback composition (borrow ≠ 0 path)
-- ============================================================================

/-- Mulsub + correction addback (without BEQ): when mulsub produces borrow≠0, run addback.
    Entry: base+516, Exit: base+880 (before BEQ at [108]).
    CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_correction_addback_880_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- Mulsub intermediates (same as in addback spec)
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
    cpsTriple (base + 516) (base + 880) (sharedDivModCode base)
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

  dsimp only [] at MS hborrow
  -- 2. Correction addback (base+728 → base+880) with borrow ≠ 0
  have CA := divK_correction_addback_spec sp u_base
    (if BitVec.ult u_top c3 then (1 : Word) else 0)
    q_hat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base hborrow

  dsimp only [] at CA
  -- 3. Compose mulsub + correction_addback
  seqFrame MS CA
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    MSCA

/-- Mulsub + correction addback (→880), named postcondition variant.
    Uses addbackN4/addbackN4_carry in postcondition for rewritability. -/
theorem divK_mulsub_correction_addback_named_880_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    let q_hat' := q_hat + signExtend12 4095
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 516) (base + 880) (sharedDivModCode base)
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
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ ab.2.2.2.2) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ ab.2.2.2.1) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ ab.1) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ ab.2.1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ ab.2.2.1) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ ab.2.2.2.1) **
       ((u_base + signExtend12 4064) ↦ₘ ab.2.2.2.2)) := by
  intro u_base ms c3 ab q_hat' hborrow
  exact (divK_mulsub_correction_addback_880_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    v1_old v5_old v6_old v7_old v10_old v2_old base) hborrow

set_option maxRecDepth 4096 in
/-- Mulsub + correction addback + BEQ passthrough: when mulsub produces borrow≠0,
    run addback, then BEQ falls through (carry ≠ 0).
    Entry: base+516, Exit: base+884, CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_correction_addback_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word) :
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
    -- Hypothesis: addback carry ≠ 0 (single addback sufficient)
    aco3 ≠ 0 →
    cpsTriple (base + 516) (base + 884) (sharedDivModCode base)
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
        hborrow hcarry
  -- 1. Mulsub full (base+516 → base+728)
  have MS := divK_mulsub_full_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    v1_old v5_old v6_old v7_old v10_old v2_old base

  dsimp only [] at MS hborrow
  -- 2. Correction addback (base+728 → base+880) with borrow ≠ 0
  have CA := divK_correction_addback_spec sp u_base
    (if BitVec.ult u_top c3 then (1 : Word) else 0)
    q_hat v0 v1 v2 v3 un0 un1 un2 un3 u4_new
    u4_new un3 base hborrow

  dsimp only [] at CA
  -- 3. BEQ passthrough (base+880 → base+884) with carry ≠ 0
  have BEQ := divK_beq_passthrough aco3 base hcarry
  -- 4. Compose mulsub + correction_addback (→880)
  seqFrame MS CA
  -- 5. Frame BEQ with remaining atoms and compose (880→884)
  have BEQf := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_hat') **
     (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ aun4) ** (.x6 ↦ᵣ u_base) **
     (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ j) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4))
    (by pcFree) BEQ
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) MSCA BEQf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

-- ============================================================================
-- Section 11: Trial quotient max path (BLTU not-taken)
-- Composes: save_trial_load → BLTU ntaken → trial_max.
-- Entry: base+448, Exit: base+516 with x11 = MAX64.
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Trial quotient max path: save j + load + BLTU not-taken + trial_max.
    When u_hi >= v_top, sets q_hat = MAX64 without calling div128.
    Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base. -/
theorem divK_trial_max_full_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old u_hi u_lo v_top : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u_hi v_top) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + 516) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ u_lo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ u_hi) ** (.x10 ↦ᵣ v_top) ** (.x11 ↦ᵣ signExtend12 4095) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top)) := by
  intro uAddr vtopBase
  -- 1. Save j + trial load (base+448 → base+500)
  have STL := divK_save_trial_load_spec sp j n j_old v5_old v6_old v7_old v10_old u_hi u_lo v_top
    base
  dsimp only [] at STL
  -- 2. BLTU x7 x10 12 at base+500
  have hbltu_raw := bltu_spec_gen .x7 .x10 (12 : BitVec 13) u_hi v_top (base + 500)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  -- Eliminate taken path (⌜BitVec.ult u_hi v_top⌝ contradicts hbltu)
  have ntaken := cpsBranch_ntakenPath hbltu_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hbltu hpure)
  -- Strip pure fact
  have ntaken_clean := cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp) ntaken
  -- 3. Trial max (base+504 → base+516)
  have TM := divK_trial_max_extended v11_old base
  -- 4. Frame save_trial_load with x11 + x0, compose with BLTU ntaken
  have STLf := cpsTriple_frameR
    ((.x11 ↦ᵣ v11_old) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) STL
  seqFrame STLf ntaken_clean
  -- 5. Frame BLTU ntaken result with x0 + memory, compose with trial_max
  seqFrame STLfntaken_clean TM
  -- 6. Final permutation
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    STLfntaken_cleanTM

-- ============================================================================
-- Section 11b: Trial quotient call path (BLTU taken): save + load + BLTU + JAL + div128
-- When u_hi < v_top, calls div128 to compute the trial quotient.
-- Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base.
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Trial quotient call path: save j + load + BLTU taken + JAL + div128.
    When u_hi < v_top, computes q_hat = div128(u_hi, u_lo, v_top).
    Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base. -/
theorem divK_trial_call_full_spec
    (sp j n j_old v5_old v6_old v7_old v10_old v11_old v2_old u_hi u_lo v_top : Word)
    (ret_mem d_mem dlo_mem un0_mem : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u_hi v_top) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let dHi := v_top >>> (32 : BitVec 6).toNat
    let dLo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0_div := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_hi dHi
    let rhat := u_hi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q_dlo := q1c * dLo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0_dlo := q0c * dLo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0_div
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTriple (base + loopBodyOff) (base + 516) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ rhat2_un0) **
       (.x5 ↦ᵣ q0') ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ q0_dlo) ** (.x10 ↦ᵣ q1') ** (.x11 ↦ᵣ q) **
       (.x2 ↦ᵣ (base + 516)) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ u_hi) ** ((uAddr + 8) ↦ₘ u_lo) **
       (vtopBase + signExtend12 32 ↦ₘ v_top) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v_top) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ un0_div)) := by
  intro uAddr vtopBase
        dHi dLo un1 un0_div q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q
  -- 1. Save j + trial load (base+448 → base+500)
  have STL := divK_save_trial_load_spec sp j n j_old v5_old v6_old v7_old v10_old u_hi u_lo v_top
    base
  dsimp only [] at STL
  -- 2. BLTU x7 x10 12 at base+500
  have hbltu_raw := bltu_spec_gen .x7 .x10 (12 : BitVec 13) u_hi v_top (base + 500)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranch_extend_code (hmono :=
    lb_sub base 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  -- Eliminate ntaken path (⌜¬BitVec.ult u_hi v_top⌝ contradicts hbltu)
  have taken := cpsBranch_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  -- Strip pure fact from taken postcondition
  have taken_clean := cpsTriple_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp) taken
  -- 3. Trial call path (base+512 → base+516)
  have TCP := divK_trial_call_path_spec sp j u_lo u_hi v_top vtopBase base
    v2_old v11_old ret_mem d_mem dlo_mem un0_mem
    halign
  dsimp only [] at TCP
  -- 4. Frame save_trial_load with x2, x11, x0, scratch memory
  have STLf := cpsTriple_frameR
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
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    STLftaken_cleanTCP

-- ============================================================================
-- Section 10c: Mulsub + correction_addback + BEQ (both carry outcomes)
-- Combined spec: base+516 → base+884 with case-split on addback carry.
-- Uses iterWithDoubleAddback-style postcondition.
-- ============================================================================

/-- Mulsub + correction with addback + BEQ at [108]: when borrow ≠ 0, performs
    first addback and then handles the BEQ:
    - carry ≠ 0 (single addback): BEQ falls through to base+884
    - carry = 0 (double addback): BEQ takes backward branch, second addback, then falls through
    Entry: base+516, Exit: base+884. -/
theorem divK_mulsub_correction_addback_beq_spec
    (sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word)
    (v1_old v5_old v6_old v7_old v10_old v2_old : Word)
    (base : Word) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    -- Double-addback results (only used when carry = 0)
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    -- Final values depend on carry
    let q_out := if carry = 0 then q_hat + signExtend12 4095 + signExtend12 4095
                 else q_hat + signExtend12 4095
    let un0_out := if carry = 0 then ab'.1 else ab.1
    let un1_out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2_out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3_out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
    let carryOut := if carry = 0 then
        addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
      else carry
    -- Hypothesis: second addback carry nonzero (only needed if first carry = 0)
    (carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 516) (base + 884) (sharedDivModCode base)
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
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ u_base) **
       (.x7 ↦ᵣ carryOut) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3_out) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_out) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_out) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_out) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_out) **
       ((u_base + signExtend12 4064) ↦ₘ u4_out)) := by
  intro u_base ms c3 carry ab ab' q_out un0_out un1_out un2_out un3_out u4_out carryOut
        hcarry2_nz hborrow
  -- 1. Mulsub + first addback (base+516 → base+880)
  have MCA := divK_mulsub_correction_addback_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
    v1_old v5_old v6_old v7_old v10_old v2_old base

  intro_lets at MCA
  have MCA0 := MCA hborrow
  -- 2. Case split on carry
  by_cases hcarry : carry = 0
  · -- carry = 0: double addback path
    have hq : q_out = q_hat + signExtend12 4095 + signExtend12 4095 := if_pos hcarry
    have h0 : un0_out = ab'.1 := if_pos hcarry
    have h1 : un1_out = ab'.2.1 := if_pos hcarry
    have h2 : un2_out = ab'.2.2.1 := if_pos hcarry
    have h3 : un3_out = ab'.2.2.2.1 := if_pos hcarry
    have h4 : u4_out = ab'.2.2.2.2 := if_pos hcarry
    have hc : carryOut = addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 := if_pos hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    -- Use named 880 spec (→880 with addbackN4_carry in postcondition)
    have MCA_N := (divK_mulsub_correction_addback_named_880_spec sp q_hat j v0 v1 v2 v3 u0 u1 u2 u3 u_top
      v1_old v5_old v6_old v7_old v10_old v2_old base) hborrow
    -- Rewrite carry to 0
    rw [show addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = (0 : Word) from hcarry] at MCA_N
    -- Use named DA spec (880→884 with addbackN4 projections in postcondition)
    have hcarry2 : addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 :=
      hcarry2_nz hcarry
    have DA := divK_double_addback_beq_named_spec sp u_base
      (q_hat + signExtend12 4095) v0 v1 v2 v3
      ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
      base hcarry2
    -- Frame DA with extra atoms from MCA_N postcondition
    have DAf := cpsTriple_frameR
      ((.x1 ↦ᵣ j) ** (.x10 ↦ᵣ c3) **
       (sp + signExtend12 3976 ↦ₘ j))
      (by pcFree) DA
    -- Compose MCA_N(→880) with DAf(880→884)
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) MCA_N DAf
    exact cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      full
  · -- carry ≠ 0: single addback path (BEQ passthrough)
    have hq : q_out = q_hat + signExtend12 4095 := if_neg hcarry
    have h0 : un0_out = ab.1 := if_neg hcarry
    have h1 : un1_out = ab.2.1 := if_neg hcarry
    have h2 : un2_out = ab.2.2.1 := if_neg hcarry
    have h3 : un3_out = ab.2.2.2.1 := if_neg hcarry
    have h4 : u4_out = ab.2.2.2.2 := if_neg hcarry
    have hc : carryOut = carry := if_neg hcarry
    rw [hq, h0, h1, h2, h3, h4, hc]
    -- Use the existing MCA0 (which includes BEQ passthrough) with carry ≠ 0
    exact MCA0 hcarry

end EvmAsm.Evm64
