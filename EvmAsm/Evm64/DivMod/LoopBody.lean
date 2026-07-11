/-
  EvmAsm.Evm64.DivMod.LoopBody

  Hierarchical composition of the 114-instruction Knuth Algorithm D main loop body.
  Composes sub-specs from LimbSpec.lean into a single cpsBranchWithin for one iteration,
  then proves the inductive loop spec via cpsTriple_loop_with_perm.

  Issue #87: DIV/MOD loop body composition.
-/

-- `DivN4Overestimate → LoopSemantic → LoopDefs`.
import EvmAsm.Evm64.DivMod.Compose.Base
import EvmAsm.Evm64.DivMod.Compose.V4NoNop
import EvmAsm.Evm64.DivMod.LimbSpec.AddBackFinalLoopControl
import EvmAsm.Evm64.DivMod.LimbSpec.MulSub
import EvmAsm.Evm64.DivMod.LimbSpec.MulSubLimb
import EvmAsm.Evm64.DivMod.LimbSpec.MulSubSetup
import EvmAsm.Evm64.DivMod.LimbSpec.SubCarryStoreQj
import EvmAsm.Evm64.DivMod.LimbSpec.TrialQuotient
import EvmAsm.Evm64.DivMod.LimbSpec.TrialStoreComposed
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se13_7736)

-- ============================================================================
-- Section 1: CodeReq subsumption infrastructure for loop body instructions
-- ============================================================================

/-- The loopBody ofProg (block 8) is subsumed by sharedDivModCode. -/
private theorem divK_loopBody_ofProg_sub_sharedCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (sharedDivModCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- Helper: singleton at index k of divK_loopBody ⊆ sharedDivModCode base. -/
theorem lb_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 560 7736).length)
    (h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_sharedCode a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + loopBodyOff) (divK_loopBody 560 7736) k hk (by decide)) a i h)

/-- The loopBody ofProg (block 8) is subsumed by sharedDivModCode_v4. -/
private theorem divK_loopBody_ofProg_sub_sharedCode_v4 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (sharedDivModCode_v4 base) a = some i := by
  unfold sharedDivModCode_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- Helper: singleton at index k of divK_loopBody ⊆ sharedDivModCode_v4 base. -/
theorem lb_sub_v4 {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 560 7736).length)
    (h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCode_v4 base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_sharedCode_v4 a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + loopBodyOff) (divK_loopBody 560 7736) k hk (by decide)) a i h)

/-- The loopBody ofProg (block 8) is subsumed by sharedDivModCodeNoNop_v4. -/
private theorem divK_loopBody_ofProg_sub_sharedCodeNoNop_v4 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (sharedDivModCodeNoNop_v4 base) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock
  exact CodeReq.union_mono_left

/-- Helper: singleton at index k of divK_loopBody ⊆ sharedDivModCodeNoNop_v4 base. -/
theorem lb_sub_noNop_v4 {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 560 7736).length)
    (h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCodeNoNop_v4 base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_sharedCodeNoNop_v4 a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + loopBodyOff) (divK_loopBody 560 7736) k hk (by decide)) a i h)

/-- Helper: singleton at index k of divK_loopBody ⊆ divCode_noNop base. -/
theorem lb_sub_noNop {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < (divK_loopBody 560 7736).length)
    (h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
    (h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (divCode_noNop base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_loopBody_ofProg_sub_divCode_noNop a i
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
private theorem lb_ms1 {base : Word} : (base + mulsubOff : Word) + 44 = base + (mulsubOff + 44) := by
  rw [BitVec.add_assoc]
private theorem lb_ms2 {base : Word} : (base + (mulsubOff + 44) : Word) + 44 = base + correctionSkipOff := by bv_addr
private theorem lb_ms3 {base : Word} : (base + correctionSkipOff : Word) + 44 = base + (correctionSkipOff + 44) := by
  rw [BitVec.add_assoc]
private theorem lb_ms_end {base : Word} : (base + (correctionSkipOff + 44) : Word) + 44 = base + correctionAddbackOff := by bv_addr

-- ============================================================================
-- Section 3: Mulsub 4-limbs composition
-- Composes 4 × divK_mulsub_limb_spec using seqFrame for automatic framing.
-- ============================================================================

@[irreducible]
private def divKMulsub4LimbsPre
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (v5Init v7Init v2Init : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) ** (.x10 ↦ᵣ (signExtend12 0 : Word)) **
  (.x6 ↦ᵣ uBase) ** (.x5 ↦ᵣ v5Init) ** (.x7 ↦ᵣ v7Init) **
  (.x2 ↦ᵣ v2Init) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3)

@[irreducible]
private def divKMulsub4LimbsPost
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Assertion :=
  let p0_lo := qHat * v0
  let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0
  let c0 := pc0 + bs0
  let p1_lo := qHat * v1
  let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1
  let c1 := pc1 + bs1
  let p2_lo := qHat * v2
  let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2
  let c2 := pc2 + bs2
  let p3_lo := qHat * v3
  let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3
  let c3 := pc3 + bs3
  (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) ** (.x10 ↦ᵣ c3) **
  (.x6 ↦ᵣ uBase) ** (.x5 ↦ᵣ bs3) ** (.x7 ↦ᵣ fs3) **
  (.x2 ↦ᵣ un3) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3)

/-- Multiply-subtract all 4 limbs: u[j+k] -= qHat * v[k] for k=0..3 with carry chain.
    44 instructions, loop body indices [22]-[65].
    Entry: base+536, Exit: base+712, CodeReq: sharedDivModCode base. -/
private theorem divK_mulsub_4limbs_spec_within_of_sub
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (v5_init v7_init v2_init : Word)
    (base : Word)
    (code : CodeReq)
    (hsub : ∀ (k : Nat) (addr : Word) (instr : Instr)
        (hk : k < (divK_loopBody 560 7736).length)
        (_h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
        (_h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr),
        ∀ a i, CodeReq.singleton addr instr a = some i → code a = some i) :
    cpsTripleWithin 44 (base + mulsubOff) (base + correctionAddbackOff) code
      (divKMulsub4LimbsPre sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3
        v5_init v7_init v2_init)
      (divKMulsub4LimbsPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3) := by
  unfold divKMulsub4LimbsPre divKMulsub4LimbsPost
  let p0_lo := qHat * v0
  let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0
  let c0 := pc0 + bs0
  let p1_lo := qHat * v1
  let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1
  let c1 := pc1 + bs1
  let p2_lo := qHat * v2
  let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2
  let c2 := pc2 + bs2
  let p3_lo := qHat * v3
  let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3
  let c3 := pc3 + bs3
  -- Limb 0: instrs [22]-[32] at base+536
  have L0 := divK_mulsub_limb_spec_within sp uBase qHat (signExtend12 0 : Word)
    v5_init v7_init v2_init v0 u0 32 0 (base + mulsubOff)

  rw [lb_ms1] at L0
  have L0e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 22 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 23 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 24 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 25 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 26 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 27 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 28 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 29 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 30 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 31 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 32 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L0
  -- Limb 1: instrs [33]-[43] at base+580
  have L1 := divK_mulsub_limb_spec_within sp uBase qHat c0
    bs0 fs0 un0 v1 u1 40 4088 (base + (mulsubOff + 44))

  rw [lb_ms2] at L1
  have L1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 33 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 34 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 35 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 36 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 37 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 38 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 39 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 40 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 41 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 42 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 43 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L1
  -- Frame L0 with memory for limbs 1-3 (so seqFrame can find L1's precondition atoms)
  have L0f := cpsTripleWithin_frameR
    (((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3))
    (by pcFree) L0e
  -- Compose L0 + L1
  seqFrame L0f L1e
  -- Limb 2: instrs [44]-[54] at base+624
  have L2 := divK_mulsub_limb_spec_within sp uBase qHat c1
    bs1 fs1 un1 v2 u2 48 4080 (base + correctionSkipOff)

  rw [lb_ms3] at L2
  have L2e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 44 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 45 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 46 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 47 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 48 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 49 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 50 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 51 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 52 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 53 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 54 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L2
  -- Compose (L0+L1) + L2
  seqFrame L0fL1e L2e
  -- Limb 3: instrs [55]-[65] at base+668
  have L3 := divK_mulsub_limb_spec_within sp uBase qHat c2
    bs2 fs2 un2 v3 u3 56 4072 (base + (correctionSkipOff + 44))

  rw [lb_ms_end] at L3
  have L3e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 55 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 56 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 57 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 58 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 59 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 60 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 61 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 62 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 63 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 64 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 65 _ _ (by decide) (by bv_addr) (by decide))))))))))))
    L3
  -- Compose (L0+L1+L2) + L3
  seqFrame L0fL1eL2e L3e
  -- Final permutation to match goal pre/postcondition order
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    L0fL1eL2eL3e

private theorem lb_ab0 {base : Word} : (base + addbackInitOff : Word) + 4 = base + addbackLimb0Off := by bv_addr
private theorem lb_ab0_end {base : Word} : (base + addbackLimb0Off : Word) + 32 = base + addbackLimb1Off := by bv_addr
private theorem lb_ab1_end {base : Word} : (base + addbackLimb1Off : Word) + 32 = base + addbackLimb2Off := by bv_addr
private theorem lb_ab2_end {base : Word} : (base + addbackLimb2Off : Word) + 32 = base + addbackLimb3Off := by bv_addr
private theorem lb_ab3_end {base : Word} : (base + addbackLimb3Off : Word) + 32 = base + addbackFinalOff := by bv_addr
private theorem lb_abf_end {base : Word} : (base + addbackFinalOff : Word) + 16 = base + addbackBeqOff := by bv_addr

@[irreducible]
def addbackFullPre
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7Init v5Init v2Init : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ v7Init) **
  (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Init) ** (.x2 ↦ᵣ v2Init) ** (.x0 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ u4)

/-- Postcondition bundle for the full addback: bundles the 22-let chain
    so callers see a flat postcondition. -/
@[irreducible]
def addbackFullPost (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word) :
    EvmAsm.Rv64.Assertion :=
  let upc0 := u0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := u1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := u2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := u3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4 + aco3; let qHat' := qHat + signExtend12 4095
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ aco3) **
  (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
  ((uBase + signExtend12 4064) ↦ₘ aun4)

theorem addbackFullPost_unfold {sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word} :
    addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 =
      (let upc0 := u0 + (signExtend12 0 : Word)
       let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
       let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
       let aco0 := ac1_0 ||| ac2_0
       let upc1 := u1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
       let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
       let aco1 := ac1_1 ||| ac2_1
       let upc2 := u2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
       let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
       let aco2 := ac1_2 ||| ac2_2
       let upc3 := u3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
       let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
       let aco3 := ac1_3 ||| ac2_3
       let aun4 := u4 + aco3; let qHat' := qHat + signExtend12 4095
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ aco3) **
       (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4)) := by
  delta addbackFullPost; rfl

/-- Full add-back correction: init carry + 4 limb corrections + final u[j+4] adjust + qHat--.
    37 instructions, loop body indices [71]-[107].
    Entry: base+732, Exit: base+880, CodeReq: sharedDivModCode base. -/
theorem divK_addback_full_spec_within_of_sub
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word)
    (code : CodeReq)
    (hsub : ∀ (k : Nat) (addr : Word) (instr : Instr)
        (hk : k < (divK_loopBody 560 7736).length)
        (_h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
        (_h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr),
        ∀ a i, CodeReq.singleton addr instr a = some i → code a = some i) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) code
      (addbackFullPre sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
        v7_init v5_init v2_init)
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) := by
  unfold addbackFullPre addbackFullPost
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
  let qHat' := qHat + signExtend12 4095
  -- Init: instr [71] at base+732
  have I := divK_addback_init_spec_within v7_init (base + addbackInitOff)
  rw [lb_ab0] at I
  have Ie := cpsTripleWithin_extend_code (hmono := by
    exact hsub 71 _ _ (by decide) (by bv_addr) (by decide)) I
  -- Frame init with all addback state
  have If := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x11 ↦ᵣ qHat) **
     (.x5 ↦ᵣ v5_init) ** (.x2 ↦ᵣ v2_init) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ u4))
    (by pcFree) Ie
  -- Limb 0: instrs [72]-[79] at base+addbackLimb0Off
  have A0 := divK_addback_limb_spec_within sp uBase (signExtend12 0 : Word)
    v5_init v2_init v0 u0 32 0 (base + addbackLimb0Off)
  rw [lb_ab0_end] at A0
  have A0e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 72 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 73 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 74 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 75 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 76 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 77 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 78 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 79 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A0
  -- Compose init + limb 0
  seqFrame If A0e
  -- Limb 1: instrs [80]-[87] at base+addbackLimb1Off
  have A1 := divK_addback_limb_spec_within sp uBase aco0
    ac2_0 aun0 v1 u1 40 4088 (base + addbackLimb1Off)
  rw [lb_ab1_end] at A1
  have A1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 80 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 81 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 82 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 83 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 84 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 85 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 86 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 87 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A1
  seqFrame IfA0e A1e
  -- Limb 2: instrs [88]-[95] at base+addbackLimb2Off
  have A2 := divK_addback_limb_spec_within sp uBase aco1
    ac2_1 aun1 v2 u2 48 4080 (base + addbackLimb2Off)
  rw [lb_ab2_end] at A2
  have A2e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 88 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 89 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 90 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 91 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 92 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 93 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 94 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 95 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A2
  seqFrame IfA0eA1e A2e
  -- Limb 3: instrs [96]-[103] at base+addbackLimb3Off
  have A3 := divK_addback_limb_spec_within sp uBase aco2
    ac2_2 aun2 v3 u3 56 4072 (base + addbackLimb3Off)
  rw [lb_ab3_end] at A3
  have A3e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 96 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 97 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 98 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 99 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 100 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 101 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 102 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 103 _ _ (by decide) (by bv_addr) (by decide)))))))))
    A3
  seqFrame IfA0eA1eA2e A3e
  -- Final: instrs [104]-[107] at base+addbackFinalOff
  have AF := divK_addback_final_spec_within uBase aco3 qHat ac2_3 u4 4064 (base + addbackFinalOff)
  rw [lb_abf_end] at AF
  have AFe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 104 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 105 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 106 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 107 _ _ (by decide) (by bv_addr) (by decide)))))
    AF
  seqFrame IfA0eA1eA2eA3e AFe
  -- Final permutation
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IfA0eA1eA2eA3eAFe

/-- Full add-back correction over `sharedDivModCode`. -/
private theorem divK_addback_full_spec_within
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) (sharedDivModCode base)
      (addbackFullPre sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
        v7_init v5_init v2_init)
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  divK_addback_full_spec_within_of_sub sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
    v7_init v5_init v2_init base (sharedDivModCode base) lb_sub

/-- Full add-back correction over `sharedDivModCodeNoNop_v4`. -/
private theorem divK_addback_full_v4_spec_within_noNop
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) (sharedDivModCodeNoNop_v4 base)
      (addbackFullPre sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
        v7_init v5_init v2_init)
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  divK_addback_full_spec_within_of_sub sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
    v7_init v5_init v2_init base (sharedDivModCodeNoNop_v4 base) lb_sub_noNop_v4

/-- Full add-back correction over the DIV no-NOP code surface. -/
private theorem divK_addback_full_spec_within_noNop
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) (divCode_noNop base)
      (addbackFullPre sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
        v7_init v5_init v2_init)
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  divK_addback_full_spec_within_of_sub sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
    v7_init v5_init v2_init base (divCode_noNop base) lb_sub_noNop

/-- Named-postcondition no-NOP wrapper for `divK_addback_full_spec_within_noNop`.
    Bundles the 22-let result into `addbackFullPost`; 0 statement lets. -/
theorem divK_addback_full_named_spec_within_noNop
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ v7_init) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5_init) ** (.x2 ↦ᵣ v2_init) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  cpsTripleWithin_weaken
    (fun h hp => by unfold addbackFullPre; exact hp)
    (fun h hp => hp)
    (divK_addback_full_spec_within_noNop sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 v7_init v5_init v2_init base)

theorem divK_addback_full_named_v4_spec_within_noNop
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word)
    (base : Word) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ v7_init) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5_init) ** (.x2 ↦ᵣ v2_init) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  cpsTripleWithin_weaken
    (fun h hp => by unfold addbackFullPre; exact hp)
    (fun h hp => hp)
    (divK_addback_full_v4_spec_within_noNop sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 v7_init v5_init v2_init base)

private theorem lb_ms_setup {base : Word} : (base + div128CallRetOff : Word) + 20 = base + mulsubOff := by bv_addr

-- Address normalization for sub_carry
private theorem lb_sc {base : Word} : (base + correctionAddbackOff : Word) + 16 = base + correctionSkipBeqOff := by bv_addr

/-- Mulsub full: setup + 4-limb multiply-subtract + carry subtraction from u[j+4].
    53 instructions, loop body indices [17]-[69].
    Entry: base+516, Exit: base+728, CodeReq: sharedDivModCode base. -/
theorem divK_mulsub_full_spec_within_of_sub
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v9Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word)
    (code : CodeReq)
    (hsub : ∀ (k : Nat) (addr : Word) (instr : Instr)
        (hk : k < (divK_loopBody 560 7736).length)
        (_h_addr : addr = (base + loopBodyOff) + BitVec.ofNat 64 (4 * k))
        (_h_instr : (divK_loopBody 560 7736).get ⟨k, hk⟩ = instr),
        ∀ a i, CodeReq.singleton addr instr a = some i → code a = some i) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- Mulsub intermediates (same as mulsub_4limbs_spec)
    let p0_lo := qHat * v0
    let p0_hi := rv64_mulhu qHat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0
    let c0 := pc0 + bs0
    let p1_lo := qHat * v1
    let p1_hi := rv64_mulhu qHat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1
    let c1 := pc1 + bs1
    let p2_lo := qHat * v2
    let p2_hi := rv64_mulhu qHat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2
    let c2 := pc2 + bs2
    let p3_lo := qHat * v3
    let p3_hi := rv64_mulhu qHat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3
    let c3 := pc3 + bs3
    -- Sub-carry intermediates
    let borrow := if BitVec.ult uTop c3 then (1 : Word) else 0
    let u4_new := uTop - c3
    cpsTripleWithin 53 (base + div128CallRetOff) (base + correctionSkipBeqOff) code
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v9Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ borrow) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
       ((uBase + signExtend12 4064) ↦ₘ u4_new)) := by
  intro uBase
        p0_lo p0_hi fs0 ba0 pc0 bs0 un0 c0
        p1_lo p1_hi fs1 ba1 pc1 bs1 un1 c1
        p2_lo p2_hi fs2 ba2 pc2 bs2 un2 c2
        p3_lo p3_hi fs3 ba3 pc3 bs3 un3 c3
        borrow u4_new
  -- 1. Mulsub setup: instrs [17]-[21] at base+516
  have S := divK_mulsub_setup_spec_within sp qHat j v9Old v5Old v6Old v10Old (base + div128CallRetOff)
  rw [lb_ms_setup] at S
  have Se := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 17 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 18 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 19 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 20 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 21 _ _ (by decide) (by bv_addr) (by decide)))))) S
  -- Frame setup with all memory + x7/x2 for mulsub
  have Sf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7Old) ** (.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop))
    (by pcFree) Se
  -- 2. Mulsub 4 limbs: instrs [22]-[65] at base+536
  have M := divK_mulsub_4limbs_spec_within_of_sub sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3
    (j <<< (3 : BitVec 6).toNat) v7Old v2Old base code hsub
  unfold divKMulsub4LimbsPre divKMulsub4LimbsPost at M
  -- Compose setup + mulsub
  seqFrame Sf M
  -- 3. Sub-carry: instrs [66]-[69] at base+712
  have SC := divK_sub_carry_spec_within uBase c3 bs3 fs3 uTop 4064 (base + correctionAddbackOff)
  rw [lb_sc] at SC
  have SCe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (hsub 66 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 67 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (hsub 68 _ _ (by decide) (by bv_addr) (by decide))
      (hsub 69 _ _ (by decide) (by bv_addr) (by decide))))) SC
  -- Compose (setup+mulsub) + sub_carry
  seqFrame SfM SCe
  -- Final permutation
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SfMSCe

theorem divK_mulsub_full_spec_within
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v9Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let p0_lo := qHat * v0
    let p0_hi := rv64_mulhu qHat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0
    let c0 := pc0 + bs0
    let p1_lo := qHat * v1
    let p1_hi := rv64_mulhu qHat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1
    let c1 := pc1 + bs1
    let p2_lo := qHat * v2
    let p2_hi := rv64_mulhu qHat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2
    let c2 := pc2 + bs2
    let p3_lo := qHat * v3
    let p3_hi := rv64_mulhu qHat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3
    let c3 := pc3 + bs3
    let borrow := if BitVec.ult uTop c3 then (1 : Word) else 0
    let u4_new := uTop - c3
    cpsTripleWithin 53 (base + div128CallRetOff) (base + correctionSkipBeqOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v9Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ borrow) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
       ((uBase + signExtend12 4064) ↦ₘ u4_new)) :=
  divK_mulsub_full_spec_within_of_sub sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v9Old v5Old v6Old v7Old v10Old v2Old base (sharedDivModCode base) lb_sub

/-- Bundled precondition for mulsub-full wrappers. -/
@[irreducible]
def divKMulsubFullPre
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
     v9Old v5Old v6Old v7Old v10Old v2Old : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
  (.x9 ↦ᵣ v9Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
  (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3976 ↦ₘ j) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop)

/-- Bundled postcondition for mulsub-full wrappers. -/
@[irreducible]
def divKMulsubFullPost
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let p0_lo := qHat * v0
  let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0
  let c0 := pc0 + bs0
  let p1_lo := qHat * v1
  let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1
  let c1 := pc1 + bs1
  let p2_lo := qHat * v2
  let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2
  let c2 := pc2 + bs2
  let p3_lo := qHat * v3
  let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3
  let c3 := pc3 + bs3
  let borrow := if BitVec.ult uTop c3 then (1 : Word) else 0
  let u4_new := uTop - c3
  (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
  (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ uBase) **
  (.x7 ↦ᵣ borrow) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
  (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3976 ↦ₘ j) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
  ((uBase + signExtend12 4064) ↦ₘ u4_new)

theorem divK_mulsub_full_v4_spec_within
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) (v9Old v5Old v6Old v7Old v10Old v2Old : Word) (base : Word) :
    cpsTripleWithin 53 (base + div128CallRetOff) (base + correctionSkipBeqOff) (sharedDivModCode_v4 base)
      (divKMulsubFullPre sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop v9Old v5Old v6Old v7Old v10Old v2Old)
      (divKMulsubFullPost sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  unfold divKMulsubFullPre divKMulsubFullPost
  exact divK_mulsub_full_spec_within_of_sub sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v9Old v5Old v6Old v7Old v10Old v2Old base (sharedDivModCode_v4 base) lb_sub_v4

/-- `divK_mulsub_full_spec_within` replayed over the DIV no-NOP code surface. -/
theorem divK_mulsub_full_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v9Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let p0_lo := qHat * v0
    let p0_hi := rv64_mulhu qHat v0
    let fs0 := p0_lo + (signExtend12 0 : Word)
    let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
    let pc0 := ba0 + p0_hi
    let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
    let un0 := u0 - fs0
    let c0 := pc0 + bs0
    let p1_lo := qHat * v1
    let p1_hi := rv64_mulhu qHat v1
    let fs1 := p1_lo + c0
    let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
    let pc1 := ba1 + p1_hi
    let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
    let un1 := u1 - fs1
    let c1 := pc1 + bs1
    let p2_lo := qHat * v2
    let p2_hi := rv64_mulhu qHat v2
    let fs2 := p2_lo + c1
    let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
    let pc2 := ba2 + p2_hi
    let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
    let un2 := u2 - fs2
    let c2 := pc2 + bs2
    let p3_lo := qHat * v3
    let p3_hi := rv64_mulhu qHat v3
    let fs3 := p3_lo + c2
    let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
    let pc3 := ba3 + p3_hi
    let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
    let un3 := u3 - fs3
    let c3 := pc3 + bs3
    let borrow := if BitVec.ult uTop c3 then (1 : Word) else 0
    let u4_new := uTop - c3
    cpsTripleWithin 53 (base + div128CallRetOff) (base + correctionSkipBeqOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ v9Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x9 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ borrow) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
       ((uBase + signExtend12 4064) ↦ₘ u4_new)) :=
  divK_mulsub_full_spec_within_of_sub sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
    v9Old v5Old v6Old v7Old v10Old v2Old base (divCode_noNop base) lb_sub_noNop

theorem lb_beq_taken {base : Word} : (base + correctionSkipBeqOff : Word) + signExtend13 (156 : BitVec 13) = base + storeLoopOff := by
  rv64_addr

theorem lb_beq_ntaken {base : Word} : (base + correctionSkipBeqOff : Word) + 4 = base + addbackInitOff := by bv_addr

theorem divK_correction_addback_spec_within
    (sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word)
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
    let qHat' := qHat + signExtend12 4095
    cpsTripleWithin 38 (base + correctionSkipBeqOff) (base + addbackBeqOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ borrow) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ aco3) **
       (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4)) := by
  intro upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 qHat'
  -- BEQ x7 x0 156 at base+728
  have hbeq := beq_spec_gen_within .x7 .x0 (156 : BitVec 13) borrow 0 (base + correctionSkipBeqOff)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  -- Eliminate taken path (⌜borrow = 0⌝ contradicts hb)
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hb hpure)
  -- Strip pure fact from not-taken postcondition
  have ntaken_clean : cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + addbackInitOff) (sharedDivModCode base)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      ntaken
  -- Frame ntaken with all addback state
  have ntaken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ u4))
    (by pcFree) ntaken_clean
  -- Compose with addback_full (base+732 → base+880)
  have AB := divK_addback_full_spec_within sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
    borrow v5Old v2Old base
  unfold addbackFullPre addbackFullPost at AB
  seqFrame ntaken_framed AB
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    ntaken_framedAB

/-- `divK_correction_addback_spec_within` replayed over the DIV no-NOP code surface. -/
theorem divK_correction_addback_spec_within_noNop
    (sp uBase borrow qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v5Old v2Old : Word) (base : Word)
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
    let qHat' := qHat + signExtend12 4095
    cpsTripleWithin 38 (base + correctionSkipBeqOff) (base + addbackBeqOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ borrow) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ aco3) **
       (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4)) := by
  intro upc0 ac1_0 aun0 ac2_0 aco0 upc1 ac1_1 aun1 ac2_1 aco1
        upc2 ac1_2 aun2 ac2_2 aco2 upc3 ac1_3 aun3 ac2_3 aco3 aun4 qHat'
  -- BEQ x7 x0 156 at base+728
  have hbeq := beq_spec_gen_within .x7 .x0 (156 : BitVec 13) borrow 0 (base + correctionSkipBeqOff)
  rw [lb_beq_taken, lb_beq_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop 70 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  -- Eliminate taken path (⌜borrow = 0⌝ contradicts hb)
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hb hpure)
  -- Strip pure fact from not-taken postcondition
  have ntaken_clean : cpsTripleWithin 1 (base + correctionSkipBeqOff) (base + addbackInitOff) (divCode_noNop base)
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ borrow) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      ntaken
  -- Frame ntaken with all addback state
  have ntaken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5Old) ** (.x2 ↦ᵣ v2Old) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ u4))
    (by pcFree) ntaken_clean
  -- Compose with addback_full (base+732 → base+880)
  have AB := divK_addback_full_spec_within_noNop sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
    borrow v5Old v2Old base
  unfold addbackFullPre addbackFullPost at AB
  seqFrame ntaken_framed AB
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    ntaken_framedAB

private theorem lb_save_j {base : Word} :
    (base + loopBodyOff : Word) + 4 = base + (loopBodyOff + 4) := by
  simp [BitVec.add_assoc]
private theorem lb_trial_load {base : Word} :
    (base + (loopBodyOff + 4) : Word) + 48 = base + trialCallOff := by bv_addr

/-- Save j + trial load: save j to memory, then load uHi, uLo, vTop for trial quotient.
    13 instructions, loop body indices [0]-[12].
    Entry: base+448, Exit: base+500, CodeReq: sharedDivModCode base. -/
theorem divK_save_trial_load_spec_within
    (sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 13 (base + loopBodyOff) (base + trialCallOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
       (sp + signExtend12 3976 ↦ₘ jOld) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro uAddr vtopBase
  -- 1. Save j: instr [0] at base+448
  have SJ := divK_save_j_spec_within sp j jOld (base + loopBodyOff)
  rw [lb_save_j] at SJ
  have SJe := cpsTripleWithin_extend_code (hmono :=
    lb_sub 0 _ _ (by decide) (by bv_addr) (by decide)) SJ
  -- Frame save_j with trial_load state
  have SJf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) SJe
  -- 2. Trial load: instrs [1]-[12] at base+452
  have TL := divK_trial_load_spec_within sp j n v5Old v6Old v7Old v10Old uHi uLo vTop
    (base + (loopBodyOff + 4))
  dsimp only [] at TL
  rw [lb_trial_load] at TL
  have TLe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 8 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 9 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub 11 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub 12 _ _ (by decide) (by bv_addr) (by decide))))))))))))) TL
  -- 3. Compose save_j + trial_load
  seqFrame SJf TLe
  -- Final permutation
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

/-- Save j + trial load over `divCode_noNop`: save j to memory, then load
    uHi, uLo, vTop for trial quotient. -/
theorem divK_save_trial_load_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 13 (base + loopBodyOff) (base + trialCallOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
       (sp + signExtend12 3976 ↦ₘ jOld) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro uAddr vtopBase
  -- 1. Save j: instr [0] at base+448
  have SJ := divK_save_j_spec_within sp j jOld (base + loopBodyOff)
  rw [lb_save_j] at SJ
  have SJe := cpsTripleWithin_extend_code (hmono :=
    lb_sub_noNop 0 _ _ (by decide) (by bv_addr) (by decide)) SJ
  -- Frame save_j with trial_load state
  have SJf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) SJe
  -- 2. Trial load: instrs [1]-[12] at base+452
  have TL := divK_trial_load_spec_within sp j n v5Old v6Old v7Old v10Old uHi uLo vTop
    (base + (loopBodyOff + 4))
  dsimp only [] at TL
  rw [lb_trial_load] at TL
  have TLe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_noNop 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 8 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 9 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop 11 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_noNop 12 _ _ (by decide) (by bv_addr) (by decide))))))))))))) TL
  -- 3. Compose save_j + trial_load
  seqFrame SJf TLe
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

theorem lb_bltu_taken {base : Word} : (base + trialCallOff : Word) + signExtend13 (12 : BitVec 13) = base + trialJalOff := by
  rv64_addr
theorem lb_bltu_ntaken {base : Word} : (base + trialCallOff : Word) + 4 = base + trialMaxOff := by bv_addr

-- ============================================================================
-- Section 9: Store q[j] + loop control
-- Store q[j] at instrs [109]-[112] (base+884→base+900).
-- Loop control at instrs [113]-[114] (base+900): j--, BGE back to base+448 or exit base+908.
-- ============================================================================

-- Address normalization for store_qj and loop control
theorem lb_sqj {base : Word} : (base + storeLoopOff : Word) + 16 = base + loopControlOff := by bv_addr
private theorem lb_beq_back_ntaken {base : Word} : (base + addbackBeqOff : Word) + 4 = base + storeLoopOff := by bv_addr

/-- BEQ passthrough at [108]: when carry (x7) ≠ 0, BEQ falls through from base+880 to base+884.
    Used to bridge addback exit (base+880) to store_loop entry (base+884). -/
theorem divK_beq_passthrough_within {carry : Word} (base : Word) (hne : carry ≠ 0) :
    cpsTripleWithin 1 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCode base)
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) carry 0 (base + addbackBeqOff)
  rw [lb_beq_back_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hne hpure)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    ntaken

/-- No-NOP variant of `divK_beq_passthrough_within`. -/
theorem divK_beq_passthrough_within_noNop {carry : Word} (base : Word) (hne : carry ≠ 0) :
    cpsTripleWithin 1 (base + addbackBeqOff) (base + storeLoopOff) (divCode_noNop base)
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) carry 0 (base + addbackBeqOff)
  rw [lb_beq_back_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hne hpure)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    ntaken

private theorem lb_beq_back_taken {base : Word} :
    (base + addbackBeqOff : Word) + signExtend13 (8044 : BitVec 13) = base + addbackInitOff := by
  rv64_addr

@[irreducible]
private def n4DoubleAddbackPre
    (sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
  ((uBase + signExtend12 4064) ↦ₘ aun4)

@[irreducible]
def n4DoubleAddbackNamedPost
    (sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word) : Assertion :=
  let ab'   := addbackN4 aun0 aun1 aun2 aun3 aun4 v0 v1 v2 v3
  let qHat'' := qHat' + signExtend12 4095
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
  (.x7 ↦ᵣ addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3) **
  (.x11 ↦ᵣ qHat'') ** (.x5 ↦ᵣ ab'.2.2.2.2) ** (.x2 ↦ᵣ ab'.2.2.2.1) **
  (.x0 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ ab'.1) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ ab'.2.1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ ab'.2.2.1) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ ab'.2.2.2.1) **
  ((uBase + signExtend12 4064) ↦ₘ ab'.2.2.2.2)

theorem n4DoubleAddbackNamedPost_unfold
    {sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word} :
    n4DoubleAddbackNamedPost sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 =
      (let ab'   := addbackN4 aun0 aun1 aun2 aun3 aun4 v0 v1 v2 v3
       let qHat'' := qHat' + signExtend12 4095
       (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3) **
       (.x11 ↦ᵣ qHat'') ** (.x5 ↦ᵣ ab'.2.2.2.2) ** (.x2 ↦ᵣ ab'.2.2.2.1) **
       (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ ab'.1) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ ab'.2.1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ ab'.2.2.1) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ ab'.2.2.2.1) **
       ((uBase + signExtend12 4064) ↦ₘ ab'.2.2.2.2)) := by
  delta n4DoubleAddbackNamedPost; rfl

/-- Double-addback path at [108]: when first addback carry (x7) = 0, BEQ jumps back to [71]
    for a second addback pass. The second addback always produces carry ≠ 0, so BEQ at [108]
    then falls through to base+884.
    Entry: base+880 (after first addback), x7 = 0.
    Exit: base+884 (store entry), with double-addback results. -/
private theorem divK_double_addback_beq_spec_within
    (sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word)
    (base : Word)
    (hcarry2_nz : addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 39 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCode base)
      (n4DoubleAddbackPre sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4)
      (n4DoubleAddbackNamedPost sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4) := by
  unfold n4DoubleAddbackPre n4DoubleAddbackNamedPost addbackN4
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
  let qHat'' := qHat' + signExtend12 4095
  -- 1. BEQ at [108] taken (carry = 0, x7 = 0 = x0) → base+732
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) (0 : Word) 0 (base + addbackBeqOff)
  rw [lb_beq_back_taken, lb_beq_back_ntaken] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  -- Eliminate not-taken path (⌜0 ≠ 0⌝ is absurd)
  have beq_taken := cpsBranchWithin_takenPath hbeq_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure rfl)
  -- Strip pure fact from taken postcondition
  have beq_taken' := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    beq_taken
  have AB2 := divK_addback_full_spec_within sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4
    (0 : Word) aun4 aun3 base
  unfold addbackFullPre addbackFullPost at AB2
  -- 3. BEQ at [108] not taken (carry2 ≠ 0) → base+884
  have haco3_nz : aco3' ≠ 0 := by
    unfold addbackN4_carry at hcarry2_nz
    simp only [] at hcarry2_nz
    exact hcarry2_nz
  have BPT := divK_beq_passthrough_within base haco3_nz
  -- 4. Compose: BEQ taken (→732) + addback2 (732→880) + BEQ ntaken (880→884)
  -- Frame BEQ with addback atoms
  have beq_f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
     ((uBase + signExtend12 4064) ↦ₘ aun4))
    (by pcFree) beq_taken'
  have beq_ab2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) beq_f AB2
  -- Frame BEQ passthrough with addback2 postcondition atoms
  have BPTf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) **
     (.x11 ↦ᵣ qHat'') ** (.x5 ↦ᵣ aun4') ** (.x2 ↦ᵣ aun3') **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0') **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1') **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2') **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3') **
     ((uBase + signExtend12 4064) ↦ₘ aun4'))
    (by pcFree) BPT
  -- Compose (BEQ+addback2) → BEQ passthrough
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) beq_ab2 BPTf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      unfold addbackN4_carry
      xperm_hyp hp)
    full
theorem divK_double_addback_beq_named_spec_within
    (sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4 : Word)
    (base : Word)
    (hcarry2_nz : addbackN4_carry aun0 aun1 aun2 aun3 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 39 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ qHat') ** (.x5 ↦ᵣ aun4) ** (.x2 ↦ᵣ aun3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ aun0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ aun1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ aun2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ aun3) **
       ((uBase + signExtend12 4064) ↦ₘ aun4))
      (n4DoubleAddbackNamedPost sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by unfold n4DoubleAddbackPre; exact hp)
    (fun h hp => hp)
    (divK_double_addback_beq_spec_within sp uBase qHat' v0 v1 v2 v3 aun0 aun1 aun2 aun3 aun4
      base hcarry2_nz)

end EvmAsm.Evm64
