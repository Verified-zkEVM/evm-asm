/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepCompare

  CPS scaffolding for the MULMOD reducer compare ladder.
-/

import EvmAsm.Evm64.MulMod.ReduceCompare
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The high-to-low compare ladder of `evm_mulmod_reduce512_inner_step`.

Entry is `base + 84` relative to the full inner step.  The ladder branches to
`base + 144` when the shifted remainder is at least the modulus, and to
`base + 248` when it is smaller. -/
def evm_mulmod_reduce512_inner_step_compare : Program :=
  LD .x6 .x12 4088 ;;
  LD .x7 .x12 88 ;;
  BLTU .x7 .x6 (52 : BitVec 13) ;;
  BLTU .x6 .x7 (152 : BitVec 13) ;;
  LD .x6 .x12 4080 ;;
  LD .x7 .x12 80 ;;
  BLTU .x7 .x6 (36 : BitVec 13) ;;
  BLTU .x6 .x7 (136 : BitVec 13) ;;
  LD .x6 .x12 4072 ;;
  LD .x7 .x12 72 ;;
  BLTU .x7 .x6 (20 : BitVec 13) ;;
  BLTU .x6 .x7 (120 : BitVec 13) ;;
  LD .x6 .x12 4064 ;;
  LD .x7 .x12 64 ;;
  BLTU .x6 .x7 (108 : BitVec 13)

abbrev evm_mulmod_reduce512_inner_step_compare_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 84) evm_mulmod_reduce512_inner_step_compare

/-- Shared memory footprint for the reducer compare ladder. -/
@[irreducible]
def mulModReduceCompareMem (sp : Word) (r n : EvmWord) : Assertion :=
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded precondition for the reducer compare ladder. -/
@[irreducible]
def mulModReduceComparePre (sp x6Old x7Old : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
  mulModReduceCompareMem sp r n

/-- Folded postcondition for the reducer compare ladder.

The ladder leaves `x6` and `x7` with path-dependent comparison limbs, so this
post keeps ownership of those registers without committing to concrete values.
The Boolean selects the semantic branch result: `true` for the subtract entry
and `false` for the no-sub tail. -/
@[irreducible]
def mulModReduceComparePost (sp : Word) (r n : EvmWord) (willSubtract : Bool) : Assertion :=
  (.x12 ↦ᵣ sp) ** regOwn .x6 ** regOwn .x7 ** mulModReduceCompareMem sp r n **
  ⌜if willSubtract then mulModReduceRemGE r n else mulModReduceRemLT r n⌝


/-- Explicit code requirement for the high-limb `n3 < r3` subtract path. -/
def evm_mulmod_reduce512_inner_step_compare_limb3_gt_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton (base + 84) (.LD .x6 .x12 4088))
    (CodeReq.union (CodeReq.singleton (base + 88) (.LD .x7 .x12 88))
      (CodeReq.singleton (base + 92) (.BLTU .x7 .x6 (52 : BitVec 13))))

/-- Explicit code requirement for the high-limb `r3 < n3` no-sub path. -/
def evm_mulmod_reduce512_inner_step_compare_limb3_lt_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton (base + 84) (.LD .x6 .x12 4088))
    (CodeReq.union (CodeReq.singleton (base + 88) (.LD .x7 .x12 88))
      (CodeReq.union (CodeReq.singleton (base + 92) (.BLTU .x7 .x6 (52 : BitVec 13)))
        (CodeReq.singleton (base + 96) (.BLTU .x6 .x7 (152 : BitVec 13)))))

/-- Raw post after loading the top comparison limbs and exiting through the first BLTU. -/
def mulModReduceCompareLimb3GtRawPost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ EvmWord.getLimbN n 3) ** (.x6 ↦ᵣ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Raw post after the high-limb less/equality branch has passed the second BLTU. -/
def mulModReduceCompareLimb3FallthroughRawPost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ EvmWord.getLimbN r 3) ** (.x7 ↦ᵣ EvmWord.getLimbN n 3) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

def mulModReduceCompareLimb3GtPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb3GtRawPost sp r n ** ⌜mulModReduceRemGE r n⌝

def mulModReduceCompareLimb3LtPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb3FallthroughRawPost sp r n ** ⌜mulModReduceRemLT r n⌝

def mulModReduceCompareLimb3EqPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb3FallthroughRawPost sp r n **
  ⌜EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3⌝

theorem evm_mulmod_reduce512_inner_step_compare_limb3_gt_raw_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hgt : BitVec.ult (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3)) :
    cpsTripleWithin 3 (base + 84) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb3_gt_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3GtRawPost sp r n) := by
  unfold mulModReduceComparePre mulModReduceCompareMem
  unfold evm_mulmod_reduce512_inner_step_compare_limb3_gt_code
  unfold mulModReduceCompareLimb3GtRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old (EvmWord.getLimbN r 3) 4088 (base + 84) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old (EvmWord.getLimbN n 3) 88 (base + 88) (by decide)
  have Braw := bltu_spec_gen_within .x7 .x6 (52 : BitVec 13)
    (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3) (base + 92)
  have B := cpsBranchWithin_takenStripPure2 Braw (fun hp hQf => by
    extract_pure hQf
    obtain ⟨h_not, _⟩ := hQf
    exact h_not hgt)
  rw [show (base + 92 : Word) + signExtend13 (52 : BitVec 13) = base + 144 by rv64_addr] at B
  runBlock L0 L1 B

theorem evm_mulmod_reduce512_inner_step_compare_limb3_gt_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hgt : BitVec.ult (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3)) :
    cpsTripleWithin 3 (base + 84) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb3_gt_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3GtPost sp r n) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
    unfold mulModReduceCompareLimb3GtPost
    exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemGE_of_limb3_gt r n hgt⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb3_gt_raw_spec_within sp base x6Old x7Old r n hgt)

theorem evm_mulmod_reduce512_inner_step_compare_limb3_lt_raw_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hlt : BitVec.ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3)) :
    cpsTripleWithin 4 (base + 84) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb3_lt_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3FallthroughRawPost sp r n) := by
  unfold mulModReduceComparePre mulModReduceCompareMem
  unfold evm_mulmod_reduce512_inner_step_compare_limb3_lt_code
  unfold mulModReduceCompareLimb3FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old (EvmWord.getLimbN r 3) 4088 (base + 84) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old (EvmWord.getLimbN n 3) 88 (base + 88) (by decide)
  have B0raw := bltu_spec_gen_within .x7 .x6 (52 : BitVec 13)
    (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3) (base + 92)
  have B0 := cpsBranchWithin_ntakenStripPure2 B0raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_gt, _⟩ := hQt
    have h_gt_nat := EvmWord.ult_iff.mp h_gt
    have h_lt_nat := EvmWord.ult_iff.mp hlt
    omega)
  rw [show (base + 92 : Word) + 4 = base + 96 by bv_addr] at B0
  have B1raw := bltu_spec_gen_within .x6 .x7 (152 : BitVec 13)
    (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3) (base + 96)
  have B1 := cpsBranchWithin_takenStripPure2 B1raw (fun hp hQf => by
    extract_pure hQf
    obtain ⟨h_not, _⟩ := hQf
    exact h_not hlt)
  rw [show (base + 96 : Word) + signExtend13 (152 : BitVec 13) = base + 248 by rv64_addr] at B1
  runBlock L0 L1 B0 B1

theorem evm_mulmod_reduce512_inner_step_compare_limb3_lt_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hlt : BitVec.ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3)) :
    cpsTripleWithin 4 (base + 84) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb3_lt_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3LtPost sp r n) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
    unfold mulModReduceCompareLimb3LtPost
    exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemLT_of_limb3_lt r n hlt⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb3_lt_raw_spec_within sp base x6Old x7Old r n hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb3_eq_raw_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (h_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3) :
    cpsTripleWithin 4 (base + 84) (base + 100)
      (evm_mulmod_reduce512_inner_step_compare_limb3_lt_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3FallthroughRawPost sp r n) := by
  unfold mulModReduceComparePre mulModReduceCompareMem
  unfold evm_mulmod_reduce512_inner_step_compare_limb3_lt_code
  unfold mulModReduceCompareLimb3FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp x6Old (EvmWord.getLimbN r 3) 4088 (base + 84) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp x7Old (EvmWord.getLimbN n 3) 88 (base + 88) (by decide)
  have B0raw := bltu_spec_gen_within .x7 .x6 (52 : BitVec 13)
    (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3) (base + 92)
  have B0 := cpsBranchWithin_ntakenStripPure2 B0raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_gt, _⟩ := hQt
    rw [← h_eq] at h_gt
    have h_gt_nat := EvmWord.ult_iff.mp h_gt
    omega)
  rw [show (base + 92 : Word) + 4 = base + 96 by bv_addr] at B0
  have B1raw := bltu_spec_gen_within .x6 .x7 (152 : BitVec 13)
    (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3) (base + 96)
  have B1 := cpsBranchWithin_ntakenStripPure2 B1raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_lt, _⟩ := hQt
    rw [h_eq] at h_lt
    have h_lt_nat := EvmWord.ult_iff.mp h_lt
    omega)
  rw [show (base + 96 : Word) + 4 = base + 100 by bv_addr] at B1
  runBlock L0 L1 B0 B1

theorem evm_mulmod_reduce512_inner_step_compare_limb3_eq_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (h_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3) :
    cpsTripleWithin 4 (base + 84) (base + 100)
      (evm_mulmod_reduce512_inner_step_compare_limb3_lt_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3EqPost sp r n) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
    unfold mulModReduceCompareLimb3EqPost
    exact (sepConj_pure_right h).2 ⟨hp, h_eq⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb3_eq_raw_spec_within sp base x6Old x7Old r n h_eq)


/-- Explicit code requirement for the limb2 `n2 < r2` subtract path. -/
def evm_mulmod_reduce512_inner_step_compare_limb2_gt_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton (base + 100) (.LD .x6 .x12 4080))
    (CodeReq.union (CodeReq.singleton (base + 104) (.LD .x7 .x12 80))
      (CodeReq.singleton (base + 108) (.BLTU .x7 .x6 (36 : BitVec 13))))

/-- Explicit code requirement for the limb2 `r2 < n2` no-sub path. -/
def evm_mulmod_reduce512_inner_step_compare_limb2_lt_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton (base + 100) (.LD .x6 .x12 4080))
    (CodeReq.union (CodeReq.singleton (base + 104) (.LD .x7 .x12 80))
      (CodeReq.union (CodeReq.singleton (base + 108) (.BLTU .x7 .x6 (36 : BitVec 13)))
        (CodeReq.singleton (base + 112) (.BLTU .x6 .x7 (136 : BitVec 13)))))

/-- Raw post after loading limb2 comparison operands. -/
def mulModReduceCompareLimb2FallthroughRawPost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ EvmWord.getLimbN r 2) ** (.x7 ↦ᵣ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

def mulModReduceCompareLimb2GtPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb2FallthroughRawPost sp r n ** ⌜mulModReduceRemGE r n⌝

def mulModReduceCompareLimb2LtPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb2FallthroughRawPost sp r n ** ⌜mulModReduceRemLT r n⌝

def mulModReduceCompareLimb2EqPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb2FallthroughRawPost sp r n **
  ⌜EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
    EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2⌝

theorem evm_mulmod_reduce512_inner_step_compare_limb2_gt_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (hgt : BitVec.ult (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2)) :
    cpsTripleWithin 3 (base + 100) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb2_gt_code base)
      (mulModReduceCompareLimb3FallthroughRawPost sp r n)
      (mulModReduceCompareLimb2FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb3FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb2_gt_code
  unfold mulModReduceCompareLimb2FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 3) (EvmWord.getLimbN r 2) 4080 (base + 100) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 3) (EvmWord.getLimbN n 2) 80 (base + 104) (by decide)
  have Braw := bltu_spec_gen_within .x7 .x6 (36 : BitVec 13)
    (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2) (base + 108)
  have B := cpsBranchWithin_takenStripPure2 Braw (fun hp hQf => by
    extract_pure hQf
    obtain ⟨h_not, _⟩ := hQf
    exact h_not hgt)
  rw [show (base + 108 : Word) + signExtend13 (36 : BitVec 13) = base + 144 by rv64_addr] at B
  runBlock L0 L1 B

theorem evm_mulmod_reduce512_inner_step_compare_limb2_gt_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (hgt : BitVec.ult (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2)) :
    cpsTripleWithin 3 (base + 100) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb2_gt_code base)
      (mulModReduceCompareLimb3EqPost sp r n)
      (mulModReduceCompareLimb2GtPost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb3EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb2GtPost
      exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemGE_of_limb2_gt r n h3_eq hgt⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb2_gt_raw_spec_within sp base r n hgt)

theorem evm_mulmod_reduce512_inner_step_compare_limb2_lt_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (hlt : BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)) :
    cpsTripleWithin 4 (base + 100) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb2_lt_code base)
      (mulModReduceCompareLimb3FallthroughRawPost sp r n)
      (mulModReduceCompareLimb2FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb3FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb2_lt_code
  unfold mulModReduceCompareLimb2FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 3) (EvmWord.getLimbN r 2) 4080 (base + 100) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 3) (EvmWord.getLimbN n 2) 80 (base + 104) (by decide)
  have B0raw := bltu_spec_gen_within .x7 .x6 (36 : BitVec 13)
    (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2) (base + 108)
  have B0 := cpsBranchWithin_ntakenStripPure2 B0raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_gt, _⟩ := hQt
    have h_gt_nat := EvmWord.ult_iff.mp h_gt
    have h_lt_nat := EvmWord.ult_iff.mp hlt
    omega)
  rw [show (base + 108 : Word) + 4 = base + 112 by bv_addr] at B0
  have B1raw := bltu_spec_gen_within .x6 .x7 (136 : BitVec 13)
    (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2) (base + 112)
  have B1 := cpsBranchWithin_takenStripPure2 B1raw (fun hp hQf => by
    extract_pure hQf
    obtain ⟨h_not, _⟩ := hQf
    exact h_not hlt)
  rw [show (base + 112 : Word) + signExtend13 (136 : BitVec 13) = base + 248 by rv64_addr] at B1
  runBlock L0 L1 B0 B1

theorem evm_mulmod_reduce512_inner_step_compare_limb2_lt_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (hlt : BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)) :
    cpsTripleWithin 4 (base + 100) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb2_lt_code base)
      (mulModReduceCompareLimb3EqPost sp r n)
      (mulModReduceCompareLimb2LtPost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb3EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb2LtPost
      exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemLT_of_limb2_lt r n h3_eq hlt⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb2_lt_raw_spec_within sp base r n hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb2_eq_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (h_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2) :
    cpsTripleWithin 4 (base + 100) (base + 116)
      (evm_mulmod_reduce512_inner_step_compare_limb2_lt_code base)
      (mulModReduceCompareLimb3FallthroughRawPost sp r n)
      (mulModReduceCompareLimb2FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb3FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb2_lt_code
  unfold mulModReduceCompareLimb2FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 3) (EvmWord.getLimbN r 2) 4080 (base + 100) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 3) (EvmWord.getLimbN n 2) 80 (base + 104) (by decide)
  have B0raw := bltu_spec_gen_within .x7 .x6 (36 : BitVec 13)
    (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2) (base + 108)
  have B0 := cpsBranchWithin_ntakenStripPure2 B0raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_gt, _⟩ := hQt
    rw [← h_eq] at h_gt
    have h_gt_nat := EvmWord.ult_iff.mp h_gt
    omega)
  rw [show (base + 108 : Word) + 4 = base + 112 by bv_addr] at B0
  have B1raw := bltu_spec_gen_within .x6 .x7 (136 : BitVec 13)
    (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2) (base + 112)
  have B1 := cpsBranchWithin_ntakenStripPure2 B1raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_lt, _⟩ := hQt
    rw [h_eq] at h_lt
    have h_lt_nat := EvmWord.ult_iff.mp h_lt
    omega)
  rw [show (base + 112 : Word) + 4 = base + 116 by bv_addr] at B1
  runBlock L0 L1 B0 B1

theorem evm_mulmod_reduce512_inner_step_compare_limb2_eq_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2) :
    cpsTripleWithin 4 (base + 100) (base + 116)
      (evm_mulmod_reduce512_inner_step_compare_limb2_lt_code base)
      (mulModReduceCompareLimb3EqPost sp r n)
      (mulModReduceCompareLimb2EqPost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb3EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb2EqPost
      exact (sepConj_pure_right h).2 ⟨hp, ⟨h3_eq, h2_eq⟩⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb2_eq_raw_spec_within sp base r n h2_eq)


/-- Explicit code requirement for the limb1 `n1 < r1` subtract path. -/
def evm_mulmod_reduce512_inner_step_compare_limb1_gt_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton (base + 116) (.LD .x6 .x12 4072))
    (CodeReq.union (CodeReq.singleton (base + 120) (.LD .x7 .x12 72))
      (CodeReq.singleton (base + 124) (.BLTU .x7 .x6 (20 : BitVec 13))))

/-- Explicit code requirement for the limb1 `r1 < n1` no-sub path. -/
def evm_mulmod_reduce512_inner_step_compare_limb1_lt_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton (base + 116) (.LD .x6 .x12 4072))
    (CodeReq.union (CodeReq.singleton (base + 120) (.LD .x7 .x12 72))
      (CodeReq.union (CodeReq.singleton (base + 124) (.BLTU .x7 .x6 (20 : BitVec 13)))
        (CodeReq.singleton (base + 128) (.BLTU .x6 .x7 (120 : BitVec 13)))))

/-- Raw post after loading limb1 comparison operands. -/
def mulModReduceCompareLimb1FallthroughRawPost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ EvmWord.getLimbN r 1) ** (.x7 ↦ᵣ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

def mulModReduceCompareLimb1GtPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb1FallthroughRawPost sp r n ** ⌜mulModReduceRemGE r n⌝

def mulModReduceCompareLimb1LtPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb1FallthroughRawPost sp r n ** ⌜mulModReduceRemLT r n⌝

def mulModReduceCompareLimb1EqPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb1FallthroughRawPost sp r n **
  ⌜EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
    EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2 ∧
    EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1⌝

theorem evm_mulmod_reduce512_inner_step_compare_limb1_gt_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (hgt : BitVec.ult (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1)) :
    cpsTripleWithin 3 (base + 116) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb1_gt_code base)
      (mulModReduceCompareLimb2FallthroughRawPost sp r n)
      (mulModReduceCompareLimb1FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb2FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb1_gt_code
  unfold mulModReduceCompareLimb1FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 1) 4072 (base + 116) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 2) (EvmWord.getLimbN n 1) 72 (base + 120) (by decide)
  have Braw := bltu_spec_gen_within .x7 .x6 (20 : BitVec 13)
    (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1) (base + 124)
  have B := cpsBranchWithin_takenStripPure2 Braw (fun hp hQf => by
    extract_pure hQf
    obtain ⟨h_not, _⟩ := hQf
    exact h_not hgt)
  rw [show (base + 124 : Word) + signExtend13 (20 : BitVec 13) = base + 144 by rv64_addr] at B
  runBlock L0 L1 B

theorem evm_mulmod_reduce512_inner_step_compare_limb1_gt_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (hgt : BitVec.ult (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1)) :
    cpsTripleWithin 3 (base + 116) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb1_gt_code base)
      (mulModReduceCompareLimb2EqPost sp r n)
      (mulModReduceCompareLimb1GtPost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb2EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb1GtPost
      exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemGE_of_limb1_gt r n h3_eq h2_eq hgt⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb1_gt_raw_spec_within sp base r n hgt)

theorem evm_mulmod_reduce512_inner_step_compare_limb1_lt_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (hlt : BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)) :
    cpsTripleWithin 4 (base + 116) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb1_lt_code base)
      (mulModReduceCompareLimb2FallthroughRawPost sp r n)
      (mulModReduceCompareLimb1FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb2FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb1_lt_code
  unfold mulModReduceCompareLimb1FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 1) 4072 (base + 116) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 2) (EvmWord.getLimbN n 1) 72 (base + 120) (by decide)
  have B0raw := bltu_spec_gen_within .x7 .x6 (20 : BitVec 13)
    (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1) (base + 124)
  have B0 := cpsBranchWithin_ntakenStripPure2 B0raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_gt, _⟩ := hQt
    have h_gt_nat := EvmWord.ult_iff.mp h_gt
    have h_lt_nat := EvmWord.ult_iff.mp hlt
    omega)
  rw [show (base + 124 : Word) + 4 = base + 128 by bv_addr] at B0
  have B1raw := bltu_spec_gen_within .x6 .x7 (120 : BitVec 13)
    (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1) (base + 128)
  have B1 := cpsBranchWithin_takenStripPure2 B1raw (fun hp hQf => by
    extract_pure hQf
    obtain ⟨h_not, _⟩ := hQf
    exact h_not hlt)
  rw [show (base + 128 : Word) + signExtend13 (120 : BitVec 13) = base + 248 by rv64_addr] at B1
  runBlock L0 L1 B0 B1

theorem evm_mulmod_reduce512_inner_step_compare_limb1_lt_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (hlt : BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)) :
    cpsTripleWithin 4 (base + 116) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb1_lt_code base)
      (mulModReduceCompareLimb2EqPost sp r n)
      (mulModReduceCompareLimb1LtPost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb2EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb1LtPost
      exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemLT_of_limb1_lt r n h3_eq h2_eq hlt⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb1_lt_raw_spec_within sp base r n hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb1_eq_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (h_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1) :
    cpsTripleWithin 4 (base + 116) (base + 132)
      (evm_mulmod_reduce512_inner_step_compare_limb1_lt_code base)
      (mulModReduceCompareLimb2FallthroughRawPost sp r n)
      (mulModReduceCompareLimb1FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb2FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb1_lt_code
  unfold mulModReduceCompareLimb1FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 1) 4072 (base + 116) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 2) (EvmWord.getLimbN n 1) 72 (base + 120) (by decide)
  have B0raw := bltu_spec_gen_within .x7 .x6 (20 : BitVec 13)
    (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1) (base + 124)
  have B0 := cpsBranchWithin_ntakenStripPure2 B0raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_gt, _⟩ := hQt
    rw [← h_eq] at h_gt
    have h_gt_nat := EvmWord.ult_iff.mp h_gt
    omega)
  rw [show (base + 124 : Word) + 4 = base + 128 by bv_addr] at B0
  have B1raw := bltu_spec_gen_within .x6 .x7 (120 : BitVec 13)
    (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1) (base + 128)
  have B1 := cpsBranchWithin_ntakenStripPure2 B1raw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_lt, _⟩ := hQt
    rw [h_eq] at h_lt
    have h_lt_nat := EvmWord.ult_iff.mp h_lt
    omega)
  rw [show (base + 128 : Word) + 4 = base + 132 by bv_addr] at B1
  runBlock L0 L1 B0 B1

theorem evm_mulmod_reduce512_inner_step_compare_limb1_eq_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1) :
    cpsTripleWithin 4 (base + 116) (base + 132)
      (evm_mulmod_reduce512_inner_step_compare_limb1_lt_code base)
      (mulModReduceCompareLimb2EqPost sp r n)
      (mulModReduceCompareLimb1EqPost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb2EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb1EqPost
      exact (sepConj_pure_right h).2 ⟨hp, ⟨h3_eq, h2_eq, h1_eq⟩⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb1_eq_raw_spec_within sp base r n h1_eq)


/-- Explicit code requirement for the limb0 `r0 < n0` no-sub path. -/
def evm_mulmod_reduce512_inner_step_compare_limb0_lt_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton (base + 132) (.LD .x6 .x12 4064))
    (CodeReq.union (CodeReq.singleton (base + 136) (.LD .x7 .x12 64))
      (CodeReq.singleton (base + 140) (.BLTU .x6 .x7 (108 : BitVec 13))))

/-- Raw post after loading limb0 comparison operands. -/
def mulModReduceCompareLimb0FallthroughRawPost (sp : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ EvmWord.getLimbN r 0) ** (.x7 ↦ᵣ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

def mulModReduceCompareLimb0GePost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb0FallthroughRawPost sp r n ** ⌜mulModReduceRemGE r n⌝

def mulModReduceCompareLimb0LtPost (sp : Word) (r n : EvmWord) : Assertion :=
  mulModReduceCompareLimb0FallthroughRawPost sp r n ** ⌜mulModReduceRemLT r n⌝

theorem evm_mulmod_reduce512_inner_step_compare_limb0_lt_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (hlt : BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    cpsTripleWithin 3 (base + 132) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb0_lt_code base)
      (mulModReduceCompareLimb1FallthroughRawPost sp r n)
      (mulModReduceCompareLimb0FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb1FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb0_lt_code
  unfold mulModReduceCompareLimb0FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 1) (EvmWord.getLimbN r 0) 4064 (base + 132) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 1) (EvmWord.getLimbN n 0) 64 (base + 136) (by decide)
  have Braw := bltu_spec_gen_within .x6 .x7 (108 : BitVec 13)
    (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0) (base + 140)
  have B := cpsBranchWithin_takenStripPure2 Braw (fun hp hQf => by
    extract_pure hQf
    obtain ⟨h_not, _⟩ := hQf
    exact h_not hlt)
  rw [show (base + 140 : Word) + signExtend13 (108 : BitVec 13) = base + 248 by rv64_addr] at B
  runBlock L0 L1 B

theorem evm_mulmod_reduce512_inner_step_compare_limb0_lt_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1)
    (hlt : BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    cpsTripleWithin 3 (base + 132) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_limb0_lt_code base)
      (mulModReduceCompareLimb1EqPost sp r n)
      (mulModReduceCompareLimb0LtPost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb1EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb0LtPost
      exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemLT_of_limb0_lt r n h3_eq h2_eq h1_eq hlt⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb0_lt_raw_spec_within sp base r n hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb0_ge_raw_spec_within
    (sp base : Word) (r n : EvmWord)
    (hge : ¬ BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    cpsTripleWithin 3 (base + 132) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb0_lt_code base)
      (mulModReduceCompareLimb1FallthroughRawPost sp r n)
      (mulModReduceCompareLimb0FallthroughRawPost sp r n) := by
  unfold mulModReduceCompareLimb1FallthroughRawPost
  unfold evm_mulmod_reduce512_inner_step_compare_limb0_lt_code
  unfold mulModReduceCompareLimb0FallthroughRawPost
  have L0 := ld_spec_gen_within .x6 .x12 sp (EvmWord.getLimbN r 1) (EvmWord.getLimbN r 0) 4064 (base + 132) (by decide)
  have L1 := ld_spec_gen_within .x7 .x12 sp (EvmWord.getLimbN n 1) (EvmWord.getLimbN n 0) 64 (base + 136) (by decide)
  have Braw := bltu_spec_gen_within .x6 .x7 (108 : BitVec 13)
    (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0) (base + 140)
  have B := cpsBranchWithin_ntakenStripPure2 Braw (fun hp hQt => by
    extract_pure hQt
    obtain ⟨h_lt, _⟩ := hQt
    exact hge h_lt)
  rw [show (base + 140 : Word) + 4 = base + 144 by bv_addr] at B
  runBlock L0 L1 B

theorem evm_mulmod_reduce512_inner_step_compare_limb0_ge_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1)
    (hge : ¬ BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    cpsTripleWithin 3 (base + 132) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_limb0_lt_code base)
      (mulModReduceCompareLimb1EqPost sp r n)
      (mulModReduceCompareLimb0GePost sp r n) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      unfold mulModReduceCompareLimb1EqPost at hp
      exact ((sepConj_pure_right h).1 hp).1)
    (fun h hp => by
      unfold mulModReduceCompareLimb0GePost
      exact (sepConj_pure_right h).2 ⟨hp, mulModReduceRemGE_of_limb0_ge r n h3_eq h2_eq h1_eq hge⟩)
    (evm_mulmod_reduce512_inner_step_compare_limb0_ge_raw_spec_within sp base r n hge)


/-- The high-limb gt path code is a prefix of the full compare ladder. -/
theorem evm_mulmod_reduce512_inner_step_compare_limb3_gt_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce512_inner_step_compare_limb3_gt_code base =
      CodeReq.ofProg (base + 84)
        [(.LD .x6 .x12 4088), (.LD .x7 .x12 88), (.BLTU .x7 .x6 (52 : BitVec 13))] := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_compare_limb3_gt_code
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 84 : Word) + 4 = base + 88 by bv_addr]
  rw [show (base + 88 : Word) + 4 = base + 92 by bv_addr]

theorem evm_mulmod_reduce512_inner_step_compare_limb3_gt_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_limb3_gt_code base a = some i →
      evm_mulmod_reduce512_inner_step_compare_code base a = some i := by
  rw [evm_mulmod_reduce512_inner_step_compare_limb3_gt_code_eq_ofProg base]
  unfold evm_mulmod_reduce512_inner_step_compare_code
  refine CodeReq.ofProg_mono_sub (base + 84) (base + 84)
    evm_mulmod_reduce512_inner_step_compare
    [(.LD .x6 .x12 4088), (.LD .x7 .x12 88), (.BLTU .x7 .x6 (52 : BitVec 13))]
    0 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

/-- The high-limb lt/equality path code is a prefix of the full compare ladder. -/
theorem evm_mulmod_reduce512_inner_step_compare_limb3_lt_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce512_inner_step_compare_limb3_lt_code base =
      CodeReq.ofProg (base + 84)
        [(.LD .x6 .x12 4088), (.LD .x7 .x12 88), (.BLTU .x7 .x6 (52 : BitVec 13)),
          (.BLTU .x6 .x7 (152 : BitVec 13))] := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_compare_limb3_lt_code
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 84 : Word) + 4 = base + 88 by bv_addr]
  rw [show (base + 88 : Word) + 4 = base + 92 by bv_addr]
  rw [show (base + 92 : Word) + 4 = base + 96 by bv_addr]

theorem evm_mulmod_reduce512_inner_step_compare_limb3_lt_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_limb3_lt_code base a = some i →
      evm_mulmod_reduce512_inner_step_compare_code base a = some i := by
  rw [evm_mulmod_reduce512_inner_step_compare_limb3_lt_code_eq_ofProg base]
  unfold evm_mulmod_reduce512_inner_step_compare_code
  refine CodeReq.ofProg_mono_sub (base + 84) (base + 84)
    evm_mulmod_reduce512_inner_step_compare
    [(.LD .x6 .x12 4088), (.LD .x7 .x12 88), (.BLTU .x7 .x6 (52 : BitVec 13)),
      (.BLTU .x6 .x7 (152 : BitVec 13))]
    0 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

/-- The limb2 gt path code is a subrange of the full compare ladder. -/
theorem evm_mulmod_reduce512_inner_step_compare_limb2_gt_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce512_inner_step_compare_limb2_gt_code base =
      CodeReq.ofProg (base + 100)
        [(.LD .x6 .x12 4080), (.LD .x7 .x12 80), (.BLTU .x7 .x6 (36 : BitVec 13))] := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_compare_limb2_gt_code
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 100 : Word) + 4 = base + 104 by bv_addr]
  rw [show (base + 104 : Word) + 4 = base + 108 by bv_addr]

theorem evm_mulmod_reduce512_inner_step_compare_limb2_gt_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_limb2_gt_code base a = some i →
      evm_mulmod_reduce512_inner_step_compare_code base a = some i := by
  rw [evm_mulmod_reduce512_inner_step_compare_limb2_gt_code_eq_ofProg base]
  unfold evm_mulmod_reduce512_inner_step_compare_code
  refine CodeReq.ofProg_mono_sub (base + 84) (base + 100)
    evm_mulmod_reduce512_inner_step_compare
    [(.LD .x6 .x12 4080), (.LD .x7 .x12 80), (.BLTU .x7 .x6 (36 : BitVec 13))]
    4 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 4) = (16 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

/-- The limb2 lt/equality path code is a subrange of the full compare ladder. -/
theorem evm_mulmod_reduce512_inner_step_compare_limb2_lt_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce512_inner_step_compare_limb2_lt_code base =
      CodeReq.ofProg (base + 100)
        [(.LD .x6 .x12 4080), (.LD .x7 .x12 80), (.BLTU .x7 .x6 (36 : BitVec 13)),
          (.BLTU .x6 .x7 (136 : BitVec 13))] := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_compare_limb2_lt_code
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 100 : Word) + 4 = base + 104 by bv_addr]
  rw [show (base + 104 : Word) + 4 = base + 108 by bv_addr]
  rw [show (base + 108 : Word) + 4 = base + 112 by bv_addr]

theorem evm_mulmod_reduce512_inner_step_compare_limb2_lt_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_limb2_lt_code base a = some i →
      evm_mulmod_reduce512_inner_step_compare_code base a = some i := by
  rw [evm_mulmod_reduce512_inner_step_compare_limb2_lt_code_eq_ofProg base]
  unfold evm_mulmod_reduce512_inner_step_compare_code
  refine CodeReq.ofProg_mono_sub (base + 84) (base + 100)
    evm_mulmod_reduce512_inner_step_compare
    [(.LD .x6 .x12 4080), (.LD .x7 .x12 80), (.BLTU .x7 .x6 (36 : BitVec 13)),
      (.BLTU .x6 .x7 (136 : BitVec 13))]
    4 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 4) = (16 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

/-- The limb1 gt path code is a subrange of the full compare ladder. -/
theorem evm_mulmod_reduce512_inner_step_compare_limb1_gt_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce512_inner_step_compare_limb1_gt_code base =
      CodeReq.ofProg (base + 116)
        [(.LD .x6 .x12 4072), (.LD .x7 .x12 72), (.BLTU .x7 .x6 (20 : BitVec 13))] := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_compare_limb1_gt_code
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 116 : Word) + 4 = base + 120 by bv_addr]
  rw [show (base + 120 : Word) + 4 = base + 124 by bv_addr]

theorem evm_mulmod_reduce512_inner_step_compare_limb1_gt_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_limb1_gt_code base a = some i →
      evm_mulmod_reduce512_inner_step_compare_code base a = some i := by
  rw [evm_mulmod_reduce512_inner_step_compare_limb1_gt_code_eq_ofProg base]
  unfold evm_mulmod_reduce512_inner_step_compare_code
  refine CodeReq.ofProg_mono_sub (base + 84) (base + 116)
    evm_mulmod_reduce512_inner_step_compare
    [(.LD .x6 .x12 4072), (.LD .x7 .x12 72), (.BLTU .x7 .x6 (20 : BitVec 13))]
    8 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 8) = (32 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

/-- The limb1 lt/equality path code is a subrange of the full compare ladder. -/
theorem evm_mulmod_reduce512_inner_step_compare_limb1_lt_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce512_inner_step_compare_limb1_lt_code base =
      CodeReq.ofProg (base + 116)
        [(.LD .x6 .x12 4072), (.LD .x7 .x12 72), (.BLTU .x7 .x6 (20 : BitVec 13)),
          (.BLTU .x6 .x7 (120 : BitVec 13))] := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_compare_limb1_lt_code
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 116 : Word) + 4 = base + 120 by bv_addr]
  rw [show (base + 120 : Word) + 4 = base + 124 by bv_addr]
  rw [show (base + 124 : Word) + 4 = base + 128 by bv_addr]

theorem evm_mulmod_reduce512_inner_step_compare_limb1_lt_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_limb1_lt_code base a = some i →
      evm_mulmod_reduce512_inner_step_compare_code base a = some i := by
  rw [evm_mulmod_reduce512_inner_step_compare_limb1_lt_code_eq_ofProg base]
  unfold evm_mulmod_reduce512_inner_step_compare_code
  refine CodeReq.ofProg_mono_sub (base + 84) (base + 116)
    evm_mulmod_reduce512_inner_step_compare
    [(.LD .x6 .x12 4072), (.LD .x7 .x12 72), (.BLTU .x7 .x6 (20 : BitVec 13)),
      (.BLTU .x6 .x7 (120 : BitVec 13))]
    8 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 8) = (32 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

/-- The limb0 path code is a suffix subrange of the full compare ladder. -/
theorem evm_mulmod_reduce512_inner_step_compare_limb0_lt_code_eq_ofProg (base : Word) :
    evm_mulmod_reduce512_inner_step_compare_limb0_lt_code base =
      CodeReq.ofProg (base + 132)
        [(.LD .x6 .x12 4064), (.LD .x7 .x12 64), (.BLTU .x6 .x7 (108 : BitVec 13))] := by
  funext a
  unfold evm_mulmod_reduce512_inner_step_compare_limb0_lt_code
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  rw [show (base + 132 : Word) + 4 = base + 136 by bv_addr]
  rw [show (base + 136 : Word) + 4 = base + 140 by bv_addr]

theorem evm_mulmod_reduce512_inner_step_compare_limb0_lt_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_limb0_lt_code base a = some i →
      evm_mulmod_reduce512_inner_step_compare_code base a = some i := by
  rw [evm_mulmod_reduce512_inner_step_compare_limb0_lt_code_eq_ofProg base]
  unfold evm_mulmod_reduce512_inner_step_compare_code
  refine CodeReq.ofProg_mono_sub (base + 84) (base + 132)
    evm_mulmod_reduce512_inner_step_compare
    [(.LD .x6 .x12 4064), (.LD .x7 .x12 64), (.BLTU .x6 .x7 (108 : BitVec 13))]
    12 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 12) = (48 : Word) by decide]
    bv_addr
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_compare_limb3_gt_full_code_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hgt : BitVec.ult (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3)) :
    cpsTripleWithin 3 (base + 84) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3GtPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb3_gt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb3_gt_spec_within sp base x6Old x7Old r n hgt)

theorem evm_mulmod_reduce512_inner_step_compare_limb3_lt_full_code_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hlt : BitVec.ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3)) :
    cpsTripleWithin 4 (base + 84) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3LtPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb3_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb3_lt_spec_within sp base x6Old x7Old r n hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb3_eq_full_code_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (h_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3) :
    cpsTripleWithin 4 (base + 84) (base + 100)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceComparePre sp x6Old x7Old r n)
      (mulModReduceCompareLimb3EqPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb3_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb3_eq_spec_within sp base x6Old x7Old r n h_eq)

theorem evm_mulmod_reduce512_inner_step_compare_limb2_gt_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (hgt : BitVec.ult (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2)) :
    cpsTripleWithin 3 (base + 100) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb3EqPost sp r n)
      (mulModReduceCompareLimb2GtPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb2_gt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb2_gt_spec_within sp base r n h3_eq hgt)

theorem evm_mulmod_reduce512_inner_step_compare_limb2_lt_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (hlt : BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)) :
    cpsTripleWithin 4 (base + 100) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb3EqPost sp r n)
      (mulModReduceCompareLimb2LtPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb2_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb2_lt_spec_within sp base r n h3_eq hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb2_eq_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2) :
    cpsTripleWithin 4 (base + 100) (base + 116)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb3EqPost sp r n)
      (mulModReduceCompareLimb2EqPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb2_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb2_eq_spec_within sp base r n h3_eq h2_eq)

theorem evm_mulmod_reduce512_inner_step_compare_limb1_gt_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (hgt : BitVec.ult (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1)) :
    cpsTripleWithin 3 (base + 116) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb2EqPost sp r n)
      (mulModReduceCompareLimb1GtPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb1_gt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb1_gt_spec_within sp base r n h3_eq h2_eq hgt)

theorem evm_mulmod_reduce512_inner_step_compare_limb1_lt_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (hlt : BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)) :
    cpsTripleWithin 4 (base + 116) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb2EqPost sp r n)
      (mulModReduceCompareLimb1LtPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb1_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb1_lt_spec_within sp base r n h3_eq h2_eq hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb1_eq_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1) :
    cpsTripleWithin 4 (base + 116) (base + 132)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb2EqPost sp r n)
      (mulModReduceCompareLimb1EqPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb1_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb1_eq_spec_within sp base r n h3_eq h2_eq h1_eq)

theorem evm_mulmod_reduce512_inner_step_compare_limb0_lt_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1)
    (hlt : BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    cpsTripleWithin 3 (base + 132) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb1EqPost sp r n)
      (mulModReduceCompareLimb0LtPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb0_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb0_lt_spec_within sp base r n h3_eq h2_eq h1_eq hlt)

theorem evm_mulmod_reduce512_inner_step_compare_limb0_ge_full_code_spec_within
    (sp base : Word) (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1)
    (hge : ¬ BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    cpsTripleWithin 3 (base + 132) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceCompareLimb1EqPost sp r n)
      (mulModReduceCompareLimb0GePost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_limb0_lt_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_limb0_ge_spec_within sp base r n h3_eq h2_eq h1_eq hge)


theorem comparePost_of_limb3GtPost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb3GtPost sp r n h → mulModReduceComparePost sp r n true h := by
  intro h hp
  unfold mulModReduceCompareLimb3GtPost mulModReduceCompareLimb3GtRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [ite_true]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _)))) h hp1
  xperm_hyp hp2

theorem comparePost_of_limb2GtPost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb2GtPost sp r n h → mulModReduceComparePost sp r n true h := by
  intro h hp
  unfold mulModReduceCompareLimb2GtPost mulModReduceCompareLimb2FallthroughRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [ite_true]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp1
  xperm_hyp hp2

theorem comparePost_of_limb1GtPost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb1GtPost sp r n h → mulModReduceComparePost sp r n true h := by
  intro h hp
  unfold mulModReduceCompareLimb1GtPost mulModReduceCompareLimb1FallthroughRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [ite_true]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp1
  xperm_hyp hp2

theorem comparePost_of_limb0GePost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb0GePost sp r n h → mulModReduceComparePost sp r n true h := by
  intro h hp
  unfold mulModReduceCompareLimb0GePost mulModReduceCompareLimb0FallthroughRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [ite_true]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp1
  xperm_hyp hp2

theorem comparePost_of_limb3LtPost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb3LtPost sp r n h → mulModReduceComparePost sp r n false h := by
  intro h hp
  unfold mulModReduceCompareLimb3LtPost mulModReduceCompareLimb3FallthroughRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp1
  xperm_hyp hp2

theorem comparePost_of_limb2LtPost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb2LtPost sp r n h → mulModReduceComparePost sp r n false h := by
  intro h hp
  unfold mulModReduceCompareLimb2LtPost mulModReduceCompareLimb2FallthroughRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp1
  xperm_hyp hp2

theorem comparePost_of_limb1LtPost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb1LtPost sp r n h → mulModReduceComparePost sp r n false h := by
  intro h hp
  unfold mulModReduceCompareLimb1LtPost mulModReduceCompareLimb1FallthroughRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp1
  xperm_hyp hp2

theorem comparePost_of_limb0LtPost (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceCompareLimb0LtPost sp r n h → mulModReduceComparePost sp r n false h := by
  intro h hp
  unfold mulModReduceCompareLimb0LtPost mulModReduceCompareLimb0FallthroughRawPost at hp
  unfold mulModReduceComparePost mulModReduceCompareMem
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp1
  xperm_hyp hp2

theorem evm_mulmod_reduce512_inner_step_compare_ge_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hge : mulModReduceRemGE r n) :
    cpsTripleWithin 15 (base + 84) (base + 144)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceComparePre sp x6Old x7Old r n ** ⌜mulModReduceRemGE r n⌝)
      (mulModReduceComparePost sp r n true) := by
  rcases mulModReduceRemGE_cases r n hge with h3_gt | hrest
  · exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb3GtPost sp r n)
        (evm_mulmod_reduce512_inner_step_compare_limb3_gt_full_code_spec_within sp base x6Old x7Old r n h3_gt))
  rcases hrest with ⟨h3_eq, h2_gt⟩ | hrest
  · have hseq := cpsTripleWithin_seq_same_cr
      (evm_mulmod_reduce512_inner_step_compare_limb3_eq_full_code_spec_within sp base x6Old x7Old r n h3_eq)
      (evm_mulmod_reduce512_inner_step_compare_limb2_gt_full_code_spec_within sp base r n h3_eq h2_gt)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb2GtPost sp r n) hseq)
  rcases hrest with ⟨h3_eq, h2_eq, h1_gt⟩ | ⟨h3_eq, h2_eq, h1_eq, h0_ge⟩
  · have hseq0 := cpsTripleWithin_seq_same_cr
      (evm_mulmod_reduce512_inner_step_compare_limb3_eq_full_code_spec_within sp base x6Old x7Old r n h3_eq)
      (evm_mulmod_reduce512_inner_step_compare_limb2_eq_full_code_spec_within sp base r n h3_eq h2_eq)
    have hseq := cpsTripleWithin_seq_same_cr hseq0
      (evm_mulmod_reduce512_inner_step_compare_limb1_gt_full_code_spec_within sp base r n h3_eq h2_eq h1_gt)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb1GtPost sp r n) hseq)
  · have hseq0 := cpsTripleWithin_seq_same_cr
      (evm_mulmod_reduce512_inner_step_compare_limb3_eq_full_code_spec_within sp base x6Old x7Old r n h3_eq)
      (evm_mulmod_reduce512_inner_step_compare_limb2_eq_full_code_spec_within sp base r n h3_eq h2_eq)
    have hseq1 := cpsTripleWithin_seq_same_cr hseq0
      (evm_mulmod_reduce512_inner_step_compare_limb1_eq_full_code_spec_within sp base r n h3_eq h2_eq h1_eq)
    have hseq := cpsTripleWithin_seq_same_cr hseq1
      (evm_mulmod_reduce512_inner_step_compare_limb0_ge_full_code_spec_within sp base r n h3_eq h2_eq h1_eq h0_ge)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb0GePost sp r n) hseq)

theorem evm_mulmod_reduce512_inner_step_compare_lt_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hlt : mulModReduceRemLT r n) :
    cpsTripleWithin 15 (base + 84) (base + 248)
      (evm_mulmod_reduce512_inner_step_compare_code base)
      (mulModReduceComparePre sp x6Old x7Old r n ** ⌜mulModReduceRemLT r n⌝)
      (mulModReduceComparePost sp r n false) := by
  rcases mulModReduceRemLT_cases r n hlt with h3_lt | hrest
  · exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb3LtPost sp r n)
        (evm_mulmod_reduce512_inner_step_compare_limb3_lt_full_code_spec_within sp base x6Old x7Old r n h3_lt))
  rcases hrest with ⟨h3_eq, h2_lt⟩ | hrest
  · have hseq := cpsTripleWithin_seq_same_cr
      (evm_mulmod_reduce512_inner_step_compare_limb3_eq_full_code_spec_within sp base x6Old x7Old r n h3_eq)
      (evm_mulmod_reduce512_inner_step_compare_limb2_lt_full_code_spec_within sp base r n h3_eq h2_lt)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb2LtPost sp r n) hseq)
  rcases hrest with ⟨h3_eq, h2_eq, h1_lt⟩ | ⟨h3_eq, h2_eq, h1_eq, h0_lt⟩
  · have hseq0 := cpsTripleWithin_seq_same_cr
      (evm_mulmod_reduce512_inner_step_compare_limb3_eq_full_code_spec_within sp base x6Old x7Old r n h3_eq)
      (evm_mulmod_reduce512_inner_step_compare_limb2_eq_full_code_spec_within sp base r n h3_eq h2_eq)
    have hseq := cpsTripleWithin_seq_same_cr hseq0
      (evm_mulmod_reduce512_inner_step_compare_limb1_lt_full_code_spec_within sp base r n h3_eq h2_eq h1_lt)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb1LtPost sp r n) hseq)
  · have hseq0 := cpsTripleWithin_seq_same_cr
      (evm_mulmod_reduce512_inner_step_compare_limb3_eq_full_code_spec_within sp base x6Old x7Old r n h3_eq)
      (evm_mulmod_reduce512_inner_step_compare_limb2_eq_full_code_spec_within sp base r n h3_eq h2_eq)
    have hseq1 := cpsTripleWithin_seq_same_cr hseq0
      (evm_mulmod_reduce512_inner_step_compare_limb1_eq_full_code_spec_within sp base r n h3_eq h2_eq h1_eq)
    have hseq := cpsTripleWithin_seq_same_cr hseq1
      (evm_mulmod_reduce512_inner_step_compare_limb0_lt_full_code_spec_within sp base r n h3_eq h2_eq h1_eq h0_lt)
    exact cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken
        (fun h hp => ((sepConj_pure_right h).1 hp).1)
        (comparePost_of_limb0LtPost sp r n) hseq)

end EvmAsm.Evm64
