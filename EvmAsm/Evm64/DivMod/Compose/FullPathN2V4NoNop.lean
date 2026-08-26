/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop

  v4/no-NOP wrappers for the n=2 DIV loop-body j=0 exit paths.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2LoopUnified
public import EvmAsm.Evm64.DivMod.Compose.FullPathV4NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2MaxV4NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2CallV4NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2AddbackV4NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2CallAddbackV4NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Sp-relative n=2 max-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2MaxSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
  ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
  ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ uTop) **
  ((sp + signExtend12 4088) ↦ₘ qOld)

/-- Sp-relative n=2 call-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2CallSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  regOwn .x1 ** (sp + signExtend12 3936 ↦ₘ scratchMem)

@[irreducible]
def loopBodyN2CallSkipJ0NormPreV4NoX1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- n=2 max-skip j>0 precondition over `divCode_noNop_v4`.
    The j-dependent address lets stay behind this irreducible boundary. -/
@[irreducible]
def loopBodyN2MaxSkipJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  loopBodyN2MaxJgt0Pre j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld

/-- n=2 call-skip j>0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2CallSkipJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1

@[irreducible]
def loopBodyN2CallSkipJgt0NormPreV4NoX1 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- n=2 call-addback j>0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN2CallAddbackJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN2CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem

/-- The callable-ready v4 n=2 loop source specializes to the j=2 max-body
    precondition, with j=1/j=0 source atoms retained as a frame. -/
theorem loopN2PreWithScratchV4NoX1_to_max_j2_pre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    ∀ h,
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) h →
      ((loopBodyN2MaxSkipJgt0NormPreV4 (2 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) h := by
  intro h hp
  delta loopN2PreWithScratchV4NoX1 loopN2PreWithScratchNoX1 loopN2Pre at hp
  delta loopBodyN2MaxSkipJgt0NormPreV4
  rw [loopBodyN2MaxJgt0Pre_unfold]
  xperm_hyp hp

/-- The callable-ready v4 n=2 loop source specializes to the j=2 call-body
    precondition, with j=1/j=0 source atoms retained as a frame. -/
theorem loopN2PreWithScratchV4NoX1_to_call_j2_pre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    ∀ h,
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) h →
      ((loopBodyN2CallSkipJgt0NormPreV4NoX1 (2 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) h := by
  intro h hp
  delta loopN2PreWithScratchV4NoX1 loopN2PreWithScratchNoX1 loopN2Pre at hp
  delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4 at ⊢
  rw [loopBodyN2MaxJgt0Pre_unfold]
  xperm_hyp hp

theorem loopBodyN2CallSkipJ0PostV4NoX1_eq_scratch
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallSkipPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallSkipJ0PostV4NoX1 loopBodyN2CallSkipPostJScratchNoX1
  rfl

theorem loopBodyN2CallSkipJgt0PostV4NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallSkipPostJScratchNoX1 sp base j
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallSkipJgt0PostV4NoX1 loopBodyN2CallSkipPostJScratchNoX1
  rfl

theorem loopBodyN2CallAddbackBeqJ0PostV4NoX1_eq_scratch
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallAddbackBeqPostJScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallAddbackBeqJ0PostV4NoX1 loopBodyN2CallAddbackBeqPostJScratchNoX1
  rfl

theorem loopBodyN2CallAddbackBeqJgt0PostV4NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop
        scratchMem =
      loopBodyN2CallAddbackBeqPostJScratchNoX1 sp base j
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallAddbackBeqJgt0PostV4NoX1 loopBodyN2CallAddbackBeqPostJScratchNoX1
  rfl

/-- Loop body n=2, max+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_max_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_skip_j0_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  rw [loopBodyN2MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN2MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=2, max+skip, j>0 over `divCode_noNop_v4`, with
    computed addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_max_skip_jgt0_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_skip_jgt0_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, max+addback (BEQ double-addback), j>0 over
    `divCode_noNop_v4`, with the precondition hidden behind an irreducible
    definition. -/
theorem divK_loop_body_n2_max_addback_jgt0_beq_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_addback_jgt0_beq_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, call+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_call_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_skip_j0_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  rw [loopBodyN2CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN2CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+skip, j=0 over `divCode_noNop_v4`, preserving the
    concrete caller `x1` outside the normalized call precondition. -/
theorem divK_loop_body_n2_call_skip_j0_norm_v4_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_skip_j0_v4_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  unfold loopBodyN2CallSkipJ0PreV4NoX1 at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+skip, j>0 over `divCode_noNop_v4`, with
    computed addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_call_skip_jgt0_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n2_call_skip_jgt0_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow
  change (let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (loopBodyN2CallSkipJgt0PostV4 sp base j
        v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem)) at raw
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJgt0NormPreV4 loopBodyN2MaxSkipJgt0NormPreV4 at hp
      rw [loopBodyN2MaxJgt0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, call+skip, j>0 over `divCode_noNop_v4`, preserving the
    concrete caller `x1` outside the normalized call precondition. -/
theorem divK_loop_body_n2_call_skip_jgt0_norm_v4_noNop_exact_x1 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_skip_jgt0_v4_spec_within_noNop_exact_x1 j hpos
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4 at hp
      unfold loopBodyN2CallSkipJgt0PreV4NoX1
      rw [loopBodyN2MaxJgt0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+addback (BEQ double-addback), j>0 over
    `divCode_noNop_v4`, with the precondition hidden behind an irreducible
    definition. -/
theorem divK_loop_body_n2_call_addback_jgt0_beq_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n2_call_addback_jgt0_beq_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow hcarry2_nz
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallAddbackJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, call+addback (BEQ double-addback), j>0 over
    `divCode_noNop_v4`, preserving the concrete caller `x1` outside the
    normalized call precondition. -/
theorem divK_loop_body_n2_call_addback_jgt0_beq_norm_v4_noNop_exact_x1 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallAddbackBeqJgt0PostV4NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop
        scratchMem ** (.x1 ↦ᵣ raVal)) := by
  have hborrow' : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
    unfold loopBodyN2CallAddbackBorrowV4 at hborrow
    exact hborrow
  have hcarry2_nz' :
      let qHat := divKTrialCallV4QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
    simpa [loopBodyN2CallAddbackCarry2NzV4] using hcarry2_nz
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1 j hpos
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow' hcarry2_nz')
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4 at hp
      unfold loopBodyN2CallSkipJgt0PreV4NoX1
      rw [loopBodyN2MaxJgt0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, max+addback (BEQ double-addback), j=0 over
    `divCode_noNop_v4`, with sp-relative addresses hidden behind a named
    precondition. -/
theorem divK_loop_body_n2_max_addback_j0_beq_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_addback_j0_beq_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  rw [loopBodyN2MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN2MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=2, call+addback (BEQ double-addback), j=0 over
    `divCode_noNop_v4`, with sp-relative addresses hidden behind a named
    precondition. -/
theorem divK_loop_body_n2_call_addback_j0_beq_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_addback_j0_beq_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  rw [loopBodyN2CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN2CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+addback (BEQ double-addback), j=0 over
    `divCode_noNop_v4`, preserving the concrete caller `x1` outside the
    normalized call precondition. -/
theorem divK_loop_body_n2_call_addback_j0_beq_norm_v4_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallAddbackBeqJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have hborrow' : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
    unfold loopBodyN2CallAddbackBorrowV4 at hborrow
    exact hborrow
  have hcarry2_nz' :
      let qHat := divKTrialCallV4QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0 := by
    simpa [loopBodyN2CallAddbackCarry2NzV4] using hcarry2_nz
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n2_call_addback_j0_beq_v4_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow' hcarry2_nz')
  unfold loopBodyN2CallSkipJ0PreV4NoX1 at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4NoX1 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Unified j=2 N2 call iteration over v4/no-NOP code, preserving concrete
    `x1` and exposing the v4 scratch cell in the postcondition. -/
theorem divK_loop_body_n2_call_j2_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 (2 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      simp [loopBodyN2CallAddbackBorrowV4, hborrow]
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJgt0PostV4NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v4_noNop_exact_x1
        (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJgt0PostV4NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_jgt0_norm_v4_noNop_exact_x1
          (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=2 N2 max iteration over v4/no-NOP code, preserving concrete
    `x1` and carrying the v4 scratch cell as frame. -/
theorem divK_loop_body_n2_max_j2_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      ((loopBodyN2MaxSkipJgt0NormPreV4 (2 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    have J := divK_loop_body_n2_max_addback_jgt0_beq_norm_v4_noNop
      (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow_nz
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        rw [loopIterPostN2Max_addback hborrow] at hp
        xperm_hyp hp)
      Jf
  · have hborrow_zero :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := by
      rw [if_neg hborrow]
    have J := divK_loop_body_n2_max_skip_jgt0_norm_v4_noNop
      (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow_zero
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by
          rw [loopIterPostN2Max_skip hborrow] at hp
          xperm_hyp hp)
        Jf

/-- Unified j=1 N2 call iteration over v4/no-NOP code, preserving concrete
    `x1` and exposing the v4 scratch cell in the postcondition. -/
theorem divK_loop_body_n2_call_j1_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 (1 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : loopBodyN2CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      simp [loopBodyN2CallAddbackBorrowV4, hborrow]
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJgt0PostV4NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v4_noNop_exact_x1
        (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJgt0PostV4NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_jgt0_norm_v4_noNop_exact_x1
          (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=1 N2 max iteration over v4/no-NOP code, preserving concrete
    `x1` and carrying the v4 scratch cell as frame. -/
theorem divK_loop_body_n2_max_j1_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      ((loopBodyN2MaxSkipJgt0NormPreV4 (1 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    have J := divK_loop_body_n2_max_addback_jgt0_beq_norm_v4_noNop
      (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow_nz
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        rw [loopIterPostN2Max_addback hborrow] at hp
        xperm_hyp hp)
      Jf
  · have hborrow_zero :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := by
      rw [if_neg hborrow]
    have J := divK_loop_body_n2_max_skip_jgt0_norm_v4_noNop
      (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow_zero
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by
          rw [loopIterPostN2Max_skip hborrow] at hp
          xperm_hyp hp)
        Jf

/-- A j=2 call iteration postcondition with v4 scratch cells specializes to the
    j=1 call-body precondition, retaining exact `x1`, j=2 stored u4/q atoms,
    and the j=0 source atoms as frame. -/
theorem loopIterPostN2CallScratchNoX1_j2_to_call_j1_pre
    (sp base qHat dLo divUn0 scratchOut : Word)
    (v0 v1 v2 v3 u0J2 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal : Word) :
    let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0J2 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0J2 u1 u2 u3
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        qHat dLo divUn0 scratchOut v0 v1 v2 v3 u0J2 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) →
      (((loopBodyN2CallSkipJgt0NormPreV4NoX1 (1 : Word) sp
          (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) uBase2 qAddr2 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig1 r.2.1 r.2.2.1
          r.2.2.2.1 r.2.2.2.2.1 q1Old (base + div128CallRetOff) v1 dLo divUn0
          scratchOut ** (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr2 ↦ₘ r.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) := by
  intro r c3 uBase2 qAddr2 uBase0 qAddr0 h hp
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  subst c3
  subst r
  delta loopIterPostN2CallScratchNoX1 loopExitPostN2 loopExitPost at hp
  delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4
  rw [loopBodyN2MaxJgt0Pre_unfold]
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_2
  rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
      u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=2 call iteration postcondition with v4 scratch cells specializes to the
    j=1 max-body precondition, retaining exact `x1`, scratch, j=2 stored u4/q
    atoms, and the j=0 source atoms as frame. -/
theorem loopIterPostN2CallScratchNoX1_j2_to_max_j1_pre
    (sp base qHat dLo divUn0 scratchOut : Word)
    (v0 v1 v2 v3 u0J2 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal : Word) :
    let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0J2 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 qHat v0 v1 v2 v3 u0J2 u1 u2 u3
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        qHat dLo divUn0 scratchOut v0 v1 v2 v3 u0J2 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) →
      (((loopBodyN2MaxSkipJgt0NormPreV4 (1 : Word) sp
          (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) uBase2 qAddr2 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig1 r.2.1 r.2.2.1
          r.2.2.2.1 r.2.2.2.2.1 q1Old **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v1) **
        (sp + signExtend12 3952 ↦ₘ dLo) **
        (sp + signExtend12 3944 ↦ₘ divUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchOut) **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr2 ↦ₘ r.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) := by
  intro r c3 uBase2 qAddr2 uBase0 qAddr0 h hp
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  subst c3
  subst r
  delta loopIterPostN2CallScratchNoX1 loopExitPostN2 loopExitPost at hp
  delta loopBodyN2MaxSkipJgt0NormPreV4
  rw [loopBodyN2MaxJgt0Pre_unfold]
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_2
  rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
      u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=2 max iteration postcondition with v4 scratch cells specializes to the
    j=1 call-body precondition, retaining exact `x1`, j=2 stored u4/q atoms,
    and the j=0 source atoms as frame. -/
theorem loopIterPostN2MaxScratchX1_j2_to_call_j1_pre
    (sp retMem dMem dloMem scratchUn0 scratchMem : Word)
    (v0 v1 v2 v3 u0J2 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal : Word) :
    let r := iterN2Max v0 v1 v2 v3 u0J2 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0J2 u1 u2 u3
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0J2 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) →
      (((loopBodyN2CallSkipJgt0NormPreV4NoX1 (1 : Word) sp
          (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) uBase2 qAddr2 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig1 r.2.1 r.2.2.1
          r.2.2.2.1 r.2.2.2.2.1 q1Old retMem dMem dloMem scratchUn0 scratchMem **
          (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr2 ↦ₘ r.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) := by
  intro r c3 uBase2 qAddr2 uBase0 qAddr0 h hp
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  subst c3
  subst r
  delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
  delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4
  rw [loopBodyN2MaxJgt0Pre_unfold]
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_2
  rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
      u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- A j=2 max iteration postcondition with v4 scratch cells specializes to the
    j=1 max-body precondition, retaining exact `x1`, scratch, j=2 stored u4/q
    atoms, and the j=0 source atoms as frame. -/
theorem loopIterPostN2MaxScratchX1_j2_to_max_j1_pre
    (sp retMem dMem dloMem scratchUn0 scratchMem : Word)
    (v0 v1 v2 v3 u0J2 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal : Word) :
    let r := iterN2Max v0 v1 v2 v3 u0J2 u1 u2 u3 uTop
    let c3 := mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0J2 u1 u2 u3
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    ∀ h,
      (((loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0J2 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) →
      (((loopBodyN2MaxSkipJgt0NormPreV4 (1 : Word) sp
          (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) uBase2 qAddr2 c3 r.1
          r.2.2.2.2.1 v0 v1 v2 v3 u0Orig1 r.2.1 r.2.2.1
          r.2.2.2.1 r.2.2.2.2.1 q1Old **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r.2.2.2.2.2) **
          (qAddr2 ↦ₘ r.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) h) := by
  intro r c3 uBase2 qAddr2 uBase0 qAddr0 h hp
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  subst c3
  subst r
  delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
  delta loopBodyN2MaxSkipJgt0NormPreV4
  rw [loopBodyN2MaxJgt0Pre_unfold]
  unfold mulsubN4_c3
  simp only [] at hp ⊢
  have hj' := EvmAsm.Evm64.DivMod.AddrNorm.jpred_2
  rw [hj', u_j2_0_eq_j1_4088, u_j2_4088_eq_j1_4080,
      u_j2_4080_eq_j1_4072, u_j2_4072_eq_j1_4064] at hp
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

end EvmAsm.Evm64
