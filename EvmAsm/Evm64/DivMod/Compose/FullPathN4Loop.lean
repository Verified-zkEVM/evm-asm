/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

  Building blocks for the n=4 full path composition:
  - Loop body j=0 specs extended from sharedDivModCode to divCode
  - Address normalization lemmas for j=0
-/

-- `LoopIterN4 → LoopBodyN4 → LoopBody → Compose → FullPath`.
module

public import EvmAsm.Evm64.DivMod.LoopIterN4

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- ============================================================================
-- Address normalization lemmas for j=0
-- ============================================================================

theorem u_base_j0 {sp : Word} :
    sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4056 := by
  divmod_addr

theorem u_base_off0_j0 {sp : Word} :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    sp + signExtend12 4056 := by divmod_addr

theorem u_base_off4088_j0 {sp : Word} :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4048 := by divmod_addr

theorem u_base_off4080_j0 {sp : Word} :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4040 := by divmod_addr

theorem u_base_off4072_j0 {sp : Word} :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4032 := by divmod_addr

theorem u_base_off4064_j0 {sp : Word} :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4024 := by divmod_addr

theorem q_addr_j0 {sp : Word} :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  divmod_addr

-- ============================================================================
-- loopExitPostN4 at j=0: address normalization to sp-relative form
-- ============================================================================

/-- At j=0, loopExitPostN4 normalizes to sp-relative addresses. -/
theorem loopExitPostN4_j0_eq (sp q_f c3 un0F un1F un2F un3F u4F
    v0 v1 v2 v3 : Word) :
    loopExitPostN4 sp (0 : Word) q_f c3 un0F un1F un2F un3F u4F v0 v1 v2 v3 =
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
     (.x2 ↦ᵣ un3F) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ un0F) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ un1F) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ un2F) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ un3F) **
     ((sp + signExtend12 4024) ↦ₘ u4F) **
     ((sp + signExtend12 4088) ↦ₘ q_f)) := by
  simp only [loopExitPost_unfold]
  rw [u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
      u_base_off4072_j0, u_base_off4064_j0, u_base_j0, q_addr_j0]
  simp only [divmod_addr]

-- ============================================================================
-- Bundled precondition (defined here so divCode/noNop theorems can use it)
-- ============================================================================

/-- Bundled precondition for the `divK_loop_body_n4_max_skip_j0_{divCode,noNop,modCode}_within`
    specs. Wraps the 21-atom sepConj chain that the `let uBase / qAddr` bindings make awkward
    in the raw statement. Marked `@[irreducible]` so the `let`-bound offsets
    don't pollute callers' types. -/
@[irreducible]
def loopBodyN4SkipJ0Pre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld)

/-- Named unfold for `loopBodyN4SkipJ0Pre`. -/
theorem loopBodyN4SkipJ0Pre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) :
    loopBodyN4SkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld =
    (let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld)) := by
  delta loopBodyN4SkipJ0Pre; rfl

/-- Sp-relative normalized precondition for the j=0 max-skip path. This is the
    public surface used by the normalized modCode wrapper; keep the long atom
    chain out of theorem statements. -/
@[irreducible]
def loopBodyN4SkipJ0NormPre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
  ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
  ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ uTop) **
  ((sp + signExtend12 4088) ↦ₘ qOld)

/-- Named unfold for `loopBodyN4SkipJ0NormPre`. -/
theorem loopBodyN4SkipJ0NormPre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) :
    loopBodyN4SkipJ0NormPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld =
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
     ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
     ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ uTop) **
     ((sp + signExtend12 4088) ↦ₘ qOld)) := by
  delta loopBodyN4SkipJ0NormPre; rfl

-- ============================================================================
-- Loop body j=0 extended to divCode / divCode_noNop (from sharedDivModCode)
-- Uses loopBodyN4SkipJ0Pre so no let-bindings appear in the statement.
-- ============================================================================

/-- Extend max_skip j=0 loop body from sharedDivModCode to divCode.
    Uses `loopBodyN4SkipJ0Pre` so no `let`-bindings appear in the statement. -/
theorem divK_loop_body_n4_max_skip_j0_divCode_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopBodyN4SkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have h := cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_divCode)
    (divK_loop_body_n4_max_skip_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow)
  refine cpsTripleWithin_weaken ?_ ?_ h
  intro _ hp
  rw [loopBodyN4SkipJ0Pre_unfold] at hp
  rw [loopBodyN4MaxSkipJ0Pre_unfold]
  exact hp
  intro _ hq
  rw [loopBodyN4MaxSkipJ0Post_unfold] at hq
  exact hq

/-- Extend max_skip j=0 loop body to `divCode_noNop`.
    Uses `loopBodyN4SkipJ0Pre` so no `let`-bindings appear in the statement. -/
theorem divK_loop_body_n4_max_skip_j0_divCode_noNop_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopBodyN4SkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have h : cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopBodyN4SkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
    have raw := divK_loop_body_n4_max_skip_j0_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow
    refine cpsTripleWithin_weaken ?_ ?_ (cpsTripleWithin_mono_nSteps (by decide) raw)
    intro _ hp
    rw [loopBodyN4SkipJ0Pre_unfold] at hp
    rw [loopBodyN4MaxSkipJ0Pre_unfold]
    exact hp
    intro _ hq
    rw [loopBodyN4MaxSkipJ0Post_unfold] at hq
    exact hq
  exact h

/-- Extend max_skip j=0 loop body from sharedDivModCode to modCode.
    Mirror of `divK_loop_body_n4_max_skip_j0_divCode_within` — same proof,
    swapping `sharedDivModCode_sub_divCode` for
    `sharedDivModCode_sub_modCode`. Uses the irreducible
    `loopBodyN4SkipJ0Pre` bundle so the `let`-bound offsets don't
    appear in the statement. -/
theorem divK_loop_body_n4_max_skip_j0_modCode_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopBodyN4SkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have h := cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_modCode)
    (divK_loop_body_n4_max_skip_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow)
  refine cpsTripleWithin_weaken ?_ ?_ h
  intro _ hp
  rw [loopBodyN4SkipJ0Pre_unfold] at hp
  rw [loopBodyN4MaxSkipJ0Pre_unfold]
  exact hp
  intro _ hq
  rw [loopBodyN4MaxSkipJ0Post_unfold] at hq
  exact hq

/-- Max_skip j=0 loop body against modCode with sp-relative addresses in the
    precondition. Mirror of the DIV `divK_loop_body_n4_max_skip_j0_norm`
    with `divCode → modCode`. `qHat = signExtend12 4095` is inlined so no
    `let` bindings appear in the statement. -/
theorem divK_loop_body_n4_max_skip_j0_norm_modCode_within (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopBodyN4SkipJ0NormPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have raw := divK_loop_body_n4_max_skip_j0_modCode_within sp jOld v5Old v6Old v7Old
    v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow
  refine cpsTripleWithin_weaken ?_ (fun _ hq => hq) raw
  intro _ hp
  rw [loopBodyN4SkipJ0NormPre_unfold] at hp
  delta loopBodyN4SkipJ0Pre
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
  exact hp

-- ============================================================================
-- Call path: bundled pre/post for j=0 extended to divCode/modCode.
-- (loopBodyN4CallSkipJ0Pre, loopBodyN4CallSkipJ0Post, and
--  loopBodyN4CallAddbackBeqJ0Post are defined in LoopIterN4, available
--  here via the import.)

/-- Sp-relative normalized precondition for the j=0 div128 call path. Shared
    by call-skip and BEQ addback normalized wrappers. -/
@[irreducible]
def loopBodyN4CallJ0NormPre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
  ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
  ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ uTop) **
  ((sp + signExtend12 4088) ↦ₘ qOld) **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

/-- Named unfold for `loopBodyN4CallJ0NormPre`. -/
theorem loopBodyN4CallJ0NormPre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) :
    loopBodyN4CallJ0NormPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
     ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
     ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ uTop) **
     ((sp + signExtend12 4088) ↦ₘ qOld) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1) := by
  delta loopBodyN4CallJ0NormPre; rfl

-- ============================================================================
-- Call path: Loop body j=0 extended to divCode (from sharedDivModCode)
-- ============================================================================

/-- Extend call_skip j=0 loop body from sharedDivModCode to divCode.
    Pre/post bundled via `loopBodyN4CallSkipJ0Pre`/`Post`; 0 statement lets. -/
theorem divK_loop_body_n4_call_skip_j0_divCode_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 126 (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopBodyN4CallSkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopBodyN4CallSkipJ0Post sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) :=
  cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_divCode)
    (cpsTripleWithin_mono_nSteps (by decide)
      (divK_loop_body_n4_call_skip_j0_spec_within_bundled sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
        halign hbltu hborrow))

/-- Extend call_skip j=0 loop body to `divCode_noNop`.
    Pre/post bundled via `loopBodyN4CallSkipJ0Pre`/`Post`; 0 statement lets. -/
theorem divK_loop_body_n4_call_skip_j0_divCode_noNop_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 126 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopBodyN4CallSkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopBodyN4CallSkipJ0Post sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (divK_loop_body_n4_call_skip_j0_spec_within_noNop_bundled sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign hbltu hborrow)

-- ============================================================================
-- _da (double-addback) variants: lift _beq_spec to divCode
-- ============================================================================

/-- Extend call_addback (BEQ double-addback) j=0 loop body from sharedDivModCode to divCode.
    Pre/post bundled; 0 statement lets. -/
theorem divK_loop_body_n4_call_addback_j0_beq_divCode_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hcarry2_nz : isAddbackCarry2NzN4Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) ≠ (0 : Word)) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (divCode base)
      (loopBodyN4CallSkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopBodyN4CallAddbackBeqJ0Post sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) :=
  cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_divCode)
    (cpsTripleWithin_mono_nSteps (by decide)
      (divK_loop_body_n4_call_addback_j0_beq_spec_within_bundled sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
        halign hbltu hcarry2_nz hborrow))

-- ============================================================================
-- Call path: Loop body j=0 extended to modCode (from sharedDivModCode)
-- ============================================================================

/-- Extend call_skip j=0 loop body from sharedDivModCode to modCode.
    Mirror of `divK_loop_body_n4_call_skip_j0_divCode_within` with
    `divCode → modCode` (uses `sharedDivModCode_sub_modCode` instead).

    Pre/post are bundled into `loopBodyN4CallSkipJ0Pre` /
    `loopBodyN4CallSkipJ0Post` so the algorithm's let-chain doesn't
    pollute the statement. -/
theorem divK_loop_body_n4_call_skip_j0_modCode_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 126 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopBodyN4CallSkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopBodyN4CallSkipJ0Post sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) :=
  cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_modCode)
    (divK_loop_body_n4_call_skip_j0_spec_within_bundled sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign hbltu hborrow)

/-- Call_skip j=0 loop body against modCode with sp-relative addresses
    in the precondition. Mirror of `divK_loop_body_n4_call_skip_j0_norm`
    (the divCode variant in FullPathN4.lean) with `divCode → modCode`. -/
theorem divK_loop_body_n4_call_skip_j0_norm_modCode_within (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTripleWithin 126 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopBodyN4CallJ0NormPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopBodyN4CallSkipJ0Post sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have raw := divK_loop_body_n4_call_skip_j0_modCode_within sp jOld v5Old v6Old v7Old
    v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratch_un0 base halign hbltu hborrow
  refine cpsTripleWithin_weaken ?_ ?_ raw
  · intro _ hp
    rw [loopBodyN4CallJ0NormPre_unfold] at hp
    delta loopBodyN4CallSkipJ0Pre
    simp only [se12_32, se12_40, se12_48, se12_56,
               u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
               u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
    exact hp
  · intro _ hq
    exact hq

-- ============================================================================
-- Call-addback path (BEQ double-addback): Loop body j=0 extended to modCode
-- ============================================================================

/-- Extend call_addback (BEQ double-addback) j=0 loop body from
    sharedDivModCode to modCode. Mirror of
    `divK_loop_body_n4_call_addback_j0_beq_divCode_within` with
    `divCode → modCode` (uses `sharedDivModCode_sub_modCode` instead).

    Pre is shared with the call_skip branch (`loopBodyN4CallSkipJ0Pre`);
    post is bundled as `loopBodyN4CallAddbackBeqJ0Post` so the algorithm's
    27-step div128 let-chain doesn't pollute the statement. -/
theorem divK_loop_body_n4_call_addback_j0_beq_modCode_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hcarry2_nz : isAddbackCarry2NzN4Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) ≠ (0 : Word)) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopBodyN4CallSkipJ0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopBodyN4CallAddbackBeqJ0Post sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) :=
  cpsTripleWithin_extend_code (hmono := sharedDivModCode_sub_modCode)
    (divK_loop_body_n4_call_addback_j0_beq_spec_within_bundled sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign hbltu hcarry2_nz hborrow)

/-- Call_addback (BEQ) j=0 loop body against modCode with sp-relative
    addresses in the precondition. -/
theorem divK_loop_body_n4_call_addback_j0_beq_norm_modCode_within (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hcarry2_nz : isAddbackCarry2NzN4Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) ≠ (0 : Word)) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopBodyN4CallJ0NormPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopBodyN4CallAddbackBeqJ0Post sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have raw := divK_loop_body_n4_call_addback_j0_beq_modCode_within sp jOld
    v5Old v6Old v7Old v10Old v11Old v2Old v0 v1 v2 v3 u0 u1 u2 u3 uTop
    qOld retMem dMem dloMem scratch_un0 base halign hbltu hcarry2_nz hborrow
  refine cpsTripleWithin_weaken ?_ ?_ raw
  · intro _ hp
    rw [loopBodyN4CallJ0NormPre_unfold] at hp
    rw [loopBodyN4CallSkipJ0Pre_unfold]
    simp only [se12_32, se12_40, se12_48, se12_56,
               u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
               u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
    exact hp
  · intro _ hq
    exact hq

end EvmAsm.Evm64
