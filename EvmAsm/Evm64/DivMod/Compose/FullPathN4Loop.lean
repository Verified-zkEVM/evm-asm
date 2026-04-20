/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop

  Building blocks for the n=4 full path composition:
  - Loop body j=0 specs extended from sharedDivModCode to divCode
  - Address normalization lemmas for j=0
-/

import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.LoopIterN4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- ============================================================================
-- Address normalization lemmas for j=0
-- ============================================================================

theorem u_base_j0 (sp : Word) :
    sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4056 := by
  divmod_addr

theorem u_base_off0_j0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    sp + signExtend12 4056 := by divmod_addr

theorem u_base_off4088_j0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4048 := by divmod_addr

theorem u_base_off4080_j0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4040 := by divmod_addr

theorem u_base_off4072_j0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4032 := by divmod_addr

theorem u_base_off4064_j0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4024 := by divmod_addr

theorem q_addr_j0 (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  divmod_addr

-- ============================================================================
-- loopExitPostN4 at j=0: address normalization to sp-relative form
-- ============================================================================

/-- At j=0, loopExitPostN4 normalizes to sp-relative addresses. -/
theorem loopExitPostN4_j0_eq (sp q_f c3 un0F un1F un2F un3F u4F
    v0 v1 v2 v3 : Word) :
    loopExitPostN4 sp (0 : Word) q_f c3 un0F un1F un2F un3F u4F v0 v1 v2 v3 =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
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
-- Loop body j=0 extended to divCode (from sharedDivModCode)
-- ============================================================================

/-- Extend max_skip j=0 loop body from sharedDivModCode to divCode. -/
theorem divK_loop_body_n4_max_skip_j0_divCode
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uTop v3) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopBodyN4SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr hborrow
  exact cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_body_n4_max_skip_j0_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow)

/-- Bundled precondition for the `divK_loop_body_n4_max_skip_j0_modCode` /
    `_divCode` code-extended loop-body specs. Wraps the 21-atom sepConj
    chain that the `let uBase / qAddr` bindings make awkward in the
    raw statement. Marked `@[irreducible]` so the `let`-bound offsets
    don't pollute callers' types. -/
@[irreducible]
def loopBodyN4SkipJ0Pre
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld)

/-- Named unfold for `loopBodyN4SkipJ0Pre`. -/
theorem loopBodyN4SkipJ0Pre_unfold
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) :
    loopBodyN4SkipJ0Pre sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld =
    (let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
     (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
     (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld)) := by
  delta loopBodyN4SkipJ0Pre; rfl

/-- Extend max_skip j=0 loop body from sharedDivModCode to modCode.
    Mirror of `divK_loop_body_n4_max_skip_j0_divCode` — same proof,
    swapping `sharedDivModCode_sub_divCode` for
    `sharedDivModCode_sub_modCode`. Uses the irreducible
    `loopBodyN4SkipJ0Pre` bundle so the `let`-bound offsets don't
    appear in the statement. -/
theorem divK_loop_body_n4_max_skip_j0_modCode
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (modCode base)
      (loopBodyN4SkipJ0Pre sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have h := cpsTriple_extend_code (hmono := sharedDivModCode_sub_modCode base)
    (divK_loop_body_n4_max_skip_j0_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow)
  refine cpsTriple_weaken ?_ (fun _ hq => hq) h
  intro _ hp
  rw [loopBodyN4SkipJ0Pre_unfold] at hp
  exact hp

/-- Max_skip j=0 loop body against modCode with sp-relative addresses in the
    precondition. Mirror of the DIV `divK_loop_body_n4_max_skip_j0_norm`
    with `divCode → modCode`. `qHat = signExtend12 4095` is inlined so no
    `let` bindings appear in the statement. -/
theorem divK_loop_body_n4_max_skip_j0_norm_modCode (sp base : Word)
    (jOld v5_old v6_old v7_old v10_old v11_old v2_old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
                  (mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3)
                then (1 : Word) else 0) = (0 : Word)) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld))
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  have raw := divK_loop_body_n4_max_skip_j0_modCode sp jOld v5_old v6_old v7_old
    v10_old v11_old v2_old v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow
  refine cpsTriple_weaken ?_ (fun _ hq => hq) raw
  intro _ hp
  rw [loopBodyN4SkipJ0Pre_unfold]
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
  exact hp

-- ============================================================================
-- Call path: Loop body j=0 extended to divCode (from sharedDivModCode)
-- ============================================================================

/-- Extend call_skip j=0 loop body from sharedDivModCode to divCode. -/
theorem divK_loop_body_n4_call_skip_j0_divCode
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult uTop v3) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let dHi := v3 >>> (32 : BitVec 6).toNat
    let dLo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uTop dHi
    let rhat := uTop - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0Dlo := q0c * dLo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c
    let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN4SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro uBase
        dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0Dlo rhat2Un0 q0' qHat
        qAddr hborrow
  exact cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_body_n4_call_skip_j0_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign hbltu hborrow)

-- ============================================================================
-- _da (double-addback) variants: lift _beq_spec to divCode
-- ============================================================================

/-- Extend max_addback (BEQ double-addback) j=0 loop body from sharedDivModCode to divCode. -/
theorem divK_loop_body_n4_max_addback_j0_beq_divCode
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hcarry2_nz : isAddbackCarry2NzN4Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopBodyN4AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr hborrow
  exact cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_body_n4_max_addback_j0_beq_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hcarry2_nz hborrow)

/-- Extend call_addback (BEQ double-addback) j=0 loop body from sharedDivModCode to divCode. -/
theorem divK_loop_body_n4_call_addback_j0_beq_divCode
    (sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult uTop v3)
    (hcarry2_nz : isAddbackCarry2NzN4Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let dHi := v3 >>> (32 : BitVec 6).toNat
    let dLo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uTop dHi
    let rhat := uTop - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0Dlo := q0c * dLo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c
    let qHat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN4AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  intro uBase
        dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0Dlo rhat2Un0 q0' qHat
        qAddr hborrow
  exact cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_body_n4_call_addback_j0_beq_spec sp jOld v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign hbltu hcarry2_nz hborrow)

end EvmAsm.Evm64
