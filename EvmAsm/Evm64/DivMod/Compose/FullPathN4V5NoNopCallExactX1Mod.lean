/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopCallExactX1Mod

  MOD analog of `FullPathN4V5NoNopCallExactX1`: the exact-x1 norm-pre wrappers for
  the n=4 v5 call-skip / call-addback-beq loop bodies (j=0), but over
  `modCode_noNop_v5` instead of `divCode_noNop_v5`.  The underlying loop-body
  `raw` (`divK_loop_body_n4_call_{skip,addback}_j0_v5_spec_within_noNop_exact_x1`)
  is proven over the op-agnostic `sharedDivModCodeNoNop_v5`, so the only change vs
  the DIV version is the code-surface extension lemma
  (`sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5`).  Toward `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopCallExactX1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=4, call+skip, j=0 over `modCode_noNop_v5`, sp-relative addresses,
    preserving concrete `x1 = raVal`.  MOD analog of
    `divK_loop_body_n4_call_skip_j0_norm_v5_noNop_exact_x1`. -/
theorem divK_loop_body_n4_call_skip_j0_norm_v5_noNop_exact_x1_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      ((loopBodyN4CallJ0NormPreNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (loopBodyN4CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have raw := divK_loop_body_n4_call_skip_j0_v5_spec_within_noNop_exact_x1
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [loopBodyN4CallJ0NormPreNoX1_unfold] at hp
      unfold loopBodyN4CallSkipJ0PreV4NoX1
      simp only [se12_32, se12_40, se12_48, se12_56,
                 u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
                 u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
      xperm_hyp hp)
    (fun _ hp => hp)
    raw'

/-- Loop body n=4, call+addback-beq, j=0 over `modCode_noNop_v5`, sp-relative
    addresses, preserving concrete `x1 = raVal`.  MOD analog of
    `divK_loop_body_n4_call_addback_j0_beq_norm_v5_noNop_exact_x1`. -/
theorem divK_loop_body_n4_call_addback_j0_beq_norm_v5_noNop_exact_x1_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat uTop u3 v3
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      ((loopBodyN4CallJ0NormPreNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (loopBodyN4CallAddbackBeqJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have raw := divK_loop_body_n4_call_addback_j0_beq_v5_spec_within_noNop_exact_x1
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow hcarry2_nz
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [loopBodyN4CallJ0NormPreNoX1_unfold] at hp
      unfold loopBodyN4CallSkipJ0PreV4NoX1
      simp only [se12_32, se12_40, se12_48, se12_56,
                 u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
                 u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
      xperm_hyp hp)
    (fun _ hp => hp)
    raw'

end EvmAsm.Evm64
