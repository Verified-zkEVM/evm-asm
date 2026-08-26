/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallExactX1Mod

  MOD mirror of `FullPathN2V5NoNopCallExactX1`: the n=2 call-path exact-x1 loop
  bodies (call+skip and call+addback, j=0 and j>0) lifted from the raw v5
  exact-x1 call bodies (over `sharedDivModCodeNoNop_v5`) to `modCode_noNop_v5`
  via `sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5`.  Byte-for-byte the DIV
  wrappers, swapping ONLY the extend target — the raw bodies and the
  (code-agnostic) NoX1 NormPre/Post defs are shared.  Brick 3 of the n=2 MOD
  loop body (completes the per-jN layer).  Bead `evm-asm-wbc4i.10.3.2.4.5`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2V5.CallSkipV5ExactX1NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2V5.CallAddbackV5ExactX1NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=2, call+skip, j=0 over `modCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_skip_j0_norm_v5_noNop_exact_x1_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n2_call_skip_j0_v5_spec_within_noNop_exact_x1
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

/-- Loop body n=2, call+skip, j>0 over `modCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1_modCode (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallSkipJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n2_call_skip_jgt0_v5_spec_within_noNop_exact_x1 j hpos
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

/-- Loop body n=2, call+addback, j=0 over `modCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_addback_j0_beq_norm_v5_noNop_exact_x1_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN2CallSkipJ0NormPreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallAddbackBeqJ0PostV5NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n2_call_addback_j0_beq_v5_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
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

/-- Loop body n=2, call+addback, j>0 over `modCode_noNop_v5`, preserving `x1`. -/
theorem divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1_modCode (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN2CallAddbackBeqJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop
        scratchMem ** (.x1 ↦ᵣ raVal)) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5)
      (divK_loop_body_n2_call_addback_jgt0_beq_v5_spec_within_noNop_exact_x1 j hpos
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJgt0NormPreV4NoX1 loopBodyN2MaxSkipJgt0NormPreV4 at hp
      unfold loopBodyN2CallSkipJgt0PreV4NoX1
      rw [loopBodyN2MaxJgt0Pre_unfold] at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

end EvmAsm.Evm64
