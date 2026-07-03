import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMax
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMaxInput
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopLoopBody
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopLoopBodyConditional
import EvmAsm.Evm64.DivMod.Compose.V4Code

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- DIV PhaseAB(n=1) + CLZ + PhaseC2(ntaken) + NormB over the full `divCode_v4` bundle. -/
theorem evm_div_phaseAB_n1_clz_c2_normB_spec_v4 (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (divCode_v4 base)
      (evmDivPhaseABN1ClzC2NormBPre sp v5 v6 v7 v10 b0 b1 b2 b3
        q0 q1 q2 q3 u5 u6 u7 nMem shiftMem ((clzResult b0).2 >>> (63 : Nat)))
      (evmDivPhaseABN1ClzC2NormBFullPost sp b0 b1 b2 b3) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_phaseAB_n1_clz_c2_normB_spec_v4_noNop sp base
      b0 b1 b2 b3 v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem shiftMem
      hbnz hb3z hb2z hb1z hshift_nz)

/-- Full n=1 path from entry to loop body start over the full `divCode_v4` bundle. -/
theorem evm_div_n1_to_loopSetup_spec_v4 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff)
      (divCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (loopSetupPost sp (1 : Word) (clzResult b0).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_n1_to_loopSetup_spec_v4_noNop sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      hbnz hb3z hb2z hb1z hshift_nz)

/-- Full n=1 path from entry to loop body start over `divCode_v4`, with generalized `x9`. -/
theorem evm_div_n1_to_loopSetup_spec_v4_x9In (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff)
      (divCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ x9In) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (loopSetupPost sp (1 : Word) (clzResult b0).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_n1_to_loopSetup_spec_v4_noNop_x9In sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      hbnz hb3z hb2z hb1z hshift_nz)

/-- Full n=1 path from entry to loop body start over `divCode_v4`, with exact caller-framed
    `x1` and the loop scratch handoff frame carried explicitly. -/
theorem evm_div_n1_to_loopSetup_spec_v4_exact_x1_scratch_frame
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff)
      (divCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
        (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      (loopSetupPost sp (1 : Word) (clzResult b0).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_n1_to_loopSetup_spec_v4_noNop_exact_x1_scratch_frame sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2z hb1z hshift_nz)

/-- Full n=1 path from entry to loop body start over `divCode_v4`, with arbitrary incoming
    `x9`, exact caller-framed `x1`, and the loop scratch handoff frame carried explicitly. -/
theorem evm_div_n1_to_loopSetup_spec_v4_x9In_exact_x1_scratch_frame
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff)
      (divCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      (loopSetupPost sp (1 : Word) (clzResult b0).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_n1_to_loopSetup_spec_v4_noNop_x9In_exact_x1_scratch_frame sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2z hb1z hshift_nz)

/-- Loop body n=1, max+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN1SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=1, max+skip, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_skip_jgt0_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN1SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_skip_jgt0_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=1, max path, j=3 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j3_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (3 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j3_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Loop body n=1, max path, j=2 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j2_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (2 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j2_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Loop body n=1, max path, j=1 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j1_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJgt0NormPreV4 (1 : Word)
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j1_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Loop body n=1, max path, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_max_j0_exact_loopIter_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1MaxSkipJ0NormPreV4
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_max_j0_exact_loopIter_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal hbltu hcarry2_nz)

/-- Exact-`x1` N1 two-iteration max/max path over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_iter10_maxmax_exact_x1_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_1 : ¬BitVec.ult u1 v0)
    (hbltu_0 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopN1Iter10PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter10PostNoX1 false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter10_maxmax_exact_x1_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 raVal hbltu_1 hbltu_0 hcarry2)

/-- Exact-`x1` N1 three-iteration all-max path over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_iter210_maxmaxmax_exact_x1_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_2 : ¬BitVec.ult u1 v0)
    (hbltu_1 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 556 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopN1Iter210PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1Iter210PostNoX1 false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 raVal hbltu_2 hbltu_1 hbltu_0 hcarry2)

/-- Exact-`x1` N1 four-iteration all-max path over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_maxmaxmaxmax_exact_x1_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (hbltu_3 : ¬BitVec.ult u1 v0)
    (hbltu_2 : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : ¬BitVec.ult
      (iterN1Max v0 v1 v2 v3 u0Orig1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0Orig2
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 758 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN1UnifiedPostNoX1 false false false false sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_maxmaxmaxmax_exact_x1_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 raVal
      hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2)

/-- Loop body n=1, call+skip, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_skip_j0_norm_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN1CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_skip_j0_norm_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow)

/-- Loop body n=1, call+skip, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_skip_jgt0_norm_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1CallSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN1CallSkipJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_skip_jgt0_norm_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow)

/-- Loop body n=1, call+addback, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_addback_jgt0_exact_loopIterScratch_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_addback_jgt0_exact_loopIterScratch_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow hcarry2_nz)

/-- Loop body n=1, call+skip, j=0 over the full `divCode_v4` bundle, preserving `x1`. -/
theorem divK_loop_body_n1_call_skip_j0_exact_loopIterScratch_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : loopBodyN1CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_skip_j0_exact_loopIterScratch_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow)

/-- Loop body n=1, call+skip, j>0 over the full `divCode_v4` bundle, preserving `x1`. -/
theorem divK_loop_body_n1_call_skip_jgt0_exact_loopIterScratch_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_skip_jgt0_exact_loopIterScratch_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow)

/-- Loop body n=1, call+addback, j=0 over the full `divCode_v4` bundle, preserving `x1`. -/
theorem divK_loop_body_n1_call_addback_j0_exact_loopIterScratch_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV4QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_addback_j0_exact_loopIterScratch_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow hcarry2_nz)

/-- Loop body n=1, call path, j=0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_j0_exact_loopIterScratch_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_v4 base)
      (loopBodyN1CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_j0_exact_loopIterScratch_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz)

/-- Loop body n=1, call path, j>0 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_jgt0_exact_loopIterScratch_v4 (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base j
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_jgt0_exact_loopIterScratch_v4_noNop j sp base hpos
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz)

/-- Loop body n=1, call path, j=3 over the full `divCode_v4` bundle. -/
theorem divK_loop_body_n1_call_j3_exact_loopIterScratch_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopBodyN1CallSkipJgt0PreV4NoX1 sp (3 : Word)
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (3 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_body_n1_call_j3_exact_loopIterScratch_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz)

/-- N1 call/max/max/max j=3 setup over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz :
      let qHat := divKTrialCallV4QHat u1 u0 v0
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_v4 base)
      (loopN1CallMaxmaxmaxScratchPreNoX1 sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN1CallScratchNoX1 sp base (3 : Word)
        (divKTrialCallV4QHat u1 u0 v0)
        (divKTrialCallV4DLo v0)
        (divKTrialCallV4Un0 u0)
        (divKTrialCallV4ScratchOut u1 u0 v0 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal) **
        ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig2) **
        ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q2Old) **
        ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig1) **
        ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old) **
        ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
          signExtend12 0) ↦ₘ u0Orig0) **
        ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_call_j3_exact_x1_framed_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratchUn0 scratchMem raVal halign hbltu hcarry2_nz)

/-- N1 call/max/max/max denormalization and DIV epilogue over the full `divCode_v4` bundle. -/
theorem evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4
    (sp base shift : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_v4 base)
      (fullDivN1CallMaxmaxmaxDenormPre sp shift
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0)
      (fullDivN1CallMaxmaxmaxDenormPost sp shift
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_noNop
      sp base shift v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 hshift_nz)

/-- Exact-`x1` framed N1 call/max/max/max denormalization and DIV epilogue over the full
    `divCode_v4` bundle. -/
theorem evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_exact_x1
    (sp base shift : Word)
    (a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0Orig2 u0Orig1 u0Orig0 scratchMem raVal : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_v4 base)
      (fullDivN1CallMaxmaxmaxDenormPre sp shift
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig2 u0Orig1 u0Orig0 **
       fullDivN1CallMaxmaxmaxDenormFrameNoX1 sp base
        a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 scratchMem **
       (.x1 ↦ᵣ raVal))
      (fullDivN1CallMaxmaxmaxUnifiedPostNoX1 sp base shift
        a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0Orig2 u0Orig1 u0Orig0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_noNop_exact_x1
      sp base shift a0 a1 a2 a3 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig2 u0Orig1 u0Orig0 scratchMem raVal hshift_nz)

/-- Bundled full-code statement for the first j=3 call-body step of the N1
    call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxJ3ExactInputSpecV4
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  cpsTripleWithin 224 (I.base + loopBodyOff) (I.base + loopBodyOff)
    (divCode_v4 I.base)
    (loopN1CallMaxmaxmaxScratchPreNoX1 I.sp
      I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
      I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem ** (.x1 ↦ᵣ I.raVal))
    (loopIterPostN1CallScratchNoX1 I.sp I.base (3 : Word)
      (divKTrialCallV4QHat I.u1 I.u0 I.v0)
      (divKTrialCallV4DLo I.v0)
      (divKTrialCallV4Un0 I.u0)
      (divKTrialCallV4ScratchOut I.u1 I.u0 I.v0 I.scratchMem)
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop **
      (.x1 ↦ᵣ I.raVal) **
      ((I.sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig2) **
      ((I.sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q2Old) **
      ((I.sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig1) **
      ((I.sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q1Old) **
      ((I.sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig0) **
      ((I.sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q0Old))

/-- Bundled first j=3 call-body step over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4
  exact divK_loop_n1_call_j3_exact_x1_framed_v4 I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxExactInputHypotheses_carry2Call I hh))

/-- Bundled full-code statement for the j=2/j=1/j=0 all-max tail after
    the first j=3 call-body step in the N1 call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210ExactInputSpecV4
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
    (divCode_v4 I.base)
    (loopN1Iter210PreWithScratchNoX1 I.sp
      I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
      I.v0 I.v1 I.v2 I.v3
      I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
      (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
      (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal))
    (loopN1Iter210PostNoX1 false false false I.sp I.base I.v0 I.v1 I.v2 I.v3
      I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      I.u0Orig1 I.u0Orig0 (I.base + div128CallRetOff) I.v0
      (divKTrialCallV4DLo I.v0) (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal))

/-- Bundled all-max tail after the first j=3 call-body step over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpecV4
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  exact divK_loop_n1_iter210_maxmaxmax_exact_x1_v4 I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (loopN1CallMaxmaxmaxExactInputHypotheses_carry2 I hh)

/-- Bundled framed all-max tail pre/post over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have H210 := divK_loop_n1_iter210_maxmaxmax_exact_x1_v4 I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (loopN1CallMaxmaxmaxExactInputHypotheses_carry2 I hh)
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxJ3PostInput I)
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) := by
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input I hh)

/-- Full-code bundled N1 call/max/max/max exact path: j=3 uses the v4 call
    path and j=2/j=1/j=0 all use the all-max path. -/
@[irreducible]
def loopN1CallMaxmaxmaxExactInputSpecV4
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  cpsTripleWithin 780 (I.base + loopBodyOff) (I.base + denormOff)
    (divCode_v4 I.base)
    (loopN1CallMaxmaxmaxScratchPreNoX1 I.sp
      I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
      I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem ** (.x1 ↦ᵣ I.raVal))
    (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal))

/-- Full bundled N1 call/max/max/max exact path over the full `divCode_v4` bundle. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxExactInputSpecV4
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_input I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4 at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_input I hh
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Full bundled N1 call/max/max/max exact path over `divCode_v4`, with hypotheses supplied
    directly as path branch facts plus the universal carry2 assumption. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_of_bltu
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0)
    (hcarry2 : Carry2NzAll I.v0 I.v1 I.v2 I.v3) :
    loopN1CallMaxmaxmaxExactInputSpecV4 I := by
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4 I halign
    (loopN1CallMaxmaxmaxExactInputHypotheses_of_bltu I
      hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)

/-- Full-code final spec wrapper for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxExactInputSpecV4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxExactInputSpecV4
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs over the full `divCode_v4` bundle. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxExactInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpecV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxExactInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs over `divCode_v4`, with hypotheses supplied directly as
    path branch facts plus the universal carry2 assumption. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_bltu
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1CallMaxmaxmaxExactInputSpecV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  exact fullDivN1_call_maxmaxmax_exact_x1_scratch_v4 sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    halign
    (fullDivN1CallMaxmaxmaxExactInputHypotheses_of_bltu sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)

/-- Full-code full-DIV n=1 preloop plus call/max/max/max path. The post keeps
    the original a[] cells and shift cell framed for the following denormalization phase. -/
@[irreducible]
def fullDivN1PreloopCallMaxmaxmaxExactSpecV4 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word) : Prop :=
  cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) base (base + denormOff)
    (divCode_v4 base)
    ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
      ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))))
    ((loopN1CallMaxmaxmaxScratchPostNoX1 sp base
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      scratchMem ** (.x1 ↦ᵣ raVal)) **
     (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)))

/-- Full-DIV n=1 preloop composed with the call/max/max/max exact loop path over
    the full `divCode_v4` bundle. -/
theorem fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_of_bltu
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1PreloopCallMaxmaxmaxExactSpecV4 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4
  have hPre := evm_div_n1_to_loopSetup_spec_v4_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz
  have hLoop := fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_bltu
    sp base
    jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
    (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
    a0 a1 a2 a3 b0 b1 b2 b3
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hbltu3 hbltu2 hbltu1 hbltu0 hcarry2
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4 at hLoop
  unfold loopN1CallMaxmaxmaxExactInputSpecV4 at hLoop
  unfold fullDivN1CallMaxmaxmaxExactInputs at hLoop
  dsimp only at hLoop
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))
    (by pcFree) hLoop
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      exact loopSetupPost_to_fullDivN1CallMaxmaxmaxScratchPreNoX1_framed
        sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
        jMem retMem dMem dloMem scratchUn0 scratchMem raVal h hp)
    hPre hLoopF

end EvmAsm.Evm64
