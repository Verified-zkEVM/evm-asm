/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopMaxAddbackNormMod

  MOD mirror of `FullPathN3V5NoNopMaxAddbackNorm`: v5/no-NOP norm-pre wrappers for
  the n=3 max+addback-beq loop bodies over `modCode_noNop_v5`.  Byte-for-byte the
  DIV wrappers, swapping ONLY the extend target
  (`sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5` →
  `sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5`).  Raw bodies (over the SHARED
  `sharedDivModCodeNoNop_v5`) + code-agnostic NormPre/Post defs reused verbatim.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopMaxAddbackNorm

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=3, max+addback-beq, j=0 over `modCode_noNop_v5`. -/
theorem divK_loop_body_n3_max_addback_j0_beq_norm_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_addback_j0_beq_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  rw [loopBodyN3MaxSkipPre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN3MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=3, max+addback-beq, j>0 over `modCode_noNop_v5`. -/
theorem divK_loop_body_n3_max_addback_jgt0_beq_norm_v5_noNop_modCode (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN3MaxAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3AddbackBeqPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_addback_jgt0_beq_v5_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3MaxAddbackJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

end EvmAsm.Evm64
