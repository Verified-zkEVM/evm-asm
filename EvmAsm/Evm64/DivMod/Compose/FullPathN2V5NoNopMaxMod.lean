/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopMaxMod

  MOD mirror of `FullPathN2V5NoNopMax`: the n=2 max-path loop bodies (max-skip
  j=0/j>0, max-addback j>0) lifted from the raw v5 bodies (over
  `sharedDivModCodeNoNop_v5`) to `modCode_noNop_v5` via
  `sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5`.  Byte-for-byte the DIV
  wrappers, swapping ONLY the extend target (`_sub_divCode_noNop_v5` →
  `_sub_modCode_noNop_v5`) — the raw bodies and the (code-agnostic) NormPre/Post
  defs are shared.  First brick of the n=2 MOD loop body over `modCode_noNop_v5`
  (bead `evm-asm-wbc4i.10.3.2.4.5`).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2V5.MaxSkipV5NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN2V5.MaxAddbackV5NoNop

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=2, max+skip, j=0 over `modCode_noNop_v5`. -/
theorem divK_loop_body_n2_max_skip_j0_norm_v5_noNop_modCode (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopBodyN2MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_skip_j0_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  rw [loopBodyN2MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN2MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=2, max+skip, j>0 over `modCode_noNop_v5`. -/
theorem divK_loop_body_n2_max_skip_jgt0_norm_v5_noNop_modCode (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2SkipPost sp j (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_skip_jgt0_v5_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=2, max+addback (BEQ double-addback), j>0 over `modCode_noNop_v5`. -/
theorem divK_loop_body_n2_max_addback_jgt0_beq_norm_v5_noNop_modCode (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v5 base)
      (loopBodyN2MaxSkipJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN2AddbackBeqPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n2_max_addback_jgt0_beq_v5_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2MaxSkipJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

end EvmAsm.Evm64
