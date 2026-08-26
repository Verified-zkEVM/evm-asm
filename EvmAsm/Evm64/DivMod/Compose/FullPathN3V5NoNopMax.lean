/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopMax

  v5/no-NOP norm-pre wrappers for the n=3 DIV max+skip loop bodies.  Mirror of
  the v4 n=3 max-skip norm wrappers (`FullPathN3V4NoNop`), lifting the raw v5
  bodies (over `sharedDivModCodeNoNop_v5`) to `divCode_noNop_v5` via
  `sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5`, and hiding the sp-relative
  addresses behind the (code-agnostic) NormPre defs reused from the v4 wrappers.
  Bead `evm-asm-wbc4i.9.3.3.2.1` (n=3 v5 max loop-body-jN norm wrappers).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN3V5.MaxSkipV5NoNop

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=3, max+skip, j=0 over `divCode_noNop_v5`, with sp-relative
    addresses hidden behind a named precondition. -/
theorem divK_loop_body_n3_max_skip_j0_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_skip_j0_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5) raw
  rw [loopBodyN3MaxSkipPre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN3MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=3, max+skip, j=1 over `divCode_noNop_v5`, with the precondition
    hidden behind an irreducible definition. -/
theorem divK_loop_body_n3_max_skip_j1_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN3MaxSkipJ1NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3SkipPost sp (1 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_skip_j1_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3MaxSkipJ1NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

end EvmAsm.Evm64
