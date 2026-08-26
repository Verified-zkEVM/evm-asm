/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopCallAddback

  v5/no-NOP norm-pre wrapper for the n=4 DIV call+addback-beq loop body (j=0).
  Mirror of the v5 n=4 call-skip norm wrapper (FullPathN4V5NoNopCall) with the
  raw call+addback-beq body (#7587) swapped in: same `loopBodyN4CallJ0NormPre`
  precondition (+ the v5 `sp+3936` scratch cell), the BEQ-nonzero `hborrow` +
  `hcarry2_nz` hypotheses, and the v5 post `loopBodyN4CallAddbackBeqJ0PostV5`
  (identity post map).  Lifts from `sharedDivModCodeNoNop_v5` to
  `divCode_noNop_v5`.  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4NoNop
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN4V5.CallAddbackBeqV5NoNop

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=4, call+addback-beq, j=0 over `divCode_noNop_v5`, with sp-relative
    addresses behind `loopBodyN4CallJ0NormPre` + the v5 `sp+3936` scratch cell. -/
theorem divK_loop_body_n4_call_addback_j0_beq_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
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
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN4CallJ0NormPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallAddbackBeqJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n4_call_addback_j0_beq_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow hcarry2_nz
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [loopBodyN4CallJ0NormPre_unfold] at hp
      rw [loopBodyN4CallSkipJ0PreV4_unfold]
      rw [loopBodyN4CallSkipJ0Pre_unfold]
      simp only [se12_32, se12_40, se12_48, se12_56,
                 u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
                 u_base_off4072_j0, u_base_off4064_j0, q_addr_j0]
      xperm_hyp hp)
    (fun _ hp => hp)
    raw'

end EvmAsm.Evm64
