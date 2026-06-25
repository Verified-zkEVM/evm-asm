/-
  EvmAsm.Evm64.DivMod.Compose.V6FastResultBridge

  Reconcile the v6 fast-path body's stored quotient limbs (`v6chainQ_j` at the
  result slots `sp+32 / +40 / +48 / +56`) with the `evmWordIs (sp+32)
  (EvmWord.div a b)` component of `divStackDispatchPost`.  This is the result
  half of the `dr466.3` postcondition weakening: it lets both fast-body lanes'
  postconditions be folded into the same dispatch post the reused v5 arm
  produces, so all arms converge under `cpsBranchWithin_merge_same_cr`.

  Proved per-cell via `congrArg` over the `getLimbN` bridges (the
  `EvmWord.div … (fromLimbs …)` term carries a `match`-motive that blocks a
  direct `rw`/`simp` rewrite, so each limb cell is rewritten individually).
  Bead `evm-asm-dr466.3`.
-/

import EvmAsm.Evm64.DivMod.Compose.V6BodyModelBridge
import EvmAsm.Evm64.DivMod.Compose.V6Shift0ChainBridge
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Scratch-ownership assembly.** The 15 div-scratch value cells (at the
    `divScratchOwn` offsets `4088 … 3976`) weaken to `divScratchOwn sp`. A
    building block of the fast-arm post → `divStackDispatchPost` weakening:
    after the fast body, every scratch cell holds a concrete value, which
    `divStackDispatchPost` only needs as anonymous ownership. -/
theorem fast_scratch_own_assemble
    (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Word) :
    ∀ h, (((sp + signExtend12 4088) ↦ₘ c0) ** ((sp + signExtend12 4080) ↦ₘ c1) **
          ((sp + signExtend12 4072) ↦ₘ c2) ** ((sp + signExtend12 4064) ↦ₘ c3) **
          ((sp + signExtend12 4056) ↦ₘ c4) ** ((sp + signExtend12 4048) ↦ₘ c5) **
          ((sp + signExtend12 4040) ↦ₘ c6) ** ((sp + signExtend12 4032) ↦ₘ c7) **
          ((sp + signExtend12 4024) ↦ₘ c8) ** ((sp + signExtend12 4016) ↦ₘ c9) **
          ((sp + signExtend12 4008) ↦ₘ c10) ** ((sp + signExtend12 4000) ↦ₘ c11) **
          ((sp + signExtend12 3992) ↦ₘ c12) ** ((sp + signExtend12 3984) ↦ₘ c13) **
          ((sp + signExtend12 3976) ↦ₘ c14)) h →
      divScratchOwn sp h := by
  intro h hp
  rw [divScratchOwn_unfold]
  revert hp
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  apply sepConj_mono (memIs_implies_memOwn)
  exact memIs_implies_memOwn

/-- **Call-scratch ownership assembly.** Extends `fast_scratch_own_assemble`
    with the four call cells (`3968 … 3944`) and `x1` to assemble the full
    `divScratchOwnCall sp` — the scratch component of `divStackDispatchPost`. -/
theorem fast_scratch_own_call_assemble
    (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 d0 d1 d2 d3 x1v : Word) :
    ∀ h, ((((sp + signExtend12 4088) ↦ₘ c0) ** ((sp + signExtend12 4080) ↦ₘ c1) **
          ((sp + signExtend12 4072) ↦ₘ c2) ** ((sp + signExtend12 4064) ↦ₘ c3) **
          ((sp + signExtend12 4056) ↦ₘ c4) ** ((sp + signExtend12 4048) ↦ₘ c5) **
          ((sp + signExtend12 4040) ↦ₘ c6) ** ((sp + signExtend12 4032) ↦ₘ c7) **
          ((sp + signExtend12 4024) ↦ₘ c8) ** ((sp + signExtend12 4016) ↦ₘ c9) **
          ((sp + signExtend12 4008) ↦ₘ c10) ** ((sp + signExtend12 4000) ↦ₘ c11) **
          ((sp + signExtend12 3992) ↦ₘ c12) ** ((sp + signExtend12 3984) ↦ₘ c13) **
          ((sp + signExtend12 3976) ↦ₘ c14)) **
          ((sp + signExtend12 3968) ↦ₘ d0) ** ((sp + signExtend12 3960) ↦ₘ d1) **
          ((sp + signExtend12 3952) ↦ₘ d2) ** ((sp + signExtend12 3944) ↦ₘ d3) **
          ((.x1 : Reg) ↦ᵣ x1v)) h →
      divScratchOwnCall sp h := by
  intro h hp
  rw [divScratchOwnCall_unfold]
  revert hp
  apply sepConj_mono (fast_scratch_own_assemble sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)
  apply sepConj_mono memIs_implies_memOwn
  apply sepConj_mono memIs_implies_memOwn
  apply sepConj_mono memIs_implies_memOwn
  apply sepConj_mono memIs_implies_memOwn
  exact regIs_implies_regOwn _

/-- **Call-scratch ownership assembly (body form).** As `fast_scratch_own_call_assemble`,
    but the four call cells arrive already as `memOwn` (the shape the fast-body
    postcondition exposes them in) rather than as value atoms. This is the form
    consumed directly by the fast-arm post weakening. -/
theorem fast_scratch_own_call_bodyform
    (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v : Word) :
    ∀ h, ((((sp + signExtend12 4088) ↦ₘ c0) ** ((sp + signExtend12 4080) ↦ₘ c1) **
          ((sp + signExtend12 4072) ↦ₘ c2) ** ((sp + signExtend12 4064) ↦ₘ c3) **
          ((sp + signExtend12 4056) ↦ₘ c4) ** ((sp + signExtend12 4048) ↦ₘ c5) **
          ((sp + signExtend12 4040) ↦ₘ c6) ** ((sp + signExtend12 4032) ↦ₘ c7) **
          ((sp + signExtend12 4024) ↦ₘ c8) ** ((sp + signExtend12 4016) ↦ₘ c9) **
          ((sp + signExtend12 4008) ↦ₘ c10) ** ((sp + signExtend12 4000) ↦ₘ c11) **
          ((sp + signExtend12 3992) ↦ₘ c12) ** ((sp + signExtend12 3984) ↦ₘ c13) **
          ((sp + signExtend12 3976) ↦ₘ c14)) **
          (memOwn (sp + signExtend12 3968)) ** (memOwn (sp + signExtend12 3960)) **
          (memOwn (sp + signExtend12 3952)) ** (memOwn (sp + signExtend12 3944)) **
          ((.x1 : Reg) ↦ᵣ x1v)) h →
      divScratchOwnCall sp h := by
  intro h hp
  rw [divScratchOwnCall_unfold]
  revert hp
  apply sepConj_mono (fast_scratch_own_assemble sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (fun _ x => x)
  exact regIs_implies_regOwn _

/-- **Fast-arm post structural weakening (core).** From the canonical
    intermediate shape — `evmWordIs` already folded for both operands,
    clobbered registers as exact values, scratch cells as values, the four
    call cells as `memOwn`, plus `x1` — derive the unfolded `divStackDispatchPost`
    shape (`** memOwn 3936`, i.e. `divStackDispatchPostV5`). Purely structural:
    weaken `regIs→regOwn`, assemble `divScratchOwnCall`. No arithmetic — the
    quotient `wq` and dividend `wa` are abstract `EvmWord`s, instantiated to
    `EvmWord.div a b` / `a` at the use site after the `evmWordIs` folds. -/
theorem fast_post_weaken_core (sp : Word) (wa wq : EvmWord)
    (x2v x11v qv0 qv1 qv2 qv3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v : Word) :
    ∀ h, ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** (.x2 ↦ᵣ x2v) **
          (.x5 ↦ᵣ qv0) ** (.x6 ↦ᵣ qv1) ** (.x7 ↦ᵣ qv2) ** (.x10 ↦ᵣ qv3) ** (.x11 ↦ᵣ x11v) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs sp wa ** evmWordIs (sp + 32) wq **
          ((((sp + signExtend12 4088) ↦ₘ c0) ** ((sp + signExtend12 4080) ↦ₘ c1) **
            ((sp + signExtend12 4072) ↦ₘ c2) ** ((sp + signExtend12 4064) ↦ₘ c3) **
            ((sp + signExtend12 4056) ↦ₘ c4) ** ((sp + signExtend12 4048) ↦ₘ c5) **
            ((sp + signExtend12 4040) ↦ₘ c6) ** ((sp + signExtend12 4032) ↦ₘ c7) **
            ((sp + signExtend12 4024) ↦ₘ c8) ** ((sp + signExtend12 4016) ↦ₘ c9) **
            ((sp + signExtend12 4008) ↦ₘ c10) ** ((sp + signExtend12 4000) ↦ₘ c11) **
            ((sp + signExtend12 3992) ↦ₘ c12) ** ((sp + signExtend12 3984) ↦ₘ c13) **
            ((sp + signExtend12 3976) ↦ₘ c14)) **
            (memOwn (sp + signExtend12 3968)) ** (memOwn (sp + signExtend12 3960)) **
            (memOwn (sp + signExtend12 3952)) ** (memOwn (sp + signExtend12 3944)) **
            ((.x1 : Reg) ↦ᵣ x1v)) **
          memOwn (sp + signExtend12 3936)) h →
        ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x9 ** regOwn .x2 **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         (.x0 ↦ᵣ (0 : Word)) ** evmWordIs sp wa ** evmWordIs (sp + 32) wq **
         divScratchOwnCall sp ** memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  revert hp
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (fun _ x => x)
  apply sepConj_mono (fast_scratch_own_call_bodyform sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 x1v)
  exact (fun _ x => x)

variable (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word)

/-- **shiftNz lane result reconciliation.** The four quotient limbs the fast
    body stores at `sp+32 / +40 / +48 / +56` form `evmWordIs (sp+32)
    (EvmWord.div a b)`. -/
theorem fast_div_result_word_shiftNz
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    evmWordIs (sp + 32)
        (EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    = (((sp + 32) ↦ₘ v6chainQ0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nU0 a0 b0) (v6nD b0)) **
       ((sp + 40) ↦ₘ v6chainQ1 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0) (v6nD b0)) **
       ((sp + 48) ↦ₘ v6chainQ2 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nD b0)) **
       ((sp + 56) ↦ₘ v6chainQ3 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nD b0))) := by
  rw [evmWordIs_sp32_unfold]
  congr 1
  · exact congrArg (fun w => (sp + 32) ↦ₘ w)
      (v6n_div_getLimbN_0 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  congr 1
  · exact congrArg (fun w => (sp + 40) ↦ₘ w)
      (v6n_div_getLimbN_1 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  congr 1
  · exact congrArg (fun w => (sp + 48) ↦ₘ w)
      (v6n_div_getLimbN_2 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  · exact congrArg (fun w => (sp + 56) ↦ₘ w)
      (v6n_div_getLimbN_3 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- **shift=0 lane result reconciliation.** As above, for the already-normalized
    lane whose window is `(0, a3, a2, a1, a0)` with `d = v6nD b0`. -/
theorem fast_div_result_word_shift0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    evmWordIs (sp + 32)
        (EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    = (((sp + 32) ↦ₘ v6chainQ0 0 a3 a2 a1 a0 (v6nD b0)) **
       ((sp + 40) ↦ₘ v6chainQ1 0 a3 a2 a1 (v6nD b0)) **
       ((sp + 48) ↦ₘ v6chainQ2 0 a3 a2 (v6nD b0)) **
       ((sp + 56) ↦ₘ v6chainQ3 0 a3 (v6nD b0))) := by
  rw [evmWordIs_sp32_unfold]
  congr 1
  · exact congrArg (fun w => (sp + 32) ↦ₘ w)
      (v6n_div_getLimbN_shift0_0 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)
  congr 1
  · exact congrArg (fun w => (sp + 40) ↦ₘ w)
      (v6n_div_getLimbN_shift0_1 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)
  congr 1
  · exact congrArg (fun w => (sp + 48) ↦ₘ w)
      (v6n_div_getLimbN_shift0_2 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)
  · exact congrArg (fun w => (sp + 56) ↦ₘ w)
      (v6n_div_getLimbN_shift0_3 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)

/-- **Dividend preservation fold.** The unchanged dividend cells `sp+0/+8/+16/+24`
    fold into `evmWordIs sp a` — the `a`-operand component of
    `divStackDispatchPost`, preserved by the fast path. -/
theorem fast_div_dividend_word (sp a0 a1 a2 a3 : Word) :
    evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
    = ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) := by
  rw [evmWordIs_sp_unfold]
  congr 1
  · exact congrArg (fun w => sp ↦ₘ w) EvmWord.getLimbN_fromLimbs_0
  congr 1
  · exact congrArg (fun w => (sp + 8) ↦ₘ w) EvmWord.getLimbN_fromLimbs_1
  congr 1
  · exact congrArg (fun w => (sp + 16) ↦ₘ w) EvmWord.getLimbN_fromLimbs_2
  · exact congrArg (fun w => (sp + 24) ↦ₘ w) EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
