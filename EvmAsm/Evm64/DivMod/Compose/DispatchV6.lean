/-
  EvmAsm.Evm64.DivMod.Compose.DispatchV6

  v6 n=1 dispatch prologue over `divCodeV6`. The dispatch (block 0) OR-reduces
  the upper divisor limbs, then `BNE` to the embedded v5 path if any is nonzero
  (n ≥ 2). This brick composes the OR-reduce (`divK_dispatchN1_orReduce`, done)
  with that `BNE` into a `cpsBranchWithin`:
    taken  (b1|b2|b3 ≠ 0, i.e. n ≥ 2) → `base + v6V5Off`
    ntaken (b1|b2|b3 = 0)             → `base + 24` (the `LD b0` + `BEQ`).

  Bead `evm-asm-bpagu`.
-/

import EvmAsm.Evm64.DivMod.Compose.OffsetsV6
import EvmAsm.Evm64.DivMod.LimbSpec.FastN1
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- The dispatch is block 0 of divCodeV6 — no skipBlock needed.
private theorem divK_dispatchN1_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg base (divK_dispatchN1 796 788)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem divK_dispatchN1_bne_taken_addr {base : Word} :
    (base + 20 : Word) + signExtend13 796 = base + v6V5Off := by rv64_addr

/-- OR-reduce ;; BNE over `divCodeV6` (6 steps, `base` → branch): if any upper
    divisor limb is nonzero (n ≥ 2) branch to the embedded v5 path; else fall
    through to the `LD b0`/`BEQ` at `base + 24`. -/
theorem divK_dispatchN1_bne_spec_within_v6 (sp v5 v10 b1 b2 b3 : Word) (base : Word) :
    cpsBranchWithin 6 base (divCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
       ((sp + signExtend12 56) ↦ₘ b3))
      (base + v6V5Off)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
         ((sp + signExtend12 56) ↦ₘ b3) ** ⌜(b1 ||| b2 ||| b3) ≠ (0 : Word)⌝)
      (base + 24)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
         ((sp + signExtend12 56) ↦ₘ b3) ** ⌜(b1 ||| b2 ||| b3) = (0 : Word)⌝) := by
  -- OR-reduce (block-0 slice), extended to divCodeV6, framed with x0.
  have hor := divK_dispatchN1_orReduce_spec_within sp base b1 b2 b3 v5 v10
  have hore := cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_dispatchN1_code_sub_divCodeV6 a i
      (CodeReq.ofProg_mono_sub base base (divK_dispatchN1 796 788)
        [.LD .x5 .x12 40, .LD .x10 .x12 48, .OR .x5 .x5 .x10, .LD .x10 .x12 56, .OR .x5 .x5 .x10]
        0 (by bv_omega) rfl (by decide) (by decide) a i h)) hor
  have horf := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) hore
  -- BNE x5 x0 796 at base+20, extended to divCodeV6, framed with the rest.
  have hbne := bne_spec_gen_within .x5 .x0 796 (b1 ||| b2 ||| b3) (0 : Word) (base + 20)
  rw [divK_dispatchN1_bne_taken_addr, show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact divK_dispatchN1_code_sub_divCodeV6 a i
      (CodeReq.singleton_mono (by
        have hl := CodeReq.ofProg_lookup base (divK_dispatchN1 796 788) 5 (by decide) (by decide)
        rw [show (base : Word) + BitVec.ofNat 64 (4 * 5) = base + 20 from by bv_omega] at hl
        exact hl) a i h)) hbne
  have hbnef := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** ((sp + signExtend12 40) ↦ₘ b1) **
     ((sp + signExtend12 48) ↦ₘ b2) ** ((sp + signExtend12 56) ↦ₘ b3))
    (by pcFree) hbnee
  -- Align the OR-reduce postcondition to the BNE-framed precondition, then seq.
  have horf' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by xperm_hyp hq)
    (Q' := ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** ((sp + signExtend12 40) ↦ₘ b1) **
       ((sp + signExtend12 48) ↦ₘ b2) ** ((sp + signExtend12 56) ↦ₘ b3))) horf
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_same_cr horf' hbnef
  refine cpsBranchWithin_weaken ?_ ?_ ?_ hbr
  · intro h hp; xperm_hyp hp
  · intro h hq; xperm_hyp hq
  · intro h hq; xperm_hyp hq

end EvmAsm.Evm64
