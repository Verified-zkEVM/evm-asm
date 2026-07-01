/-
  EvmAsm.Evm64.DivMod.Compose.DispatchV6Mod

  v6 n=1 dispatch prologue over `modCodeV6`.  MOD mirror of `Compose/DispatchV6.lean`
  (DIV): block 0 OR-reduces the upper divisor limbs and `BNE`s to the embedded v5
  path if any is nonzero (n ≥ 2), else `LD b0`/`BEQ`s to the v5 path on
  divide-by-zero or falls through to the fast body.  Only the branch displacements
  (`divK_dispatchN1 824 816` vs div's `796 788`) and the taken target
  (`modV6V5Off` vs `v6V5Off`) differ.  Brick 7 of the MOD v6 fast arm.
-/

import EvmAsm.Evm64.DivMod.Compose.OffsetsV6
import EvmAsm.Evm64.DivMod.LimbSpec.FastN1
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- The dispatch is block 0 of modCodeV6 — no skipBlock needed.
private theorem modK_dispatchN1_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg base (divK_dispatchN1 824 816)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem modK_dispatchN1_bne_taken_addr {base : Word} :
    (base + 20 : Word) + signExtend13 824 = base + modV6V5Off := by rv64_addr

/-- OR-reduce ;; BNE over `modCodeV6` (6 steps, `base` → branch): if any upper
    divisor limb is nonzero (n ≥ 2) branch to the embedded v5 path; else fall
    through to the `LD b0`/`BEQ` at `base + 24`. -/
theorem modK_dispatchN1_bne_spec_within_v6 (sp v5 v10 b1 b2 b3 : Word) (base : Word) :
    cpsBranchWithin 6 base (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
       ((sp + signExtend12 56) ↦ₘ b3))
      (base + modV6V5Off)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
         ((sp + signExtend12 56) ↦ₘ b3) ** ⌜(b1 ||| b2 ||| b3) ≠ (0 : Word)⌝)
      (base + 24)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + signExtend12 40) ↦ₘ b1) ** ((sp + signExtend12 48) ↦ₘ b2) **
         ((sp + signExtend12 56) ↦ₘ b3) ** ⌜(b1 ||| b2 ||| b3) = (0 : Word)⌝) := by
  have hor := divK_dispatchN1_orReduce_spec_within sp base b1 b2 b3 v5 v10
  have hore := cpsTripleWithin_extend_code (hmono := fun a i h =>
    modK_dispatchN1_code_sub_modCodeV6 a i
      (CodeReq.ofProg_mono_sub base base (divK_dispatchN1 824 816)
        [.LD .x5 .x12 40, .LD .x10 .x12 48, .OR .x5 .x5 .x10, .LD .x10 .x12 56, .OR .x5 .x5 .x10]
        0 (by bv_omega) rfl (by decide) (by decide) a i h)) hor
  have horf := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) hore
  have hbne := bne_spec_gen_within .x5 .x0 824 (b1 ||| b2 ||| b3) (0 : Word) (base + 20)
  rw [modK_dispatchN1_bne_taken_addr, show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact modK_dispatchN1_code_sub_modCodeV6 a i
      (CodeReq.singleton_mono (by
        have hl := CodeReq.ofProg_lookup base (divK_dispatchN1 824 816) 5 (by decide) (by decide)
        rw [show (base : Word) + BitVec.ofNat 64 (4 * 5) = base + 20 from by bv_omega] at hl
        exact hl) a i h)) hbne
  have hbnef := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** ((sp + signExtend12 40) ↦ₘ b1) **
     ((sp + signExtend12 48) ↦ₘ b2) ** ((sp + signExtend12 56) ↦ₘ b3))
    (by pcFree) hbnee
  have horf' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by xperm_hyp hq)
    (Q' := ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** ((sp + signExtend12 40) ↦ₘ b1) **
       ((sp + signExtend12 48) ↦ₘ b2) ** ((sp + signExtend12 56) ↦ₘ b3))) horf
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_same_cr horf' hbnef
  refine cpsBranchWithin_weaken ?_ ?_ ?_ hbr
  · intro h hp; xperm_hyp hp
  · intro h hq; xperm_hyp hq
  · intro h hq; xperm_hyp hq

theorem modK_dispatchN1_beq_taken_addr {base : Word} :
    (base + 28 : Word) + signExtend13 816 = base + modV6V5Off := by rv64_addr

/-- LD b0 ;; BEQ over `modCodeV6` (2 steps, `base + 24` → branch): load the single
    divisor limb `b0`; if it is zero (divide-by-zero) branch to the v5 path; else
    fall through to the fast-path body at `base + v6ClzOff`. -/
theorem modK_dispatchN1_beq_spec_within_v6 (sp v5 b0 : Word) (base : Word) :
    cpsBranchWithin 2 (base + 24) (modCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 32) ↦ₘ b0))
      (base + modV6V5Off)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + signExtend12 32) ↦ₘ b0) ** ⌜b0 = (0 : Word)⌝)
      (base + v6ClzOff)
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + signExtend12 32) ↦ₘ b0) ** ⌜b0 ≠ (0 : Word)⌝) := by
  have hld := ld_spec_gen_within .x5 .x12 sp v5 b0 32 (base + 24) (by nofun)
  have hlde := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact modK_dispatchN1_code_sub_modCodeV6 a i
      (CodeReq.singleton_mono (by
        have hl := CodeReq.ofProg_lookup base (divK_dispatchN1 824 816) 6 (by decide) (by decide)
        rw [show (base : Word) + BitVec.ofNat 64 (4 * 6) = base + 24 from by bv_omega] at hl
        exact hl) a i h)) hld
  have hldf := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) hlde
  have hbeq := beq_spec_gen_within .x5 .x0 816 b0 (0 : Word) (base + 28)
  rw [modK_dispatchN1_beq_taken_addr,
    show (base + 28 : Word) + 4 = base + v6ClzOff from by bv_omega] at hbeq
  have hbeqe := cpsBranchWithin_extend_code (hmono := by
    intro a i h
    exact modK_dispatchN1_code_sub_modCodeV6 a i
      (CodeReq.singleton_mono (by
        have hl := CodeReq.ofProg_lookup base (divK_dispatchN1 824 816) 7 (by decide) (by decide)
        rw [show (base : Word) + BitVec.ofNat 64 (4 * 7) = base + 28 from by bv_omega] at hl
        exact hl) a i h)) hbeq
  have hbeqf := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 32) ↦ₘ b0))
    (by pcFree) hbeqe
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hldf
  have hldf' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by xperm_hyp hq)
    (Q' := ((.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 32) ↦ₘ b0)))
    hldf
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_same_cr hldf' hbeqf
  refine cpsBranchWithin_weaken ?_ ?_ ?_ hbr
  · intro h hp; xperm_hyp hp
  · intro h hq; xperm_hyp hq
  · intro h hq; xperm_hyp hq

end EvmAsm.Evm64
