/-
  EvmAsm.Evm64.DivMod.Compose.FastSetupV6

  v6 fast-path setup brick over `divCodeV6`. Stores the CLZ shift `s`, computes
  `antiShift = -s`, normalizes `b0' = b0 << s`, and `BEQ x6 x0 88` to copyAU
  if `s = 0` (else fall through to normA).

  The `@[irreducible]` post wrapper (`divKFastSetupPost`) ensures downstream
  consumers (normA/copyAU lanes) see an opaque atom instead of the full 8-atom
  sepConj, keeping their `xperm` within the heartbeat budget.

  Brick of the v6 n=1 fast-path body. Bead `evm-asm-7wbf8.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.EpilogueV6
import EvmAsm.Evm64.DivMod.LimbSpec.FastN1
import EvmAsm.Evm64.DivMod.AddrNorm
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.DivMod.AddrNorm (se12_32 se12_3984 se12_3992)

-- ============================================================================
-- @[irreducible] post wrapper — downstream xperm sees 1 opaque atom, not 8.
-- ============================================================================

/-- Postcondition of the fastSetup body (instrs 0-5, before the BEQ):
    `x5 = b0'`, `x2 = antiShift`, `s` stored at 3992, `b0'` stored at 3984.
    Wrapped `@[irreducible]` so normA/copyAU lane proofs see a shallow atom. -/
@[irreducible]
def divKFastSetupPost (sp s b0 antiShift b0Prime : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ antiShift) **
  ((sp + signExtend12 32) ↦ₘ b0) **
  ((sp + signExtend12 3992) ↦ₘ s) **
  ((sp + signExtend12 3984) ↦ₘ b0Prime)

theorem divKFastSetupPost_unfold
    {sp s b0 antiShift b0Prime : Word} :
    divKFastSetupPost sp s b0 antiShift b0Prime =
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 3984) ↦ₘ b0Prime)) := by
  delta divKFastSetupPost
  rfl

-- ============================================================================
-- Code subsumption: fastSetup (block index 2 of divCodeV6) into divCodeV6.
-- ============================================================================

private theorem divK_fastSetup_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6SetupOff) (divK_fastSetup 88)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6
  exact CodeReq.union_mono_left

-- ============================================================================
-- fastSetup body (instrs 0-5): store s, compute antiShift, normalize b0'.
-- ============================================================================

abbrev divK_fastSetup_body_prog : Program :=
  [.SD .x12 .x6 3992, .ADDI .x2 .x0 0, .SUB .x2 .x2 .x6,
   .LD .x5 .x12 32, .SLL .x5 .x5 .x6, .SD .x12 .x5 3984]

abbrev divK_fastSetup_body_code (base : Word) : CodeReq :=
  CodeReq.ofProg base divK_fastSetup_body_prog

theorem divK_fastSetup_body_slice :
    (divK_fastSetup 88).take 6 = divK_fastSetup_body_prog := by rfl

theorem divK_fastSetup_body_spec_within (sp v5 s b0 v2Old m3992 m3984 : Word)
    (base : Word) :
    let antiShift := (0 : Word) - s
    let b0Prime := b0 <<< (s.toNat % 64)
    let cr := divK_fastSetup_body_code base
    cpsTripleWithin 6 base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      (divKFastSetupPost sp s b0 antiShift b0Prime) := by
  intro antiShift b0Prime cr
  rw [divKFastSetupPost_unfold]
  have I0 := sd_spec_gen_within .x12 .x6 sp s m3992 3992 base
  have I1 := addi_spec_gen_within .x2 .x0 v2Old (0 : Word) 0 (base + 4) (by nofun)
  have I2 := sub_spec_gen_rd_eq_rs1_within .x2 .x6 (0 : Word) s (base + 8) (by nofun)
  have I3 := ld_spec_gen_within .x5 .x12 sp v5 b0 32 (base + 12) (by nofun)
  have I4 := sll_spec_gen_rd_eq_rs1_within .x5 .x6 b0 s (base + 16) (by nofun)
  have I5 := sd_spec_gen_within .x12 .x5 sp b0Prime m3984 3984 (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

-- ============================================================================
-- Full fastSetup body over divCodeV6 (lift to divCodeV6 via subsumption).
-- ============================================================================

theorem divK_fastSetup_body_spec_within_v6 (sp v5 s b0 v2Old m3992 m3984 : Word)
    (base : Word) :
    let antiShift := (0 : Word) - s
    let b0Prime := b0 <<< (s.toNat % 64)
    cpsTripleWithin 6 (base + v6SetupOff) (base + v6SetupOff + 24) (divCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      (divKFastSetupPost sp s b0 antiShift b0Prime) := by
  intro antiShift b0Prime
  have h := divK_fastSetup_body_spec_within sp v5 s b0 v2Old m3992 m3984 (base + v6SetupOff)
  exact cpsTripleWithin_extend_code (hmono := fun a i h =>
    divK_fastSetup_code_sub_divCodeV6 a i
      (CodeReq.ofProg_mono_sub (base + v6SetupOff) (base + v6SetupOff) (divK_fastSetup 88)
        divK_fastSetup_body_prog 0
        (by bv_addr) divK_fastSetup_body_slice (by decide) (by decide) a i h)) h

-- ============================================================================
-- BEQ branch: x6 x0 88 at base+v6SetupOff+24.
--   taken   (s = 0): → base+v6CopyAUOff (240)
--   ntaken  (s ≠ 0): → base+v6NormAOff  (156)
-- ============================================================================

theorem divK_fastSetup_beq_taken_addr {base : Word} :
    (base + v6SetupOff + 24 : Word) + signExtend13 88 = base + v6CopyAUOff := by rv64_addr

theorem divK_fastSetup_beq_ntaken_addr {base : Word} :
    (base + v6SetupOff + 24 : Word) + 4 = base + v6NormAOff := by bv_addr

/-- Full fastSetup shift-NZ lane (s ≠ 0): body + BEQ ntaken → normA.
    7 steps total (6 body + 1 BEQ). -/
theorem divK_fastSetup_shiftNz_spec_within_v6 (sp v5 s b0 v2Old m3992 m3984 : Word)
    (base : Word) (hs_ne_0 : s ≠ (0 : Word)) :
    let antiShift := (0 : Word) - s
    let b0Prime := b0 <<< (s.toNat % 64)
    cpsTripleWithin 7 (base + v6SetupOff) (base + v6NormAOff) (divCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      (divKFastSetupPost sp s b0 antiShift b0Prime) := by
  intro antiShift b0Prime
  have hbody := divK_fastSetup_body_spec_within_v6 sp v5 s b0 v2Old m3992 m3984 base
  -- Transport hbody to unfolded post via the equation lemma.
  have hbody_u : cpsTripleWithin 6 (base + v6SetupOff) (base + v6SetupOff + 24) (divCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 3984) ↦ₘ b0Prime)) :=
    divKFastSetupPost_unfold ▸ hbody
  -- BEQ x6 x0 88 at base+v6SetupOff+24
  have hbeq := beq_spec_gen_within .x6 .x0 88 s (0 : Word) (base + v6SetupOff + 24)
  rw [divK_fastSetup_beq_taken_addr, divK_fastSetup_beq_ntaken_addr] at hbeq
  -- Strip the taken arm: prove it's absurd when s ≠ 0.
  have hbeq_ntaken := cpsBranchWithin_ntakenStripPure2 hbeq
    (fun hp hQt => by
      obtain ⟨w1, w2, _, _, _, _, hw_rest⟩ := hQt
      obtain ⟨h3, _, _, _, hpure⟩ := hw_rest
      exact absurd hpure.2 hs_ne_0)
  -- Extend to divCodeV6.
  have hbeq_e := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_fastSetup_code_sub_divCodeV6 a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + v6SetupOff) (divK_fastSetup 88) 6
          (by decide) (by decide)
        rw [show (base + v6SetupOff : Word) + BitVec.ofNat 64 (4 * 6) =
          base + v6SetupOff + 24 from by bv_addr] at hlookup
        exact hlookup) a i h)) hbeq_ntaken
  -- Frame the body post through the BEQ (exclude x6, x0 — they're in BEQ pre).
  have hbeq_f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x2 ↦ᵣ antiShift) **
     ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ s) **
     ((sp + signExtend12 3984) ↦ₘ b0Prime))
    (by pcFree) hbeq_e
  have h := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody_u hbeq_f
  rw [divKFastSetupPost_unfold]
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h

/-- Full fastSetup shift-0 lane (s = 0): body + BEQ taken → copyAU.
    7 steps total (6 body + 1 BEQ). Mirror of
    `divK_fastSetup_shiftNz_spec_within_v6`, but the BEQ is *taken* (the
    not-taken `s ≠ 0` arm is refuted as absurd). -/
theorem divK_fastSetup_shift0_spec_within_v6 (sp v5 s b0 v2Old m3992 m3984 : Word)
    (base : Word) (hs_eq_0 : s = (0 : Word)) :
    let antiShift := (0 : Word) - s
    let b0Prime := b0 <<< (s.toNat % 64)
    cpsTripleWithin 7 (base + v6SetupOff) (base + v6CopyAUOff) (divCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      (divKFastSetupPost sp s b0 antiShift b0Prime) := by
  intro antiShift b0Prime
  have hbody := divK_fastSetup_body_spec_within_v6 sp v5 s b0 v2Old m3992 m3984 base
  -- Transport hbody to unfolded post via the equation lemma.
  have hbody_u : cpsTripleWithin 6 (base + v6SetupOff) (base + v6SetupOff + 24) (divCodeV6 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ v2Old) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ m3992) **
       ((sp + signExtend12 3984) ↦ₘ m3984))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x6 ↦ᵣ s) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ antiShift) **
       ((sp + signExtend12 32) ↦ₘ b0) **
       ((sp + signExtend12 3992) ↦ₘ s) **
       ((sp + signExtend12 3984) ↦ₘ b0Prime)) :=
    divKFastSetupPost_unfold ▸ hbody
  -- BEQ x6 x0 88 at base+v6SetupOff+24
  have hbeq := beq_spec_gen_within .x6 .x0 88 s (0 : Word) (base + v6SetupOff + 24)
  rw [divK_fastSetup_beq_taken_addr, divK_fastSetup_beq_ntaken_addr] at hbeq
  -- Strip the not-taken arm: prove it's absurd when s = 0.
  have hbeq_taken := cpsBranchWithin_takenStripPure2 hbeq
    (fun hp hQf => by
      obtain ⟨w1, w2, _, _, _, _, hw_rest⟩ := hQf
      obtain ⟨h3, _, _, _, hpure⟩ := hw_rest
      exact absurd hs_eq_0 hpure.2)
  -- Extend to divCodeV6.
  have hbeq_e := cpsTripleWithin_extend_code (hmono := by
    intro a i h
    exact divK_fastSetup_code_sub_divCodeV6 a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + v6SetupOff) (divK_fastSetup 88) 6
          (by decide) (by decide)
        rw [show (base + v6SetupOff : Word) + BitVec.ofNat 64 (4 * 6) =
          base + v6SetupOff + 24 from by bv_addr] at hlookup
        exact hlookup) a i h)) hbeq_taken
  -- Frame the body post through the BEQ (exclude x6, x0 — they're in BEQ pre).
  have hbeq_f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0Prime) ** (.x2 ↦ᵣ antiShift) **
     ((sp + signExtend12 32) ↦ₘ b0) **
     ((sp + signExtend12 3992) ↦ₘ s) **
     ((sp + signExtend12 3984) ↦ₘ b0Prime))
    (by pcFree) hbeq_e
  have h := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody_u hbeq_f
  rw [divKFastSetupPost_unfold]
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h

end EvmAsm.Evm64
