/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2v4

  Full-step composition for instructions [40]-[70] of the
  `divK_div128_v4` subroutine — the v4 fix that adds a 2nd Phase 2b
  D3 correction iteration (Knuth TAOCP §4.3.1 classical D3 step,
  full 2-iteration version, Phase 2b half).

  Combines:
  - step-2-init (DIVU+MUL+SUB) — instrs [40..42] (same as v2 step2)
  - clamp-q0 (SRLI+BEQ+ADDI+ADD) — instrs [43..46] (same as v2)
  - Phase 2b guard (SRLI+BNE) — instrs [47..48] (same as v2)
  - Phase 2b 1st D3 with save/restore — instrs [49..60] (NEW shape)
  - Phase 2b 2nd D3 — instrs [61..70] (NEW)

  into a single refined `q0` computation matching the Lean abstraction
  `div128Quot_v4`'s Phase 2 output (q0 = q0'' after BOTH Phase 2b D3
  iterations).

  The v4 Phase 2b structure differs from v2 Phase 2b in two ways:
  1. The 1st D3 saves rhat2c to scratch slot 3936 before clobbering x11
     with un0, then restores it in BOTH BLTU paths so rhat2c is
     available for the 2nd D3 guard.
  2. The 2nd D3 (instrs [61..70]) mirrors Phase 1b's 2nd D3 structure
     but for q0/rhat2 instead of q1/rhat.

  PR-A2 of the v2 → v4 migration plan. Issue #1337 / Issue #61.
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The 31 instructions of the step-2-v4 block (instrs [40..70] of
    `divK_div128_v4`), as a plain `List Instr` so `step2v4_sub` can use
    `CodeReq.ofProg_lookup` — the same mechanism as `d128_v4_sub`. -/
def divKDiv128Step2V4Instrs : List Instr :=
  [.DIVU .x5 .x7 .x6,   .MUL .x9 .x5 .x6,   .SUB .x11 .x7 .x9,   -- [0..2]
   .SRLI .x9 .x5 32,     .BEQ .x9 .x0 12,     .ADDI .x5 .x5 4095,   -- [3..5]
   .ADD .x11 .x11 .x6,   .SRLI .x9 .x11 32,   .BNE .x9 .x0 92,      -- [6..8]
   .LD .x9 .x12 3952,    .MUL .x7 .x5 .x9,    .SLLI .x9 .x11 32,    -- [9..11]
   .SD .x12 .x11 3936,   .LD .x11 .x12 3944,  .OR .x9 .x9 .x11,     -- [12..14]
   .BLTU .x9 .x7 12,     .LD .x11 .x12 3936,  .JAL .x0 16,           -- [15..17]
   .ADDI .x5 .x5 4095,   .LD .x11 .x12 3936,  .ADD .x11 .x11 .x6,   -- [18..20]
   .SRLI .x9 .x11 32,    .BNE .x9 .x0 36,     .LD .x9 .x12 3952,    -- [21..23]
   .MUL .x7 .x5 .x9,    .SLLI .x9 .x11 32,   .LD .x11 .x12 3944,   -- [24..26]
   .OR .x9 .x9 .x11,    .BLTU .x9 .x7 8,     .JAL .x0 8,            -- [27..29]
   .ADDI .x5 .x5 4095]                                                  -- [30]

/-- Bundled CodeReq for `divK_div128_step2_v4_spec`. Expressed as
    `CodeReq.ofProg` (not union-of-singletons) so `step2v4_sub` can
    use `ofProg_lookup` — same pattern as `d128_v4_sub` for the full
    `divK_div128_v4` program. `@[irreducible]` to keep let-bindings
    out of theorem signatures. -/
@[irreducible]
def divKDiv128Step2V4Code (base : Word) : CodeReq :=
  CodeReq.ofProg base divKDiv128Step2V4Instrs

private theorem divKDiv128Step2V4Instrs_len : divKDiv128Step2V4Instrs.length = 31 := by decide

/-- Per-instruction subsumption: singleton at byte-offset `4*k` of
    `divKDiv128Step2V4Code base` is included in the CodeReq.
    Exactly analogous to `d128_v4_sub` for the full `divK_div128_v4`
    program — avoids repeating the union-of-singletons form. -/
private theorem step2v4_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < 31)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : divKDiv128Step2V4Instrs.get ⟨k, by
        have := divKDiv128Step2V4Instrs_len; omega⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (divKDiv128Step2V4Code base) a = some i := by
  subst h_addr; subst h_instr; unfold divKDiv128Step2V4Code
  exact fun a i h => CodeReq.singleton_mono
    (CodeReq.ofProg_lookup base divKDiv128Step2V4Instrs k (by
        have := divKDiv128Step2V4Instrs_len; omega) (by decide)) a i h

/-- The single BLTU dispatch at the start of Phase D, extended into the
    step2-v4 code requirement. The semantic path bodies are proved separately. -/
private theorem divK_div128_step2_v4_phase_D_bltu_spec
    (rhat2Un0 q0Dlo1 : Word) (base : Word) :
    cpsBranchWithin 1 (base + 60) (divKDiv128Step2V4Code base)
      ((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1))
      (base + 72)
        ((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜BitVec.ult rhat2Un0 q0Dlo1⌝)
      (base + 64)
        ((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜¬BitVec.ult rhat2Un0 q0Dlo1⌝) := by
  have hbltu_raw := bltu_spec_gen_within .x9 .x7 (12 : BitVec 13) rhat2Un0 q0Dlo1 (base + 60)
  have ha_t : (base + 60) + signExtend13 (12 : BitVec 13) = base + 72 := by rv64_addr
  have ha_f : (base + 60 : Word) + 4 = base + 64 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  exact cpsBranchWithin_extend_code (h := hbltu_raw) (hmono := by
    exact step2v4_sub 15 (base+60) (.BLTU .x9 .x7 12)
      (by omega) (by bv_omega) (by decide))

/-- Phase D BLTU taken body: correction path [18..20]. -/
private theorem divK_div128_step2_v4_phase_D_taken_body_spec
    (sp q0c rhat2c dHi un0 : Word) (base : Word) :
    cpsTripleWithin 3 (base + 72) (base + 84) (divKDiv128Step2V4Code base)
      ((.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x12 ↦ᵣ sp) **
       (sp + signExtend12 3936 ↦ₘ rhat2c) ** (.x6 ↦ᵣ dHi))
      ((.x5 ↦ᵣ (q0c + signExtend12 4095)) ** (.x11 ↦ᵣ (rhat2c + dHi)) **
       (.x12 ↦ᵣ sp) ** (sp + signExtend12 3936 ↦ₘ rhat2c) ** (.x6 ↦ᵣ dHi)) := by
  apply cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub
      (step2v4_sub 18 (base+72) (.ADDI .x5 .x5 4095) (by omega) (by bv_omega) (by decide))
      (CodeReq.union_sub
        (step2v4_sub 19 (base+76) (.LD .x11 .x12 3936) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 20 (base+80) (.ADD .x11 .x11 .x6) (by omega) (by bv_omega) (by decide))))
  have I0 := addi_spec_gen_same_within .x5 q0c 4095 (base + 72) (by nofun)
  have I1 := ld_spec_gen_within .x11 .x12 sp un0 rhat2c 3936 (base + 76) (by nofun)
  have I2 := add_spec_gen_rd_eq_rs1_within .x11 .x6 rhat2c dHi (base + 80) (by nofun)
  simp only [show (base+72:Word)+4 = base+76 from by bv_addr,
             show (base+76:Word)+4 = base+80 from by bv_addr,
             show (base+80:Word)+4 = base+84 from by bv_addr] at I0 I1 I2
  runBlock I0 I1 I2

/-- Phase D BLTU fallthrough body: restore saved rhat2c and jump to merge [16..17]. -/
private theorem divK_div128_step2_v4_phase_D_fallthrough_body_spec
    (sp rhat2c un0 : Word) (base : Word) :
    cpsTripleWithin 2 (base + 64) (base + 84) (divKDiv128Step2V4Code base)
      ((.x11 ↦ᵣ un0) ** (.x12 ↦ᵣ sp) ** (sp + signExtend12 3936 ↦ₘ rhat2c))
      ((.x11 ↦ᵣ rhat2c) ** (.x12 ↦ᵣ sp) ** (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  apply cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub
      (step2v4_sub 16 (base+64) (.LD .x11 .x12 3936) (by omega) (by bv_omega) (by decide))
      (step2v4_sub 17 (base+68) (.JAL .x0 16) (by omega) (by bv_omega) (by decide)))
  have I0 := ld_spec_gen_within .x11 .x12 sp un0 rhat2c 3936 (base + 64) (by nofun)
  have I1 := jal_x0_spec_gen_within 16 (base + 68)
  have h_jal : (base + 68 : Word) + signExtend21 (16 : BitVec 21) = base + 84 := by rv64_addr
  simp only [show (base+64:Word)+4 = base+68 from by bv_addr, h_jal] at I0 I1
  runBlock I0 I1

private def phaseDTakenBranchPost
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word) : Assertion :=
  (((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜BitVec.ult rhat2Un0 q0Dlo1⌝) **
    (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ rhat2c))

private def phaseDTakenBodyPre
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word) : Assertion :=
  (((.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x12 ↦ᵣ sp) **
    (sp + signExtend12 3936 ↦ₘ rhat2c) ** (.x6 ↦ᵣ dHi)) **
    (.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** (.x0 ↦ᵣ 0) **
    ⌜rhat2cHi = 0⌝ ** (sp + signExtend12 3952 ↦ₘ dlo) **
    (sp + signExtend12 3944 ↦ₘ un0))

private theorem divK_div128_step2_v4_phase_D_taken_body_pre
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word)
    (h : PartialState)
    (hp : phaseDTakenBranchPost sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 h) :
      phaseDTakenBodyPre sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 h := by
  dsimp only [phaseDTakenBranchPost, phaseDTakenBodyPre] at hp ⊢
  have hp' :
      ((((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1)) **
        (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) **
        (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
        (sp + signExtend12 3936 ↦ₘ rhat2c)) h) :=
    sepConj_mono_left
      (fun h0 hp0 => sepConj_strip_pure_end2 h0 hp0) h hp
  xperm_hyp hp'

private def phaseDFallthroughBranchPost
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word) : Assertion :=
  (((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜¬BitVec.ult rhat2Un0 q0Dlo1⌝) **
    (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ rhat2c))

private def phaseDFallthroughBodyPre
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word) : Assertion :=
  (((.x11 ↦ᵣ un0) ** (.x12 ↦ᵣ sp) ** (sp + signExtend12 3936 ↦ₘ rhat2c)) **
    (.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) **
    (.x5 ↦ᵣ q0c) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))

private theorem divK_div128_step2_v4_phase_D_fallthrough_body_pre
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word)
    (h : PartialState)
    (hp : phaseDFallthroughBranchPost sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 h) :
      phaseDFallthroughBodyPre sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 h := by
  dsimp only [phaseDFallthroughBranchPost, phaseDFallthroughBodyPre] at hp ⊢
  have hp' :
      ((((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1)) **
        (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) **
        (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
        (sp + signExtend12 3936 ↦ₘ rhat2c)) h) :=
    sepConj_mono_left
      (fun h0 hp0 => sepConj_strip_pure_end2 h0 hp0) h hp
  xperm_hyp hp'

private def phaseDMergedPre
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word) : Assertion :=
  (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
  (.x11 ↦ᵣ un0) ** (.x9 ↦ᵣ rhat2Un0) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ rhat2c)

private theorem divK_div128_step2_v4_phase_D_pre_zero
    (sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 : Word)
    (h : PartialState)
    (hp : phaseDMergedPre sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 h) :
    rhat2cHi = 0 := by
  dsimp only [phaseDMergedPre] at hp
  have hp' :
      (((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
        (.x11 ↦ᵣ un0) ** (.x9 ↦ᵣ rhat2Un0) **
        (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0)) ** ⌜rhat2cHi = 0⌝ **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
        (sp + signExtend12 3936 ↦ₘ rhat2c)) h := by
    xperm_hyp hp
  obtain ⟨_, _, _, _, _, hright⟩ := hp'
  exact ((sepConj_pure_left _).1 hright).1

/-- The SRLI+BNE dispatch at the start of Phase E, extended into the step2-v4
    code requirement and framed with the registers/memory live across it. -/
private theorem divK_div128_step2_v4_phase_E_guard_spec
    (sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c : Word) (base : Word) :
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
    cpsBranchWithin 2 (base + 84) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
      (base + 124)
        ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
         (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi ≠ 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ rhat2c))
      (base + 92)
        ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
         (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  intro rhat2cHi rhat2'Hi
  have hraw := divK_div128_phase2b_guard_spec_within sp rhat2' rhat2Un0 (base + 84) (36 : BitVec 13)
  simp only [show (base + 84 : Word) + 4 = base + 88 from by bv_addr,
             show (base + 84 : Word) + 8 = base + 92 from by bv_addr,
             show (base + 88 : Word) + signExtend13 (36 : BitVec 13) = base + 124 from by
               rv64_addr] at hraw
  have hguard : cpsBranchWithin 2 (base + 84) (divKDiv128Step2V4Code base) _ _ _ _ _ :=
    cpsBranchWithin_extend_code (h := hraw) (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 21 (base+84) (.SRLI .x9 .x11 32) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 22 (base+88) (.BNE .x9 .x0 36) (by omega) (by bv_omega) (by decide)))
  have hframed := cpsBranchWithin_frameR
    ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
     ⌜rhat2cHi = 0⌝ **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ rhat2c))
    (by pcFree) hguard
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hframed

/-- Phase E guard fallthrough body: the second Phase-2b product check [23..30]. -/
private theorem divK_div128_step2_v4_phase_E_fallthrough_body_spec
    (sp dHi q0' rhat2' rhat2'Hi q0Dlo1 dlo un0 rhat2c : Word) (base : Word) :
    let q0Dlo2 := q0' * dlo
    let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
    let q0'Unguarded := if BitVec.ult rhat2'Un0 q0Dlo2 then q0' + signExtend12 4095 else q0'
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    cpsTripleWithin 8 (base + 92) (base + 124) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
      ((.x5 ↦ᵣ q0'Unguarded) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ q0Dlo2) **
       (.x9 ↦ᵣ rhat2'Un0) ** (.x11 ↦ᵣ un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  intro q0Dlo2 rhat2'Un0 q0'Unguarded rhat2cHi
  have hraw := divK_div128_prodcheck2_merged_spec_within sp q0' rhat2' rhat2'Hi q0Dlo1 dlo un0 (base + 92)
  simp only [show (base+92:Word)+4 = base+96 from by bv_addr,
             show (base+92:Word)+8 = base+100 from by bv_addr,
             show (base+92:Word)+12 = base+104 from by bv_addr,
             show (base+92:Word)+16 = base+108 from by bv_addr,
             show (base+92:Word)+20 = base+112 from by bv_addr,
             show (base+92:Word)+24 = base+116 from by bv_addr,
             show (base+92:Word)+28 = base+120 from by bv_addr,
             show (base+92:Word)+32 = base+124 from by bv_addr] at hraw
  have hext : cpsTripleWithin 8 (base + 92) (base + 124) (divKDiv128Step2V4Code base) _ _ :=
    cpsTripleWithin_extend_code (h := hraw) (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 23 (base+92) (.LD .x9 .x12 3952) (by omega) (by bv_omega) (by decide))
        (CodeReq.union_sub
        (step2v4_sub 24 (base+96) (.MUL .x7 .x5 .x9) (by omega) (by bv_omega) (by decide))
        (CodeReq.union_sub
        (step2v4_sub 25 (base+100) (.SLLI .x9 .x11 32) (by omega) (by bv_omega) (by decide))
        (CodeReq.union_sub
        (step2v4_sub 26 (base+104) (.LD .x11 .x12 3944) (by omega) (by bv_omega) (by decide))
        (CodeReq.union_sub
        (step2v4_sub 27 (base+108) (.OR .x9 .x9 .x11) (by omega) (by bv_omega) (by decide))
        (CodeReq.union_sub
        (step2v4_sub 28 (base+112) (.BLTU .x9 .x7 8) (by omega) (by bv_omega) (by decide))
        (CodeReq.union_sub
        (step2v4_sub 29 (base+116) (.JAL .x0 8) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 30 (base+120) (.ADDI .x5 .x5 4095) (by omega) (by bv_omega) (by decide)))))))))
  have hframed := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi = 0⌝ **
     (sp + signExtend12 3936 ↦ₘ rhat2c))
    (by pcFree) hext
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hframed

private def phaseETakenBranchPost
    (sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c : Word) :
    Assertion :=
  (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
  (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi ≠ 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ rhat2c)

private def phaseEFallthroughBranchPost
    (sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c : Word) :
    Assertion :=
  (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
  (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi = 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ rhat2c)

private theorem phaseE_taken_post_ne
    (sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c : Word)
    (h : PartialState)
    (hp : phaseETakenBranchPost sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c h) :
    rhat2'Hi ≠ 0 := by
  dsimp only [phaseETakenBranchPost] at hp
  have hp' :
      (((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
        (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
        (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝) **
        ⌜rhat2'Hi ≠ 0⌝ **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
        (sp + signExtend12 3936 ↦ₘ rhat2c)) h := by
    xperm_hyp hp
  obtain ⟨_, _, _, _, _, hright⟩ := hp'
  exact ((sepConj_pure_left _).1 hright).1

private theorem phaseE_fallthrough_post_zero
    (sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c : Word)
    (h : PartialState)
    (hp : phaseEFallthroughBranchPost sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c h) :
    rhat2'Hi = 0 := by
  dsimp only [phaseEFallthroughBranchPost] at hp
  have hp' :
      (((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
        (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
        (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝) **
        ⌜rhat2'Hi = 0⌝ **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
        (sp + signExtend12 3936 ↦ₘ rhat2c)) h := by
    xperm_hyp hp
  obtain ⟨_, _, _, _, _, hright⟩ := hp'
  exact ((sepConj_pure_left _).1 hright).1

/-- Bundled postcondition for `divK_div128_step2_v4_spec`. Hides the
    let-chain for Step 2 v4 trial-division intermediates + Phase 2b
    1st+2nd D3 outcomes.

    The key output is `q0''` (post-2nd-D3 correction), which is what
    `div128Quot_v4` computes. Other registers (x1, x6, x7, x11) hold
    transient end-of-block values that depend on the BLTU path taken;
    the postcondition encodes them via if-then-else on the relevant
    BLTU/BNE conditions. -/
@[irreducible]
def divKDiv128Step2V4Post (sp un21 dHi dlo un0 vScratchOld : Word) : Assertion :=
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dlo            -- product for 1st D3 check
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  -- Phase 2b 1st D3 result (if outer guard doesn't fire).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  -- Post-1st-D3 rhat2: equals rhat2c + dHi if 1st BLTU fired, else rhat2c.
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dlo            -- product for 2nd D3 check
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  -- Phase 2b 2nd D3 result.
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dlo un0
  -- Exit register state at [71]:
  -- x7: un21 (outer BNE) | q0c*dlo (2nd BNE) | q0'*dlo (2nd D3 ran).
  let x7Exit := if rhat2cHi ≠ 0 then un21
                else if rhat2'Hi ≠ 0 then q0Dlo1
                else q0Dlo2
  -- x1: rhat2cHi (outer BNE) | rhat2'Hi (2nd BNE) | rhat2'*2^32|un0 (2nd D3 ran).
  let x9Exit := if rhat2cHi ≠ 0 then rhat2cHi
                else if rhat2'Hi ≠ 0 then rhat2'Hi
                else rhat2'Un0
  -- x11: rhat2c (outer BNE) | rhat2' (2nd BNE) | un0 (2nd D3 ran).
  let x11Exit := if rhat2cHi ≠ 0 then rhat2c
                 else if rhat2'Hi ≠ 0 then rhat2'
                 else un0
  -- mem3936: vScratchOld if outer BNE fired (SD at [52] not reached),
  --          else rhat2c (saved at [52]).
  let mem3936Exit := if rhat2cHi ≠ 0 then vScratchOld else rhat2c
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
  (.x9 ↦ᵣ x9Exit) ** (.x11 ↦ᵣ x11Exit) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) **
  (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ mem3936Exit)

/-- Phase D sub-lemma: BLTU+paths [15..20] of step2_v4, merged post.
    Input = midC (= output of Phase C at base+60).
    Output = midD (post-BLTU merged state at base+84).
    by_cases on ult for taken/not-taken paths; by_cases on rhat2cHi for vacuity.
    Proof outline:
    - if rhat2cHi ≠ 0: pre (⌜rhat2cHi=0⌝) is False → vacuous.
    - if rhat2cHi = 0, ult = true (taken path [18..20]):
        strip ⌜ult⌝ from pre, run ADDI+LD+ADD via runBlock.
    - if rhat2cHi = 0, ult = false (not-taken path [16..17]):
        strip ⌜¬ult⌝ from pre, run LD+JAL via runBlock. -/
theorem divK_div128_step2_v4_phase_D_merged_spec
    (sp dHi q0c rhat2c dlo un0 : Word) (base : Word) :
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let q0Dlo1   := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0'      := div128Quot_phase2b_q0' q0c rhat2c dlo un0
    let rhat2'   := if rhat2cHi = 0 then
                      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
                    else rhat2c
    cpsTripleWithin 4 (base + 60) (base + 84) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
       (.x11 ↦ᵣ un0) ** (.x9 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  intro rhat2cHi q0Dlo1 rhat2Un0 q0' rhat2'
  have hbltu := divK_div128_step2_v4_phase_D_bltu_spec rhat2Un0 q0Dlo1 base
  -- Remaining proof split:
  -- * taken path: [18..20] ADDI; LD; ADD with `add_spec_gen_rd_eq_rs1_within`
  -- * fallthrough path: [16..17] LD; JAL
  -- Both paths then rewrite `div128Quot_phase2b_q0'` under the carried
  -- `rhat2cHi = 0` fact and strip the BLTU pure fact.
  have hbltu_f := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) **
     (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ rhat2c))
    (by pcFree) hbltu
  by_cases hz : rhat2cHi = 0
  · by_cases hcond : BitVec.ult rhat2Un0 q0Dlo1
    · have taken := cpsBranchWithin_takenPath hbltu_f (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, hpure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 hpure).2 hcond)
      have taken' : cpsTripleWithin 1 (base + 60) (base + 72) (divKDiv128Step2V4Code base)
          ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
           (.x11 ↦ᵣ un0) ** (.x9 ↦ᵣ rhat2Un0) **
           (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
           (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
           (sp + signExtend12 3936 ↦ₘ rhat2c))
          (phaseDTakenBranchPost sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0) :=
          cpsTripleWithin_weaken
            (fun h hp => by xperm_hyp hp)
          (fun h hp => by dsimp only [phaseDTakenBranchPost]; exact hp)
          taken
      have hq0' : q0' = q0c + signExtend12 4095 := by
        unfold q0'
        change (if rhat2cHi = 0 then
            if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
          else q0c) = q0c + signExtend12 4095
        rw [if_pos hz, if_pos hcond]
      have hrhat2' : rhat2' = rhat2c + dHi := by
        unfold rhat2'
        rw [if_pos hz, if_pos hcond]
      rw [hq0', hrhat2']
      have hpath := divK_div128_step2_v4_phase_D_taken_body_spec sp q0c rhat2c dHi un0 base
      have hpath_f := cpsTripleWithin_frameR
        ((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
        (by pcFree) hpath
      exact cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by xperm_hyp hp)
        (cpsTripleWithin_seq_perm_same_cr
          (fun h hp => divK_div128_step2_v4_phase_D_taken_body_pre
            sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 h hp)
          taken' hpath_f)
    · have ntaken := cpsBranchWithin_ntakenPath hbltu_f (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, hpure⟩, _⟩ := hQt
        exact absurd ((sepConj_pure_right _).1 hpure).2 hcond)
      have ntaken' : cpsTripleWithin 1 (base + 60) (base + 64) (divKDiv128Step2V4Code base)
          ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
           (.x11 ↦ᵣ un0) ** (.x9 ↦ᵣ rhat2Un0) **
           (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
           (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
           (sp + signExtend12 3936 ↦ₘ rhat2c))
          (phaseDFallthroughBranchPost sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0) :=
        cpsTripleWithin_weaken
          (fun h hp => by xperm_hyp hp)
          (fun h hp => by dsimp only [phaseDFallthroughBranchPost]; exact hp)
          ntaken
      have hq0' : q0' = q0c := by
        unfold q0'
        change (if rhat2cHi = 0 then
            if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
          else q0c) = q0c
        rw [if_pos hz, if_neg hcond]
      have hrhat2' : rhat2' = rhat2c := by
        unfold rhat2'
        rw [if_pos hz, if_neg hcond]
      rw [hq0', hrhat2']
      have hpath := divK_div128_step2_v4_phase_D_fallthrough_body_spec sp rhat2c un0 base
      have hpath_f := cpsTripleWithin_frameR
        ((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
         (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
        (by pcFree) hpath
      exact cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by xperm_hyp hp)
        (cpsTripleWithin_mono_nSteps (by decide) <|
          cpsTripleWithin_seq_perm_same_cr
            (fun h hp => divK_div128_step2_v4_phase_D_fallthrough_body_pre
              sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 h hp)
            ntaken' hpath_f)
  · intro F hF s hcr hPFR hpc
    obtain ⟨hp, hcompat, hsep⟩ := hPFR
    obtain ⟨hpreSt, hframeSt, hd, hu, hpre, hframe⟩ := hsep
    have hz' : rhat2cHi = 0 :=
      divK_div128_step2_v4_phase_D_pre_zero
        sp dHi q0c rhat2c dlo un0 rhat2cHi q0Dlo1 rhat2Un0 hpreSt hpre
    exact absurd hz' hz

/-- Phase E sub-lemma: 2nd D3 guard+prodcheck [21..30] of step2_v4, merged post.
    Input = midD (at base+84). Output = finalPost_rhat2cHi0 (at base+124).
    by_cases on rhat2'Hi for guard taken/not-taken.
    Proof outline:
    - if rhat2cHi ≠ 0: midD pre (⌜rhat2cHi=0⌝) is False → vacuous.
    - if rhat2cHi = 0 and rhat2'Hi ≠ 0 (guard fires): identity, q0''=q0'.
    - if rhat2cHi = 0 and rhat2'Hi = 0:
        prodcheck2_merged_spec at base+92, extended via step2v4_sub 23..30. -/
theorem divK_div128_step2_v4_phase_E_merged_spec
    (sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c : Word) (base : Word) :
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
    let q0Dlo2   := q0' * dlo
    let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
    let q0''     := div128Quot_phase2b_q0' q0' rhat2' dlo un0
    let x7Exit   := if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2
    let x9Exit   := if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0
    let x11Exit  := if rhat2'Hi ≠ 0 then rhat2' else un0
    cpsTripleWithin 10 (base + 84) (base + 124) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
        ((.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
         (.x9 ↦ᵣ x9Exit) ** (.x11 ↦ᵣ x11Exit) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
    intro rhat2cHi rhat2'Hi q0Dlo2 rhat2'Un0 q0'' x7Exit x9Exit x11Exit
    have hguard := divK_div128_step2_v4_phase_E_guard_spec
      sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c base
    have hguard' : cpsBranchWithin 2 (base + 84) (divKDiv128Step2V4Code base)
        ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
         (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2Un0) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ rhat2c))
        (base + 124)
        (phaseETakenBranchPost sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c)
        (base + 92)
        (phaseEFallthroughBranchPost sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c) :=
      cpsBranchWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by dsimp only [phaseETakenBranchPost]; xperm_hyp hp)
        (fun h hp => by dsimp only [phaseEFallthroughBranchPost]; xperm_hyp hp)
        hguard
    have refl_of {P Q : Assertion} (h : ∀ hp, P hp → Q hp) :
        cpsTripleWithin 0 (base + 124) (base + 124) (divKDiv128Step2V4Code base) P Q :=
      cpsTripleWithin_extend_code (fun _ _ h => by simp [CodeReq.empty] at h)
        (cpsTripleWithin_refl h)
    by_cases hhi : rhat2'Hi ≠ 0
    · have htaken := cpsBranchWithin_takenPath hguard' (fun hp hfall => by
        exact hhi (phaseE_fallthrough_post_zero
          sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c hp hfall))
      have hq0'' : q0'' = q0' := by
        unfold q0''
        change (if rhat2'Hi = 0 then
            if BitVec.ult rhat2'Un0 q0Dlo2 then q0' + signExtend12 4095 else q0'
          else q0') = q0'
        exact if_neg hhi
      have hx7 : x7Exit = q0Dlo1 := by
        unfold x7Exit
        exact if_pos hhi
      have hx1 : x9Exit = rhat2'Hi := by
        unfold x9Exit
        exact if_pos hhi
      have hx11 : x11Exit = rhat2' := by
        unfold x11Exit
        exact if_pos hhi
      have hzero : cpsTripleWithin 0 (base + 124) (base + 124) (divKDiv128Step2V4Code base)
          (phaseETakenBranchPost sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c)
          ((.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
           (.x9 ↦ᵣ x9Exit) ** (.x11 ↦ᵣ x11Exit) **
           (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
           (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
           (sp + signExtend12 3936 ↦ₘ rhat2c)) := refl_of (by
        intro h hp
        dsimp only [phaseETakenBranchPost] at hp
        rw [hq0'', hx7, hx1, hx11]
        have hp' :
            ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
             (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
             (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
             (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
             (sp + signExtend12 3936 ↦ₘ rhat2c)) h := by
          have hp0 :
              (((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
                (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2'Hi) **
                (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
                (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
                (sp + signExtend12 3936 ↦ₘ rhat2c)) ** ⌜rhat2'Hi ≠ 0⌝) h := by
            xperm_hyp hp
          exact ((sepConj_pure_right h).1 hp0).1
        xperm_hyp hp')
      exact cpsTripleWithin_mono_nSteps (by decide) <|
        cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) htaken hzero
    · have hzhi : rhat2'Hi = 0 := Decidable.not_not.mp hhi
      have hfall := cpsBranchWithin_ntakenPath hguard' (fun hp htaken => by
        exact hhi (phaseE_taken_post_ne
          sp dHi q0' rhat2' rhat2cHi rhat2'Hi q0Dlo1 dlo un0 rhat2c hp htaken))
      have hbody := divK_div128_step2_v4_phase_E_fallthrough_body_spec
        sp dHi q0' rhat2' rhat2'Hi q0Dlo1 dlo un0 rhat2c base
      have hq0'' : q0'' =
          (if BitVec.ult rhat2'Un0 q0Dlo2 then q0' + signExtend12 4095 else q0') := by
        unfold q0''
        change (if rhat2'Hi = 0 then
            if BitVec.ult rhat2'Un0 q0Dlo2 then q0' + signExtend12 4095 else q0'
          else q0') =
          (if BitVec.ult rhat2'Un0 q0Dlo2 then q0' + signExtend12 4095 else q0')
        exact if_pos hzhi
      have hx7 : x7Exit = q0Dlo2 := by
        unfold x7Exit
        exact if_neg hhi
      have hx1 : x9Exit = rhat2'Un0 := by
        unfold x9Exit
        exact if_neg hhi
      have hx11 : x11Exit = un0 := by
        unfold x11Exit
        exact if_neg hhi
      exact cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by
          rw [hq0'', hx7, hx1, hx11]
          have hp0 :
              (((.x5 ↦ᵣ (if BitVec.ult rhat2'Un0 q0Dlo2 then q0' + signExtend12 4095 else q0')) **
                (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ q0Dlo2) **
                (.x9 ↦ᵣ rhat2'Un0) ** (.x11 ↦ᵣ un0) **
                (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
                (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
                (sp + signExtend12 3936 ↦ₘ rhat2c)) ** ⌜rhat2'Hi = 0⌝) h := by
            xperm_hyp hp
          exact ((sepConj_pure_right h).1 hp0).1)
        (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          dsimp only [phaseEFallthroughBranchPost] at hp
          xperm_hyp hp) hfall hbody)

/-- Full v4 Phase 2 spec — instructions [40..70] of `divK_div128_v4`.

    Proof structure (5 blocks in `divK_div128_step2_v4_spec`):
    - Block 1 [0..28]  (hA): init+clamp  → `cpsTripleWithin base (base+28)`.
    - Block 2 [28..36] (hB): outer SRLI+BNE guard → `cpsBranchWithin (base+28)`.
    - Compose hA+hB → `cpsBranchWithin base (base+124) | (base+36)`.
    - Taken (rhat2cHi≠0): `h_taken` identity at base+124.
    - Not-taken (rhat2cHi=0): `h_notTaken` = Block3(hC) + Block4(hD) + Block5(hE).
      Block 3 [36..60] (hC): pre-BLTU setup via runBlock.
      Block 4 [60..84] (hD): BLTU+paths via `phase_D_merged_spec`.
      Block 5 [84..124](hE): 2nd D3 guard+prodcheck via `phase_E_merged_spec`. -/
theorem divK_div128_step2_v4_spec
    (sp un21 dHi v9Old v5Old v11Old dlo un0 vScratchOld : Word) (base : Word) :
    cpsTripleWithin 29 base (base + 124) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) **
       (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratchOld))
      (divKDiv128Step2V4Post sp un21 dHi dlo un0 vScratchOld) := by
  unfold divKDiv128Step2V4Post
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dlo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dlo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dlo un0
  let x7Exit := if rhat2cHi ≠ 0 then un21
                else if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2
  let x9Exit := if rhat2cHi ≠ 0 then rhat2cHi
                else if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0
  let x11Exit := if rhat2cHi ≠ 0 then rhat2c
                 else if rhat2'Hi ≠ 0 then rhat2' else un0
  let mem3936Exit := if rhat2cHi ≠ 0 then vScratchOld else rhat2c
  -- Phase A: init+clamp [0..28] — cpsTripleWithin base (base+28).
  -- Reuse divK_div128_step2_upto_guard_spec_within, extend via step2v4_sub 0..6.
  have hA_raw := divK_div128_step2_upto_guard_spec_within sp un21 dHi v9Old v5Old v11Old dlo un0 base
  have hA : cpsTripleWithin 7 base (base + 28) (divKDiv128Step2V4Code base) _ _ :=
    cpsTripleWithin_extend_code (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 0 base (.DIVU .x5 .x7 .x6) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 1 (base+4) (.MUL .x9 .x5 .x6) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 2 (base+8) (.SUB .x11 .x7 .x9) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 3 (base+12) (.SRLI .x9 .x5 32) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 4 (base+16) (.BEQ .x9 .x0 12) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 5 (base+20) (.ADDI .x5 .x5 4095) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 6 (base+24) (.ADD .x11 .x11 .x6) (by omega) (by bv_omega) (by decide))))))))
    hA_raw
  have hAf := cpsTripleWithin_frameR
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
    (by pcFree) hA
  -- Phase B: outer SRLI+BNE guard [28..36] — cpsBranchWithin via step2v4_sub 7+8.
  have hB_raw := divK_div128_phase2b_guard_spec_within sp rhat2c hi (base + 28) (92 : BitVec 13)
  simp only [show (base + 28 : Word) + 4 = base + 32 from by bv_addr,
             show (base + 28 : Word) + 8 = base + 36 from by bv_addr,
             show (base + 32 : Word) + signExtend13 (92 : BitVec 13) = base + 124 from by
               rv64_addr] at hB_raw
  have hB : cpsBranchWithin 2 (base + 28) (divKDiv128Step2V4Code base) _ _ _ _ _ :=
    cpsBranchWithin_extend_code (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 7 (base+28) (.SRLI .x9 .x11 32) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 8 (base+32) (.BNE .x9 .x0 92) (by omega) (by bv_omega) (by decide))) hB_raw
  have hBf := cpsBranchWithin_frameR
    ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ vScratchOld))
    (by pcFree) hB
  have composed_AB := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  -- finalPost (merged post at base+124 for both legs).
  let finalPost : Assertion :=
    (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
    (.x9 ↦ᵣ x9Exit) ** (.x11 ↦ᵣ x11Exit) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ mem3936Exit)
  -- Taken leg (rhat2cHi ≠ 0): BNE fires, already at base+124.
  -- q0'' = q0c (both D3 guards fire), x7=un21, x1=rhat2cHi, x11=rhat2c, mem3936=vScratchOld.
  -- The taken postcondition of composed_AB:
  let takenPost : Assertion :=
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x9 ↦ᵣ rhat2cHi) **
     (.x0 ↦ᵣ 0) ** ⌜rhat2cHi ≠ 0⌝) **
    (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
  have h_taken : cpsTripleWithin 20 (base + 124) (base + 124) (divKDiv128Step2V4Code base)
      takenPost finalPost :=
    cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_extend_code (hmono := fun _ _ h => by simp [CodeReq.empty] at h)
    (cpsTripleWithin_refl (by
      intro hp htp
      -- Extract ⌜rhat2cHi ≠ 0⌝ from takenPost (inside a have so htp survives).
      -- takenPost = (.x12 ** .x11 ** .x9 ** .x0 ** ⌜rhat2cHi ≠ 0⌝) ** rest.
      have h_ne : rhat2cHi ≠ 0 := by
        obtain ⟨_, _, _, _, hleft, _⟩ := htp
        obtain ⟨_, _, _, _, _, h1⟩ := hleft  -- peel .x12
        obtain ⟨_, _, _, _, _, h2⟩ := h1     -- peel .x11
        obtain ⟨_, _, _, _, _, h3⟩ := h2     -- peel .x9
        obtain ⟨_, _, _, _, _, h4⟩ := h3     -- peel .x0
        obtain ⟨_, hpure⟩ := h4             -- ⌜rhat2cHi ≠ 0⌝
        exact hpure
      -- When rhat2cHi ≠ 0: both D3 guards skip → q0'' = q0c.
      have hq0' : q0' = q0c := by
        show div128Quot_phase2b_q0' q0c rhat2c dlo un0 = q0c
        simp only [div128Quot_phase2b_q0']; exact if_neg h_ne
      have hrhat2' : rhat2' = rhat2c := by
        show (if rhat2cHi = 0 then _ else rhat2c) = rhat2c
        exact if_neg h_ne
      have hq0'' : q0'' = q0c := by
        show div128Quot_phase2b_q0' q0' rhat2' dlo un0 = q0c
        rw [hq0', hrhat2']
        simp only [div128Quot_phase2b_q0']; exact if_neg h_ne
      have hx7 : x7Exit = un21   := by show (if rhat2cHi ≠ 0 then un21 else _) = un21; exact if_pos h_ne
      have hx1 : x9Exit = rhat2cHi := by show (if rhat2cHi ≠ 0 then rhat2cHi else _) = rhat2cHi; exact if_pos h_ne
      have hx11 : x11Exit = rhat2c  := by show (if rhat2cHi ≠ 0 then rhat2c else _) = rhat2c; exact if_pos h_ne
      have hmem : mem3936Exit = vScratchOld := by show (if rhat2cHi ≠ 0 then vScratchOld else _) = vScratchOld; exact if_pos h_ne
      -- Strip ⌜rhat2cHi ≠ 0⌝ from htp for xperm_hyp.
      -- takenPost = (.x12 ** .x11 ** .x9 ** .x0 ** ⌜...⌝) ** rest.
      -- Strip: 3x sepConj_mono_right to reach .x0 ** ⌜...⌝, then strip.
      have htp' : (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x9 ↦ᵣ rhat2cHi) ** (.x0 ↦ᵣ 0)) **
          (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ vScratchOld)) hp :=
        sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (fun h'' hp'' => ((sepConj_pure_right h'').1 hp'').1)))) hp htp
      -- Rewrite finalPost to explicit form, then xperm_hyp htp'.
      show finalPost hp
      rw [show finalPost = ((.x5 ↦ᵣ q0c) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ un21) **
          (.x9 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
          (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
          (sp + signExtend12 3952 ↦ₘ dlo) **
          (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ vScratchOld)) from by
        simp only [finalPost, hq0'', hx7, hx1, hx11, hmem]]
      xperm_hyp htp'))
  -- The not-taken postcondition of composed_AB:
  let notTakenPost : Assertion :=
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x9 ↦ᵣ rhat2cHi) **
     (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝) **
    (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
  -- Not-taken leg (rhat2cHi = 0): run [36..120] → base+124.
  have h_notTaken : cpsTripleWithin 20 (base + 36) (base + 124) (divKDiv128Step2V4Code base)
      notTakenPost finalPost := by
    -- Phase C: pre-BLTU setup [9..14] = LD+MUL+SLLI+SD+LD+OR.
    let midC : Assertion :=
      (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
      (.x11 ↦ᵣ un0) ** (.x9 ↦ᵣ rhat2Un0) **
      (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
      (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
      (sp + signExtend12 3936 ↦ₘ rhat2c)
    have hC : cpsTripleWithin 6 (base+36) (base+60) (divKDiv128Step2V4Code base)
        notTakenPost midC := by
      apply cpsTripleWithin_extend_code (hmono := by
        exact CodeReq.union_sub (step2v4_sub 9 (base+36) (.LD .x9 .x12 3952) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 10 (base+40) (.MUL .x7 .x5 .x9) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 11 (base+44) (.SLLI .x9 .x11 32) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 12 (base+48) (.SD .x12 .x11 3936) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 13 (base+52) (.LD .x11 .x12 3944) (by omega) (by bv_omega) (by decide))
          (step2v4_sub 14 (base+56) (.OR .x9 .x9 .x11) (by omega) (by bv_omega) (by decide)))))))
      have I0 := ld_spec_gen_within .x9 .x12 sp rhat2cHi dlo 3952 (base+36) (by nofun)
      have I1 := mul_spec_gen_within .x7 .x5 .x9 un21 q0c dlo (base+40) (by nofun)
      have I2 := slli_spec_gen_within .x9 .x11 dlo rhat2c 32 (base+44) (by nofun)
      have I3 := sd_spec_gen_within .x12 .x11 sp rhat2c vScratchOld 3936 (base+48)
      have I4 := ld_spec_gen_within .x11 .x12 sp rhat2c un0 3944 (base+52) (by nofun)
      have I5 := or_spec_gen_rd_eq_rs1_within .x9 .x11
            (rhat2c <<< (32 : BitVec 6).toNat) un0 (base+56) (by nofun)
      simp only [show (base+36:Word)+4 = base+40 from by bv_omega,
                 show (base+40:Word)+4 = base+44 from by bv_omega,
                 show (base+44:Word)+4 = base+48 from by bv_omega,
                 show (base+48:Word)+4 = base+52 from by bv_omega,
                 show (base+52:Word)+4 = base+56 from by bv_omega,
                 show (base+56:Word)+4 = base+60 from by bv_omega] at *
      runBlock I0 I1 I2 I3 I4 I5
    -- Phase D: BLTU+paths [15..20] via `divK_div128_step2_v4_phase_D_merged_spec`.
    let midD : Assertion :=
      (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
      (.x11 ↦ᵣ rhat2') ** (.x9 ↦ᵣ rhat2Un0) **
      (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
      (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
      (sp + signExtend12 3936 ↦ₘ rhat2c)
    have hD_raw := divK_div128_step2_v4_phase_D_merged_spec sp dHi q0c rhat2c dlo un0 base
    have hD : cpsTripleWithin 10 (base+36) (base+84) (divKDiv128Step2V4Code base) notTakenPost midD :=
      cpsTripleWithin_seq_perm_same_cr (fun h hp => by exact hp) hC hD_raw
    -- Phase E: 2nd D3 guard+prodcheck [21..30] via `divK_div128_step2_v4_phase_E_merged_spec`.
    -- Bridge hE_raw post → finalPost: by_cases on rhat2cHi (midD has ⌜rhat2cHi=0⌝
    -- so ≠0 is vacuous); then reduce outer if-then-else by h_z + xperm.
    have hE : cpsTripleWithin 10 (base+84) (base+124) (divKDiv128Step2V4Code base)
        midD finalPost := by
      have hE_raw := divK_div128_step2_v4_phase_E_merged_spec
                       sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c base
      exact cpsTripleWithin_weaken
          (fun h hp => by xperm_hyp hp)
        (fun h hp => by
            have hz : rhat2cHi = 0 := by
              have hp0 :
                  ((.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) **
                   (.x7 ↦ᵣ (if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2)) **
                   (.x9 ↦ᵣ (if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0)) **
                   (.x11 ↦ᵣ (if rhat2'Hi ≠ 0 then rhat2' else un0)) **
                   (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
                   (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
                   (sp + signExtend12 3936 ↦ₘ rhat2c)) h := by
                xperm_hyp hp
              obtain ⟨_, _, _, _, _, h1⟩ := hp0
              obtain ⟨_, _, _, _, _, h2⟩ := h1
              obtain ⟨_, _, _, _, _, h3⟩ := h2
              obtain ⟨_, _, _, _, _, h4⟩ := h3
              obtain ⟨_, _, _, _, _, h5⟩ := h4
              obtain ⟨_, _, _, _, _, h6⟩ := h5
              obtain ⟨_, _, _, _, _, h7⟩ := h6
              exact ((sepConj_pure_left _).1 h7).1
            have hne : ¬ rhat2cHi ≠ 0 := fun hne => hne hz
            have hx7 : x7Exit = (if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2) := by
              unfold x7Exit
              exact if_neg hne
            have hx1 : x9Exit = (if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0) := by
              unfold x9Exit
              exact if_neg hne
            have hx11 : x11Exit = (if rhat2'Hi ≠ 0 then rhat2' else un0) := by
              unfold x11Exit
              exact if_neg hne
            have hmem : mem3936Exit = rhat2c := by
              unfold mem3936Exit
              exact if_neg hne
            let noPure : Assertion :=
              (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) **
              (.x7 ↦ᵣ (if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2)) **
              (.x9 ↦ᵣ (if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0)) **
              (.x11 ↦ᵣ (if rhat2'Hi ≠ 0 then rhat2' else un0)) **
              (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
              (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
              (sp + signExtend12 3936 ↦ₘ rhat2c)
            show finalPost h
            rw [show finalPost = noPure from by
              dsimp only [noPure]
              simp only [finalPost, hx7, hx1, hx11, hmem]]
            have hp0 : (noPure ** ⌜rhat2cHi = 0⌝) h := by
              dsimp only [noPure]
              xperm_hyp hp
            exact ((sepConj_pure_right h).1 hp0).1)
          hE_raw
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hD hE)
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsBranchWithin_merge_same_cr composed_AB h_taken h_notTaken)

end EvmAsm.Evm64
