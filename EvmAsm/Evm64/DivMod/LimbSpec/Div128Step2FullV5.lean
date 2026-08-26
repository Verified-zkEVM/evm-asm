/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2FullV5

  Full v5 div128 Phase-2 block spec: instrs [46]-[80], exit at [81]
  (base+140). Composes the prefix+Phase-2b-leading-guard
  (`divK_div128_step2_initcapguard_v5_spec_within`, [46..58]) with the
  Phase-2b body (`divK_div128_phase2b_body_v5_spec_within`, [59..80]).

  Control flow (nested branch):
    * Outer guard (rhat2c ≥ 2^32, i.e. rhat2c>>32 ≠ 0): skip both D3
      corrections, exit [81] with q0''=q0c, rhat2'=rhat2c.
    * Otherwise (rhat2c>>32 = 0): run the body — 1st D3 (spill) then
      2nd D3 (prodcheck2b, guarded) — exit [81] with the corrected q0.

  Mirror of `divK_div128_step1_v5_spec_within` (Div128Step1FullV5.lean).
  Bead `evm-asm-wbc4i.6.12` (V5.6.13).
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2V5
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase2bV5
public import EvmAsm.Rv64.Tactics.XPermPure

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Phase-2b body code [59..80] (1st-D3 spill ∪ 2nd-D3 prodcheck2b),
    matching the inline CR of `divK_div128_phase2b_body_v5_spec_within`. -/
def divKDiv128Phase2bBodyV5Code (base : Word) : CodeReq :=
  (CodeReq.union (CodeReq.singleton base (.LD .x9 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x9))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x9 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x11 3936))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x11 .x12 3944))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x9 .x9 .x11))
  (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x9 .x7 12))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x11 .x12 3936))
  (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 16))
  (CodeReq.union (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))
  (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3936))
   (CodeReq.singleton (base + 44) (.ADD .x11 .x11 .x6))))))))))))).union
  (divKDiv128Prodcheck2bV5MergedCode (base + 48))

/-- Code requirement for the full v5 step-2 block [46..80]. -/
def divKDiv128Step2FullV5Code (base : Word) : CodeReq :=
  (divKDiv128Step2InitCapGuardV5Code base).union
  (divKDiv128Phase2bBodyV5Code (base + 52))

/-- Precondition for the full v5 step-2 block: the prefix entry state plus the
    spilled-scratch / un0 / dlo memory cells (threaded for the body). -/
def divKDiv128Step2FullV5Pre
    (sp un21 dHi un0 dlo v5Old v9Old v11Old vScratchOld : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
  (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ vScratchOld)

/-- Small final register/mem spine for the full v5 step-2 post. Folded behind
    an irreducible def so `xperm` does not re-expand the nested arithmetic. -/
@[irreducible]
def divKDiv128Step2FullV5PostCore
    (sp dHi un0 dlo q0Final x7Exit x9Exit x11Exit mem3936Exit : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0Final) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
  (.x9 ↦ᵣ x9Exit) ** (.x11 ↦ᵣ x11Exit) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ mem3936Exit)

/-- Folded body-level form of the full v5 step-2 post: computes the 2nd-D3
    intermediates + 3-path conditionals and delegates to the core spine. -/
def divKDiv128Step2FullV5PostFromBody
    (sp dHi un0 dlo vScratchOld q0c rhat2c x7o rhat2cHi qDlo1 q0' rhat2' : Word) :
    Assertion :=
  let brhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let qDlo2 := q0' * dlo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := if BitVec.ult rhat2'Un0 qDlo2 then q0' + signExtend12 4095 else q0'
  let q0Final := if rhat2cHi ≠ 0 then q0c else (if brhat2'Hi = 0 then q0'' else q0')
  let x7Exit := if rhat2cHi ≠ 0 then x7o else (if brhat2'Hi = 0 then qDlo2 else qDlo1)
  let x9Exit := if rhat2cHi ≠ 0 then rhat2cHi else (if brhat2'Hi = 0 then rhat2'Un0 else brhat2'Hi)
  let x11Exit := if rhat2cHi ≠ 0 then rhat2c else (if brhat2'Hi = 0 then un0 else rhat2')
  let mem3936Exit := if rhat2cHi ≠ 0 then vScratchOld else rhat2c
  divKDiv128Step2FullV5PostCore sp dHi un0 dlo q0Final x7Exit x9Exit x11Exit mem3936Exit

/-- Postcondition: the v5 Phase-2 register state at [81] (base+140).
    `q0''` in x5; `x7`/`x9`/`x11`/`mem3936` are 3-path scratch. -/
def divKDiv128Step2FullV5Post (sp un21 dHi un0 dlo vScratchOld : Word) : Assertion :=
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0cCap
  let rhat2c := if hi = 0 then rhat2 else rhat2 + (q0 - q0cCap) * dHi
  let x7o := if hi = 0 then un21 else (q0 - q0cCap) * dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let qDlo1 := q0c * dlo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let bq0' := if BitVec.ult rhat2Un0 qDlo1 then q0c + signExtend12 4095 else q0c
  let brhat2' := if BitVec.ult rhat2Un0 qDlo1 then rhat2c + dHi else rhat2c
  divKDiv128Step2FullV5PostFromBody sp dHi un0 dlo vScratchOld q0c rhat2c x7o rhat2cHi qDlo1 bq0' brhat2'

/-- Disjointness of the prefix+guard code [46..58] and the Phase-2b body code
    [59..80] (at base+52). Top-level (fresh heartbeat budget), peeled to
    singleton leaves. -/
theorem divKDiv128Step2FullV5_code_disjoint (base : Word) :
    (divKDiv128Step2InitCapGuardV5Code base).Disjoint
      (divKDiv128Phase2bBodyV5Code (base + 52)) := by
  unfold divKDiv128Step2InitCapGuardV5Code divKDiv128Step2InitCapV5Code
    divKDiv128Phase2bBodyV5Code divKDiv128Prodcheck2bV5MergedCode
  repeat' apply CodeReq.Disjoint.union_left
  all_goals (repeat' apply CodeReq.Disjoint.union_right)
  all_goals exact CodeReq.Disjoint.singleton (by bv_omega)

/-- Bridge for the body-TAKEN exit (outer guard fell through, 2nd-D3 guard
    fired): the prodcheck2b taken-post collapses to the full step-2 post. -/
theorem divKDiv128Step2FullV5_ht2_bridge (sp un21 dHi un0 dlo vScratchOld : Word) :
    let q0 := rv64_divu un21 dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0cCap
    let rhat2c := if hi = 0 then (un21 - q0 * dHi) else (un21 - q0 * dHi) + (q0 - q0cCap) * dHi
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let qDlo1 := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2Un0 qDlo1 then q0c + signExtend12 4095 else q0c
    let rhat2' := if BitVec.ult rhat2Un0 qDlo1 then rhat2c + dHi else rhat2c
    ∀ hp, ((divKDiv128Prodcheck2bV5MergedTakenPost sp q0' rhat2' qDlo1 dlo un0 **
              ((.x6 ↦ᵣ dHi) ** (sp + signExtend12 3936 ↦ₘ rhat2c))) ** ⌜rhat2cHi = 0⌝) hp →
          divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld hp := by
  intro q0 hi q0cCap q0c rhat2c rhat2cHi qDlo1 rhat2Un0 q0' rhat2' h hp
  show divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld h
  unfold divKDiv128Step2FullV5Post
  change divKDiv128Step2FullV5PostFromBody sp dHi un0 dlo vScratchOld q0c rhat2c
    (if hi = 0 then un21 else (q0 - q0cCap) * dHi) rhat2cHi qDlo1 q0' rhat2' h
  unfold divKDiv128Step2FullV5PostFromBody
  unfold divKDiv128Prodcheck2bV5MergedTakenPost at hp
  have hpc := hp
  obtain ⟨_, _, _, _, hX, ⟨_, h_eq⟩⟩ := hpc
  obtain ⟨_, _, _, _, hT, _⟩ := hX
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, ⟨_, h_inner⟩, _⟩ := hT
  simp only [if_neg (not_not_intro h_eq), if_neg h_inner]
  delta divKDiv128Step2FullV5PostCore
  extract_pure hp
  obtain ⟨hp, _⟩ := hp
  rw [show (⌜rhat2' >>> (32 : BitVec 6).toNat ≠ 0⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p; exact h_p.1
    · intro h_empty; exact ⟨h_empty, h_inner⟩] at hp
  simp only [sepConj_emp_right'] at hp
  xperm_hyp hp

/-- Bridge for the body-FALL-THROUGH exit (outer guard fell through, 2nd-D3
    guard fell through): the prodcheck2b ft-post collapses to the full post. -/
theorem divKDiv128Step2FullV5_hf_bridge (sp un21 dHi un0 dlo vScratchOld : Word) :
    let q0 := rv64_divu un21 dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0cCap
    let rhat2c := if hi = 0 then (un21 - q0 * dHi) else (un21 - q0 * dHi) + (q0 - q0cCap) * dHi
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let qDlo1 := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2Un0 qDlo1 then q0c + signExtend12 4095 else q0c
    let rhat2' := if BitVec.ult rhat2Un0 qDlo1 then rhat2c + dHi else rhat2c
    ∀ hp, ((divKDiv128Prodcheck2bV5MergedFTPost sp q0' rhat2' dlo un0 **
              ((.x6 ↦ᵣ dHi) ** (sp + signExtend12 3936 ↦ₘ rhat2c))) ** ⌜rhat2cHi = 0⌝) hp →
          divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld hp := by
  intro q0 hi q0cCap q0c rhat2c rhat2cHi qDlo1 rhat2Un0 q0' rhat2' h hp
  show divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld h
  unfold divKDiv128Step2FullV5Post
  change divKDiv128Step2FullV5PostFromBody sp dHi un0 dlo vScratchOld q0c rhat2c
    (if hi = 0 then un21 else (q0 - q0cCap) * dHi) rhat2cHi qDlo1 q0' rhat2' h
  unfold divKDiv128Step2FullV5PostFromBody
  unfold divKDiv128Prodcheck2bV5MergedFTPost at hp
  have hpc := hp
  obtain ⟨_, _, _, _, hX, ⟨_, h_eq⟩⟩ := hpc
  obtain ⟨_, _, _, _, hT, _⟩ := hX
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, _, hT⟩ := hT
  obtain ⟨_, _, _, _, ⟨_, h_inner⟩, _⟩ := hT
  simp only [if_neg (not_not_intro h_eq), if_pos h_inner]
  delta divKDiv128Step2FullV5PostCore
  extract_pure hp
  obtain ⟨hp, _⟩ := hp
  rw [show (⌜rhat2' >>> (32 : BitVec 6).toNat = 0⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p; exact h_p.1
    · intro h_empty; exact ⟨h_empty, h_inner⟩] at hp
  simp only [sepConj_emp_right'] at hp
  xperm_hyp hp

/-- Full v5 div128 Phase-2 block (instrs [46]-[80], exit [81]=base+140):
    init + Phase-2a cap + Phase-2b leading guard + both D3 corrections. -/
theorem divK_div128_step2_v5_spec_within
    (sp un21 dHi un0 dlo v5Old v9Old v11Old vScratchOld : Word) (base : Word) :
    cpsTripleWithin 33 base (base + 140) (divKDiv128Step2FullV5Code base)
      (divKDiv128Step2FullV5Pre sp un21 dHi un0 dlo v5Old v9Old v11Old vScratchOld)
      (divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld) := by
  let q0 := rv64_divu un21 dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0cCap
  let rhat2c := if hi = 0 then (un21 - q0 * dHi) else (un21 - q0 * dHi) + (q0 - q0cCap) * dHi
  let x7o := if hi = 0 then un21 else (q0 - q0cCap) * dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let cr := (divKDiv128Step2InitCapGuardV5Code base).union
            (divKDiv128Phase2bBodyV5Code (base + 52))
  show cpsTripleWithin 33 base (base + 140) cr
    (divKDiv128Step2FullV5Pre sp un21 dHi un0 dlo v5Old v9Old v11Old vScratchOld)
    (divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld)
  have refl_of {P : Assertion}
      (h : ∀ hp, P hp → divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld hp) :
      cpsTripleWithin 0 (base + 140) (base + 140) cr P
        (divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld) :=
    cpsTripleWithin_extend_code (fun _ _ h => by simp [CodeReq.empty] at h)
      (cpsTripleWithin_refl h)
  -- h1: prefix + Phase-2b guard [46..58], framed with the dlo/un0/scratch mem.
  have hg0 := divK_div128_step2_initcapguard_v5_spec_within sp un21 dHi v5Old v9Old v11Old base
  have h1 := cpsBranchWithin_frameR
    ((sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ vScratchOld)) (by pcFree) hg0
  -- h2: Phase-2b body [59..80] at base+52, framed with the outer-guard pure.
  have hb0 := divK_div128_phase2b_body_v5_spec_within
    sp q0c rhat2c dHi x7o rhat2cHi dlo un0 vScratchOld (base + 52)
  have hbe : (base + 52 : Word) + 88 = base + 140 := by bv_addr
  rw [hbe] at hb0
  have h2 := cpsBranchWithin_frameR (⌜rhat2cHi = 0⌝) (by pcFree) hb0
  have hd := divKDiv128Step2FullV5_code_disjoint base
  have combined := cpsBranchWithin_seq_cpsBranchWithin_with_perm
    (Q_t := divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld)
    hd
    h1
    (fun h hp => by xperm_hyp hp)
    h2
    -- ht1: guard-taken post → Post (outer if_pos via ⌜rhat2cHi≠0⌝)
    (fun h hp => by
      show divKDiv128Step2FullV5Post sp un21 dHi un0 dlo vScratchOld h
      unfold divKDiv128Step2FullV5Post
      change divKDiv128Step2FullV5PostFromBody sp dHi un0 dlo vScratchOld q0c rhat2c x7o rhat2cHi
        (q0c * dlo)
        (if ((rhat2c <<< (32 : BitVec 6).toNat) ||| un0).ult (q0c * dlo) = true then q0c + signExtend12 4095 else q0c)
        (if ((rhat2c <<< (32 : BitVec 6).toNat) ||| un0).ult (q0c * dlo) = true then rhat2c + dHi else rhat2c) h
      unfold divKDiv128Step2FullV5PostFromBody
      have hpc := hp
      obtain ⟨_, _, _, _, hL, _⟩ := hpc
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, ⟨_, hpure⟩, _⟩ := hL
      change rhat2cHi ≠ 0 at hpure
      simp only [if_pos hpure]
      delta divKDiv128Step2FullV5PostCore
      rw [show (⌜rhat2cHi ≠ 0⌝ : Assertion) = empAssertion by
        funext h
        unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
        apply propext
        constructor
        · intro h_p; exact h_p.1
        · intro h_empty; exact ⟨h_empty, hpure⟩] at hp
      simp only [sepConj_emp_left'] at hp
      xperm_hyp hp)
    (divKDiv128Step2FullV5_ht2_bridge sp un21 dHi un0 dlo vScratchOld)
  have merged := cpsBranchWithin_merge_same_cr combined (refl_of (fun hp h => h))
    (refl_of (divKDiv128Step2FullV5_hf_bridge sp un21 dHi un0 dlo vScratchOld))
  exact cpsTripleWithin_weaken
    (fun h hp => by unfold divKDiv128Step2FullV5Pre at hp; xperm_hyp hp)
    (fun h hp => hp) merged

end EvmAsm.Evm64
