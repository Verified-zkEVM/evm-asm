/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1FullV5

  Full v5 div128 Phase-1 block spec: instrs [10]-[40], exit at [41]
  (base+124). Composes the prefix+Phase-1b-leading-guard
  (`divK_div128_step1_initcapguard_v5_spec_within`, [10..22]) with the
  Phase-1b body (`divK_div128_phase1b_body_v5_spec_within`, [23..40]).

  Control flow (nested branch):
    * Outer guard (rhatc ≥ 2^32, i.e. rhatc>>32 ≠ 0): skip both D3
      corrections, exit [41] with q1''=q1c, rhat''=rhatc.
    * Otherwise (rhatc>>32 = 0): run the body — 1st D3 (prodcheck1) then
      2nd D3 (prodcheck1b, guarded) — exit [41] with the corrected q/rhat.

  Composition: `cpsBranchWithin_seq_cpsBranchWithin_with_perm` advances
  BOTH combined exits to base+124, then `cpsBranchWithin_merge_same_cr`
  collapses to a `cpsTripleWithin` with the unified Phase-1 postcondition.
  The outer-guard pure `⌜rhatc>>32 = 0⌝` is FRAMED onto the body so the
  merge bridges can resolve the outer conditional.

  Output `q1''`/`rhat''` agree with `div128Quot_v5`'s Phase-1 result (the
  model-form match — model uses `decide(rhatc>>32=0) && …` — is deferred
  to the `div128_v5_spec` composition).

  Bead `evm-asm-wbc4i.6.6` (V5.6.7).
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1V5
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase1bV5
public import EvmAsm.Rv64.Tactics.XPermPure

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Code requirement for the full v5 step-1 block [10..40]: the
    init+cap+Phase-1b-guard code unioned with the Phase-1b body code. -/
def divKDiv128Step1FullV5Code (base : Word) : CodeReq :=
  (divKDiv128Step1InitCapGuardV5Code base).union
  (divKDiv128Phase1bBodyV5Code (base + 52))

/-- Precondition for the full v5 step-1 block: the init+cap+guard entry
    state plus `un1` in x11 and `dlo` in memory (threaded for the body). -/
def divKDiv128Step1FullV5Pre (sp uHi dHi un1 v10Old v5Old v9Old dlo : Word) :
    Assertion :=
  (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ v10Old) **
  (.x5 ↦ᵣ v5Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) ** (.x11 ↦ᵣ un1) **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- Small final register assertion for the full v5 step-1 post.  Keeping the
    register spine behind an irreducible def prevents `xperm` from comparing
    the full nested arithmetic let-chain while the bridge proofs select a
    branch of `divKDiv128Step1FullV5Post`. -/
@[irreducible]
def divKDiv128Step1FullV5PostCore
    (sp dHi un1 dlo q1Final rhatFinal x5Exit x9Exit : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhatFinal) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1Final) **
  (.x5 ↦ᵣ x5Exit) ** (.x11 ↦ᵣ un1) ** (.x9 ↦ᵣ x9Exit) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- Folded body-level form of the full v5 step-1 post.  The main post computes
    the init/cap/first-D3 intermediates and delegates here; bridge proofs can
    fold the expanded goal back to these parameters before selecting branches. -/
def divKDiv128Step1FullV5PostFromBody
    (sp dHi un1 dlo q1c rhatc x5o rhatcHi qDlo1 q1' rhat' : Word) : Assertion :=
  let brhat'Hi := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dlo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1'
  let rhat'' := if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
  let q1Final := if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else q1')
  let rhatFinal := if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else rhat')
  let x5Exit := if rhatcHi ≠ 0 then x5o else (if brhat'Hi = 0 then qDlo2 else qDlo1)
  let x9Exit := if rhatcHi ≠ 0 then rhatcHi else (if brhat'Hi = 0 then rhatUn1' else brhat'Hi)
  divKDiv128Step1FullV5PostCore sp dHi un1 dlo q1Final rhatFinal x5Exit x9Exit

/-- Postcondition: the v5 Phase-1 register state at [41] (base+124).
    `q1''` in x10, `rhat''` in x7 — the corrected trial quotient/remainder.
    Expressed as the outer `rhatc>>32` guard over the body's two-D3 output;
    `x5`/`x9` are scratch (3-path conditional). -/
def divKDiv128Step1FullV5Post (sp uHi dHi un1 dlo : Word) : Assertion :=
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1c := if hi = 0 then q1 else q1cCap
  let rhatc := if hi = 0 then rhat else rhat + (q1 - q1cCap) * dHi
  let x5o := if hi = 0 then hi else q1cCap
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  -- Body 1st D3 (only meaningful when rhatcHi = 0).
  let qDlo1 := q1c * dlo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
  let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
  divKDiv128Step1FullV5PostFromBody sp dHi un1 dlo q1c rhatc x5o rhatcHi qDlo1 bq1' brhat'

/-- Disjointness of the two halves of the full step-1 code (prefix+guard at
    [10..22] vs Phase-1b body at [23..40]). Top-level (fresh heartbeat budget)
    and peeled to singleton-vs-singleton leaves to keep each `bv_omega` cheap. -/
theorem divKDiv128Step1FullV5_code_disjoint (base : Word) :
    (divKDiv128Step1InitCapGuardV5Code base).Disjoint
      (divKDiv128Phase1bBodyV5Code (base + 52)) := by
  unfold divKDiv128Step1InitCapGuardV5Code divKDiv128Step1InitCapV5Code
    divKDiv128Phase1bBodyV5Code divKDiv128Prodcheck1bMergedCode
  repeat' apply CodeReq.Disjoint.union_left
  all_goals (repeat' apply CodeReq.Disjoint.union_right)
  all_goals exact CodeReq.Disjoint.singleton (by bv_omega)

/-- Bridge for the body-TAKEN exit (outer guard fell through, 2nd D3 fired):
    the Phase-1b merged taken-post collapses to the full step-1 post.  Split
    into its own theorem for a fresh heartbeat budget — the `Post` unfold is a
    large nested-`if` term and three such bridges in one proof exhaust 200k. -/
theorem divKDiv128Step1FullV5_ht2_bridge (sp uHi dHi un1 dlo : Word) :
    let q1 := rv64_divu uHi dHi
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1cCap
    let rhatc := if hi = 0 then (uHi - q1 * dHi) else (uHi - q1 * dHi) + (q1 - q1cCap) * dHi
    let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
    let qDlo1 := q1c * dlo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
    ∀ hp, (divKDiv128Prodcheck1bMergedTakenPost sp q1' rhat' dHi un1 qDlo1 dlo ** ⌜rhatcHi = 0⌝) hp →
          divKDiv128Step1FullV5Post sp uHi dHi un1 dlo hp := by
  intro q1 hi q1cCap q1c rhatc rhatcHi qDlo1 rhatUn1 q1' rhat' h hp
  show divKDiv128Step1FullV5Post sp uHi dHi un1 dlo h
  unfold divKDiv128Step1FullV5Post
  change divKDiv128Step1FullV5PostFromBody sp dHi un1 dlo q1c rhatc
    (if hi = 0 then hi else q1cCap) rhatcHi qDlo1 q1' rhat' h
  unfold divKDiv128Step1FullV5PostFromBody
  unfold divKDiv128Prodcheck1bMergedTakenPost at hp
  have hpc := hp
  obtain ⟨_, _, _, _, hL, ⟨_, h_eq⟩⟩ := hpc
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, ⟨_, h_inner⟩, _⟩ := hL
  simp only [if_neg (not_not_intro h_eq), if_neg h_inner]
  delta divKDiv128Step1FullV5PostCore
  extract_pure hp
  obtain ⟨hp, _⟩ := hp
  rw [sepConj_assoc'] at hp
  simp only [EvmAsm.Rv64.Tactics.sepConj_pure_mid_left] at hp
  obtain ⟨_, hp⟩ := hp
  xperm_hyp hp

/-- Bridge for the body-FALL-THROUGH exit (outer guard fell through, 2nd D3
    fell through): the Phase-1b merged ft-post collapses to the full step-1
    post.  Mirrors `…_ht2_bridge` but the inner guard falls through
    (`brhat'Hi = 0` → inner `if_pos`).  Own theorem for a fresh budget. -/
theorem divKDiv128Step1FullV5_hf_bridge (sp uHi dHi un1 dlo : Word) :
    let q1 := rv64_divu uHi dHi
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1cCap
    let rhatc := if hi = 0 then (uHi - q1 * dHi) else (uHi - q1 * dHi) + (q1 - q1cCap) * dHi
    let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
    let qDlo1 := q1c * dlo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
    ∀ hp, (divKDiv128Prodcheck1bMergedFTPost sp q1' rhat' dHi un1 dlo ** ⌜rhatcHi = 0⌝) hp →
          divKDiv128Step1FullV5Post sp uHi dHi un1 dlo hp := by
  intro q1 hi q1cCap q1c rhatc rhatcHi qDlo1 rhatUn1 q1' rhat' h hp
  show divKDiv128Step1FullV5Post sp uHi dHi un1 dlo h
  unfold divKDiv128Step1FullV5Post
  change divKDiv128Step1FullV5PostFromBody sp dHi un1 dlo q1c rhatc
    (if hi = 0 then hi else q1cCap) rhatcHi qDlo1 q1' rhat' h
  unfold divKDiv128Step1FullV5PostFromBody
  unfold divKDiv128Prodcheck1bMergedFTPost at hp
  have hpc := hp
  obtain ⟨_, _, _, _, hL, ⟨_, h_eq⟩⟩ := hpc
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, _, hL⟩ := hL
  obtain ⟨_, _, _, _, ⟨_, h_inner⟩, _⟩ := hL
  simp only [if_neg (not_not_intro h_eq), if_pos h_inner]
  delta divKDiv128Step1FullV5PostCore
  extract_pure hp
  obtain ⟨hp, _⟩ := hp
  rw [sepConj_assoc'] at hp
  simp only [EvmAsm.Rv64.Tactics.sepConj_pure_mid_left] at hp
  obtain ⟨_, hp⟩ := hp
  xperm_hyp hp

/-- Full v5 div128 Phase-1 block (instrs [10]-[40], exit [41]=base+124):
    init + Phase-1a cap + Phase-1b leading guard + both D3 corrections. -/
theorem divK_div128_step1_v5_spec_within
    (sp uHi dHi un1 v10Old v5Old v9Old dlo : Word) (base : Word) :
    cpsTripleWithin 31 base (base + 124) (divKDiv128Step1FullV5Code base)
      (divKDiv128Step1FullV5Pre sp uHi dHi un1 v10Old v5Old v9Old dlo)
      (divKDiv128Step1FullV5Post sp uHi dHi un1 dlo) := by
  -- Minimal locals for the body call (matching the guard's outputs).
  let q1 := rv64_divu uHi dHi
  let hi := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1c := if hi = 0 then q1 else q1cCap
  let rhatc := if hi = 0 then (uHi - q1 * dHi) else (uHi - q1 * dHi) + (q1 - q1cCap) * dHi
  let x5o := if hi = 0 then hi else q1cCap
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  let cr := (divKDiv128Step1InitCapGuardV5Code base).union
            (divKDiv128Phase1bBodyV5Code (base + 52))
  -- Swap only the code requirement (keep Pre/Post folded → light whnf).
  show cpsTripleWithin 31 base (base + 124) cr
    (divKDiv128Step1FullV5Pre sp uHi dHi un1 v10Old v5Old v9Old dlo)
    (divKDiv128Step1FullV5Post sp uHi dHi un1 dlo)
  -- 0-step bridge helper (mirrors step1_v2_spec).
  have refl_of {P : Assertion}
      (h : ∀ hp, P hp → divKDiv128Step1FullV5Post sp uHi dHi un1 dlo hp) :
      cpsTripleWithin 0 (base + 124) (base + 124) cr P
        (divKDiv128Step1FullV5Post sp uHi dHi un1 dlo) :=
    cpsTripleWithin_extend_code (fun _ _ h => by simp [CodeReq.empty] at h)
      (cpsTripleWithin_refl h)
  -- h1: prefix + Phase-1b guard [10..22], framed with x11=un1 + dlo-mem.
  have hg0 := divK_div128_step1_initcapguard_v5_spec_within sp uHi dHi v10Old v5Old v9Old base
  have h1 := cpsBranchWithin_frameR
    ((.x11 ↦ᵣ un1) ** (sp + signExtend12 3952 ↦ₘ dlo)) (by pcFree) hg0
  -- h2: Phase-1b body [23..40] at base+52, framed with the outer-guard pure.
  have hb0 := divK_div128_phase1b_body_v5_spec_within sp q1c rhatc dHi un1 rhatcHi x5o dlo (base + 52)
  have hbe : (base + 52 : Word) + 72 = base + 124 := by bv_addr
  rw [hbe] at hb0
  have h2 := cpsBranchWithin_frameR (⌜rhatcHi = 0⌝) (by pcFree) hb0
  -- Compose the two branches (both exits at base+124).
  have hd := divKDiv128Step1FullV5_code_disjoint base
  have combined := cpsBranchWithin_seq_cpsBranchWithin_with_perm
    (Q_t := divKDiv128Step1FullV5Post sp uHi dHi un1 dlo)
    hd
    h1
    -- hperm: guard-ft post (framed) → body pre (framed with ⌜rhatcHi=0⌝)
    (fun h hp => by xperm_hyp hp)
    h2
    -- ht1: guard-taken post (framed) → Post (outer if_pos via ⌜rhatcHi≠0⌝)
    (fun h hp => by
      show divKDiv128Step1FullV5Post sp uHi dHi un1 dlo h
      unfold divKDiv128Step1FullV5Post
      change divKDiv128Step1FullV5PostFromBody sp dHi un1 dlo q1c rhatc x5o rhatcHi
        (q1c * dlo) (if ((rhatc <<< (32 : BitVec 6).toNat) ||| un1).ult (q1c * dlo) = true then q1c + signExtend12 4095 else q1c)
        (if ((rhatc <<< (32 : BitVec 6).toNat) ||| un1).ult (q1c * dlo) = true then rhatc + dHi else rhatc) h
      unfold divKDiv128Step1FullV5PostFromBody
      have hpc := hp
      obtain ⟨_, _, _, _, hL, _⟩ := hpc
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, _, hL⟩ := hL
      obtain ⟨_, _, _, _, ⟨_, hpure⟩, _⟩ := hL
      change rhatcHi ≠ 0 at hpure
      simp only [if_pos hpure]
      delta divKDiv128Step1FullV5PostCore
      set sh : Nat := (32 : BitVec 6).toNat with hsh
      drop_pure hp
      xperm_hyp hp)
    -- ht2: body-taken post (framed ⌜rhatcHi=0⌝) → Post (own theorem, fresh budget)
    (divKDiv128Step1FullV5_ht2_bridge sp uHi dHi un1 dlo)
  -- Collapse: both exits at base+124, 0-step bridges.
  have merged := cpsBranchWithin_merge_same_cr combined (refl_of (fun hp h => h))
    -- h_f: body-ft post (framed ⌜rhatcHi=0⌝) → Post (own theorem, fresh budget)
    (refl_of (divKDiv128Step1FullV5_hf_bridge sp uHi dHi un1 dlo))
  -- Reconcile the framed prefix pre with the flat `…Pre` def.
  exact cpsTripleWithin_weaken
    (fun h hp => by unfold divKDiv128Step1FullV5Pre at hp; xperm_hyp hp)
    (fun h hp => hp) merged

end EvmAsm.Evm64
