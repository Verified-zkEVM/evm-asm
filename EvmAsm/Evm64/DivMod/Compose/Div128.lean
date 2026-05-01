import EvmAsm.Evm64.DivMod.Compose.Base

/-!
# DivMod Compose: div128 subroutine composition

Section 15 of the DivMod composition: composes 5 block specs
(phase1, step1, compute_un21, step2, end) into a single `div128_spec_within` theorem
for the div128 subroutine.
-/

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 15: div128 subroutine composition (Issue #88)
-- Compose 5 block specs into a single div128_spec_within theorem.
-- ============================================================================

-- Master subsumption: ofProg (base+1072) divK_div128 ⊆ sharedDivModCode base
-- Block 12 in sharedDivModCode's unionAll; skip blocks 0-11.
private theorem divK_div128_ofProg_sub_sharedCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128) a = some i →
      (sharedDivModCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

-- Helper: combine two subsumption proofs over a union.
-- `CodeReq.union_sub` — use `CodeReq.union_sub` from `Rv64/SepLogic.lean` (shared).

-- Helper: singleton at index k of divK_div128 with explicit instr ⊆ sharedDivModCode base.
-- Used to prove each singleton in a block's cr is subsumed by sharedDivModCode.
private theorem d128_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128.length)
    (h_addr : addr = (base + div128Off) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_div128_ofProg_sub_sharedCode a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + div128Off) divK_div128 k hk (by decide)) a i h)

-- Abbreviation for repeated `by decide` / `by bv_addr` calls
-- Each block's subsumption uses: CodeReq.union_sub (d128_sub ...) (CodeReq.union_sub ...)

-- ============================================================================
-- div128_spec_within: compose 5 block specs into single subroutine theorem.
-- Entry: base+1072, Exit: retAddr (via JALR), CodeReq: sharedDivModCode base.
-- ============================================================================

/-- Bundled postcondition for `div128_spec_within` (and `mod_div128_spec_within`).
    Hides the 25-let chain that computes Phase 1 / compute-un21 / Phase 2 /
    Phase 2b-guarded / end-combine intermediates so the theorem signature
    stays a clean `cpsTripleWithin n A B C P (div128SpecPost …)` instead of a
    let-chain immediately preceding the triple (anti-pattern, slows
    elaboration). Marked `@[irreducible]` so callers see only the bundled
    assertion; `unfold` to expose the lets when threading downstream.
    Part of #1139. -/
@[irreducible]
def div128SpecPost (sp retAddr d uLo uHi : Word) : Assertion :=
  -- Phase 1 intermediates
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  -- Step 1 intermediates
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  -- compute_un21 intermediates
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  -- Step 2 intermediates
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ q1') **
  (.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ x7Exit) **
  (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ q) **
  (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ retAddr) **
  (sp + signExtend12 3960 ↦ₘ d) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0)

theorem div128_spec_within (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 51 (base + div128Off) retAddr (sharedDivModCode base)
      (-- Precondition: caller registers + scratch memory
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem))
      (div128SpecPost sp retAddr d uLo uHi) := by
  unfold div128SpecPost
  -- Phase 1 intermediates
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  -- Step 1 intermediates
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  -- compute_un21 intermediates
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  -- Step 2 intermediates
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let x11Exit := if rhat2cHi = 0 then un0 else rhat2c
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  -- ================================================================
  -- Block 1: Phase 1 (base+1072 → base+1112)
  -- Saves ret/d, splits d and uLo into halves.
  -- ================================================================
  have hph1 := divK_div128_phase1_spec_within sp retAddr d uLo uHi v1Old v6Old v11Old
    retMem dMem dloMem un0Mem (base + div128Off)
  -- Extend phase1 cr to sharedDivModCode
  have hph1e := cpsTripleWithin_extend_code (hmono := by
    -- phase1 cr: 10 singletons at (base+1072)+{0,4,...,36}, indices 0-9
    exact CodeReq.union_sub (d128_sub 0 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 8 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub 9 _ _ (by decide) (by bv_addr) (by decide)))))))))))
    hph1
  -- Frame phase1 with x0=0 (not used by phase1)
  have hph1f := cpsTripleWithin_frameR
    (.x0 ↦ᵣ (0 : Word))
    (by pcFree) hph1e
  -- ================================================================
  -- Block 2: Step 1 (base+1112 → base+1172)
  -- Trial division q1, clamp, product check.
  -- ================================================================
  have hst1 := divK_div128_step1_spec_within sp uHi dHi un1 dLo un0 d dLo
    (base + div128Off + 40)
  rw [show (base + div128Off + 40 : Word) + 60 = base + div128Off + 100 from by bv_addr] at hst1
  have hst1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 11 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 12 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 13 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 14 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 15 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 16 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 17 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 18 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 19 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 20 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 21 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 22 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 23 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub 24 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))
    hst1
  -- Frame step1 with x2, mem[3968], mem[3960], mem[3944]
  have hst1f := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hst1e
  -- Compose phase1 → step1
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hph1f hst1f
  -- ================================================================
  -- Block 3: Compute un21 (base+1172 → base+1192)
  -- un21 = rhat*2^32 + un1 - q1*dLo.
  -- ================================================================
  have hcu := divK_div128_compute_un21_spec_within sp q1' rhat' un1 rhatUn1 qDlo dLo
    (base + div128Off + 100)
  rw [show (base + div128Off + 100 : Word) + 20 = base + div128Off + 120 from by bv_addr] at hcu
  have hcue := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub 25 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 26 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 27 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 28 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub 29 _ _ (by decide) (by bv_addr) (by decide))))))
    hcu
  -- Frame compute_un21 with x6, x0, x2, mem[3968], mem[3960], mem[3944]
  have hcuf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hcue
  -- Compose (phase1→step1) → compute_un21
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 hcuf
  -- ================================================================
  -- Block 4: Step 2 (base+1192 → base+1260)
  -- Trial division q0, clamp, Phase 2b guard, product check.
  -- Params: un21(x7), dHi(x6), v1Old=cu_q1_dlo(x1),
  --         v5Old=cu_rhat_un1(x5), v11Old=un1(x11),
  --         dlo=dLo(mem[3952]), un0(mem[3944])
  -- NOTE: 17 instructions (was 15) — SRLI+BNE guard added between clamp
  -- and mul-check per Knuth TAOCP §4.3.1 Step D3.
  -- ================================================================
  have hst2 := divK_div128_step2_spec_within sp un21 dHi cu_q1_dlo cu_rhat_un1 un1 dLo un0
    (base + div128Off + 120)
  unfold divKDiv128Step2Code divKDiv128Step2Post at hst2
  rw [show (base + div128Off + 120 : Word) + 68 = base + div128Off + 188 from by bv_addr] at hst2
  have hst2e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub 30 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 31 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 32 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 33 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 34 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 35 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 36 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 37 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 38 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 39 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 40 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 41 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 42 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 43 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 44 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 45 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub 46 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))))
    hst2
  -- Frame step2 with x10, x2, mem[3968], mem[3960]
  have hst2f := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ q1') ** (.x2 ↦ᵣ retAddr) **
     (sp + signExtend12 3968 ↦ₘ retAddr) ** (sp + signExtend12 3960 ↦ₘ d))
    (by pcFree) hst2e
  -- Compose (→step1→compute_un21) → step2
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hst2f
  -- ================================================================
  -- Block 5: End (base+1260 → retAddr via JALR)
  -- Combine q1'|q0' into q, restore return addr, return.
  -- Params: q1=q1'(x10), q0=q0'(x5), v2Old=retAddr(x2),
  --         v11Old=x11Exit(x11), retAddr(mem[3968])
  -- ================================================================
  have hend := divK_div128_end_spec_within sp q1' q0' retAddr x11Exit retAddr
    (base + div128Off + 188) halign
  have hende := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub 47 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 48 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub 49 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub 50 _ _ (by decide) (by bv_addr) (by decide)))))
    hend
  -- Frame end with x7, x6, x1, x0, mem[3960], mem[3952], mem[3944]
  have hendf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ x7Exit) ** (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ x1Exit) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hende
  -- Compose (→step2) → end
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 hendf
  -- Final permutation to canonical pre/post order
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12345

def div128V2SpecPost (sp retAddr d uLo uHi : Word) : Assertion :=
  -- Phase 1 split intermediates (unchanged).
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  -- Step 1 1st D3 (unchanged).
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  -- Step 1 2nd D3 (NEW in v2 — gated by `rhatHi2 = 0`).
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
              then q1' + signExtend12 4095 else q1'
  let rhat'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                then rhat' + dHi else rhat'
  -- compute_un21: now uses q1''/rhat'' instead of q1'/rhat'.
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  -- Step 2 (unchanged from div128_spec_within, but starts with v2's un21).
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1'' <<< (32 : BitVec 6).toNat) ||| q0'
  (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ q1'') **
  (.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ x7Exit) **
  (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ q) **
  (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ retAddr) **
  (sp + signExtend12 3960 ↦ₘ d) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0)

-- v2 helper: singleton at index k of divK_div128_v2 ⊆ ofProg-based v2 cr.
-- Mirrors `d128_sub` but uses `ofProg (base + div128Off) divK_div128_v2`
-- directly as the target cr (no master subsumption needed since we don't
-- target sharedDivModCode for v2).
private theorem d128_v2_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128_v2.length)
    (h_addr : addr = (base + div128Off) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128_v2.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (CodeReq.ofProg (base + div128Off) divK_div128_v2) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => CodeReq.singleton_mono
    (CodeReq.ofProg_lookup (base + div128Off) divK_div128_v2 k hk (by decide)) a i h

/-- **STUB**: equivalence between `divK_div128_v2` (fixed RISC-V) and
    `div128Quot_v2` (fixed Lean abstraction).

    Mirrors `div128_spec_within` but for the v2 algorithm. The proof structure
    parallels `div128_spec_within` with two changes:
    - The Phase 1 block uses `divK_div128_step1_v2_spec` (covering instrs
      [10..34]) instead of `divK_div128_step1_spec` ([10..24]).
    - Offsets in the shifted `[35..60]` blocks bump by +40 bytes from
      the original `[25..50]`.

    Total instruction count: 61 (vs original 51). Total byte span: 244
    (vs original 204).

    Estimated: ~600 LOC for the full proof.

    Tracked in issue #1337's algorithm-fix migration. -/
theorem div128_v2_spec_within (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (_halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 61 (base + div128Off) retAddr
      (CodeReq.ofProg (base + div128Off) divK_div128_v2)
      (-- Precondition: same as div128_spec_within.
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem))
      (div128V2SpecPost sp retAddr d uLo uHi) := by
  unfold div128V2SpecPost
  -- Phase 1 intermediates (same as div128_spec_within).
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  -- Step 1 v2 intermediates (q1 / rhat through both D3 corrections).
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo1 := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
              then q1' + signExtend12 4095 else q1'
  let rhat'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                then rhat' + dHi else rhat'
  -- ================================================================
  -- Block 1: Phase 1 (base+1072 → base+1112). Same instructions [0..9]
  -- as divK_div128 — the v2 fix doesn't touch Phase 1.
  -- ================================================================
  have hph1 := divK_div128_phase1_spec_within sp retAddr d uLo uHi v1Old v6Old v11Old
    retMem dMem dloMem un0Mem (base + div128Off)
  have hph1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v2_sub 0 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 8 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v2_sub 9 _ _ (by decide) (by bv_addr) (by decide)))))))))))
    hph1
  have hph1f := cpsTripleWithin_frameR
    (.x0 ↦ᵣ (0 : Word))
    (by pcFree) hph1e
  -- ================================================================
  -- Block 2 (NEW for v2): Step 1 v2 (base+1112 → base+1212).
  -- Covers instructions [10..34] = step1 init + clamp + 1st D3 +
  -- 2nd D3 (the inserted block).
  -- ================================================================
  have hst1 := divK_div128_step1_v2_spec_within sp uHi dHi un1 dLo un0 d dLo
    (base + div128Off + 40)
  unfold divKDiv128Step1V2Code divKDiv128Step1V2Pre divKDiv128Step1V2Post at hst1
  rw [show (base + div128Off + 40 : Word) + 100 = base + div128Off + 140 from by bv_addr] at hst1
  -- Extend step1_v2's 25-singleton cr to ofProg-of-divK_div128_v2.
  -- Indices 10..34 in divK_div128_v2 (instructions [10..34]).
  have hst1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v2_sub 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 11 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 12 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 13 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 14 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 15 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 16 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 17 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 18 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 19 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 20 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 21 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 22 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 23 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 24 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 25 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 26 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 27 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 28 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 29 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 30 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 31 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 32 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 33 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v2_sub 34 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))))))))))))
    hst1
  -- Frame step1_v2 with x2, mem[3968], mem[3960], mem[3944]
  have hst1f := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hst1e
  -- Compose phase1 → step1_v2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hph1f hst1f
  -- ================================================================
  -- Block 3: Compute un21 (base+1212 → base+1232) — shifted +40 from v1.
  -- Uses q1''/rhat'' (post-2nd-D3) and step1_v2's conditional .x5/.x1
  -- exits as the "old" register values.
  -- ================================================================
  let x5Exit_st1 := if rhatHi2 = 0 then qDlo2 else qDlo1
  let x1Exit_st1 := if rhatHi2 = 0 then rhatUn1' else rhatHi2
  have hcu := divK_div128_compute_un21_spec_within sp q1'' rhat'' un1 x1Exit_st1 x5Exit_st1 dLo
    (base + div128Off + 140)
  rw [show (base + div128Off + 140 : Word) + 20 = base + div128Off + 160 from by bv_addr] at hcu
  have hcue := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v2_sub 35 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 36 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 37 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 38 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v2_sub 39 _ _ (by decide) (by bv_addr) (by decide))))))
    hcu
  -- Frame compute_un21 with x6, x0, x2, mem[3968], mem[3960], mem[3944]
  have hcuf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hcue
  -- Compose (phase1→step1_v2) → compute_un21
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 hcuf
  -- ================================================================
  -- Block 4: Step 2 (base+1232 → base+1300) — shifted +40 from v1.
  -- Trial division q0, clamp, Phase 2b guard, product check.
  -- Same 17 instructions as v1's step2, just at higher offset.
  -- ================================================================
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  have hst2 := divK_div128_step2_spec_within sp un21 dHi cu_q1_dlo cu_rhat_un1 un1 dLo un0
    (base + div128Off + 160)
  unfold divKDiv128Step2Code divKDiv128Step2Post at hst2
  rw [show (base + div128Off + 160 : Word) + 68 = base + (div128Off + 228) from by bv_addr] at hst2
  have hst2e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v2_sub 40 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 41 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 42 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 43 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 44 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 45 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 46 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 47 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 48 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 49 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 50 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 51 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 52 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 53 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 54 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 55 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v2_sub 56 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))))
    hst2
  -- Frame step2 with x10, x2, mem[3968], mem[3960]
  have hst2f := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ q1'') ** (.x2 ↦ᵣ retAddr) **
     (sp + signExtend12 3968 ↦ₘ retAddr) ** (sp + signExtend12 3960 ↦ₘ d))
    (by pcFree) hst2e
  -- Compose (→step1_v2→compute_un21) → step2
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hst2f
  -- ================================================================
  -- Block 5: End (base+1300 → retAddr via JALR) — shifted +40 from v1.
  -- Combine q1''|q0' into q, restore return addr, return. 4 instructions.
  -- ================================================================
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let x11Exit := if rhat2cHi = 0 then un0 else rhat2c
  have hend := divK_div128_end_spec_within sp q1'' q0' retAddr x11Exit retAddr
    (base + (div128Off + 228)) _halign
  have hende := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v2_sub 57 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 58 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v2_sub 59 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v2_sub 60 _ _ (by decide) (by bv_addr) (by decide)))))
    hend
  -- Frame end with x7, x6, x1, x0, mem[3960], mem[3952], mem[3944]
  have hendf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ x7Exit) ** (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ x1Exit) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hende
  -- Compose (→step2) → end
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 hendf
  -- Final permutation to canonical pre/post order
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12345

theorem div128_v2_spec_shared_within (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 61 (base + div128Off) retAddr (sharedDivModCode_v2 base)
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem))
      (div128V2SpecPost sp retAddr d uLo uHi) :=
  cpsTripleWithin_extend_code (hmono := shared_b12_div128_v2_sub)
    (div128_v2_spec_within sp retAddr d uLo uHi base v1Old v6Old v11Old
                     retMem dMem dloMem un0Mem halign)
