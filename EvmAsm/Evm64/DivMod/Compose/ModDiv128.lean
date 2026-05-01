import EvmAsm.Evm64.DivMod.Compose.Div128

/-!
# DivMod Compose: div128 subroutine composition (modCode)

MOD mirror of Div128.lean: composes 5 block specs
(phase1, step1, compute_un21, step2, end) into a single `mod_div128_spec_within` theorem
for the div128 subroutine under modCode.
Block 13 (div128 at base+1072) is identical between divCode and modCode.
-/

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- div128 subroutine composition for modCode (Issue #89)
-- Compose 5 block specs into a single mod_div128_spec_within theorem.
-- ============================================================================

-- Master subsumption: ofProg (base+1072) divK_div128 ⊆ modCode base
-- Block 13 in modCode's unionAll; skip blocks 0-12.
private theorem divK_div128_ofProg_sub_modCode {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock
  exact CodeReq.union_mono_left

-- Helper: combine two subsumption proofs over a union.
-- `CodeReq.union_sub` — use `CodeReq.union_sub` from `Rv64/SepLogic.lean` (shared).

-- Helper: singleton at index k of divK_div128 with explicit instr ⊆ modCode base.
-- Used to prove each singleton in a block's cr is subsumed by modCode.
private theorem d128_sub_mod {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128.length)
    (h_addr : addr = (base + div128Off) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (modCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_div128_ofProg_sub_modCode a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + div128Off) divK_div128 k hk (by decide)) a i h)

-- ============================================================================
-- mod_div128_spec_within: compose 5 block specs into single subroutine theorem.
-- Entry: base+1072, Exit: retAddr (via JALR), CodeReq: modCode base.
-- ============================================================================

theorem mod_div128_spec_within (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem : Word)
    (halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 51 (base + div128Off) retAddr (modCode base)
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
  -- Reuse the bundled post from Compose/Div128.lean (the post is identical
  -- for div128_spec_within and mod_div128_spec_within — only the CodeReq subsumption
  -- differs). Unfold to expose the lets so the proof body can reference
  -- q1', q0', x7Exit, etc. by name.
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
  -- Extend phase1 cr to modCode
  have hph1e := cpsTripleWithin_extend_code (hmono := by
    -- phase1 cr: 10 singletons at (base+1072)+{0,4,...,36}, indices 0-9
    exact CodeReq.union_sub (d128_sub_mod 0 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 8 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub_mod 9 _ _ (by decide) (by bv_addr) (by decide)))))))))))
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
    exact CodeReq.union_sub (d128_sub_mod 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 11 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 12 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 13 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 14 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 15 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 16 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 17 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 18 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 19 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 20 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 21 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 22 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 23 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub_mod 24 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))
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
    exact CodeReq.union_sub (d128_sub_mod 25 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 26 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 27 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 28 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub_mod 29 _ _ (by decide) (by bv_addr) (by decide))))))
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
  -- 17 instructions (was 15) — SRLI+BNE guard added per Knuth TAOCP §4.3.1 Step D3.
  -- ================================================================
  have hst2 := divK_div128_step2_spec_within sp un21 dHi cu_q1_dlo cu_rhat_un1 un1 dLo un0
    (base + div128Off + 120)
  unfold divKDiv128Step2Code divKDiv128Step2Post at hst2
  rw [show (base + div128Off + 120 : Word) + 68 = base + div128Off + 188 from by bv_addr] at hst2
  have hst2e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub_mod 30 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 31 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 32 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 33 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 34 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 35 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 36 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 37 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 38 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 39 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 40 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 41 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 42 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 43 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 44 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 45 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub_mod 46 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))))
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
  -- ================================================================
  have hend := divK_div128_end_spec_within sp q1' q0' retAddr x11Exit retAddr
    (base + div128Off + 188) halign
  have hende := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub_mod 47 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 48 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub_mod 49 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub_mod 50 _ _ (by decide) (by bv_addr) (by decide)))))
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


