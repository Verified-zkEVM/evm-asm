import EvmAsm.Evm64.DivMod.Compose.Base

/-!
# DivMod Compose: div128 subroutine composition

Section 15 of the DivMod composition: composes 5 block specs
(phase1, step1, compute_un21, step2, end) into a single `div128_spec` theorem
for the div128 subroutine.
-/

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 15: div128 subroutine composition (Issue #88)
-- Compose 5 block specs into a single div128_spec theorem.
-- ============================================================================

-- Master subsumption: ofProg (base+1072) divK_div128 ⊆ sharedDivModCode base
-- Block 12 in sharedDivModCode's unionAll; skip blocks 0-11.
private theorem divK_div128_ofProg_sub_sharedCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128) a = some i →
      (sharedDivModCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

-- Helper: combine two subsumption proofs over a union.
-- `CodeReq.union_sub` — use `CodeReq.union_sub` from `Rv64/SepLogic.lean` (shared).

-- Helper: singleton at index k of divK_div128 with explicit instr ⊆ sharedDivModCode base.
-- Used to prove each singleton in a block's cr is subsumed by sharedDivModCode.
private theorem d128_sub (base : Word) (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128.length)
    (h_addr : addr = (base + div128Off) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (sharedDivModCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_div128_ofProg_sub_sharedCode base a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + div128Off) divK_div128 k hk (by decide)) a i h)

-- Abbreviation for repeated `by decide` / `by bv_addr` calls
-- Each block's subsumption uses: CodeReq.union_sub (d128_sub ...) (CodeReq.union_sub ...)

-- ============================================================================
-- div128_spec: compose 5 block specs into single subroutine theorem.
-- Entry: base+1072, Exit: ret_addr (via JALR), CodeReq: sharedDivModCode base.
-- ============================================================================

theorem div128_spec (sp ret_addr d uLo uHi : Word) (base : Word)
    (v1_old v6_old v11_old : Word)
    (ret_mem d_mem dlo_mem un0_mem : Word)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
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
    let q_dlo := q1c * dLo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + dHi else rhatc
    -- Compute un21 intermediates (x5, x1 values after compute_un21)
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    -- Step 2 intermediates
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0_dlo := q0c * dLo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    -- End: combine q1' and q0'
    let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTriple (base + div128Off) ret_addr (sharedDivModCode base)
      (-- Precondition: caller registers + scratch memory
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      (-- Postcondition: x11=quotient, all regs/mem updated
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ q1') **
       (.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ q0_dlo) **
       (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ rhat2_un0) ** (.x11 ↦ᵣ q) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ dLo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  -- Introduce all let bindings
  intro dHi dLo un1 un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q
  -- ================================================================
  -- Block 1: Phase 1 (base+1072 → base+1112)
  -- Saves ret/d, splits d and uLo into halves.
  -- ================================================================
  have hph1 := divK_div128_phase1_spec sp ret_addr d uLo uHi v1_old v6_old v11_old
    ret_mem d_mem dlo_mem un0_mem (base + div128Off)
  rw [show (base + div128Off : Word) + 40 = base + 1112 from by bv_addr] at hph1
  -- Extend phase1 cr to sharedDivModCode
  have hph1e := cpsTriple_extend_code (hmono := by
    -- phase1 cr: 10 singletons at (base+1072)+{0,4,...,36}, indices 0-9
    exact CodeReq.union_sub (d128_sub base 0 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 8 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub base 9 _ _ (by decide) (by bv_addr) (by decide)))))))))))
    hph1
  -- Frame phase1 with x0=0 (not used by phase1)
  have hph1f := cpsTriple_frameR
    (.x0 ↦ᵣ (0 : Word))
    (by pcFree) hph1e
  -- ================================================================
  -- Block 2: Step 1 (base+1112 → base+1172)
  -- Trial division q1, clamp, product check.
  -- ================================================================
  have hst1 := divK_div128_step1_spec sp uHi dHi un1 dLo un0 d dLo
    (base + 1112)
  rw [show (base + 1112 : Word) + 60 = base + 1172 from by bv_addr] at hst1
  have hst1e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub base 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 11 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 12 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 13 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 14 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 15 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 16 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 17 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 18 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 19 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 20 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 21 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 22 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 23 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub base 24 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))
    hst1
  -- Frame step1 with x2, mem[3968], mem[3960], mem[3944]
  have hst1f := cpsTriple_frameR
    ((.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hst1e
  -- Compose phase1 → step1
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hph1f hst1f
  -- ================================================================
  -- Block 3: Compute un21 (base+1172 → base+1192)
  -- un21 = rhat*2^32 + un1 - q1*dLo.
  -- ================================================================
  have hcu := divK_div128_compute_un21_spec sp q1' rhat' un1 rhat_un1 q_dlo dLo
    (base + 1172)
  rw [show (base + 1172 : Word) + 20 = base + 1192 from by bv_addr] at hcu
  have hcue := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub base 25 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 26 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 27 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 28 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub base 29 _ _ (by decide) (by bv_addr) (by decide))))))
    hcu
  -- Frame compute_un21 with x6, x0, x2, mem[3968], mem[3960], mem[3944]
  have hcuf := cpsTriple_frameR
    ((.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hcue
  -- Compose (phase1→step1) → compute_un21
  have h123 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 hcuf
  -- ================================================================
  -- Block 4: Step 2 (base+1192 → base+1252)
  -- Trial division q0, clamp, product check.
  -- Params: un21(x7), dHi(x6), v1_old=cu_q1_dlo(x1),
  --         v5_old=cu_rhat_un1(x5), v11_old=un1(x11),
  --         dlo=dLo(mem[3952]), un0(mem[3944])
  -- ================================================================
  have hst2 := divK_div128_step2_spec sp un21 dHi cu_q1_dlo cu_rhat_un1 un1 dLo un0
    (base + 1192)
  rw [show (base + 1192 : Word) + 60 = base + 1252 from by bv_addr] at hst2
  have hst2e := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub base 30 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 31 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 32 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 33 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 34 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 35 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 36 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 37 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 38 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 39 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 40 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 41 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 42 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 43 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub base 44 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))
    hst2
  -- Frame step2 with x10, x2, mem[3968], mem[3960]
  have hst2f := cpsTriple_frameR
    ((.x10 ↦ᵣ q1') ** (.x2 ↦ᵣ ret_addr) **
     (sp + signExtend12 3968 ↦ₘ ret_addr) ** (sp + signExtend12 3960 ↦ₘ d))
    (by pcFree) hst2e
  -- Compose (→step1→compute_un21) → step2
  have h1234 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hst2f
  -- ================================================================
  -- Block 5: End (base+1252 → ret_addr via JALR)
  -- Combine q1'|q0' into q, restore return addr, return.
  -- Params: q1=q1'(x10), q0=q0'(x5), v2_old=ret_addr(x2),
  --         v11_old=un0(x11), ret_addr(mem[3968])
  -- ================================================================
  have hend := divK_div128_end_spec sp q1' q0' ret_addr un0 ret_addr
    (base + 1252) halign
  have hende := cpsTriple_extend_code (hmono := by
    exact CodeReq.union_sub (d128_sub base 45 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 46 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_sub base 47 _ _ (by decide) (by bv_addr) (by decide))
      (d128_sub base 48 _ _ (by decide) (by bv_addr) (by decide)))))
    hend
  -- Frame end with x7, x6, x1, x0, mem[3960], mem[3952], mem[3944]
  have hendf := cpsTriple_frameR
    ((.x7 ↦ᵣ q0_dlo) ** (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ rhat2_un0) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hende
  -- Compose (→step2) → end
  have h12345 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 hendf
  -- Final permutation to canonical pre/post order
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12345

end EvmAsm.Evm64
