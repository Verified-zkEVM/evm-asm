import EvmAsm.Evm64.DivMod.Compose.Base

/-!
# DivMod Compose: div128 subroutine composition

Section 15 of the DivMod composition: composes 5 block specs
(phase1, step1, compute_un21, step2, end) into a single `div128_spec` theorem
for the div128 subroutine.
-/

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 15: div128 subroutine composition (Issue #88)
-- Compose 5 block specs into a single div128_spec theorem.
-- ============================================================================

-- Master subsumption: ofProg (base+1068) divK_div128 ⊆ divCode base
-- Block 13 in divCode's unionAll; skip blocks 0-12.
private theorem divK_div128_ofProg_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1068) divK_div128) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock
  exact CodeReq.union_mono_left _ _

-- Helper: combine two subsumption proofs over a union.
private theorem CodeReq_union_sub {cr1 cr2 target : CodeReq}
    (h1 : ∀ a i, cr1 a = some i → target a = some i)
    (h2 : ∀ a i, cr2 a = some i → target a = some i) :
    ∀ a i, (cr1.union cr2) a = some i → target a = some i := by
  intro a i h
  simp only [CodeReq.union] at h
  cases h1a : cr1 a with
  | some j => rw [h1a] at h; simp at h; exact h ▸ h1 a j h1a
  | none => rw [h1a] at h; simp at h; exact h2 a i h

-- Helper: singleton at index k of divK_div128 with explicit instr ⊆ divCode base.
-- Used to prove each singleton in a block's cr is subsumed by divCode.
private theorem d128_sub (base : Word) (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128.length)
    (h_addr : addr = (base + 1068) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (divCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_div128_ofProg_sub_divCode base a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + 1068) divK_div128 k hk (by native_decide)) a i h)

-- Abbreviation for repeated `by native_decide` / `by bv_addr` calls
-- Each block's subsumption uses: CodeReq_union_sub (d128_sub ...) (CodeReq_union_sub ...)

-- Address normalization: block entry offsets relative to (base + 1068)
private theorem d128_off_40 (base : Word) : (base + 1068 : Word) + 40 = base + 1108 := by bv_addr
private theorem d128_off_100 (base : Word) : (base + 1068 : Word) + 100 = base + 1168 := by bv_addr
private theorem d128_off_120 (base : Word) : (base + 1068 : Word) + 120 = base + 1188 := by bv_addr
private theorem d128_off_180 (base : Word) : (base + 1068 : Word) + 180 = base + 1248 := by bv_addr

-- ============================================================================
-- div128_spec: compose 5 block specs into single subroutine theorem.
-- Entry: base+1068, Exit: ret_addr (via JALR), CodeReq: divCode base.
-- ============================================================================

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
theorem div128_spec (sp ret_addr d u_lo u_hi : Word) (base : Word)
    (v1_old v6_old v11_old : Word)
    (ret_mem d_mem dlo_mem un0_mem : Word)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    -- Phase 1 intermediates
    let d_hi := d >>> (32 : BitVec 6).toNat
    let d_lo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    -- Step 1 intermediates
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    -- Compute un21 intermediates (x5, x1 values after compute_un21)
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    -- Step 2 intermediates
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    -- End: combine q1' and q0'
    let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTriple (base + 1068) ret_addr (divCode base)
      (-- Precondition: caller registers + scratch memory
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ u_lo) ** (.x7 ↦ᵣ u_hi) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      (-- Postcondition: x11=quotient, all regs/mem updated
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ q1') **
       (.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ q0_dlo) **
       (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ rhat2_un0) ** (.x11 ↦ᵣ q) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  -- Introduce all let bindings
  intro d_hi d_lo un1 un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q
  -- ================================================================
  -- Block 1: Phase 1 (base+1068 → base+1108)
  -- Saves ret/d, splits d and u_lo into halves.
  -- ================================================================
  have hph1 := divK_div128_phase1_spec sp ret_addr d u_lo u_hi v1_old v6_old v11_old
    ret_mem d_mem dlo_mem un0_mem (base + 1068) hv_ret hv_d hv_dlo hv_un0
  rw [show (base + 1068 : Word) + 40 = base + 1108 from by bv_addr] at hph1
  -- Extend phase1 cr to divCode
  have hph1e := cpsTriple_extend_code (hmono := by
    -- phase1 cr: 10 singletons at (base+1068)+{0,4,...,36}, indices 0-9
    exact CodeReq_union_sub (d128_sub base 0 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 1 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 2 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 3 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 4 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 5 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 6 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 7 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 8 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (d128_sub base 9 _ _ (by native_decide) (by bv_addr) (by native_decide)))))))))))
    hph1
  -- Frame phase1 with x0=0 (not used by phase1)
  have hph1f := cpsTriple_frame_left _ _ _ _ _
    (.x0 ↦ᵣ (0 : Word))
    (by pcFree) hph1e
  -- ================================================================
  -- Block 2: Step 1 (base+1108 → base+1168)
  -- Trial division q1, clamp, product check.
  -- ================================================================
  have hst1 := divK_div128_step1_spec sp u_hi d_hi un1 d_lo un0 d d_lo
    (base + 1108) hv_dlo
  rw [show (base + 1108 : Word) + 60 = base + 1168 from by bv_addr] at hst1
  have hst1e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 10 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 11 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 12 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 13 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 14 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 15 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 16 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 17 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 18 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 19 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 20 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 21 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 22 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 23 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (d128_sub base 24 _ _ (by native_decide) (by bv_addr) (by native_decide))))))))))))))))
    hst1
  -- Frame step1 with x2, mem[3968], mem[3960], mem[3944]
  have hst1f := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hst1e
  -- Compose phase1 → step1
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hph1f hst1f
  -- ================================================================
  -- Block 3: Compute un21 (base+1168 → base+1188)
  -- un21 = rhat*2^32 + un1 - q1*d_lo.
  -- ================================================================
  have hcu := divK_div128_compute_un21_spec sp q1' rhat' un1 rhat_un1 q_dlo d_lo
    (base + 1168) hv_dlo
  rw [show (base + 1168 : Word) + 20 = base + 1188 from by bv_addr] at hcu
  have hcue := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 25 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 26 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 27 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 28 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (d128_sub base 29 _ _ (by native_decide) (by bv_addr) (by native_decide))))))
    hcu
  -- Frame compute_un21 with x6, x0, x2, mem[3968], mem[3960], mem[3944]
  have hcuf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ d_hi) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hcue
  -- Compose (phase1→step1) → compute_un21
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 hcuf
  -- ================================================================
  -- Block 4: Step 2 (base+1188 → base+1248)
  -- Trial division q0, clamp, product check.
  -- Params: un21(x7), d_hi(x6), v1_old=cu_q1_dlo(x1),
  --         v5_old=cu_rhat_un1(x5), v11_old=un1(x11),
  --         dlo=d_lo(mem[3952]), un0(mem[3944])
  -- ================================================================
  have hst2 := divK_div128_step2_spec sp un21 d_hi cu_q1_dlo cu_rhat_un1 un1 d_lo un0
    (base + 1188) hv_dlo hv_un0
  rw [show (base + 1188 : Word) + 60 = base + 1248 from by bv_addr] at hst2
  have hst2e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 30 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 31 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 32 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 33 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 34 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 35 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 36 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 37 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 38 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 39 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 40 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 41 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 42 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 43 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (d128_sub base 44 _ _ (by native_decide) (by bv_addr) (by native_decide))))))))))))))))
    hst2
  -- Frame step2 with x10, x2, mem[3968], mem[3960]
  have hst2f := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ q1') ** (.x2 ↦ᵣ ret_addr) **
     (sp + signExtend12 3968 ↦ₘ ret_addr) ** (sp + signExtend12 3960 ↦ₘ d))
    (by pcFree) hst2e
  -- Compose (→step1→compute_un21) → step2
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hst2f
  -- ================================================================
  -- Block 5: End (base+1248 → ret_addr via JALR)
  -- Combine q1'|q0' into q, restore return addr, return.
  -- Params: q1=q1'(x10), q0=q0'(x5), v2_old=ret_addr(x2),
  --         v11_old=un0(x11), ret_addr(mem[3968])
  -- ================================================================
  have hend := divK_div128_end_spec sp q1' q0' ret_addr un0 ret_addr
    (base + 1248) hv_ret halign
  have hende := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 45 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 46 _ _ (by native_decide) (by bv_addr) (by native_decide))
     (CodeReq_union_sub (d128_sub base 47 _ _ (by native_decide) (by bv_addr) (by native_decide))
      (d128_sub base 48 _ _ (by native_decide) (by bv_addr) (by native_decide)))))
    hend
  -- Frame end with x7, x6, x1, x0, mem[3960], mem[3952], mem[3944]
  have hendf := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ q0_dlo) ** (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ rhat2_un0) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hende
  -- Compose (→step2) → end
  have h12345 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 hendf
  -- Final permutation to canonical pre/post order
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12345

end EvmAsm.Rv64
