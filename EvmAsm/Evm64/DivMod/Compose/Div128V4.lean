/-
  EvmAsm.Evm64.DivMod.Compose.Div128V4

  div128 subroutine composition for the v4 algorithm — the FULL
  Knuth Algorithm D with 2-correction in BOTH Phase 1b and Phase 2b.

  The v4 RV64 program `divK_div128_v4` (defined in `Program.lean`) is
  identical to `divK_div128_v2` for instructions [0..46], then adds a
  Phase 2b 2nd D3 correction at [47..70] (vs v2's single correction at
  [47..56]). Total length: 75 vs 61 instructions for v2.

  Companion to `Compose/Div128.lean` (v1 + v2 specs). PR-A2 of the
  v2 → v4 migration plan.

  Issue #1337 algorithm fix migration / Issue #61 stack spec closure.
-/

import EvmAsm.Evm64.DivMod.Compose.Div128
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2v4
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 15-v4: div128 subroutine composition (v4 algorithm).
-- ============================================================================

-- v4 helper: singleton at index k of divK_div128_v4 ⊆ ofProg-based v4 cr.
-- Mirrors `d128_v2_sub` but uses `divK_div128_v4`.
private theorem d128_v4_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < divK_div128_v4.length)
    (h_addr : addr = (base + div128Off) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128_v4.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (CodeReq.ofProg (base + div128Off) divK_div128_v4) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => CodeReq.singleton_mono
    (CodeReq.ofProg_lookup (base + div128Off) divK_div128_v4 k hk (by decide)) a i h

/-- Bundled postcondition for `div128_v4_spec`.

    Mirrors `div128V2SpecPost` but uses `q0''` (post-Phase-2b-2nd-D3)
    instead of `q0'`, matching `div128Quot_v4`'s output. The Phase 1
    intermediates (q1, rhat, q1c, rhatc, q1', rhat', q1'', rhat'') are
    identical between v2 and v4 — the v4 fix is in Phase 2b only.

    `@[irreducible]` to keep the let-chain out of the theorem signature. -/
@[irreducible]
def div128V4SpecPost (sp retAddr d uLo uHi scratchMem : Word) : Assertion :=
  -- Phase 1 split intermediates (unchanged from v2).
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
  -- Step 1 2nd D3 (unchanged from v2).
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
              then q1' + signExtend12 4095 else q1'
  let rhat'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                then rhat' + dHi else rhat'
  -- compute_un21 (unchanged shape — uses q1''/rhat'').
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  -- Step 2 init/clamp (unchanged shape).
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  -- Phase 2b 1st D3 (unchanged shape — same `div128Quot_phase2b_q0'`).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  -- Phase 2b 2nd D3 (NEW in v4).
  let rhat2' :=
    if rhat2c >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2c := q0c * dLo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
      if BitVec.ult rhatUn0 qDlo2c then rhat2c + dHi else rhat2c
    else rhat2c
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo un0
  let q := (q1'' <<< (32 : BitVec 6).toNat) ||| q0''
  -- Register and memory state (final). x1/x7 from step2_v4 post (transient
  -- values depending on which BLTU/BNE branches fired); end_spec overwrites
  -- x11 with q (combined result) from x10 and x5.
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dLo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let x7Exit_step2 := if rhat2cHi ≠ 0 then un21
                      else if rhat2'Hi ≠ 0 then q0Dlo1
                      else q0Dlo2
  let x1Exit_step2 := if rhat2cHi ≠ 0 then rhat2cHi
                      else if rhat2'Hi ≠ 0 then rhat2'Hi
                      else rhat2'Un0
  (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ q1'') **
  (.x5 ↦ᵣ q0'') ** (.x7 ↦ᵣ x7Exit_step2) **
  (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ x1Exit_step2) ** (.x11 ↦ᵣ q) **
  (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ retAddr) **
  (sp + signExtend12 3960 ↦ₘ d) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ (if rhat2cHi ≠ 0 then scratchMem else rhat2c))

/-- **STUB**: equivalence between `divK_div128_v4` (full Knuth D RISC-V)
    and `div128Quot_v4` (Lean abstraction).

    Mirrors `div128_v2_spec` but for the v4 algorithm. Proof structure:
    - Block 1 (Phase 1, instrs [0..9]): identical to v2.
    - Block 2 (Step1 v2, instrs [10..34]): identical to v2 — Phase 1b
      2-correction is the same.
    - Block 3 (compute_un21, instrs [35..39]): identical shape — uses
      q1''/rhat'' (post-Phase-1b-2nd-D3).
    - Block 4 (Step2 + Phase 2b 1st D3 + 2nd D3, instrs [40..70]):
      **NEW for v4**. v2's Step2 covered [40..56]; v4's covers [40..70]
      with 14 extra instructions for the 2nd Phase 2b D3 correction.
    - Block 5 (end, instrs [71..74]): identical shape — combine + return.

    The Block 4 proof requires:
    - `divK_div128_step2_v4_spec` (NEW): RV64 → val256 spec for instrs
      [40..70] producing q0''.
    - This in turn requires either reusing `div128Quot_phase2b_q0'`
      twice (matching v4's Lean def) or composing 1st D3 + 2nd D3
      sub-specs.

    Estimated: ~700 LOC for the full proof (vs ~600 for v2). -/
theorem div128_v4_spec (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (_halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 73 (base + div128Off) retAddr
      (CodeReq.ofProg (base + div128Off) divK_div128_v4)
      (-- Precondition: same as div128_v2_spec, plus the new scratch slot
       -- 3936 (used to save rhat2c across the un0 LD clobber).
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V4SpecPost sp retAddr d uLo uHi scratchMem) := by
  unfold div128V4SpecPost
  -- Phase 1 intermediates.
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
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
  -- Block 1: Phase 1 (base+1072 → base+1112).
  have hph1 := divK_div128_phase1_spec_within sp retAddr d uLo uHi v1Old v6Old v11Old
    retMem dMem dloMem un0Mem (base + div128Off)
  have hph1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v4_sub 0 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 8 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v4_sub 9 _ _ (by decide) (by bv_addr) (by decide)))))))))))
    hph1
  have hph1f := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) hph1e
  -- Block 2: Step1_v2 (base+1112 → base+1212).
  have hst1 := divK_div128_step1_v2_spec_within sp uHi dHi un1 dLo un0 d dLo (base + div128Off + 40)
  unfold divKDiv128Step1V2Code divKDiv128Step1V2Pre divKDiv128Step1V2Post at hst1
  rw [show (base + div128Off + 40 : Word) + 100 = base + div128Off + 140 from by bv_addr] at hst1
  have hst1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v4_sub 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 11 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 12 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 13 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 14 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 15 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 16 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 17 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 18 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 19 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 20 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 21 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 22 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 23 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 24 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 25 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 26 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 27 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 28 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 29 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 30 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 31 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 32 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 33 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v4_sub 34 _ _ (by decide) (by bv_addr) (by decide))))))))))))))))))))))))))
    hst1
  have hst1f := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) hst1e
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hph1f hst1f
  -- Block 3: compute_un21 (base+1212 → base+1232).
  let x5Exit_st1 := if rhatHi2 = 0 then qDlo2 else qDlo1
  let x1Exit_st1 := if rhatHi2 = 0 then rhatUn1' else rhatHi2
  have hcu := divK_div128_compute_un21_spec_within sp q1'' rhat'' un1 x1Exit_st1 x5Exit_st1 dLo
    (base + div128Off + 140)
  rw [show (base + div128Off + 140 : Word) + 20 = base + div128Off + 160 from by bv_addr] at hcu
  have hcue := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v4_sub 35 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 36 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 37 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 38 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v4_sub 39 _ _ (by decide) (by bv_addr) (by decide))))))
    hcu
  have hcuf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) hcue
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 hcuf
  -- Block 4: step2_v4 (base+1232 → base+1356).
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  have hst2 := divK_div128_step2_v4_spec sp un21 dHi cu_q1_dlo cu_rhat_un1 un1 dLo un0
    scratchMem (base + div128Off + 160)
  unfold divKDiv128Step2V4Code divKDiv128Step2V4Post at hst2
  rw [show (base + div128Off + 160 : Word) + 124 = base + (div128Off + 284) from by bv_addr] at hst2
  have hst2e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.ofProg_mono_sub (base + div128Off) (base + div128Off + 160)
      divK_div128_v4 divKDiv128Step2V4Instrs 40
      (by bv_addr) (by decide) (by decide) (by decide))
    hst2
  have hst2f := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ q1'') ** (.x2 ↦ᵣ retAddr) **
     (sp + signExtend12 3968 ↦ₘ retAddr) ** (sp + signExtend12 3960 ↦ₘ d))
    (by pcFree) hst2e
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hst2f
  -- Block 5: end (base+1356 → retAddr via JALR).
  -- step2_v4's q0'' is x5 from divKDiv128Step2V4Post.
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dLo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo un0
  let x7Exit_step2 := if rhat2cHi ≠ 0 then un21
                      else if rhat2'Hi ≠ 0 then q0Dlo1
                      else q0Dlo2
  let x1Exit_step2 := if rhat2cHi ≠ 0 then rhat2cHi
                      else if rhat2'Hi ≠ 0 then rhat2'Hi
                      else rhat2'Un0
  let x11Exit_step2 := if rhat2cHi ≠ 0 then rhat2c
                       else if rhat2'Hi ≠ 0 then rhat2'
                       else un0
  let mem3936Exit := if rhat2cHi ≠ 0 then scratchMem else rhat2c
  have hend := divK_div128_end_spec_within sp q1'' q0'' retAddr x11Exit_step2 retAddr
    (base + (div128Off + 284)) _halign
  have hende := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v4_sub 71 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 72 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v4_sub 73 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v4_sub 74 _ _ (by decide) (by bv_addr) (by decide)))))
    hend
  have hendf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ x7Exit_step2) ** (.x6 ↦ᵣ dHi) ** (.x1 ↦ᵣ x1Exit_step2) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3952 ↦ₘ dLo) **
     (sp + signExtend12 3944 ↦ₘ un0) ** (sp + signExtend12 3936 ↦ₘ mem3936Exit))
    (by pcFree) hende
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 hendf
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12345

/-- Lifted `div128_v4_spec` over `sharedDivModCode_v4 base` — a thin
    wrapper that lifts the cr from singleton `ofProg`-form to the
    shared cr via `cpsTripleWithin_extend_code` + `shared_b12_div128_v4_sub`.

    Future v4-migrated specs (loop body, full path) will use this
    lifted form. -/
theorem div128_v4_spec_shared (sp retAddr d uLo uHi : Word) (base : Word)
    (v1Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 73 (base + div128Off) retAddr (sharedDivModCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V4SpecPost sp retAddr d uLo uHi scratchMem) :=
  cpsTripleWithin_extend_code (hmono := shared_b12_div128_v4_sub)
    (div128_v4_spec sp retAddr d uLo uHi base v1Old v6Old v11Old
      retMem dMem dloMem un0Mem scratchMem halign)

end EvmAsm.Evm64
