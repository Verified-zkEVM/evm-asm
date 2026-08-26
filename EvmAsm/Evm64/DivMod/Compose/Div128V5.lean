/-
  EvmAsm.Evm64.DivMod.Compose.Div128V5

  div128 subroutine composition for the v5 algorithm — the capped Knuth
  Algorithm D that repairs v4's two buggy ULTs by clamping `q1c`/`q0c` at
  `2^32 - 1` (Knuth's classical b-1 cap) and guarding the Phase-1b/2b
  1st-correction ULTs with `rhat(c) >> 32 = 0`.

  Mirror of `Compose/Div128V4.lean` (`div128_v4_spec`, lines 151-335),
  composing the v5 full step blocks:
    * Phase 1            [0..9]   (base+div128Off → +40)   — version-agnostic
    * Step 1 v5          [10..40] (+40 → +164)             — divK_div128_step1_v5_spec_within
    * compute_un21       [41..45] (+164 → +184)            — version-agnostic
    * Step 2 v5          [46..80] (+184 → +324)            — divK_div128_step2_v5_spec_within
    * end                [81..84] (+324 → retAddr)         — version-agnostic
  Total: 85 instructions (vs v4's 75).

  Bead `evm-asm-wbc4i.6.14` (V5.6.15) / `evm-asm-wbc4i.6` (V5.6).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.Div128V4
public import EvmAsm.Evm64.DivMod.Compose.V5Code
public import EvmAsm.Evm64.DivMod.Compose.Div128V5CodeBridge
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1FullV5
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2FullV5

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 15-v5: div128 subroutine composition (v5 capped algorithm).
-- ============================================================================

/-- Bundled postcondition for `div128_v5_spec`.

    Mirrors `div128V4SpecPost` but with v5 cap semantics: `q1c`/`q0c` clamp
    to `2^32 - 1` (`q1cCap := (allOnes 64) >>> 32`) rather than `q - 1`, the
    remainder is recomputed as `rhat + (q - cap) * dHi`, and the Phase-1b/2b
    body conditionals come from the v5 step `PostFromBody` defs.

    The 3-path `x7`/`x9`/`mem3936` exit values are taken directly from
    `divKDiv128Step2FullV5PostFromBody` (the step-2 block post); `q1''`/`q0''`
    are the final corrected trial quotients; `q := (q1'' <<< 32) ||| q0''`.

    `@[irreducible]` to keep the let-chain out of the theorem signature. -/
@[irreducible]
def div128V5SpecPost (sp retAddr d uLo uHi scratchMem : Word) : Assertion :=
  -- Phase 1 splits.
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  -- Step 1 v5 (Phase-1a cap + Phase-1b body), mirrors divKDiv128Step1FullV5Post.
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else cap
  let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  let qDlo1 := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
  let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
  let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := bq1' * dLo
  let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
  let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + dHi else brhat'
  let q1Final := if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1')
  let rhatFinal := if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat')
  -- compute_un21 (version-agnostic): un21 = (rhatFinal << 32 | un1) - q1Final * dLo.
  let un21 := ((rhatFinal <<< (32 : BitVec 6).toNat) ||| un1) - q1Final * dLo
  -- Step 2 v5 (Phase-2a cap + Phase-2b body), mirrors divKDiv128Step2FullV5Post.
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else cap
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi
  let x7o := if hi2 = 0 then un21 else (q0 - cap) * dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let bq0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
  let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := bq0' * dLo
  let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := if BitVec.ult rhat2'Un0 q0Dlo2 then bq0' + signExtend12 4095 else bq0'
  let q0Final := if rhat2cHi ≠ 0 then q0c else (if brhat2'Hi = 0 then q0'' else bq0')
  let x7Exit := if rhat2cHi ≠ 0 then x7o else (if brhat2'Hi = 0 then q0Dlo2 else q0Dlo1)
  let x9Exit := if rhat2cHi ≠ 0 then rhat2cHi else (if brhat2'Hi = 0 then rhat2'Un0 else brhat2'Hi)
  let mem3936Exit := if rhat2cHi ≠ 0 then scratchMem else rhat2c
  let q := (q1Final <<< (32 : BitVec 6).toNat) ||| q0Final
  (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ q1Final) **
  (.x5 ↦ᵣ q0Final) ** (.x7 ↦ᵣ x7Exit) **
  (.x6 ↦ᵣ dHi) ** (.x9 ↦ᵣ x9Exit) ** (.x11 ↦ᵣ q) **
  (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ retAddr) **
  (sp + signExtend12 3960 ↦ₘ d) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ mem3936Exit)

/-- Equivalence between `divK_div128_v5` (capped Knuth D RISC-V) and the
    val256 view. Mirror of `div128_v4_spec`. -/
theorem div128_v5_spec (sp retAddr d uLo uHi : Word) (base : Word)
    (v9Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (_halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 83 (base + div128Off) retAddr
      (CodeReq.ofProg (base + div128Off) divK_div128_v5)
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V5SpecPost sp retAddr d uLo uHi scratchMem) := by
  unfold div128V5SpecPost
  -- Phase 1 splits.
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  -- Step 1 v5 intermediates (mirror divKDiv128Step1FullV5Post).
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else cap
  let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  let qDlo1 := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
  let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
  let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := bq1' * dLo
  let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
  let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + dHi else brhat'
  let q1Final := if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1')
  let rhatFinal := if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat')
  let x5Exit1 := if rhatcHi ≠ 0 then (if hi1 = 0 then hi1 else cap) else (if brhat'Hi = 0 then qDlo2 else qDlo1)
  let x9Exit1 := if rhatcHi ≠ 0 then rhatcHi else (if brhat'Hi = 0 then rhatUn1' else brhat'Hi)
  -- compute_un21 outputs.
  let un21 := ((rhatFinal <<< (32 : BitVec 6).toNat) ||| un1) - q1Final * dLo
  let cuRhatUn1 := (rhatFinal <<< (32 : BitVec 6).toNat) ||| un1
  let cuQ1Dlo := q1Final * dLo
  -- Step 2 v5 intermediates (mirror divKDiv128Step2FullV5Post).
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else cap
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi
  let x7o := if hi2 = 0 then un21 else (q0 - cap) * dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let bq0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
  let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := bq0' * dLo
  let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := if BitVec.ult rhat2'Un0 q0Dlo2 then bq0' + signExtend12 4095 else bq0'
  let q0Final := if rhat2cHi ≠ 0 then q0c else (if brhat2'Hi = 0 then q0'' else bq0')
  let x7Exit2 := if rhat2cHi ≠ 0 then x7o else (if brhat2'Hi = 0 then q0Dlo2 else q0Dlo1)
  let x9Exit2 := if rhat2cHi ≠ 0 then rhat2cHi else (if brhat2'Hi = 0 then rhat2'Un0 else brhat2'Hi)
  let x11Exit2 := if rhat2cHi ≠ 0 then rhat2c else (if brhat2'Hi = 0 then un0 else brhat2')
  let mem3936Exit := if rhat2cHi ≠ 0 then scratchMem else rhat2c
  -- Block 1: Phase 1 (base+div128Off → +40).
  have hph1 := divK_div128_phase1_spec_within sp retAddr d uLo uHi v9Old v6Old v11Old
    retMem dMem dloMem un0Mem (base + div128Off)
  have hph1e := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v5_sub 0 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 8 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v5_sub 9 _ _ (by decide) (by bv_addr) (by decide)))))))))))
    hph1
  have hph1f := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) hph1e
  -- Block 2: Step1 v5 (base+div128Off+40 → +164).
  have hst1 := divK_div128_step1_v5_spec_within sp uHi dHi un1 d un0 dLo dLo
    (base + div128Off + 40)
  simp only [divKDiv128Step1FullV5Pre, divKDiv128Step1FullV5Post,
    divKDiv128Step1FullV5PostFromBody, divKDiv128Step1FullV5PostCore] at hst1
  rw [show (base + div128Off + 40 : Word) + 124 = base + div128Off + 164 from by bv_addr] at hst1
  have hst1e := cpsTripleWithin_extend_code (hmono := step1FullV5Code_sub_v5) hst1
  have hst1f := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) hst1e
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hph1f hst1f
  -- Block 3: compute_un21 (base+div128Off+164 → +184).
  have hcu := divK_div128_compute_un21_spec_within sp q1Final rhatFinal un1 x9Exit1 x5Exit1 dLo
    (base + div128Off + 164)
  rw [show (base + div128Off + 164 : Word) + 20 = base + div128Off + 184 from by bv_addr] at hcu
  have hcue := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v5_sub 41 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 42 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 43 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 44 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v5_sub 45 _ _ (by decide) (by bv_addr) (by decide))))))
    hcu
  have hcuf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ retAddr) ** (sp + signExtend12 3968 ↦ₘ retAddr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ scratchMem))
    (by pcFree) hcue
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 hcuf
  -- Block 4: step2 v5 (base+div128Off+184 → +324).
  have hst2 := divK_div128_step2_v5_spec_within sp un21 dHi un0 dLo cuRhatUn1 cuQ1Dlo un1 scratchMem
    (base + div128Off + 184)
  simp only [divKDiv128Step2FullV5Pre, divKDiv128Step2FullV5Post,
    divKDiv128Step2FullV5PostFromBody, divKDiv128Step2FullV5PostCore] at hst2
  rw [show (base + div128Off + 184 : Word) + 140 = base + div128Off + 324 from by bv_addr] at hst2
  have hst2e := cpsTripleWithin_extend_code (hmono := step2FullV5Code_sub_v5) hst2
  have hst2f := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ q1Final) ** (.x2 ↦ᵣ retAddr) **
     (sp + signExtend12 3968 ↦ₘ retAddr) ** (sp + signExtend12 3960 ↦ₘ d))
    (by pcFree) hst2e
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hst2f
  -- Block 5: end (base+div128Off+324 → retAddr via JALR).
  have hend := divK_div128_end_spec_within sp q1Final q0Final retAddr x11Exit2 retAddr
    (base + div128Off + 324) _halign
  have hende := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (d128_v5_sub 81 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 82 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (d128_v5_sub 83 _ _ (by decide) (by bv_addr) (by decide))
      (d128_v5_sub 84 _ _ (by decide) (by bv_addr) (by decide)))))
    hend
  have hendf := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ x7Exit2) ** (.x6 ↦ᵣ dHi) ** (.x9 ↦ᵣ x9Exit2) **
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

/-- Lifted `div128_v5_spec` over `sharedDivModCode_v5 base`. -/
theorem div128_v5_spec_shared (sp retAddr d uLo uHi : Word) (base : Word)
    (v9Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 83 (base + div128Off) retAddr (sharedDivModCode_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V5SpecPost sp retAddr d uLo uHi scratchMem) :=
  cpsTripleWithin_extend_code (hmono := shared_b12_div128_v5_sub)
    (div128_v5_spec sp retAddr d uLo uHi base v9Old v6Old v11Old
      retMem dMem dloMem un0Mem scratchMem halign)

/-- Lifted `div128_v5_spec` over `sharedDivModCodeNoNop_v5 base`. -/
theorem div128_v5_spec_shared_noNop (sp retAddr d uLo uHi : Word) (base : Word)
    (v9Old v6Old v11Old : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : (retAddr + signExtend12 0) &&& ~~~1 = retAddr) :
    cpsTripleWithin 83 (base + div128Off) retAddr (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ uLo) ** (.x7 ↦ᵣ uHi) **
       (.x6 ↦ᵣ v6Old) ** (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (div128V5SpecPost sp retAddr d uLo uHi scratchMem) :=
  cpsTripleWithin_extend_code (hmono := sharedNoNop_b11_div128_v5_sub)
    (div128_v5_spec sp retAddr d uLo uHi base v9Old v6Old v11Old
      retMem dMem dloMem un0Mem scratchMem halign)

end EvmAsm.Evm64
