/-
  EvmAsm.Evm64.DivMod.Compose.DigitChainV6

  Composition of the v6 fast-path division digits over `divCodeV6`, threading
  the running remainder through memory (`uLoOff` of digit `k` = `uHiOff` of digit
  `k-1`). Built incrementally: `divK_digit32_spec_within_v6` composes digit3 and
  digit2 (the hardest case — digit2 receives digit3's owned registers/scratch).

  Bead `evm-asm-7wbf8.3.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.DigitOwnV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- digit3 ;; digit2 over `divCodeV6` (186 steps, `v6Digit3Off` → `v6Digit1Off`).
    digit3 divides `(u[4], u[3])`, producing quotient digit `Q3` at `q[3]@4064`
    and remainder `rem3 = u[3] -₆₄ Q3·d` at `4032`; digit2 then divides
    `(rem3, u[2])`. The owned registers/scratch thread automatically; digit3's
    output cells (`q[3]@4064`, `u[4]@4024`) and digit2's input cells
    (`u[2]@4040`, `q[2]@4072`) are framed across. -/
theorem divK_digit32_spec_within_v6
    (sp u4 u3 u2 d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm3 qm2 retMem dMem dloMem un0Mem scratchMem : Word)
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16) :
    cpsTripleWithin 186 (base + v6Digit3Off) (base + v6Digit1Off) (divCodeV6 base)
      ((((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem)) **
       ((sp + signExtend12 4064) ↦ₘ qm3)) **
       (((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4072) ↦ₘ qm2)))
      ((((.x12 ↦ᵣ sp) **
        (.x11 ↦ᵣ (div128V5CodeQuot (u3 - div128V5CodeQuot u4 u3 d * d) u2 d)) **
        (.x5 ↦ᵣ (u2 - div128V5CodeQuot (u3 - div128V5CodeQuot u4 u3 d * d) u2 d * d)) **
        (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (div128V5CodeQuot (u3 - div128V5CodeQuot u4 u3 d * d) u2 d * d)) **
        ((sp + signExtend12 4072) ↦ₘ (div128V5CodeQuot (u3 - div128V5CodeQuot u4 u3 d * d) u2 d)) **
        ((sp + signExtend12 4040) ↦ₘ
          (u2 - div128V5CodeQuot (u3 - div128V5CodeQuot u4 u3 d * d) u2 d * d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + v6Digit2Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) **
        ((sp + signExtend12 4032) ↦ₘ (u3 - div128V5CodeQuot u4 u3 d * d)))) **
       (((sp + signExtend12 4064) ↦ₘ (div128V5CodeQuot u4 u3 d)) **
        ((sp + signExtend12 4024) ↦ₘ u4))) := by
  -- digit3 over divCodeV6, framed with digit2's untouched cells.
  have h3 := divK_fastDigit3_full_spec_within_v6 sp u4 u3 d base
    v2 v5 v6 v7 v9 v10 v11 qm3 retMem dMem dloMem un0Mem scratchMem halign3
  have h3f := cpsTripleWithin_frameR
    (((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4072) ↦ₘ qm2))
    (by pcFree) h3
  rw [show (base + v6Digit3Off + 40 : Word) = base + v6Digit2Off from by bv_addr] at h3f
  -- digit2 (own-input form), framed with digit3's output cells.
  have h2 := divK_fastDigit2_own_spec_within_v6 sp
    (u3 - div128V5CodeQuot u4 u3 d * d) u2 d base
    (base + v6Digit3Off + 16) (u3 - div128V5CodeQuot u4 u3 d * d)
    (div128V5CodeQuot u4 u3 d * d) d (div128V5CodeQuot u4 u3 d) qm2 halign2
  have h2f := cpsTripleWithin_frameR
    (((sp + signExtend12 4064) ↦ₘ (div128V5CodeQuot u4 u3 d)) ** ((sp + signExtend12 4024) ↦ₘ u4))
    (by pcFree) h2
  rw [show (base + v6Digit2Off + 40 : Word) = base + v6Digit1Off from by bv_addr] at h2f
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h3f h2f

-- ============================================================================
-- Full 4-digit chain. Threaded quotient digits and remainders (abbreviations
-- keep the depth-4 nesting readable; unfolded at each seq boundary).
-- ============================================================================

/-- Quotient digit `j=3` = `u[4]:u[3] / b0'`. -/
abbrev v6chainQ3 (u4 u3 d : Word) : Word := div128V5CodeQuot u4 u3 d
/-- Remainder after digit 3 (= digit 2's high word). -/
abbrev v6chainR3 (u4 u3 d : Word) : Word := u3 - v6chainQ3 u4 u3 d * d
abbrev v6chainQ2 (u4 u3 u2 d : Word) : Word := div128V5CodeQuot (v6chainR3 u4 u3 d) u2 d
abbrev v6chainR2 (u4 u3 u2 d : Word) : Word := u2 - v6chainQ2 u4 u3 u2 d * d
abbrev v6chainQ1 (u4 u3 u2 u1 d : Word) : Word := div128V5CodeQuot (v6chainR2 u4 u3 u2 d) u1 d
abbrev v6chainR1 (u4 u3 u2 u1 d : Word) : Word := u1 - v6chainQ1 u4 u3 u2 u1 d * d
abbrev v6chainQ0 (u4 u3 u2 u1 u0 d : Word) : Word := div128V5CodeQuot (v6chainR1 u4 u3 u2 u1 d) u0 d
abbrev v6chainR0 (u4 u3 u2 u1 u0 d : Word) : Word := u0 - v6chainQ0 u4 u3 u2 u1 u0 d * d

/-- The full four-digit fast-path division chain over `divCodeV6` (372 steps,
    `v6Digit3Off` → `v6EpilogueOff`). Divides the 5-limb dividend window
    `u[4..0]` by the single normalized limb `d = b0'`, leaving quotient digits
    `q[3..0]` at offsets `4064/4072/4080/4088` (each the exact `div128V5CodeQuot`
    of its window) and the final remainder `r0 = u[0] -₆₄ q[0]·d` at `4056`.
    Clobbered registers and div128 scratch are owned. -/
theorem divK_digitChain_spec_within_v6
    (sp u4 u3 u2 u1 u0 d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm3 qm2 qm1 qm0 retMem dMem dloMem un0Mem scratchMem : Word)
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16)
    (halign1 : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16)
    (halign0 : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 372 (base + v6Digit3Off) (base + v6EpilogueOff) (divCodeV6 base)
      ((((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem)) **
       ((sp + signExtend12 4064) ↦ₘ qm3)) **
       (((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
        ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
        ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0)))
      ((((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (v6chainQ0 u4 u3 u2 u1 u0 d)) **
        (.x5 ↦ᵣ (v6chainR0 u4 u3 u2 u1 u0 d)) ** (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (v6chainQ0 u4 u3 u2 u1 u0 d * d)) **
        ((sp + signExtend12 4088) ↦ₘ (v6chainQ0 u4 u3 u2 u1 u0 d)) **
        ((sp + signExtend12 4056) ↦ₘ (v6chainR0 u4 u3 u2 u1 u0 d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) **
        ((sp + signExtend12 4048) ↦ₘ (v6chainR1 u4 u3 u2 u1 d)))) **
       (((sp + signExtend12 4064) ↦ₘ (v6chainQ3 u4 u3 d)) ** ((sp + signExtend12 4024) ↦ₘ u4) **
        ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 u4 u3 u2 d)) **
        ((sp + signExtend12 4032) ↦ₘ (v6chainR3 u4 u3 d)) **
        ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 u4 u3 u2 u1 d)) **
        ((sp + signExtend12 4040) ↦ₘ (v6chainR2 u4 u3 u2 d)))) := by
  -- digit3, framed with all cells it does not touch.
  have h3 := divK_fastDigit3_full_spec_within_v6 sp u4 u3 d base
    v2 v5 v6 v7 v9 v10 v11 qm3 retMem dMem dloMem un0Mem scratchMem halign3
  have h3f := cpsTripleWithin_frameR
    (((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
     ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0))
    (by pcFree) h3
  rw [show (base + v6Digit3Off + 40 : Word) = base + v6Digit2Off from by bv_addr] at h3f
  -- digit2 (own form), framed with digit3's outputs + digit1/0's cells.
  have h2 := divK_fastDigit2_own_spec_within_v6 sp (v6chainR3 u4 u3 d) u2 d base
    (base + v6Digit3Off + 16) (v6chainR3 u4 u3 d) (v6chainQ3 u4 u3 d * d) d (v6chainQ3 u4 u3 d)
    qm2 halign2
  have h2f := cpsTripleWithin_frameR
    (((sp + signExtend12 4064) ↦ₘ (v6chainQ3 u4 u3 d)) ** ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4048) ↦ₘ u1) ** ((sp + signExtend12 4056) ↦ₘ u0) **
     ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0))
    (by pcFree) h2
  rw [show (base + v6Digit2Off + 40 : Word) = base + v6Digit1Off from by bv_addr] at h2f
  have h32 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [v6chainR3, v6chainQ3] at hp ⊢; xperm_hyp hp) h3f h2f
  -- digit1 (own form), framed with digit3/2's outputs + digit0's cells.
  have h1 := divK_fastDigit1_own_spec_within_v6 sp (v6chainR2 u4 u3 u2 d) u1 d base
    (base + v6Digit2Off + 16) (v6chainR2 u4 u3 u2 d) (v6chainQ2 u4 u3 u2 d * d) d
    (v6chainQ2 u4 u3 u2 d) qm1 halign1
  have h1f := cpsTripleWithin_frameR
    (((sp + signExtend12 4064) ↦ₘ (v6chainQ3 u4 u3 d)) ** ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 u4 u3 u2 d)) **
     ((sp + signExtend12 4032) ↦ₘ (v6chainR3 u4 u3 d)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4088) ↦ₘ qm0))
    (by pcFree) h1
  rw [show (base + v6Digit1Off + 40 : Word) = base + v6Digit0Off from by bv_addr] at h1f
  have h321 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [v6chainR3, v6chainR2, v6chainQ2] at hp ⊢; xperm_hyp hp) h32 h1f
  -- digit0 (own form), framed with all earlier outputs.
  have h0 := divK_fastDigit0_own_spec_within_v6 sp (v6chainR1 u4 u3 u2 u1 d) u0 d base
    (base + v6Digit1Off + 16) (v6chainR1 u4 u3 u2 u1 d) (v6chainQ1 u4 u3 u2 u1 d * d) d
    (v6chainQ1 u4 u3 u2 u1 d) qm0 halign0
  have h0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4064) ↦ₘ (v6chainQ3 u4 u3 d)) ** ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 u4 u3 u2 d)) **
     ((sp + signExtend12 4032) ↦ₘ (v6chainR3 u4 u3 d)) **
     ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 u4 u3 u2 u1 d)) **
     ((sp + signExtend12 4040) ↦ₘ (v6chainR2 u4 u3 u2 d)))
    (by pcFree) h0
  rw [show (base + v6Digit0Off + 40 : Word) = base + v6EpilogueOff from by bv_addr] at h0f
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [v6chainR3, v6chainR2, v6chainR1, v6chainQ1] at hp ⊢; xperm_hyp hp)
    h321 h0f

end EvmAsm.Evm64
