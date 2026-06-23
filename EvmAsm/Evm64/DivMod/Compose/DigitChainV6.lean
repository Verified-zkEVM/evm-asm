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

end EvmAsm.Evm64
