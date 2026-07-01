/-
  EvmAsm.Evm64.DivMod.Compose.FastDigitChainV6Mod

  MOD mirror of `DigitChainV6` over `modCodeV6`: composition of the v6 fast-path
  division digits, threading the running remainder through memory (`uLoOff` of
  digit `k` = `uHiOff` of digit `k-1`). The digit blocks sit at the SAME offsets
  in `modCodeV6` as in `divCodeV6` (the mod-only `divK_fastDenorm` +
  `divK_mod_epilogue` blocks are inserted AFTER the digits), so the chain is the
  DIV proof verbatim with `divCodeV6 → modCodeV6`, the MOD per-digit specs
  (`divK_fastDigit3_full_spec_within_v6_mod`, `divK_fastDigit{2,1,0}_own_spec_within_v6_mod`),
  and the exit landing at `modV6DenormOff` (=436, numerically identical to div's
  `v6EpilogueOff`). The op-agnostic `v6chain{Q,R}*` remainder/quotient
  abbreviations are reused from `DigitChainV6`.
-/

import EvmAsm.Evm64.DivMod.Compose.FastDigitOwnV6Mod
import EvmAsm.Evm64.DivMod.Compose.DigitChainV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- digit3 ;; digit2 over `modCodeV6` (186 steps, `v6Digit3Off` → `v6Digit1Off`). -/
theorem divK_digit32_spec_within_v6_mod
    (sp u4 u3 u2 d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm3 qm2 retMem dMem dloMem un0Mem scratchMem : Word)
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16) :
    cpsTripleWithin 186 (base + v6Digit3Off) (base + v6Digit1Off) (modCodeV6 base)
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
  have h3 := divK_fastDigit3_full_spec_within_v6_mod sp u4 u3 d base
    v2 v5 v6 v7 v9 v10 v11 qm3 retMem dMem dloMem un0Mem scratchMem halign3
  have h3f := cpsTripleWithin_frameR
    (((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4072) ↦ₘ qm2))
    (by pcFree) h3
  rw [show (base + v6Digit3Off + 40 : Word) = base + v6Digit2Off from by bv_addr] at h3f
  have h2 := divK_fastDigit2_own_spec_within_v6_mod sp
    (u3 - div128V5CodeQuot u4 u3 d * d) u2 d base
    (base + v6Digit3Off + 16) (u3 - div128V5CodeQuot u4 u3 d * d)
    (div128V5CodeQuot u4 u3 d * d) d (div128V5CodeQuot u4 u3 d) qm2 halign2
  have h2f := cpsTripleWithin_frameR
    (((sp + signExtend12 4064) ↦ₘ (div128V5CodeQuot u4 u3 d)) ** ((sp + signExtend12 4024) ↦ₘ u4))
    (by pcFree) h2
  rw [show (base + v6Digit2Off + 40 : Word) = base + v6Digit1Off from by bv_addr] at h2f
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h3f h2f

/-- The full four-digit fast-path division chain over `modCodeV6` (372 steps,
    `v6Digit3Off` → `modV6DenormOff`). Same threaded structure as the DIV chain
    `divK_digitChain_spec_within_v6`; only the code surface and the semantic
    successor block (mod's `divK_fastDenorm` at `modV6DenormOff`) differ. -/
theorem divK_digitChain_spec_within_v6_mod
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
    cpsTripleWithin 372 (base + v6Digit3Off) (base + modV6DenormOff) (modCodeV6 base)
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
  have h3 := divK_fastDigit3_full_spec_within_v6_mod sp u4 u3 d base
    v2 v5 v6 v7 v9 v10 v11 qm3 retMem dMem dloMem un0Mem scratchMem halign3
  have h3f := cpsTripleWithin_frameR
    (((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4072) ↦ₘ qm2) **
     ((sp + signExtend12 4080) ↦ₘ qm1) ** ((sp + signExtend12 4088) ↦ₘ qm0))
    (by pcFree) h3
  rw [show (base + v6Digit3Off + 40 : Word) = base + v6Digit2Off from by bv_addr] at h3f
  have h2 := divK_fastDigit2_own_spec_within_v6_mod sp (v6chainR3 u4 u3 d) u2 d base
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
  have h1 := divK_fastDigit1_own_spec_within_v6_mod sp (v6chainR2 u4 u3 u2 d) u1 d base
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
  have h0 := divK_fastDigit0_own_spec_within_v6_mod sp (v6chainR1 u4 u3 u2 u1 d) u0 d base
    (base + v6Digit1Off + 16) (v6chainR1 u4 u3 u2 u1 d) (v6chainQ1 u4 u3 u2 u1 d * d) d
    (v6chainQ1 u4 u3 u2 u1 d) qm0 halign0
  have h0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4064) ↦ₘ (v6chainQ3 u4 u3 d)) ** ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4072) ↦ₘ (v6chainQ2 u4 u3 u2 d)) **
     ((sp + signExtend12 4032) ↦ₘ (v6chainR3 u4 u3 d)) **
     ((sp + signExtend12 4080) ↦ₘ (v6chainQ1 u4 u3 u2 u1 d)) **
     ((sp + signExtend12 4040) ↦ₘ (v6chainR2 u4 u3 u2 d)))
    (by pcFree) h0
  rw [show (base + v6Digit0Off + 40 : Word) = base + modV6DenormOff from by bv_addr] at h0f
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [v6chainR3, v6chainR2, v6chainR1, v6chainQ1] at hp ⊢; xperm_hyp hp)
    h321 h0f

end EvmAsm.Evm64
