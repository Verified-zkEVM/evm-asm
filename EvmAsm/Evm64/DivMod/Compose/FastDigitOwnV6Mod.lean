/-
  EvmAsm.Evm64.DivMod.Compose.FastDigitOwnV6Mod

  MOD mirror of `DigitOwnV6` over `modCodeV6`: own-input variants of the v6
  fast-path digit lifts. For digits 2/1/0 — which receive the previous digit's
  *owned* clobbered registers (`x6`, `x9`) and *owned* div128 scratch cells — the
  precondition's `regIs`/`memIs` atoms for those 7 cells are lifted to
  `regOwn`/`memOwn`, so each digit's PRE matches the previous digit's POST.

  The generic own-lift proof is pure ownership peeling (code-surface agnostic),
  so it is the DIV proof verbatim with `divCodeV6 → modCodeV6`; the three concrete
  lifts instantiate it with the MOD per-digit `_full` specs
  (`divK_fastDigit{2,1,0}_full_spec_within_v6_mod`, `FastDigitV6Mod`).
-/

import EvmAsm.Evm64.DivMod.Compose.FastDigitV6Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Generic own-input digit lift over `modCodeV6`: from the full digit lift
    (universally quantified over the clobbered inputs), expose `x6`/`x9` as
    `regOwn` and the five scratch cells as `memOwn`. -/
theorem divK_fastDigit_own_spec_within_v6_mod
    (sp uHi uLo d base digitOff : Word) (uHiOff uLoOff qOff : BitVec 12)
    (v2 v5 v7 v10 v11 qm : Word)
    (hfull : ∀ v6 v9 retMem dMem dloMem un0Mem scratchMem,
      cpsTripleWithin 93 (base + digitOff) (base + digitOff + 40) (modCodeV6 base)
        (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
          ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
          ((sp + signExtend12 3984) ↦ₘ d) **
          (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
          (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
          (sp + signExtend12 3936 ↦ₘ scratchMem)) **
         ((sp + signExtend12 qOff) ↦ₘ qm))
        (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (div128V5CodeQuot uHi uLo d)) **
          (.x5 ↦ᵣ (uLo - div128V5CodeQuot uHi uLo d * d)) ** (.x10 ↦ᵣ d) **
          (.x7 ↦ᵣ (div128V5CodeQuot uHi uLo d * d)) **
          ((sp + signExtend12 qOff) ↦ₘ (div128V5CodeQuot uHi uLo d)) **
          ((sp + signExtend12 uLoOff) ↦ₘ (uLo - div128V5CodeQuot uHi uLo d * d)) **
          ((sp + signExtend12 3984) ↦ₘ d)) **
         ((.x2 ↦ᵣ (base + digitOff + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
          memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
          memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
          memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 uHiOff) ↦ₘ uHi)))) :
    cpsTripleWithin 93 (base + digitOff) (base + digitOff + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
        regOwn .x9 ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936)) **
       ((sp + signExtend12 qOff) ↦ₘ qm))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (div128V5CodeQuot uHi uLo d)) **
        (.x5 ↦ᵣ (uLo - div128V5CodeQuot uHi uLo d * d)) ** (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 qOff) ↦ₘ (div128V5CodeQuot uHi uLo d)) **
        ((sp + signExtend12 uLoOff) ↦ₘ (uLo - div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + digitOff + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 uHiOff) ↦ₘ uHi))) := by
  -- Peel x6.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** regOwn .x9 **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 qOff) ↦ₘ qm))
      (r := .x6) (fun v6 => ?_))
  -- Peel x9.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 qOff) ↦ₘ qm))
      (r := .x9) (fun v9 => ?_))
  -- Peel scratch 3968.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        memOwn (sp + signExtend12 3960) ** memOwn (sp + signExtend12 3952) **
        memOwn (sp + signExtend12 3944) ** memOwn (sp + signExtend12 3936) **
        ((sp + signExtend12 qOff) ↦ₘ qm))
      (a := sp + signExtend12 3968) (fun w68 => ?_))
  -- Peel scratch 3960.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) ** (sp + signExtend12 3968 ↦ₘ w68) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 qOff) ↦ₘ qm))
      (a := sp + signExtend12 3960) (fun w60 => ?_))
  -- Peel scratch 3952.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) ** (sp + signExtend12 3968 ↦ₘ w68) **
        (sp + signExtend12 3960 ↦ₘ w60) **
        memOwn (sp + signExtend12 3944) ** memOwn (sp + signExtend12 3936) **
        ((sp + signExtend12 qOff) ↦ₘ qm))
      (a := sp + signExtend12 3952) (fun w52 => ?_))
  -- Peel scratch 3944.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) ** (sp + signExtend12 3968 ↦ₘ w68) **
        (sp + signExtend12 3960 ↦ₘ w60) ** (sp + signExtend12 3952 ↦ₘ w52) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 qOff) ↦ₘ qm))
      (a := sp + signExtend12 3944) (fun w44 => ?_))
  -- Peel scratch 3936, then discharge with the full lift.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_memIs_to_memOwn
      (P := (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 uHiOff) ↦ₘ uHi) ** ((sp + signExtend12 uLoOff) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) ** (sp + signExtend12 3968 ↦ₘ w68) **
        (sp + signExtend12 3960 ↦ₘ w60) ** (sp + signExtend12 3952 ↦ₘ w52) **
        (sp + signExtend12 3944 ↦ₘ w44) ** ((sp + signExtend12 qOff) ↦ₘ qm))
      (a := sp + signExtend12 3936) (fun w36 => ?_))
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (hfull v6 v9 w68 w60 w52 w44 w36)

-- ============================================================================
-- The three concrete own-input digit lifts (digit2/1/0) over `modCodeV6`.
-- ============================================================================

theorem divK_fastDigit2_own_spec_within_v6_mod
    (sp uHi uLo d base : Word) (v2 v5 v7 v10 v11 qm : Word)
    (halign : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16) :
    cpsTripleWithin 93 (base + v6Digit2Off) (base + v6Digit2Off + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
        regOwn .x9 ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4032) ↦ₘ uHi) ** ((sp + signExtend12 4040) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936)) **
       ((sp + signExtend12 4072) ↦ₘ qm))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (div128V5CodeQuot uHi uLo d)) **
        (.x5 ↦ᵣ (uLo - div128V5CodeQuot uHi uLo d * d)) ** (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 4072) ↦ₘ (div128V5CodeQuot uHi uLo d)) **
        ((sp + signExtend12 4040) ↦ₘ (uLo - div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + v6Digit2Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 4032) ↦ₘ uHi))) :=
  divK_fastDigit_own_spec_within_v6_mod sp uHi uLo d base v6Digit2Off 4032 4040 4072
    v2 v5 v7 v10 v11 qm
    (fun v6 v9 retMem dMem dloMem un0Mem scratchMem =>
      divK_fastDigit2_full_spec_within_v6_mod sp uHi uLo d base v2 v5 v6 v7 v9 v10 v11 qm
        retMem dMem dloMem un0Mem scratchMem halign)

theorem divK_fastDigit1_own_spec_within_v6_mod
    (sp uHi uLo d base : Word) (v2 v5 v7 v10 v11 qm : Word)
    (halign : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16) :
    cpsTripleWithin 93 (base + v6Digit1Off) (base + v6Digit1Off + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
        regOwn .x9 ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4040) ↦ₘ uHi) ** ((sp + signExtend12 4048) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936)) **
       ((sp + signExtend12 4080) ↦ₘ qm))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (div128V5CodeQuot uHi uLo d)) **
        (.x5 ↦ᵣ (uLo - div128V5CodeQuot uHi uLo d * d)) ** (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 4080) ↦ₘ (div128V5CodeQuot uHi uLo d)) **
        ((sp + signExtend12 4048) ↦ₘ (uLo - div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + v6Digit1Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 4040) ↦ₘ uHi))) :=
  divK_fastDigit_own_spec_within_v6_mod sp uHi uLo d base v6Digit1Off 4040 4048 4080
    v2 v5 v7 v10 v11 qm
    (fun v6 v9 retMem dMem dloMem un0Mem scratchMem =>
      divK_fastDigit1_full_spec_within_v6_mod sp uHi uLo d base v2 v5 v6 v7 v9 v10 v11 qm
        retMem dMem dloMem un0Mem scratchMem halign)

theorem divK_fastDigit0_own_spec_within_v6_mod
    (sp uHi uLo d base : Word) (v2 v5 v7 v10 v11 qm : Word)
    (halign : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 93 (base + v6Digit0Off) (base + v6Digit0Off + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
        regOwn .x9 ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4048) ↦ₘ uHi) ** ((sp + signExtend12 4056) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936)) **
       ((sp + signExtend12 4088) ↦ₘ qm))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (div128V5CodeQuot uHi uLo d)) **
        (.x5 ↦ᵣ (uLo - div128V5CodeQuot uHi uLo d * d)) ** (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 4088) ↦ₘ (div128V5CodeQuot uHi uLo d)) **
        ((sp + signExtend12 4056) ↦ₘ (uLo - div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + v6Digit0Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 4048) ↦ₘ uHi))) :=
  divK_fastDigit_own_spec_within_v6_mod sp uHi uLo d base v6Digit0Off 4048 4056 4088
    v2 v5 v7 v10 v11 qm
    (fun v6 v9 retMem dMem dloMem un0Mem scratchMem =>
      divK_fastDigit0_full_spec_within_v6_mod sp uHi uLo d base v2 v5 v6 v7 v9 v10 v11 qm
        retMem dMem dloMem un0Mem scratchMem halign)

end EvmAsm.Evm64
