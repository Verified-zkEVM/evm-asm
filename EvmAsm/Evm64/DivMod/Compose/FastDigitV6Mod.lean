/-
  EvmAsm.Evm64.DivMod.Compose.FastDigitV6Mod

  MOD v6 single-digit lift over `modCodeV6` (Brick 2 of the MOD v6 fast arm).
  Mirror of `DigitV6.lean` (over `divCodeV6`): the fast-path digit step
  (`divK_fastDigit_full_spec_within`, 93 steps over a 4-way union bundle) lifted
  onto `modCodeV6`, at each of the four digit offsets.  Two differences from
  DIV: (1) the digit-block JAL displacements are 216/176/136/96 (vs div's
  188/148/108/68), because the fast path's own `divK_div128_v5` copy sits at
  `modV6Div128Off=504` (vs `v6Div128Off=476`); (2) the block list is
  `modCodeV6` (div128 is block index 11, past the inserted fastDenorm +
  mod_epilogue) so the div128/digit code-subsumption uses `skipBlockV6Mod`.
  The 93-step core spec and its intra-bundle disjointness obligations are
  op-agnostic and reused verbatim.
-/

import EvmAsm.Evm64.DivMod.Compose.FastPrefixV6Mod
import EvmAsm.Evm64.DivMod.LimbSpec.FastN1

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Code subsumption into modCodeV6: div128 copy (block index 11) and the four
-- digit blocks (indices 5-8).
-- ============================================================================

theorem div128_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + modV6Div128Off) divK_div128_v5) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  skipBlockV6Mod
  exact CodeReq.union_mono_left

theorem divK_digit3_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit3Off) (divK_fastDigit 4024 4032 4064 216)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

theorem divK_digit2_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit2Off) (divK_fastDigit 4032 4040 4072 176)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

theorem divK_digit1_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit1Off) (divK_fastDigit 4040 4048 4080 136)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  skipBlockV6Mod
  exact CodeReq.union_mono_left

theorem divK_digit0_code_sub_modCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit0Off) (divK_fastDigit 4048 4056 4088 96)) a = some i →
      (modCodeV6 base) a = some i := by
  unfold modCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod; skipBlockV6Mod
  skipBlockV6Mod; skipBlockV6Mod
  exact CodeReq.union_mono_left

-- ============================================================================
-- Generic single-digit lift over modCodeV6.  Mirror of
-- `divK_fastDigit_full_spec_within_v6` (DigitV6.lean:85).
-- ============================================================================

private theorem modV6_divBase_eq {base : Word} :
    (base + modV6Div128Off - div128Off) + div128Off = base + modV6Div128Off := by
  simp only [modV6Div128Off, div128Off]; bv_omega

theorem divK_fastDigit_full_spec_within_v6_mod
    (sp uHi uLo d base digitOff : Word) (uHiOff uLoOff qOff : BitVec 12) (callOff : BitVec 21)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (hcode_sub : ∀ a i,
      (CodeReq.ofProg (base + digitOff) (divK_fastDigit uHiOff uLoOff qOff callOff)) a = some i →
      (modCodeV6 base) a = some i)
    (htarget : (base + digitOff + 12) + signExtend21 callOff
      = (base + modV6Div128Off - div128Off) + div128Off)
    (halign : ((base + digitOff + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + digitOff + 16)
    (hdisj_loads : (divK_fastDigit_loads_code uHiOff uLoOff (base + digitOff)).Disjoint
      ((CodeReq.singleton (base + digitOff + 12) (.JAL .x2 callOff)).union
        (CodeReq.ofProg ((base + modV6Div128Off - div128Off) + div128Off) divK_div128_v5)))
    (hdisj_jal : (CodeReq.singleton (base + digitOff + 12) (.JAL .x2 callOff)).Disjoint
      (CodeReq.ofProg ((base + modV6Div128Off - div128Off) + div128Off) divK_div128_v5))
    (hdisj_post : (((divK_fastDigit_loads_code uHiOff uLoOff (base + digitOff)).union
      ((CodeReq.singleton (base + digitOff + 12) (.JAL .x2 callOff)).union
        (CodeReq.ofProg ((base + modV6Div128Off - div128Off) + div128Off) divK_div128_v5))).Disjoint
      (divK_fastDigit_post_code uLoOff qOff (base + digitOff + 16)))) :
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
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 uHiOff) ↦ₘ uHi))) := by
  have core := divK_fastDigit_full_spec_within
    sp uHi uLo d uHiOff uLoOff qOff callOff (base + digitOff) (base + modV6Div128Off - div128Off)
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    htarget halign hdisj_loads hdisj_jal hdisj_post
  refine cpsTripleWithin_extend_code (hmono := ?_) core
  refine CodeReq.union_sub (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ ?_)) ?_
  · intro a i h
    exact hcode_sub a i
      (CodeReq.ofProg_mono_sub (base + digitOff) (base + digitOff)
        (divK_fastDigit uHiOff uLoOff qOff callOff)
        [.LD .x7 .x12 uHiOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984] 0 (by bv_omega) rfl
        (by simp only [divK_fastDigit_length, List.length_cons, List.length_nil]; omega)
        (by rw [divK_fastDigit_length]; omega) a i h)
  · intro a i h
    exact hcode_sub a i
      (CodeReq.singleton_mono (by
        have hl := CodeReq.ofProg_lookup (base + digitOff) (divK_fastDigit uHiOff uLoOff qOff callOff) 3
          (by rw [divK_fastDigit_length]; omega) (by rw [divK_fastDigit_length]; omega)
        rw [show (base + digitOff : Word) + BitVec.ofNat 64 (4 * 3) = base + digitOff + 12
          from by bv_addr] at hl
        exact hl) a i h)
  · rw [modV6_divBase_eq]; exact div128_code_sub_modCodeV6
  · intro a i h
    exact hcode_sub a i
      (CodeReq.ofProg_mono_sub (base + digitOff) (base + digitOff + 16)
        (divK_fastDigit uHiOff uLoOff qOff callOff)
        [.SD .x12 .x11 qOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984,
         .MUL .x7 .x11 .x10, .SUB .x5 .x5 .x7, .SD .x12 .x5 uLoOff] 4 (by bv_omega) rfl
        (by simp only [divK_fastDigit_length, List.length_cons, List.length_nil]; omega)
        (by rw [divK_fastDigit_length]; omega) a i h)

-- ============================================================================
-- The four concrete digit lifts (digit3..digit0) over modCodeV6.
-- ============================================================================

theorem divK_fastDigit3_full_spec_within_v6_mod
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16) :
    cpsTripleWithin 93 (base + v6Digit3Off) (base + v6Digit3Off + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4024) ↦ₘ uHi) ** ((sp + signExtend12 4032) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem)) **
       ((sp + signExtend12 4064) ↦ₘ qm))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ (div128V5CodeQuot uHi uLo d)) **
        (.x5 ↦ᵣ (uLo - div128V5CodeQuot uHi uLo d * d)) ** (.x10 ↦ᵣ d) **
        (.x7 ↦ᵣ (div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 4064) ↦ₘ (div128V5CodeQuot uHi uLo d)) **
        ((sp + signExtend12 4032) ↦ₘ (uLo - div128V5CodeQuot uHi uLo d * d)) **
        ((sp + signExtend12 3984) ↦ₘ d)) **
       ((.x2 ↦ᵣ (base + v6Digit3Off + 16)) ** regOwn .x6 ** regOwn .x9 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp + signExtend12 3968) ** memOwn (sp + signExtend12 3960) **
        memOwn (sp + signExtend12 3952) ** memOwn (sp + signExtend12 3944) **
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 4024) ↦ₘ uHi))) := by
  refine divK_fastDigit_full_spec_within_v6_mod sp uHi uLo d base v6Digit3Off 4024 4032 4064 216
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit3_code_sub_modCodeV6 ?_ halign ?_ ?_ ?_
  · rw [modV6_divBase_eq]; have h : signExtend21 (216 : BitVec 21) = (216 : Word) := by decide
    rw [h]; simp only [v6Digit3Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit3Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit3Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit3Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit3Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit3Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit3Off, modV6Div128Off] at h1 h2 ⊢
      bv_omega

theorem divK_fastDigit2_full_spec_within_v6_mod
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16) :
    cpsTripleWithin 93 (base + v6Digit2Off) (base + v6Digit2Off + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4032) ↦ₘ uHi) ** ((sp + signExtend12 4040) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem)) **
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
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 4032) ↦ₘ uHi))) := by
  refine divK_fastDigit_full_spec_within_v6_mod sp uHi uLo d base v6Digit2Off 4032 4040 4072 176
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit2_code_sub_modCodeV6 ?_ halign ?_ ?_ ?_
  · rw [modV6_divBase_eq]; have h : signExtend21 (176 : BitVec 21) = (176 : Word) := by decide
    rw [h]; simp only [v6Digit2Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit2Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit2Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit2Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit2Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit2Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit2Off, modV6Div128Off] at h1 h2 ⊢
      bv_omega

theorem divK_fastDigit1_full_spec_within_v6_mod
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16) :
    cpsTripleWithin 93 (base + v6Digit1Off) (base + v6Digit1Off + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4040) ↦ₘ uHi) ** ((sp + signExtend12 4048) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem)) **
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
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 4040) ↦ₘ uHi))) := by
  refine divK_fastDigit_full_spec_within_v6_mod sp uHi uLo d base v6Digit1Off 4040 4048 4080 136
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit1_code_sub_modCodeV6 ?_ halign ?_ ?_ ?_
  · rw [modV6_divBase_eq]; have h : signExtend21 (136 : BitVec 21) = (136 : Word) := by decide
    rw [h]; simp only [v6Digit1Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit1Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit1Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit1Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit1Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit1Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit1Off, modV6Div128Off] at h1 h2 ⊢
      bv_omega

theorem divK_fastDigit0_full_spec_within_v6_mod
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 93 (base + v6Digit0Off) (base + v6Digit0Off + 40) (modCodeV6 base)
      (((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 4048) ↦ₘ uHi) ** ((sp + signExtend12 4056) ↦ₘ uLo) **
        ((sp + signExtend12 3984) ↦ₘ d) **
        (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ un0Mem) **
        (sp + signExtend12 3936 ↦ₘ scratchMem)) **
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
        memOwn (sp + signExtend12 3936) ** ((sp + signExtend12 4048) ↦ₘ uHi))) := by
  refine divK_fastDigit_full_spec_within_v6_mod sp uHi uLo d base v6Digit0Off 4048 4056 4088 96
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit0_code_sub_modCodeV6 ?_ halign ?_ ?_ ?_
  · rw [modV6_divBase_eq]; have h : signExtend21 (96 : BitVec 21) = (96 : Word) := by decide
    rw [h]; simp only [v6Digit0Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit0Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit0Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit0Off, modV6Div128Off]; bv_omega
  · rw [modV6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit0Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit0Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit0Off, modV6Div128Off] at h1 h2 ⊢
      bv_omega

end EvmAsm.Evm64
