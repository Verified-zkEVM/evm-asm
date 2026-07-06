/-
  EvmAsm.Evm64.DivMod.Compose.DigitV6

  v6 single-digit lift: the complete fast-path digit step
  (`divK_fastDigit_full_spec_within`, a 93-step triple over a 4-way union code
  bundle) lifted onto the full `divCodeV6` bundle, at each of the four digit
  offsets (digit3..digit0). The fast path's own `divK_div128_v5` copy lives in a
  separate block (`v6Div128Off`); the digit's loads/JAL/post live in the digit
  block. Routing both into `divCodeV6` is via the `skipBlockV6` macro
  (`CLZV6.lean`) + `CodeReq.union_sub` / `ofProg_mono_sub` / `ofProg_lookup`.

  Bead `evm-asm-7wbf8.3.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.CLZV6
import EvmAsm.Evm64.DivMod.LimbSpec.FastN1

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Code subsumption: div128 copy (block index 10) and the four digit blocks
-- (indices 5-8) into divCodeV6.
-- ============================================================================

/-- The fast path's own `divK_div128_v5` copy (block index 10 of `divCodeV6`) is
    subsumed by `divCodeV6`. 10 `skipBlockV6` (it follows the dispatch, clz,
    setup, normA, copyAU, 4 digits, epilogue). -/
theorem div128_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Div128Off) divK_div128_v5) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6
  skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6
  exact CodeReq.union_mono_left

theorem divK_digit3_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit3Off) (divK_fastDigit 4024 4032 4064 188)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6
  exact CodeReq.union_mono_left

theorem divK_digit2_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit2Off) (divK_fastDigit 4032 4040 4072 148)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6
  exact CodeReq.union_mono_left

theorem divK_digit1_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit1Off) (divK_fastDigit 4040 4048 4080 108)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6
  skipBlockV6
  exact CodeReq.union_mono_left

theorem divK_digit0_code_sub_divCodeV6 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + v6Digit0Off) (divK_fastDigit 4048 4056 4088 68)) a = some i →
      (divCodeV6 base) a = some i := by
  unfold divCodeV6; simp only [CodeReq.unionAll_cons]
  skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6; skipBlockV6
  skipBlockV6; skipBlockV6
  exact CodeReq.union_mono_left

-- ============================================================================
-- Generic single-digit lift: full digit step over divCodeV6, parameterized by
-- the digit offset / memory offsets / call offset, taking the digit-block code
-- subsumption + the intra-bundle obligations as hypotheses.
-- ============================================================================

/-- `base + v6Div128Off - div128Off` is chosen so the embedded JAL's div128
    target (`divBase + div128Off`) lands on the shared `v6Div128Off` block. -/
private theorem v6_divBase_eq {base : Word} :
    (base + v6Div128Off - div128Off) + div128Off = base + v6Div128Off := by
  simp only [v6Div128Off, div128Off]; bv_omega

/-- The complete digit step (`divK_fastDigit_full_spec_within`, 93 steps) lifted
    onto `divCodeV6`. The fast path's own `divK_div128_v5` copy is routed to the
    shared `v6Div128Off` block; loads/JAL/post are routed to the digit block via
    the supplied `hcode_sub`. `htarget`/`halign`/`hdisj_*` are the per-digit
    obligations (discharged by the four wrappers below). -/
theorem divK_fastDigit_full_spec_within_v6
    (sp uHi uLo d base digitOff : Word) (uHiOff uLoOff qOff : BitVec 12) (callOff : BitVec 21)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (hcode_sub : ∀ a i,
      (CodeReq.ofProg (base + digitOff) (divK_fastDigit uHiOff uLoOff qOff callOff)) a = some i →
      (divCodeV6 base) a = some i)
    (htarget : (base + digitOff + 12) + signExtend21 callOff
      = (base + v6Div128Off - div128Off) + div128Off)
    (halign : ((base + digitOff + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + digitOff + 16)
    (hdisj_loads : (divK_fastDigit_loads_code uHiOff uLoOff (base + digitOff)).Disjoint
      ((CodeReq.singleton (base + digitOff + 12) (.JAL .x2 callOff)).union
        (CodeReq.ofProg ((base + v6Div128Off - div128Off) + div128Off) divK_div128_v5)))
    (hdisj_jal : (CodeReq.singleton (base + digitOff + 12) (.JAL .x2 callOff)).Disjoint
      (CodeReq.ofProg ((base + v6Div128Off - div128Off) + div128Off) divK_div128_v5))
    (hdisj_post : (((divK_fastDigit_loads_code uHiOff uLoOff (base + digitOff)).union
      ((CodeReq.singleton (base + digitOff + 12) (.JAL .x2 callOff)).union
        (CodeReq.ofProg ((base + v6Div128Off - div128Off) + div128Off) divK_div128_v5))).Disjoint
      (divK_fastDigit_post_code uLoOff qOff (base + digitOff + 16)))) :
    cpsTripleWithin 93 (base + digitOff) (base + digitOff + 40) (divCodeV6 base)
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
    sp uHi uLo d uHiOff uLoOff qOff callOff (base + digitOff) (base + v6Div128Off - div128Off)
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    htarget halign hdisj_loads hdisj_jal hdisj_post
  refine cpsTripleWithin_extend_code (hmono := ?_) core
  refine CodeReq.union_sub (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ ?_)) ?_
  · -- loads ⊆ divCodeV6 (digit block, slice idx 0 len 3)
    intro a i h
    exact hcode_sub a i
      (CodeReq.ofProg_mono_sub (base + digitOff) (base + digitOff)
        (divK_fastDigit uHiOff uLoOff qOff callOff)
        [.LD .x7 .x12 uHiOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984] 0 (by bv_omega) rfl
        (by simp only [divK_fastDigit_length, List.length_cons, List.length_nil]; omega)
        (by rw [divK_fastDigit_length]; omega) a i h)
  · -- JAL ⊆ divCodeV6 (digit block, idx 3)
    intro a i h
    exact hcode_sub a i
      (CodeReq.singleton_mono (by
        have hl := CodeReq.ofProg_lookup (base + digitOff) (divK_fastDigit uHiOff uLoOff qOff callOff) 3
          (by rw [divK_fastDigit_length]; omega) (by rw [divK_fastDigit_length]; omega)
        rw [show (base + digitOff : Word) + BitVec.ofNat 64 (4 * 3) = base + digitOff + 12
          from by bv_addr] at hl
        exact hl) a i h)
  · -- div128 ⊆ divCodeV6 (shared div128 block)
    rw [v6_divBase_eq]; exact div128_code_sub_divCodeV6
  · -- post ⊆ divCodeV6 (digit block, slice idx 4 len 6)
    intro a i h
    exact hcode_sub a i
      (CodeReq.ofProg_mono_sub (base + digitOff) (base + digitOff + 16)
        (divK_fastDigit uHiOff uLoOff qOff callOff)
        [.SD .x12 .x11 qOff, .LD .x5 .x12 uLoOff, .LD .x10 .x12 3984,
         .MUL .x7 .x11 .x10, .SUB .x5 .x5 .x7, .SD .x12 .x5 uLoOff] 4 (by bv_omega) rfl
        (by simp only [divK_fastDigit_length, List.length_cons, List.length_nil]; omega)
        (by rw [divK_fastDigit_length]; omega) a i h)

-- ============================================================================
-- The four concrete digit lifts (digit3..digit0), discharging the obligations.
-- ============================================================================

/-- digit3 step over `divCodeV6`: `uHi=u[4]@4024`, `uLo=u[3]@4032`, `q[3]@4064`,
    JAL imm 188. Remainder `u[3]-q·b0'` lands at 4032 = digit2's `uHi`. -/
theorem divK_fastDigit3_full_spec_within_v6
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16) :
    cpsTripleWithin 93 (base + v6Digit3Off) (base + v6Digit3Off + 40) (divCodeV6 base)
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
  refine divK_fastDigit_full_spec_within_v6 sp uHi uLo d base v6Digit3Off 4024 4032 4064 188
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit3_code_sub_divCodeV6 ?_ halign ?_ ?_ ?_
  · rw [v6_divBase_eq]; have h : signExtend21 (188 : BitVec 21) = (188 : Word) := by decide
    rw [h]; simp only [v6Digit3Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit3Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit3Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit3Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit3Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit3Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit3Off, v6Div128Off] at h1 h2 ⊢
      bv_omega

/-- digit2 step over `divCodeV6`: `uHi@4032`, `uLo@4040`, `q[2]@4072`, JAL imm 148. -/
theorem divK_fastDigit2_full_spec_within_v6
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16) :
    cpsTripleWithin 93 (base + v6Digit2Off) (base + v6Digit2Off + 40) (divCodeV6 base)
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
  refine divK_fastDigit_full_spec_within_v6 sp uHi uLo d base v6Digit2Off 4032 4040 4072 148
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit2_code_sub_divCodeV6 ?_ halign ?_ ?_ ?_
  · rw [v6_divBase_eq]; have h : signExtend21 (148 : BitVec 21) = (148 : Word) := by decide
    rw [h]; simp only [v6Digit2Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit2Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit2Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit2Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit2Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit2Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit2Off, v6Div128Off] at h1 h2 ⊢
      bv_omega

/-- digit1 step over `divCodeV6`: `uHi@4040`, `uLo@4048`, `q[1]@4080`, JAL imm 108. -/
theorem divK_fastDigit1_full_spec_within_v6
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16) :
    cpsTripleWithin 93 (base + v6Digit1Off) (base + v6Digit1Off + 40) (divCodeV6 base)
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
  refine divK_fastDigit_full_spec_within_v6 sp uHi uLo d base v6Digit1Off 4040 4048 4080 108
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit1_code_sub_divCodeV6 ?_ halign ?_ ?_ ?_
  · rw [v6_divBase_eq]; have h : signExtend21 (108 : BitVec 21) = (108 : Word) := by decide
    rw [h]; simp only [v6Digit1Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit1Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit1Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit1Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit1Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit1Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit1Off, v6Div128Off] at h1 h2 ⊢
      bv_omega

/-- digit0 step over `divCodeV6`: `uHi@4048`, `uLo@4056`, `q[0]@4088`, JAL imm 68. -/
theorem divK_fastDigit0_full_spec_within_v6
    (sp uHi uLo d base : Word)
    (v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem : Word)
    (halign : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 93 (base + v6Digit0Off) (base + v6Digit0Off + 40) (divCodeV6 base)
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
  refine divK_fastDigit_full_spec_within_v6 sp uHi uLo d base v6Digit0Off 4048 4056 4088 68
    v2 v5 v6 v7 v9 v10 v11 qm retMem dMem dloMem un0Mem scratchMem
    divK_digit0_code_sub_divCodeV6 ?_ halign ?_ ?_ ?_
  · rw [v6_divBase_eq]; have h : signExtend21 (68 : BitVec 21) = (68 : Word) := by decide
    rw [h]; simp only [v6Digit0Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_right ?_ ?_
    · refine CodeReq.Disjoint.ofProg_singleton ?_
      refine CodeReq.ofProg_none_range_len _ _ 3 _ rfl (fun k hk => ?_)
      simp only [v6Digit0Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range_len _ _ 3 _ _ 85 rfl divK_div128_v5_len (fun k1 k2 h1 h2 => ?_)
      simp only [v6Digit0Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.singleton_ofProg ?_
    refine CodeReq.ofProg_none_range_len _ _ 85 _ divK_div128_v5_len (fun k hk => ?_)
    simp only [v6Digit0Off, v6Div128Off]; bv_omega
  · rw [v6_divBase_eq]; refine CodeReq.Disjoint.union_left ?_ (CodeReq.Disjoint.union_left ?_ ?_)
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, v6Digit0Off] at h1 h2 ⊢; bv_omega
    · refine (CodeReq.Disjoint.ofProg_singleton ?_).symm
      refine CodeReq.ofProg_none_range_len _ _ 6 _ rfl (fun k hk => ?_)
      simp only [v6Digit0Off]; bv_omega
    · refine CodeReq.ofProg_disjoint_range (fun k1 k2 h1 h2 => ?_)
      simp only [List.length_cons, List.length_nil, divK_div128_v5_len, v6Digit0Off, v6Div128Off] at h1 h2 ⊢
      bv_omega

end EvmAsm.Evm64
