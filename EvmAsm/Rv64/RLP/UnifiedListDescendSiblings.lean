/-
  EvmAsm.Rv64.RLP.UnifiedListDescendSiblings

  EL.3 / Phase 5 — SEQUENTIAL sibling descent. A concrete RV64 program descends
  TWO successive sibling sub-lists of a buffer — `.list aItems` then `.list bItems`
  — and coincides with the pure `decode` of each. This is the pattern the
  fixed-schema STF block decoder repeats over `[header, txs, ommers]`.

  The two descents chain with NO glue: `unified_list_descend_concrete_bridge_at`'s
  post and `unified_list_descend_concrete_bridge_at_regOwn`'s pre are both
  `unified_lenloop_post`, and the first leaves `x13` exactly at the next sibling
  (the free stride), so `cpsTripleWithin_seq` matches the intermediate state
  syntactically.

  Layout (program base `base`; aligned `regionBase`, buffer `bs`, offset `O`):
      base       < descend .list aItems at offset O >        (base .. base+308)
                 x13 → O + (encode (.list aItems)).length
      base+308   < descend .list bItems at that offset >     (base+308 .. base+616)
      base+616   (exit)
-/

import EvmAsm.Rv64.RLP.UnifiedListDescendConcrete

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- The descent program's 7-leaf code requirement at base `b` (LBU + decoder + ADD,
    then LBU + decoder + ADD + BNE) — matches the CR of
    `unified_list_descend_concrete_bridge_at`/`…_regOwn`. The 77 instruction slots
    sit at `b + 4*k` for `k < 77`. -/
def descendCR (b : Word) : CodeReq :=
  (((((CodeReq.singleton b (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (b + 4) unified_decoder_prog)).union
        (CodeReq.singleton (b + 148) (.ADD .x15 .x13 .x11))).union
        ((((CodeReq.singleton (b + 152) (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (b + 156) unified_decoder_prog)).union
          (CodeReq.singleton (b + 300) (.ADD .x13 .x13 .x11))).union
          ((CodeReq.singleton (b + 300 + 4) (.BNE .x13 .x15 (-152))).union CodeReq.empty))))

/-- A descent CR maps to `none` at any address outside its 77 instruction slots
    `{b + 4*k : k < 77}`. -/
theorem descendCR_none (b a : Word) (h : ∀ k, k < 77 → a ≠ b + BitVec.ofNat 64 (4 * k)) :
    descendCR b a = none := by
  have ep1 : CodeReq.ofProg (b + 4) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len (b + 4) unified_decoder_prog 36 a unified_decoder_prog_length
      (fun k hk => by
        have := h (k + 1) (by omega)
        rwa [show b + BitVec.ofNat 64 (4 * (k + 1)) = (b + 4) + BitVec.ofNat 64 (4 * k)
          from by bv_omega] at this)
  have ep2 : CodeReq.ofProg (b + 156) unified_decoder_prog a = none :=
    CodeReq.ofProg_none_range_len (b + 156) unified_decoder_prog 36 a unified_decoder_prog_length
      (fun k hk => by
        have := h (k + 39) (by omega)
        rwa [show b + BitVec.ofNat 64 (4 * (k + 39)) = (b + 156) + BitVec.ofNat 64 (4 * k)
          from by bv_omega] at this)
  have s0 : CodeReq.singleton b (.LBU .x5 .x13 0) a = none :=
    CodeReq.singleton_miss (by have := h 0 (by omega); simpa using this)
  have s37 : CodeReq.singleton (b + 148) (.ADD .x15 .x13 .x11) a = none :=
    CodeReq.singleton_miss (by have := h 37 (by omega); bv_omega)
  have s38 : CodeReq.singleton (b + 152) (.LBU .x5 .x13 0) a = none :=
    CodeReq.singleton_miss (by have := h 38 (by omega); bv_omega)
  have s75 : CodeReq.singleton (b + 300) (.ADD .x13 .x13 .x11) a = none :=
    CodeReq.singleton_miss (by have := h 75 (by omega); bv_omega)
  have s76 : CodeReq.singleton (b + 300 + 4) (.BNE .x13 .x15 (-152)) a = none :=
    CodeReq.singleton_miss (by have := h 76 (by omega); bv_omega)
  simp only [descendCR, CodeReq.union, s0, ep1, s37, s38, ep2, s75, s76, CodeReq.empty]

/-- **Reusable descent-CR disjointness.** Two descent programs whose code ranges
    don't overlap (`base2 ≥ base1 + 308`) have disjoint code requirements. Used to
    compose sequential sibling descents (and, later, the N-sibling block walk). -/
theorem descend_cr_disjoint (base1 base2 : Word)
    (hsep : base1.toNat + 308 ≤ base2.toNat) (hov : base2.toNat + 308 < 2 ^ 64) :
    (descendCR base1).Disjoint (descendCR base2) := by
  intro a
  by_cases hin : ∀ k, k < 77 → a ≠ base1 + BitVec.ofNat 64 (4 * k)
  · exact Or.inl (descendCR_none base1 a hin)
  · push Not at hin
    obtain ⟨k, hk, rfl⟩ := hin
    exact Or.inr (descendCR_none base2 _ (fun k2 hk2 => by bv_omega))

set_option maxRecDepth 8000 in
/-- **Two-sibling sequential descent.** For a buffer whose suffix from offset `O`
    is two consecutive list values followed by `tail`
    (`bs.drop O = encode (.list aItems) ++ encode (.list bItems) ++ tail`), the
    program descends `.list aItems` (at `O`) then `.list bItems` (at the next-sibling
    offset `O + (encode (.list aItems)).length`) in
    `(62 + 63*aItems.length) + (62 + 63*bItems.length)` steps, coinciding with the
    pure `decode` of each. -/
theorem unified_list_descend_two_siblings_bridge
    (base regionBase : Word) (aItems bItems : List RLPItem) (bs : List Byte) (O : Nat)
    (tail : List Byte) (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hcode : base.toNat + 616 < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsizeA : (encode (.list aItems)).length < 256 ^ 8)
    (hsizeB : (encode (.list bItems)).length < 256 ^ 8)
    (haNe : aItems ≠ []) (hbNe : bItems ≠ [])
    (hdrop : bs.drop O = encode (.list aItems) ++ encode (.list bItems) ++ tail) :
    cpsTripleWithin ((62 + 63 * aItems.length) + (62 + 63 * bItems.length)) base (base + 616)
      ((descendCR base).union (descendCR (base + 308)))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      (unified_lenloop_post regionBase bs
        (regionBase + BitVec.ofNat 64
          ((O + (encode (.list aItems)).length) + (encode (.list bItems)).length)))
    ∧ decode (bs.drop O) = some (.list aItems, encode (.list bItems) ++ tail)
    ∧ decode (bs.drop (O + (encode (.list aItems)).length)) = some (.list bItems, tail) := by
  have hdropA : bs.drop O = encode (.list aItems) ++ (encode (.list bItems) ++ tail) := by
    rw [hdrop, List.append_assoc]
  have A := unified_list_descend_concrete_bridge_at base regionBase aItems bs O
    (encode (.list bItems) ++ tail) v5Old v10 v11Old v12Old v14Old v15Old
    halign hover hwin hsizeA haNe hdropA
  have hdropB : bs.drop (O + (encode (.list aItems)).length) = encode (.list bItems) ++ tail := by
    rw [← List.drop_drop, hdropA, List.drop_append_length]
  have B := unified_list_descend_concrete_bridge_at_regOwn (base + 308) regionBase bItems bs
    (O + (encode (.list aItems)).length) tail halign hover hwin hsizeB hbNe hdropB
  rw [show base + 308 + 308 = base + 616 from by bv_omega] at B
  refine ⟨?_, A.2, by rw [hdropB]; exact decode_encode_append (.list bItems) tail hsizeB⟩
  exact cpsTripleWithin_seq
    (descend_cr_disjoint base (base + 308) (by bv_omega) (by bv_omega)) A.1 B

-- Concrete cross-check: two consecutive single-item lists at `0x2000`,
-- `[0xc1, 0x01, 0xc1, 0x02]` (`= encode (.list [.bytes [1]]) ++ encode (.list [.bytes [2]])`).
-- The program at `0x1000` descends the first sub-list `[1]`, strides to the second,
-- and descends `[2]`; pure `decode` recovers each with the right remainder.
example :=
  unified_list_descend_two_siblings_bridge (0x1000 : Word) (0x2000 : Word)
    [.bytes [(0x01 : Byte)]] [.bytes [(0x02 : Byte)]]
    [(0xc1 : Byte), (0x01 : Byte), (0xc1 : Byte), (0x02 : Byte)] 0 []
    0 0 0 0 0 0
    (by decide) (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0xc1 : Byte), (0x01 : Byte), (0xc1 : Byte), (0x02 : Byte)]).length = 4 := by
          decide
        rw [hlen] at hi; interval_cases i <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end EvmAsm.Rv64.RLP
