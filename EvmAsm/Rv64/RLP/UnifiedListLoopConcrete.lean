/-
  EvmAsm.Rv64.RLP.UnifiedListLoopConcrete

  EL.3 — the fully CONCRETE end-to-end ALL-class RLP list decoder. Wires the
  concrete single-item decoder (`unified_decoder_spec`, `UnifiedDecoderConcrete.lean`)
  into the unified list-loop bridge (`unified_loop_bridge`, `UnifiedListLoop.lean`),
  discharging the loop's abstract `UnifiedDecoderH` and all its code-layout
  side-conditions. The result `unified_list_loop_concrete_bridge` has NO abstract
  hypotheses: a real RV64 program — `[LBU x5,x13,0] ++ unified_decoder_prog ++
  [ADD, ADDI, BNE]` laid out at `lbase` — decodes a non-empty list of ARBITRARY
  RLP items (all 5 classes, including long strings/lists) from `bytesRegion` in
  `64 * items.length` steps AND coincides with the pure `decodeItems` round-trip.
  This completes single-level long-item list decoding (the all-class analog of
  `FlatListLoopConcrete.lean`).

  Layout (program base `lbase`; the loop scaffold brackets the 36-instruction
  decoder, so `joinPC = lbase + 148`, loop exit `lbase + 160`):
      lbase       LBU  x5, x13, 0          ; read prefix byte
      lbase+4     < unified_decoder_prog : 36 instr, joins at lbase+148 >
      lbase+148   ADD  x13, x13, x11       ; advance to next item
      lbase+152   ADDI x15, x15, -1        ; item counter (x15)
      lbase+156   BNE  x15, x0, -156       ; loop back to lbase
-/

import EvmAsm.Rv64.RLP.UnifiedListLoop
import EvmAsm.Rv64.RLP.UnifiedDecoderConcrete
import EvmAsm.Rv64.Tactics.SeqFrame

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- **Fully concrete end-to-end all-class list decoder.** The RV64 program laid
    out at `lbase` (loop scaffold + `unified_decoder_prog`) decodes a non-empty
    list of arbitrary RLP items from `bytesRegion regionBase (encode.encodeItems
    items)` in `64 * items.length` steps — leaving the pointer at the region end
    and the counter zero — and the pure decoder recovers exactly `items`. No
    abstract decoder hypothesis remains. -/
theorem unified_list_loop_concrete_bridge
    (lbase regionBase : Word) (items : List RLPItem) (v5Old v10 v11Old v12Old v14Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hne : items ≠ [])
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode.encodeItems items).length < 256 ^ 8) :
    cpsTripleWithin (64 * items.length) lbase (lbase + 148 + 12)
      (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (lbase + 4) unified_decoder_prog)).union
            (CodeReq.singleton (lbase + 148) (.ADD .x13 .x13 .x11))).union
            (CodeReq.singleton (lbase + 148 + 4) (.ADDI .x15 .x15 (-1)))).union
            ((CodeReq.singleton (lbase + 148 + 8) (.BNE .x15 .x0 (-156))).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ BitVec.ofNat 64 items.length) ** bytesRegion regionBase (encode.encodeItems items))
      (unified_loop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length))
    ∧ decodeItems (2 * (encode.encodeItems items).length + 1) (encode.encodeItems items)
        = some (items, []) := by
  -- Discharge the loop's abstract decoder hypothesis with the concrete decoder spec.
  have decoderH : UnifiedDecoderH regionBase (lbase + 4) (lbase + 148)
      (CodeReq.ofProg (lbase + 4) unified_decoder_prog) (encode.encodeItems items) := by
    intro i hi v10' v11' v12' v14' hwindow
    have hd := unified_decoder_spec (lbase + 4) regionBase (encode.encodeItems items) i hi
      v10' v11' v12' v14' halign hover hwindow
    rwa [show (lbase + 4) + 144 = lbase + 148 from by bv_omega] at hd
  have hback : (lbase + 148 + 8) + signExtend13 (-156 : BitVec 13) = lbase := by
    have h156 : signExtend13 (-156 : BitVec 13) = (-156 : Word) := by decide
    rw [h156]; bv_omega
  -- The decoder occupies `[lbase+4, lbase+148)`; every loop-scaffold address is outside it.
  have dcr_none : ∀ (a : Word),
      (∀ k, k < 36 → a ≠ (lbase + 4) + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg (lbase + 4) unified_decoder_prog a = none :=
    fun a h => CodeReq.ofProg_none_range_len (lbase + 4) unified_decoder_prog 36 a
      unified_decoder_prog_length h
  exact unified_loop_bridge regionBase lbase (lbase + 148) (lbase + 4)
    (CodeReq.ofProg (lbase + 4) unified_decoder_prog) (-156)
    items v5Old v10 v11Old v12Old v14Old halign hover rfl decoderH hback
    (by bv_omega) (by bv_omega) (by bv_omega)
    (CodeReq.Disjoint.singleton_ofProg (dcr_none lbase (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none (lbase + 148) (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none (lbase + 148 + 4) (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none (lbase + 148 + 8) (by intro k hk; bv_omega)))
    hne hwin hsize

-- Concrete cross-check: the program at `lbase = 0x1000` decodes the two-item list
-- `[0x01, 0x02]` from the region at `0x2000` (in `64 * 2 = 128` steps), and the
-- pure decoder recovers it. The inferred type is the full end-to-end bridge.
example :=
  unified_list_loop_concrete_bridge (0x1000 : Word) (0x2000 : Word)
    [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]] 0 0 0 0 0
    (by decide) (by decide) (by decide)
    (by intro i hi
        have hlen : (encode.encodeItems
            [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]).length = 2 := by decide
        rw [hlen] at hi; interval_cases i <;> decide)
    (by decide)

end EvmAsm.Rv64.RLP
