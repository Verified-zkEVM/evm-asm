/-
  EvmAsm.Rv64.RLP.FlatListLoopConcrete

  EL.3 — the fully CONCRETE end-to-end flat RLP list decoder. Wires the concrete
  single-item decoder (`flat_decoder_spec`, `FlatDecoderConcrete.lean`) into the
  list-loop bridge (`fll_loop_bridge`, `FlatListLoop.lean`), discharging the
  loop's abstract `decoderH` and all its code-layout side-conditions. The result
  `flat_list_loop_concrete_bridge` has NO abstract hypotheses: a real RV64
  program — `[LBU x5,x13,0] ++ flat_decoder_prog ++ [ADD, ADDI, BNE]` laid out at
  `base` — decodes a non-empty list of flat RLP items from `bytesRegion` in
  `15 * items.length` steps AND coincides with the pure `decodeItems` round-trip.

  Layout (program base `base`; the loop scaffold brackets the 16-instruction
  decoder, so `joinPC = base + 68`, loop exit `base + 80`):
      base       LBU  x5, x13, 0          ; read prefix byte
      base+4     < flat_decoder_prog : 16 instr, joins at base+68 >
      base+68    ADD  x13, x13, x11       ; advance to next item
      base+72    ADDI x14, x14, -1        ; item counter
      base+76    BNE  x14, x0, -76        ; loop back to base
-/

import EvmAsm.Rv64.RLP.FlatListLoop
import EvmAsm.Rv64.RLP.FlatDecoderConcrete
import EvmAsm.Rv64.Tactics.SeqFrame

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- **Fully concrete end-to-end flat list decoder.** The RV64 program laid out at
    `base` (loop scaffold + `flat_decoder_prog`) decodes a non-empty list of flat
    RLP items from `bytesRegion regionBase (encode.encodeItems items)` in
    `15 * items.length` steps — leaving the pointer at the region end and the
    counter zero — and the pure decoder recovers exactly `items`. No abstract
    decoder hypothesis remains. -/
theorem flat_list_loop_concrete_bridge
    (base regionBase : Word) (items : List RLPItem) (v5Old v10 v11Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hne : items ≠ [])
    (hflat_all : ∀ item ∈ items, isFlatItem item)
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode.encodeItems items).length < 256 ^ 8) :
    cpsTripleWithin (15 * items.length) base (base + 68 + 12)
      (((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) flat_decoder_prog)).union
            (CodeReq.singleton (base + 68) (.ADD .x13 .x13 .x11))).union
            (CodeReq.singleton (base + 68 + 4) (.ADDI .x14 .x14 (-1)))).union
            ((CodeReq.singleton (base + 68 + 8) (.BNE .x14 .x0 (-76))).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ BitVec.ofNat 64 items.length) **
       bytesRegion regionBase (encode.encodeItems items))
      (fll_loop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length))
    ∧ decodeItems (2 * (encode.encodeItems items).length + 1) (encode.encodeItems items)
        = some (items, []) := by
  have decoderH : ∀ (pfx : Byte) (w10 w11 w13 : Word),
      (classifyPrefix pfx = .singleByte ∨ classifyPrefix pfx = .shortBytes
        ∨ classifyPrefix pfx = .shortList) →
      cpsTripleWithin 11 (base + 4) (base + 68) (CodeReq.ofProg (base + 4) flat_decoder_prog)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ w10) **
         (.x11 ↦ᵣ w11) ** (.x13 ↦ᵣ w13))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemPayloadPtr pfx w13)) := by
    intro pfx w10 w11 w13 h
    have hd := flat_decoder_spec (base + 4) pfx w10 w11 w13 h
    rwa [show (base + 4) + 64 = base + 68 from by bv_omega] at hd
  have hback : (base + 68 + 8) + signExtend13 (-76 : BitVec 13) = base := by
    have h76 : signExtend13 (-76 : BitVec 13) = (-76 : Word) := by decide
    rw [h76]; bv_omega
  -- The decoder occupies `[base+4, base+64)`; every loop-scaffold address is outside it.
  have dcr_none : ∀ (a : Word),
      (∀ k, k < 16 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg (base + 4) flat_decoder_prog a = none :=
    fun a h => CodeReq.ofProg_none_range_len (base + 4) flat_decoder_prog 16 a
      flat_decoder_prog_length h
  exact fll_loop_bridge regionBase base (base + 68) (base + 4)
    (CodeReq.ofProg (base + 4) flat_decoder_prog) (-76)
    items v5Old v10 v11Old halign hover rfl decoderH hback
    (by bv_omega) (by bv_omega) (by bv_omega)
    (CodeReq.Disjoint.singleton_ofProg (dcr_none base (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none (base + 68) (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none (base + 68 + 4) (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none (base + 68 + 8) (by intro k hk; bv_omega)))
    hne hflat_all hwin hsize

-- Concrete cross-check: the program at `base = 0x1000` decodes the two-item flat
-- list `[0x01, 0x02]` from the legacy mem zone at `0x2000` (in `15 * 2 = 30`
-- steps), and the pure decoder recovers it. The inferred type is the full
-- end-to-end bridge instantiated at these concrete values.
example :=
  flat_list_loop_concrete_bridge (0x1000 : Word) (0x2000 : Word)
    [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]] 0 0 0
    (by decide) (by decide) (by decide)
    (by intro item hitem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hitem
        rcases hitem with rfl | rfl <;> simp [isFlatItem])
    (by intro i hi
        have hlen : (encode.encodeItems
            [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]).length = 2 := by decide
        rw [hlen] at hi; interval_cases i <;> decide)
    (by decide)

end EvmAsm.Rv64.RLP
