/-
  EvmAsm.Rv64.RLP.UnifiedDecoderConcrete

  EL.3 — a CONCRETE assembled program for the ALL-class RLP single-item decoder,
  and its spec `unified_decoder_spec` in exactly the shape the unified list-loop
  closure's `UnifiedDecoderH` hypothesis (`UnifiedListLoop.lean`) expects. The
  all-class analog of the flat `FlatDecoderConcrete.lean`.

  `rlp_decode_single_item_reconverged_all_region` (`UnifiedDecodeItemReconverge-
  AllRegion.lean`) proves the `cpsTripleWithin 60` for the reconverged 5-class
  region decoder *given* concrete branch/jump offsets and the ~30 disjointness /
  subset / back-edge side-conditions on a `cr : CodeReq`. Here we lay out ONE
  linear 36-instruction program `unified_decoder_prog` (the 4-step phase-1 cascade
  + the 5 phase-3 handlers + the two long-form length-read loops + reconvergence
  `JAL`s), pick the forced offsets, and discharge every side-condition for
  `cr := CodeReq.ofProg base unified_decoder_prog`.

  Layout (word k ⇒ byte 4k; `joinPC = base + 144`; the cascade fall-through
  x5 ≥ 0xF8 flows into e5 @ base+32):
      0  ADDI x10 x0 0x80   1  BLTU x5 x10 68  → e1 = base+72   (singleByte)
      2  ADDI x10 x0 0xB8   3  BLTU x5 x10 68  → e2 = base+80   (shortBytes)
      4  ADDI x10 x0 0xC0   5  BLTU x5 x10 84  → e3 = base+104  (longBytes)
      6  ADDI x10 x0 0xF8   7  BLTU x5 x10 64  → e4 = base+92   (shortList)
      8..10  long_list (e5 phase3 @ base+32)
      11..16 long loop body (e5 @ base+44)      17  JAL x0 76   (→ joinPC)
      18 single_byte (e1 @ base+72)             19  JAL x0 68
      20..21 short_string (e2 @ base+80)         22  JAL x0 56
      23..24 short_list (e4 @ base+92)           25  JAL x0 44
      26..28 long_string (e3 phase3 @ base+104)
      29..34 long loop body (e3 @ base+116)      35  JAL x0 4
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItemReconvergeAllRegion
import EvmAsm.Rv64.RLP.UnifiedListLoop
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.AddrNorm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The concrete all-class single-item decoder program (36 instructions).
    Assembled from the phase-1 cascade, the 5 phase-3 handlers, the two long-form
    length-read loops, and their reconvergence `JAL`s, so each piece is a
    contiguous slice. Offsets are the forced values (see file header). -/
def unified_decoder_prog : List Instr :=
  [ .ADDI .x10 .x0 0x80, .BLTU .x5 .x10 68,
    .ADDI .x10 .x0 0xB8, .BLTU .x5 .x10 68,
    .ADDI .x10 .x0 0xC0, .BLTU .x5 .x10 84,
    .ADDI .x10 .x0 0xF8, .BLTU .x5 .x10 64,
    -- e5 long-list handler (base+32)
    .ADDI .x14 .x5 (-0xF7), .ADDI .x11 .x0 0, .ADDI .x13 .x13 1,
    -- e5 long loop body (base+44)
    .LBU .x12 .x13 0, .SLLI .x11 .x11 8, .ADD .x11 .x11 .x12,
    .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1), .BNE .x14 .x0 (-20),
    .JAL .x0 76,
    -- e1 single-byte handler (base+72)
    .ADDI .x11 .x0 1, .JAL .x0 68,
    -- e2 short-string handler (base+80)
    .ADDI .x11 .x5 (-0x80), .ADDI .x13 .x13 1, .JAL .x0 56,
    -- e4 short-list handler (base+92)
    .ADDI .x11 .x5 (-0xC0), .ADDI .x13 .x13 1, .JAL .x0 44,
    -- e3 long-string handler (base+104)
    .ADDI .x14 .x5 (-0xB7), .ADDI .x11 .x0 0, .ADDI .x13 .x13 1,
    -- e3 long loop body (base+116)
    .LBU .x12 .x13 0, .SLLI .x11 .x11 8, .ADD .x11 .x11 .x12,
    .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1), .BNE .x14 .x0 (-20),
    .JAL .x0 4 ]

theorem unified_decoder_prog_length : unified_decoder_prog.length = 36 := rfl

-- A `CodeReq.ofProg`-leaf (a contiguous slice of `unified_decoder_prog` at byte
-- offset `4*idx`) is subsumed by the whole program.
private theorem unified_piece (base subBase : Word) (idx : Nat) (sub : List Instr)
    (h_addr : subBase = base + BitVec.ofNat 64 (4 * idx))
    (h_slice : (unified_decoder_prog.drop idx).take sub.length = sub)
    (h_range : idx + sub.length ≤ 36) :
    ∀ a i, (CodeReq.ofProg subBase sub) a = some i
         → (CodeReq.ofProg base unified_decoder_prog) a = some i :=
  CodeReq.ofProg_mono_sub base subBase unified_decoder_prog sub idx h_addr h_slice
    (by rw [unified_decoder_prog_length]; exact h_range) (by rw [unified_decoder_prog_length]; decide)

-- A `JAL` singleton at byte offset `4*idx` is subsumed by the whole program.
private theorem unified_jal_piece (base addr : Word) (idx : Nat) (joff : BitVec 21)
    (hk : idx < 36) (h_addr : addr = base + BitVec.ofNat 64 (4 * idx))
    (h_get : unified_decoder_prog.get ⟨idx, by rw [unified_decoder_prog_length]; exact hk⟩
              = .JAL .x0 joff) :
    ∀ a i, (CodeReq.singleton addr (.JAL .x0 joff)) a = some i
         → (CodeReq.ofProg base unified_decoder_prog) a = some i := by
  apply CodeReq.singleton_mono
  rw [CodeReq.ofProg_lookup_addr base unified_decoder_prog idx addr
        (by rw [unified_decoder_prog_length]; exact hk) (by rw [unified_decoder_prog_length]; decide)
        h_addr, h_get]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- **Concrete all-class decoder spec.** Matches the `UnifiedDecoderH` hypothesis
    of the unified list-loop closure (`UnifiedListLoop.lean`): for the prefix byte
    `bs[off]`, the program `unified_decoder_prog` at `base` runs in 60 steps from
    `base` to `base + 144`, leaving the region decode results in the registers. The
    long-form window obligation is supplied as `regionLongWindow` (the closure
    discharges it at each item start); the loop back-edge is the concrete `-20`. -/
theorem unified_decoder_spec (base regionBase : Word) (bs : List Byte) (off : Nat)
    (hoff : off < bs.length) (v10 v11 v12 v14 : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwindow : regionLongWindow regionBase bs off hoff) :
    cpsTripleWithin 60 base (base + 144) (CodeReq.ofProg base unified_decoder_prog)
      ((.x5 ↦ᵣ (bs[off]'hoff).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ v14) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ (bs[off]'hoff).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ itemResidue (bs[off]'hoff)) ** (.x11 ↦ᵣ itemLenRegion (bs[off]'hoff) bs off) **
       (.x12 ↦ᵣ itemX12Region (bs[off]'hoff) bs off v12) **
       (.x13 ↦ᵣ itemPtrRegion (bs[off]'hoff) regionBase off) **
       (.x14 ↦ᵣ itemX14 (bs[off]'hoff) v14) ** bytesRegion regionBase bs) := by
  -- Long-form proof obligation: combine the passed window with the concrete back-edge.
  have hsext : signExtend13 (-20 : BitVec 13) = (-20 : Word) := by decide
  have hlong : rlpDecodeLongHypsRegion (bs[off]'hoff) regionBase off bs base (-20 : BitVec 13)
      (base + 104) := by
    simp only [rlpDecodeLongHypsRegion]
    simp only [regionLongWindow] at hwindow
    cases hc : classifyPrefix (bs[off]'hoff) with
    | singleByte => trivial
    | shortBytes => trivial
    | shortList => trivial
    | longBytes => simp only [hc] at hwindow ⊢; exact ⟨hwindow, by rw [hsext]; bv_omega⟩
    | longList => simp only [hc] at hwindow ⊢; exact ⟨hwindow, by rw [hsext]; bv_omega⟩
  exact rlp_decode_single_item_reconverged_all_region (bs[off]'hoff) v10 v11 v12
    (regionBase + BitVec.ofNat 64 off) v14 regionBase off bs
    68 68 84 64 (-20) 68 56 4 44 76
    base (base + 72) (base + 80) (base + 104) (base + 92) (base + 144)
    (CodeReq.ofProg base unified_decoder_prog)
    (by rv64_addr) (by rv64_addr) (by rv64_addr) (by rv64_addr)
    halign hover rfl hlong
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by rv64_addr) (by rv64_addr) (by rv64_addr) (by rv64_addr) (by rv64_addr)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    -- hsub1 (e1): step1 ∪ single_byte ∪ JAL
    (by
      refine CodeReq.union_sub (CodeReq.union_sub ?_ ?_) ?_
      · exact unified_piece base base 0 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 72) 18 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_jal_piece base (base + 72 + 4) 19 68 (by decide) (by rv64_addr) (by decide))
    -- hsub2 (e2): step1 ∪ step2 ∪ short_string ∪ JAL
    (by
      refine CodeReq.union_sub (CodeReq.union_sub (CodeReq.union_sub ?_ ?_) ?_) ?_
      · exact unified_piece base base 0 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 8) 2 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 80) 20 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_jal_piece base (base + 80 + 8) 22 56 (by decide) (by rv64_addr) (by decide))
    -- hsub3 (e3): step1 ∪ (step2 ∪ step3) ∪ long_string ∪ loop ∪ JAL
    (by
      refine CodeReq.union_sub (CodeReq.union_sub (CodeReq.union_sub
        (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ ?_)) ?_) ?_) ?_
      · exact unified_piece base base 0 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 8) 2 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 16) 4 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 104) 26 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base ((base + 104) + 12) 29 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_jal_piece base (((base + 104) + 12) + 24) 35 4 (by decide) (by rv64_addr) (by decide))
    -- hsub4 (e4): step1 ∪ (step2 ∪ (step3 ∪ step4)) ∪ short_list ∪ JAL
    (by
      refine CodeReq.union_sub (CodeReq.union_sub
        (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ ?_))) ?_) ?_
      · exact unified_piece base base 0 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 8) 2 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 16) 4 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 24) 6 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 92) 23 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_jal_piece base (base + 92 + 8) 25 44 (by decide) (by rv64_addr) (by decide))
    -- hsub5 (e5): step1 ∪ (step2 ∪ (step3 ∪ step4)) ∪ long_list ∪ loop ∪ JAL
    (by
      refine CodeReq.union_sub (CodeReq.union_sub (CodeReq.union_sub
        (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ ?_))) ?_) ?_) ?_
      · exact unified_piece base base 0 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 8) 2 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 16) 4 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 24) 6 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 32) 8 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_piece base (base + 44) 11 _ (by rv64_addr) (by decide) (by decide)
      · exact unified_jal_piece base (base + 44 + 24) 17 76 (by decide) (by rv64_addr) (by decide))

-- Sanity: program length and the head-instruction lookup.
example : unified_decoder_prog.length = 36 := unified_decoder_prog_length
example : (CodeReq.ofProg (0 : Word) unified_decoder_prog) 0 = some (.ADDI .x10 .x0 0x80) := by decide

end EvmAsm.Rv64.RLP
