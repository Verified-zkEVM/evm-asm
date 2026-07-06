/-
  EvmAsm.Rv64.RLP.FlatDecoderConcrete

  EL.3 — a CONCRETE assembled program for the flat RLP single-item decoder, and
  its spec `flat_decoder_spec` in exactly the shape the flat list-loop closure's
  `decoderH` hypothesis (`FlatListLoop.lean`) expects.

  `rlp_decode_single_item_reconverged_flat` (`UnifiedDecodeItemReconverge.lean`)
  proves the `cpsTripleWithin 11` for the reconverged flat decoder *given*
  concrete branch/jump offsets and the disjointness/subset side-conditions on a
  `cr : CodeReq`. Here we lay out ONE linear 16-instruction program
  `flat_decoder_prog` (the 4-step phase-1 cascade + the three flat-class handlers
  + their reconvergence `JAL`s), pick the forced offsets, and discharge every
  side-condition for `cr := CodeReq.ofProg base flat_decoder_prog`. This grounds
  the abstract decoder in real RISC-V code; wiring it into the loop
  (`fll_loop_n_spec_within`) is a follow-up.

  Layout (word k ⇒ byte 4k; `joinPC = base + 64`):
      0  ADDI x10 x0 0x80   1  BLTU x5 x10 28   → e1 = base+32   (singleByte)
      2  ADDI x10 x0 0xB8   3  BLTU x5 x10 28   → e2 = base+40   (shortBytes)
      4  ADDI x10 x0 0xC0   5  BLTU x5 x10 0    (longBytes; unreached for flat)
      6  ADDI x10 x0 0xF8   7  BLTU x5 x10 24   → e4 = base+52   (shortList)
      8  ADDI x11 x0 1      9  JAL  x0 28       (e1 handler + reconverge)
     10  ADDI x11 x5 -0x80 11  ADDI x13 x13 1  12  JAL x0 16     (e2 handler)
     13  ADDI x11 x5 -0xC0 14  ADDI x13 x13 1  15  JAL x0 4      (e4 handler)
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItemReconverge
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.AddrNorm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- The concrete flat single-item decoder program (16 instructions). Assembled
    from the phase-1 cascade step programs, the three flat-class phase-3
    handlers, and their reconvergence `JAL`s, so each piece is a contiguous slice. -/
def flat_decoder_prog : List Instr :=
  [ .ADDI .x10 .x0 0x80, .BLTU .x5 .x10 28,
    .ADDI .x10 .x0 0xB8, .BLTU .x5 .x10 28,
    .ADDI .x10 .x0 0xC0, .BLTU .x5 .x10 0,
    .ADDI .x10 .x0 0xF8, .BLTU .x5 .x10 24,
    .ADDI .x11 .x0 1, .JAL .x0 28,
    .ADDI .x11 .x5 (-0x80), .ADDI .x13 .x13 1, .JAL .x0 16,
    .ADDI .x11 .x5 (-0xC0), .ADDI .x13 .x13 1, .JAL .x0 4 ]

theorem flat_decoder_prog_length : flat_decoder_prog.length = 16 := rfl

-- A `CodeReq.ofProg`-leaf (a contiguous slice of `flat_decoder_prog` at byte
-- offset `4*idx`) is subsumed by the whole program.
private theorem flat_piece (base subBase : Word) (idx : Nat) (sub : List Instr)
    (h_addr : subBase = base + BitVec.ofNat 64 (4 * idx))
    (h_slice : (flat_decoder_prog.drop idx).take sub.length = sub)
    (h_range : idx + sub.length ≤ 16) :
    ∀ a i, (CodeReq.ofProg subBase sub) a = some i
         → (CodeReq.ofProg base flat_decoder_prog) a = some i :=
  CodeReq.ofProg_mono_sub base subBase flat_decoder_prog sub idx h_addr h_slice
    (by rw [flat_decoder_prog_length]; exact h_range) (by rw [flat_decoder_prog_length]; decide)

-- A `JAL` singleton at byte offset `4*idx` (instruction `flat_decoder_prog[idx]`)
-- is subsumed by the whole program.
private theorem flat_jal_piece (base addr : Word) (idx : Nat) (joff : BitVec 21)
    (hk : idx < 16) (h_addr : addr = base + BitVec.ofNat 64 (4 * idx))
    (h_get : flat_decoder_prog.get ⟨idx, by rw [flat_decoder_prog_length]; exact hk⟩
              = .JAL .x0 joff) :
    ∀ a i, (CodeReq.singleton addr (.JAL .x0 joff)) a = some i
         → (CodeReq.ofProg base flat_decoder_prog) a = some i := by
  apply CodeReq.singleton_mono
  rw [CodeReq.ofProg_lookup_addr base flat_decoder_prog idx addr
        (by rw [flat_decoder_prog_length]; exact hk) (by rw [flat_decoder_prog_length]; decide) h_addr,
      h_get]

/-- **Concrete flat decoder spec.** Matches the `decoderH` hypothesis of the flat
    list-loop closure (`FlatListLoop.lean`): for every flat prefix, the program
    `flat_decoder_prog` at `base` runs in 11 steps from `base` to `base + 64`,
    leaving the cascade residue / payload length / payload pointer in
    `x10`/`x11`/`x13`. -/
theorem flat_decoder_spec (base : Word) :
    ∀ (pfx : Byte) (w10 w11 w13 : Word),
      (classifyPrefix pfx = .singleByte ∨ classifyPrefix pfx = .shortBytes
        ∨ classifyPrefix pfx = .shortList) →
      cpsTripleWithin 11 base (base + 64) (CodeReq.ofProg base flat_decoder_prog)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ w10) **
         (.x11 ↦ᵣ w11) ** (.x13 ↦ᵣ w13))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemPayloadPtr pfx w13)) := by
  intro pfx w10 w11 w13 hflat
  exact rlp_decode_single_item_reconverged_flat pfx w10 w11 w13
    28 28 0 24 28 16 4
    base (base + 32) (base + 40) (base + 52) (base + 64)
    (CodeReq.ofProg base flat_decoder_prog)
    hflat
    (by rv64_addr) (by rv64_addr) (by rv64_addr)
    (by rv64_addr) (by rv64_addr) (by rv64_addr)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by simp only [rlp_phase1_step_code]; crDisjoint)
    (by
      simp only [rlp_phase1_step_code]
      refine CodeReq.union_sub (CodeReq.union_sub ?_ ?_) ?_
      · exact flat_piece base base 0 _ (by bv_omega) (by decide) (by decide)
      · exact flat_piece base (base + 32) 8 _ (by bv_omega) (by decide) (by decide)
      · exact flat_jal_piece base (base + 32 + 4) 9 28 (by decide) (by bv_omega) (by decide))
    (by
      simp only [rlp_phase1_step_code]
      refine CodeReq.union_sub (CodeReq.union_sub (CodeReq.union_sub ?_ ?_) ?_) ?_
      · exact flat_piece base base 0 _ (by bv_omega) (by decide) (by decide)
      · exact flat_piece base (base + 8) 2 _ (by bv_omega) (by decide) (by decide)
      · exact flat_piece base (base + 40) 10 _ (by bv_omega) (by decide) (by decide)
      · exact flat_jal_piece base (base + 40 + 8) 12 16 (by decide) (by bv_omega) (by decide))
    (by
      simp only [rlp_phase1_step_code]
      refine CodeReq.union_sub (CodeReq.union_sub
        (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ (CodeReq.union_sub ?_ ?_))) ?_) ?_
      · exact flat_piece base base 0 _ (by bv_omega) (by decide) (by decide)
      · exact flat_piece base (base + 8) 2 _ (by bv_omega) (by decide) (by decide)
      · exact flat_piece base (base + 16) 4 _ (by bv_omega) (by decide) (by decide)
      · exact flat_piece base (base + 24) 6 _ (by bv_omega) (by decide) (by decide)
      · exact flat_piece base (base + 52) 13 _ (by bv_omega) (by decide) (by decide)
      · exact flat_jal_piece base (base + 52 + 8) 15 4 (by decide) (by bv_omega) (by decide))

-- Sanity: program length, and the head-instruction lookup.
example : flat_decoder_prog.length = 16 := flat_decoder_prog_length
example : (CodeReq.ofProg (0 : Word) flat_decoder_prog) 0 = some (.ADDI .x10 .x0 0x80) := by decide

end EvmAsm.Rv64.RLP
