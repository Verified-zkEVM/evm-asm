/-
  EvmAsm.Evm64.Exp.MarshalPair

  Composition of the two consecutive marshal blocks that precede the JAL to
  `mul_callable` on the EXP squaring path:

      exp_loop_marshal_factor1            -- 8 instr, base..(base+32)
      exp_loop_marshal_result_to_factor2  -- 8 instr, (base+32)..(base+64)

  Both leaves read `sp[0..24]` (the local accumulator scratch) and write into
  the LP64 factor slots beneath `x12`. Their write footprints are disjoint
  (`evmSp[0..24]` vs `evmSp[32..56]`), so the composition is a clean
  `cpsTripleWithin_seq` with frame-extensions on each side.

  This file factors the two-block prefix out of the four-block
  `exp_squaring_call_block` composition (`evm-asm-nrfpf`), shrinking the JAL
  + un-marshal compose step that follows it.

  Reference: GH #92 (parent evm-asm-20z6), beads slice evm-asm-ms8ms (sub-
  slice of evm-asm-nrfpf). Authored by @pirapira; implemented by Hermes-bot.
-/

module

public import EvmAsm.Evm64.Exp.LimbSpec
public import EvmAsm.Evm64.Exp.AddrNorm

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (CodeReq cpsTripleWithin cpsTripleWithin_frameL cpsTripleWithin_frameR
  cpsTripleWithin_seq_with_perm cpsTripleWithin_weaken signExtend12)

/-- Code requirement for the two-block squaring marshal prefix: the union
    of `factor1` at `base..(base+32)` and `result_to_factor2` at
    `(base+32)..(base+64)`. -/
abbrev exp_loop_squaring_marshal_pair_code (base : Word) : CodeReq :=
  (CodeReq.ofProg base exp_loop_marshal_factor1).union
    (CodeReq.ofProg (base + 32) exp_loop_marshal_result_to_factor2)

private theorem exp_loop_squaring_marshal_pair_codes_disjoint (base : Word) :
    (CodeReq.ofProg base exp_loop_marshal_factor1).Disjoint
      (CodeReq.ofProg (base + 32) exp_loop_marshal_result_to_factor2) := by
  apply CodeReq.ofProg_disjoint_range
  intro k1 k2 hk1 hk2
  simp only [exp_loop_marshal_factor1_length,
    exp_loop_marshal_result_to_factor2_length] at hk1 hk2
  exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor1_factor2_disjoint_addr
    base hk1 hk2

/-- factor1 sub-block ⊆ squaring marshal-pair code. -/
theorem exp_loop_squaring_marshal_pair_code_factor1_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg base exp_loop_marshal_factor1) a = some i →
      (exp_loop_squaring_marshal_pair_code base) a = some i := by
  unfold exp_loop_squaring_marshal_pair_code
  exact CodeReq.union_mono_left

/-- result-to-factor2 sub-block ⊆ squaring marshal-pair code. -/
theorem exp_loop_squaring_marshal_pair_code_result_to_factor2_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 32)
      exp_loop_marshal_result_to_factor2) a = some i →
      (exp_loop_squaring_marshal_pair_code base) a = some i := by
  unfold exp_loop_squaring_marshal_pair_code
  apply CodeReq.mono_union_right
    (exp_loop_squaring_marshal_pair_codes_disjoint base)
  intro a i h
  exact h

/-- Composition of `exp_loop_marshal_factor1` followed by
    `exp_loop_marshal_result_to_factor2`. Both blocks read the four limbs
    of the accumulator from `sp[0..24]`; `factor1` writes them into
    `evmSp[0..24]` (the LP64 factor-1 slot) and `result_to_factor2` then
    copies the same limbs into `evmSp[32..56]` (the LP64 factor-2 slot).
    Net effect: factor1 = factor2 = accumulator, scratch unchanged. -/
theorem exp_loop_squaring_marshal_pair_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 : Word) (base : Word) :
    cpsTripleWithin 16 base (base + 64)
      (exp_loop_squaring_marshal_pair_code base)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) := by
  -- Frame for h1 (factor1): the four factor-2 slots evmSp[32..56].
  have h1 := exp_loop_marshal_factor1_spec_within sp evmSp tOld
    r0 r1 r2 r3 d0 d1 d2 d3 base
  rw [show exp_loop_marshal_factor1_code base
        = CodeReq.ofProg base exp_loop_marshal_factor1 from
        exp_loop_marshal_factor1_code_eq_ofProg base] at h1
  have h1Frame :=
    cpsTripleWithin_frameR
      (((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3))
      (by pcFree) h1
  -- Frame for h2 (result_to_factor2): the four factor-1 slots evmSp[0..24]
  -- (now holding r0..r3 after h1).
  have h2 := exp_loop_marshal_result_to_factor2_spec_within sp evmSp r3
    r0 r1 r2 r3 e0 e1 e2 e3 (base + 32)
  rw [show exp_loop_marshal_result_to_factor2_code (base + 32)
        = CodeReq.ofProg (base + 32) exp_loop_marshal_result_to_factor2 from
        exp_loop_marshal_result_to_factor2_code_eq_ofProg (base + 32)] at h2
  have h2Frame :=
    cpsTripleWithin_frameL
      (((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))
      (by pcFree) h2
  -- Compose; bounds 8 + 8 = 16, exit (base + 32) + 32 = base + 64. h1's
  -- post-condition is right-leaning over h1's frame `(... factor2 slots)`,
  -- whereas h2's pre is right-leaning over h2's frame `(... factor1 slots)`;
  -- bridge with `xperm_hyp` via `cpsTripleWithin_seq_with_perm`.
  have hd := exp_loop_squaring_marshal_pair_codes_disjoint base
  have hseq := cpsTripleWithin_seq_with_perm hd
    (fun _ hp => by xperm_hyp hp) h1Frame h2Frame
  -- Normalize the exit address (base + 32) + 32 → base + 64.
  have hexit : (base + 32 : Word) + 32 = base + 64 :=
    EvmAsm.Evm64.Exp.AddrNorm.expMarshalPairExitPc base
  rw [hexit] at hseq
  -- Permute pre and post into the natural shape.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

end EvmAsm.Evm64
