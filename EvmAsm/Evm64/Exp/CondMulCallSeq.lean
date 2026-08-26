/-
  EvmAsm.Evm64.Exp.CondMulCallSeq

  Cond-mul sibling of `Exp/SquaringCallSeq.lean`. Composes the 16-instruction
  `exp_loop_cond_mul_marshal_pair` (factor1 ;; a_to_factor2) with the 1-instr
  JAL into `mul_callable` at `base + 64`, lifted to the
  `exp_cond_mul_call_block_code base mulOff` requirement.

  After this composition: a single `cpsTripleWithin 17 base
  ((base + 64) + signExtend21 mulOff)` over `exp_cond_mul_call_block_code
  base mulOff`, with post = marshal-pair post (factor1 = `r0..r3`,
  factor2 = `a0..a3`) plus `(.x1 ↦ᵣ (base + 68))`.

  Building block for the cond-mul `pair_then_mul_call` round-trip
  (evm-asm-sgzf0), the cond-mul sibling of
  `Exp/SquaringPairThenMulCall.lean`.

  Refs: GH #92 (parent evm-asm-20z6), bead evm-asm-womkp (sub-slice of
  evm-asm-sgzf0). Authored by @pirapira; implemented by Hermes-bot
  (claude-c1).
-/

module

public import EvmAsm.Evm64.Exp.CondMulMarshalPair
public import EvmAsm.Evm64.Exp.CondMulCall

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (cpsTripleWithin cpsTripleWithin_extend_code cpsTripleWithin_frameL
  cpsTripleWithin_frameR cpsTripleWithin_seq_perm_same_cr cpsTripleWithin_weaken
  signExtend12 signExtend21)

/-- Compose the cond-mul marshal pair (16 instr, `base..(base+64)`) with
    its trailing JAL into `mul_callable` (1 instr at `base+64`).

    Pre-state (entry, at `base`):
    * Local scratch frame: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * LP64 frame for `mul_callable`: `(.x12 ↦ᵣ evmSp)`, with
      `evmSp[0..56]` holding any prior values `d_i / e_i` (overwritten
      by the marshal pair).
    * EVM-stack-resident base operand `a`: `evmSp[-64..-40] = a0..a3`
      (unchanged across the pair).
    * `(.x5 ↦ᵣ tOld)` — the marshal pair overwrites with `a3`.
    * Return-address slot: `(.x1 ↦ᵣ vOld)` — the JAL overwrites this
      with `base + 68`, which `mul_callable`'s `cc_ret` reads back.

    Post-state (exit, at `(base + 64) + signExtend21 mulOff`):
    * Local scratch unchanged: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * LP64 factor-1 = `r0..r3` at `evmSp[0..24]`,
      factor-2 = `a0..a3` at `evmSp[32..56]`.
    * Base operand preserved at `evmSp[-64..-40]`.
    * `(.x5 ↦ᵣ a3)` (last value written by `a_to_factor2`).
    * `(.x1 ↦ᵣ (base + 68))`. -/
theorem exp_loop_cond_mul_marshal_pair_then_call_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (base : Word) :
    cpsTripleWithin 17 base ((base + 64) + signExtend21 mulOff)
      (exp_cond_mul_call_block_code base mulOff)
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
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x1 ↦ᵣ (base + 68))) := by
  -- (1) Marshal pair: 16 instr, base..(base+64).
  have hpair := exp_loop_cond_mul_marshal_pair_spec_within
    sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 base
  -- Frame `(.x1 ↦ᵣ vOld)` on the right; the marshal pair never touches `.x1`.
  have hpairFramed := cpsTripleWithin_frameR (.x1 ↦ᵣ vOld) (by pcFree) hpair
  -- Lift pair code ⊆ exp_cond_mul_call_block_code base mulOff.
  have hpairLifted := cpsTripleWithin_extend_code
    (exp_cond_mul_call_block_code_marshal_pair_sub base mulOff) hpairFramed
  -- (2) JAL: 1 instr at base+64, exit (base+64)+signExtend21 mulOff.
  have hjalRaw := exp_square_block_spec_within mulOff vOld (base + 64)
  have hb : (base + 64 : Word) + 4 = base + 68 := by
    exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_square_end_addr base
  rw [hb] at hjalRaw
  -- Frame the entire pair-post (every slot but `.x1`) on the left of the JAL.
  have hjalFramed :=
    cpsTripleWithin_frameL
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))
      (by pcFree) hjalRaw
  -- Lift the JAL's narrow code (square block at base+64) into the full code.
  have hjalLifted := cpsTripleWithin_extend_code
    (exp_cond_mul_call_block_code_square_sub base mulOff) hjalFramed
  -- (3) Compose with a midpoint permutation.
  have hseq : cpsTripleWithin (16 + 1) base ((base + 64) + signExtend21 mulOff)
      (exp_cond_mul_call_block_code base mulOff) _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hpairLifted hjalLifted
  -- Permute the entry pre and exit post into the natural right-leaning shape.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

end EvmAsm.Evm64
