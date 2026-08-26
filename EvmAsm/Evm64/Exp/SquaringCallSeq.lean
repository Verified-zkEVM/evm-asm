/-
  EvmAsm.Evm64.Exp.SquaringCallSeq

  First half of the four-block `exp_squaring_call_block` composition
  (`evm-asm-nrfpf`): the 16-instruction squaring marshal pair followed by the
  1-instruction JAL into `mul_callable`. Compose those two pieces, framing
  `.x1` through the pair (the pair does not touch `x1`) and the pair's
  post-state through the JAL (the JAL only touches `x1`), and lift the
  resulting `cpsTripleWithin` to the full `exp_squaring_call_block_code`.

  This factors the harder JAL-into-mul_callable round-trip step out of the
  full four-block compose: downstream slice (`evm-asm-nrfpf`) only has to
  splice `mul_callable_spec_within` at the JAL target and then continue
  into `exp_loop_un_marshal_and_restore_spec_within`, instead of also
  composing the marshal pair from scratch.

  Refs: GH #92, beads `evm-asm-9w0jy` (sub-slice of `evm-asm-nrfpf`).
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Evm64.Exp.MarshalPair
public import EvmAsm.Evm64.Exp.SquaringCall

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (Assertion CodeReq cpsTripleWithin cpsTripleWithin_extend_code
  cpsTripleWithin_frameL cpsTripleWithin_frameR cpsTripleWithin_seq_perm_same_cr
  cpsTripleWithin_weaken signExtend12 signExtend21)

/-- Composition of the squaring marshal pair (factor1 ;; result_to_factor2,
    16 instr at offsets 0..32..64) and the squaring JAL (1 instr at offset 64),
    lifted to `exp_squaring_call_block_code base mulOff`.

    After this composition, control transfers to `(base + 64) + signExtend21
    mulOff` (the JAL target — the entry of `mul_callable`) with `.x1`
    holding the JAL's link address `base + 68` (offset of the un_marshal
    block, which is what `mul_callable`'s `cc_ret` will jump back to).

    Pair pre: scratch `sp[0..24] = result limbs r0..r3`; LP64 factor1 slot
    `evmSp[0..24]` and factor2 slot `evmSp[32..56]` hold any prior values
    `d_i` / `e_i`. Pair post: factor1 = factor2 = result limbs, scratch
    unchanged. The JAL only updates `.x1`. -/
theorem exp_loop_squaring_marshal_pair_then_square_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (base : Word) :
    cpsTripleWithin 17 base ((base + 64) + signExtend21 mulOff)
      (exp_squaring_call_block_code base mulOff)
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
       (.x1 ↦ᵣ vOld))
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
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) **
       (.x1 ↦ᵣ (base + 68))) := by
  -- (1) Pair: 16 instr, base..(base+64), code = exp_loop_squaring_marshal_pair_code base.
  have hpair := exp_loop_squaring_marshal_pair_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 base
  -- Frame `(.x1 ↦ᵣ vOld)` on the right; the pair never touches `.x1`.
  have hpairFramed := cpsTripleWithin_frameR (.x1 ↦ᵣ vOld) (by pcFree) hpair
  -- Lift pair code ⊆ exp_squaring_call_block_code base mulOff.
  have hpairSub : ∀ a i, exp_loop_squaring_marshal_pair_code base a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
    intro a i h
    exact CodeReq.union_sub
      (exp_squaring_call_block_code_marshal_factor1_sub base mulOff)
      (exp_squaring_call_block_code_marshal_result_to_factor2_sub base mulOff)
      a i h
  have hpairLifted := cpsTripleWithin_extend_code hpairSub hpairFramed
  -- (2) JAL: 1 instr at base+64, exit (base+64)+signExtend21 mulOff,
  --     code = exp_square_block_code (base+64) mulOff.
  have hjalRaw := exp_square_block_spec_within mulOff vOld (base + 64)
  -- Normalize the link-address: (base+64) + 4 = base + 68.
  have hb : (base + 64 : Word) + 4 = base + 68 := by
    exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_square_end_addr base
  rw [hb] at hjalRaw
  -- Frame the entire pair-post (every slot but `.x1`) on the left of the JAL.
  -- The pair-post is exactly the assertion below, in the same right-leaning shape.
  have hjalFramed :=
    cpsTripleWithin_frameL
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
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3))
      (by pcFree) hjalRaw
  -- Lift the JAL's narrow code (square block at base+64) into the full code.
  have hjalLifted := cpsTripleWithin_extend_code
    (exp_squaring_call_block_code_square_sub base mulOff) hjalFramed
  -- (3) Compose with a midpoint permutation that re-associates the pair-post
  --     `(P_pair) ** (.x1 ↦ᵣ vOld)` (left-leaning at the join with the framed
  --     `.x1`) into the JAL pre's right-leaning shape `memPost ** (.x1 ↦ᵣ vOld)`.
  have hseq : cpsTripleWithin (16 + 1) base ((base + 64) + signExtend21 mulOff)
      (exp_squaring_call_block_code base mulOff) _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hpairLifted hjalLifted
  -- Permute the entry pre and exit post into the natural right-leaning shape
  -- declared in the theorem's type.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

/-- Right-framed wrapper for
    `exp_loop_squaring_marshal_pair_then_square_spec_within`, useful when the
    squaring prefix is spliced into a larger composition with an untouched
    frame. -/
theorem exp_loop_squaring_marshal_pair_then_square_spec_within_right
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (base : Word) (Q : Assertion) (hQ : Q.pcFree) :
    cpsTripleWithin 17 base ((base + 64) + signExtend21 mulOff)
      (exp_squaring_call_block_code base mulOff)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       (.x1 ↦ᵣ vOld)) ** Q)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
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
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) **
       (.x1 ↦ᵣ (base + 68))) ** Q) := by
  exact cpsTripleWithin_frameR Q hQ
    (exp_loop_squaring_marshal_pair_then_square_spec_within
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff base)

end EvmAsm.Evm64
