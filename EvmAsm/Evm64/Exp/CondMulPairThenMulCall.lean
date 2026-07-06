/-
  EvmAsm.Evm64.Exp.CondMulPairThenMulCall

  Cond-mul sibling of `Exp/SquaringPairThenMulCall.lean`. Composes the
  17-instruction `exp_loop_cond_mul_marshal_pair_then_call_spec_within`
  (marshal pair + JAL into `mul_callable`) with `mul_callable_spec_within`
  at the JAL target, framing the local scratch slots and the EVM-stack
  base operand through the call, and shrinking the pair-post's 8-limb
  sub-tree at `evmSp[0..56]` to the two `evmWordIs` predicates expected
  by `mul_callable_spec_within`.

  After this composition: a single `cpsTripleWithin (17 + 64) base
  ((base + 68) &&& ~~~1)` over the disjoint `CodeReq.union` of
  `exp_cond_mul_call_block_code base mulOff` and `mul_callable_code mul_target`.
  Unlike the squaring case the two factors differ: factor1 is the running
  result `r := expResultWord r0..r3`, factor2 is the base operand
  `aw := expResultWord a0..a3`, so the post is `evmMulStackPost evmSp r aw`
  (`r * aw`, not a square).

  Refs: GH #92 (parent evm-asm-20z6), bead evm-asm-sgzf0.
  Authored by @pirapira; implemented by Hermes-bot (claude-c1).
-/

import EvmAsm.Evm64.Exp.CondMulCallSeq
import EvmAsm.Evm64.Exp.SquaringMarshalPairPost
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Multiply.Callable

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (CodeReq cpsTripleWithin cpsTripleWithin_extend_code
  cpsTripleWithin_frameL cpsTripleWithin_frameR cpsTripleWithin_seq
  cpsTripleWithin_seq_perm_same_cr cpsTripleWithin_weaken memOwn regOwn
  signExtend12 signExtend21)

/-- Result word produced by the EXP conditional-multiply call block. -/
abbrev expCondMulCallProductW
    (r0 r1 r2 r3 a0 a1 a2 a3 : Word) : EvmWord :=
  expResultWord r0 r1 r2 r3 * expResultWord a0 a1 a2 a3

/-- Compose the cond-mul marshal pair plus its trailing JAL (17 instr) with
    `mul_callable_spec_within` (64 instr) at the JAL target.

    Pre-state (entry, at `base`):
    * Local scratch frame: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3` (running
      result).
    * LP64 frame for `mul_callable`: `(.x12 ↦ᵣ evmSp)`, with
      `evmSp[0..56]` holding any prior values `d_i / e_i` (overwritten
      by the marshal pair).
    * EVM-stack-resident base operand `a` at `evmSp[-64..-40] = a0..a3`
      (read by `a_to_factor2`, preserved across the call).
    * Caller-saved registers consumed by `mul_callable`:
      `(.x5 ↦ᵣ tOld)`, `(.x6 ↦ᵣ v6)`, `(.x7 ↦ᵣ v7)`,
      `(.x10 ↦ᵣ v10)`, `(.x11 ↦ᵣ v11)`.
    * Return-address slot: `(.x1 ↦ᵣ vOld)` — JAL overwrites with
      `base + 68`.

    Post-state (exit, at `(base + 68) &&& ~~~1`):
    * Local scratch unchanged: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * Base operand preserved at `evmSp[-64..-40] = a0..a3`.
    * `mul_callable`'s `evmMulStackPost evmSp r aw` over
      `r := expResultWord r0..r3`, `aw := expResultWord a0..a3`:
      `(.x12 ↦ᵣ evmSp + 32)`, `regOwn` on caller-saved scratch,
      `memOwn` on the four below-sp bytes, and
      `evmWordIs (evmSp + 32) (r * aw)`.
    * `(.x1 ↦ᵣ (base + 68))` — `mul_callable` preserves `.x1`. -/
theorem exp_cond_mul_marshal_pair_then_mul_call_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mul_target : Word)
    (mulOff : BitVec 21) (base : Word)
    (hmt : mul_target = (base + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (exp_cond_mul_call_block_code base mulOff)
            (mul_callable_code mul_target)) :
    cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
      ((exp_cond_mul_call_block_code base mulOff).union
        (mul_callable_code mul_target))
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmMulStackPost evmSp (expResultWord r0 r1 r2 r3)
                              (expResultWord a0 a1 a2 a3) **
       (.x1 ↦ᵣ (base + 68))) := by
  -- (1) Marshal pair + JAL: 17 instr, exit (base+64) + signExtend21 mulOff.
  have hpair := exp_loop_cond_mul_marshal_pair_then_call_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff base
  -- Frame the four extra registers `.x6/.x7/.x10/.x11` consumed by
  -- `mul_callable_spec_within`; the marshal pair never touches them and the
  -- JAL only touches `.x1`.
  have hpairFramed :=
    cpsTripleWithin_frameR
      ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      (by pcFree) hpair
  -- (2) `mul_callable_spec_within` at `mul_target` with factor1 = `r`,
  --     factor2 = `aw` (the EVM-stack base operand), and `ra_val = base+68`.
  have hmul := mul_callable_spec_within
    evmSp mul_target (base + 68)
    (expResultWord r0 r1 r2 r3) (expResultWord a0 a1 a2 a3)
    a3 v6 v7 v10 v11
  -- Frame the local scratch frame `(.x2 ↦ᵣ sp) ** sp[0..24]` AND the
  -- preserved EVM-stack base operand at `evmSp[-64..-40]` on the left;
  -- `mul_callable` does not touch any of those.
  have hmulFramed :=
    cpsTripleWithin_frameL
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))
      (by pcFree) hmul
  -- (3) Compose. The pair-then-JAL exits at `mul_target = (base+64) +
  --     signExtend21 mulOff` (rewrite via hmt to match the mul_callable
  --     entry). Midpoint permutation folds the 8-limb sub-tree at
  --     `evmSp[0..56]` into the two `evmWordIs` predicates.
  rw [← hmt] at hpairFramed
  have hseq :
      cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
        ((exp_cond_mul_call_block_code base mulOff).union
          (mul_callable_code mul_target)) _ _ :=
    cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun h hp => by
          have h0  : (evmSp + signExtend12 (0  : BitVec 12) : Word) = evmSp       := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          have h8  : (evmSp + signExtend12 (8  : BitVec 12) : Word) = evmSp + 8   := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          have h16 : (evmSp + signExtend12 (16 : BitVec 12) : Word) = evmSp + 16  := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          have h24 : (evmSp + signExtend12 (24 : BitVec 12) : Word) = evmSp + 24  := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          have h32 : (evmSp + signExtend12 (32 : BitVec 12) : Word) = evmSp + 32  := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          have h40 : (evmSp + signExtend12 (40 : BitVec 12) : Word) = evmSp + 40  := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          have h48 : (evmSp + signExtend12 (48 : BitVec 12) : Word) = evmSp + 48  := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          have h56 : (evmSp + signExtend12 (56 : BitVec 12) : Word) = evmSp + 56  := by
            simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
          rw [h0, h8, h16, h24, h32, h40, h48, h56] at hp
          have hL : evmWordIs evmSp (expResultWord r0 r1 r2 r3) = _ :=
            evmWordIs_sp_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
              (expResultWord_getLimbN_0 r0 r1 r2 r3)
              (expResultWord_getLimbN_1 r0 r1 r2 r3)
              (expResultWord_getLimbN_2 r0 r1 r2 r3)
              (expResultWord_getLimbN_3 r0 r1 r2 r3)
          have hR : evmWordIs (evmSp + 32) (expResultWord a0 a1 a2 a3) = _ :=
            evmWordIs_sp32_limbs_eq evmSp (expResultWord a0 a1 a2 a3) a0 a1 a2 a3
              (expResultWord_getLimbN_0 a0 a1 a2 a3)
              (expResultWord_getLimbN_1 a0 a1 a2 a3)
              (expResultWord_getLimbN_2 a0 a1 a2 a3)
              (expResultWord_getLimbN_3 a0 a1 a2 a3)
          rw [hL, hR]
          xperm_hyp hp)
        hpairFramed)
      hmulFramed
  -- Re-associate entry pre and exit post into the natural shapes declared.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

/-- Cond-mul full call-block: sequence the cond-mul marshal-pair + JAL +
    mul_callable round-trip with `un_marshal_and_restore` to obtain a single
    `cpsTripleWithin` from `base` to `base + 104` over the disjoint union of
    `exp_cond_mul_call_block_code base mulOff` and `mul_callable_code
    mul_target`. Result word `r * a` (the multiply of running result
    `expResultWord r0..r3` by base operand `expResultWord a0..a3`) is
    delivered into the EXP-local scratch frame at `sp` and the LP64 frame at
    `evmSp + 32`. The EVM-stack base operand at `evmSp[-64..-40]` is
    preserved. Slice 5 micro evm-asm-c03pg, cond-mul sibling of
    `exp_squaring_call_block_spec_within`. -/
theorem exp_cond_mul_call_block_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mul_target : Word)
    (mulOff : BitVec 21) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mul_target = (base + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (exp_cond_mul_call_block_code base mulOff)
            (mul_callable_code mul_target)) :
    let productW := expCondMulCallProductW r0 r1 r2 r3 a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) base (base + 104)
      ((exp_cond_mul_call_block_code base mulOff).union
        (mul_callable_code mul_target))
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ productW.getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp productW ** evmWordIs (evmSp + 32) productW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ (base + 68))) := by
  intro productW
  let r := expResultWord r0 r1 r2 r3
  let aw := expResultWord a0 a1 a2 a3
  -- (1) Marshal-pair + JAL + mul_callable: 81 instrs, exit (base+68) &&& ~~~1.
  have h1 := exp_cond_mul_marshal_pair_then_mul_call_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mul_target mulOff base hmt hd
  -- (2) Alignment under base &&& 1 = 0.
  have halign : (base + 68 : Word) &&& ~~~(1 : Word) = base + 68 := by
    have hb0 : base.getLsbD 0 = false := by
      have h : (base &&& 1).getLsbD 0 = (0 : Word).getLsbD 0 := by rw [hbase]
      rw [BitVec.getLsbD_and] at h
      rw [show BitVec.getLsbD (1 : Word) 0 = true from rfl,
          show BitVec.getLsbD (0 : Word) 0 = false from rfl, Bool.and_true] at h
      exact h
    have hsum0 : (base + 68 : Word).getLsbD 0 = false := by
      rw [BitVec.getLsbD_add (by omega), hb0, BitVec.carry_zero]; rfl
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
    by_cases h0 : i = 0
    · subst h0; rw [hsum0]; simp
    · have h1 : (1 : Word).getLsbD i = false := by simp [BitVec.getLsbD_one, h0]
      rw [h1]; simp [hi]
  rw [halign] at h1
  -- (3) un_marshal_and_restore_word at offset (base+68) with w' = r * aw.
  have h2_raw := exp_loop_un_marshal_and_restore_word_spec_within_regOwn5
    sp evmSp r0 r1 r2 r3 (base + 68) (r * aw)
  -- Lift code: ofProg (base+68) un_marshal_and_restore ⊆ union.
  have h2_lifted : cpsTripleWithin 9 (base + 68) ((base + 68) + 36)
      ((exp_cond_mul_call_block_code base mulOff).union
        (mul_callable_code mul_target)) _ _ :=
    cpsTripleWithin_extend_code
      (hmono := fun a i h =>
        CodeReq.union_mono_left (cr2 := mul_callable_code mul_target) a i
          (exp_cond_mul_call_block_code_un_marshal_and_restore_sub base mulOff a i h))
      h2_raw
  -- Frame on the LEFT extras not consumed by un_marshal: a-source slots,
  -- regOwn x6/x7/x10/x11, memOwn evmSp[0..24], (.x1 ↦ (base+68)).
  have h2_framed :=
    cpsTripleWithin_frameL
      (((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ (base + 68)))
      (by pcFree) h2_lifted
  have hexit : (base + 68 : Word) + 36 = base + 104 :=
    EvmAsm.Evm64.Exp.AddrNorm.expCallBlockRestoreExitPc base
  rw [hexit] at h2_framed
  -- (4) Compose with mid-point permutation.
  have hseq : cpsTripleWithin (17 + 64 + 9) base (base + 104)
      ((exp_cond_mul_call_block_code base mulOff).union
        (mul_callable_code mul_target)) _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        delta evmMulStackPost at hp
        xperm_hyp hp)
      h1 h2_framed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

end EvmAsm.Evm64
