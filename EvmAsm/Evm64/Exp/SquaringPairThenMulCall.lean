/-
  EvmAsm.Evm64.Exp.SquaringPairThenMulCall

  Second prep step for `exp_squaring_call_block_spec_within` (#92 slice
  4-squaring-call, parent `evm-asm-nrfpf`): compose the existing
  `exp_loop_squaring_marshal_pair_then_square_spec_within` (16 marshal-pair
  instructions plus the 1-instruction JAL into `mul_callable`) with
  `mul_callable_spec_within` at the JAL target, framing the local scratch
  slots `sp[0..24]` and `(.x2 ↦ᵣ sp)` through the call (mul_callable does
  not touch them, since its LP64 frame pointer is `evmSp` carried in
  `x12`), and shrinking the pair-post's 8-limb sub-tree at `evmSp[0..56]`
  to the two `evmWordIs` predicates expected by `mul_callable_spec_within`
  via `exp_squaring_marshal_pair_post_evmWordIs`.

  After this composition: a single `cpsTripleWithin (16 + 1 + 64) base
  ((base + 68) &&& ~~~1)` over the disjoint `CodeReq.union` of
  `exp_squaring_call_block_code base mulOff` and `mul_callable_code mul_target`.
  The downstream slice (`evm-asm-nrfpf`) then only has to seq this with
  `exp_loop_un_marshal_and_restore_spec_within` to obtain
  `exp_squaring_call_block_spec_within`.

  Refs: GH #92, beads `evm-asm-ct3ti` (sub-slice of `evm-asm-nrfpf`).
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Exp.SquaringCallSeq
import EvmAsm.Evm64.Exp.SquaringMarshalPairPost
import EvmAsm.Evm64.Multiply.Callable

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (Assertion CodeReq cpsTripleWithin cpsTripleWithin_extend_code
  cpsTripleWithin_frameL cpsTripleWithin_frameR cpsTripleWithin_of_forall_regIs_to_regOwn
  cpsTripleWithin_seq cpsTripleWithin_seq_perm_same_cr cpsTripleWithin_weaken
  memOwn regOwn signExtend12 signExtend21)

abbrev expSquaringCallSquareW (r0 r1 r2 r3 : Word) : EvmWord :=
  let w := expResultWord r0 r1 r2 r3
  w * w

/-- Code required by the squaring-call block plus the out-of-line
    `mul_callable` body reached by the JAL inside the block. -/
abbrev exp_squaring_call_with_mul_code
    (base mulTarget : Word) (mulOff : BitVec 21) : CodeReq :=
  (exp_squaring_call_block_code base mulOff).union
    (mul_callable_code mulTarget)

theorem exp_squaring_call_with_mul_code_block_sub
    (base mulTarget : Word) (mulOff : BitVec 21) :
    ∀ a i, (exp_squaring_call_block_code base mulOff) a = some i →
      (exp_squaring_call_with_mul_code base mulTarget mulOff) a = some i := by
  unfold exp_squaring_call_with_mul_code
  exact CodeReq.union_mono_left

theorem exp_squaring_call_with_mul_code_mul_callable_sub
    (base mulTarget : Word) (mulOff : BitVec 21)
    (hd : CodeReq.Disjoint
            (exp_squaring_call_block_code base mulOff)
            (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (exp_squaring_call_with_mul_code base mulTarget mulOff) a = some i := by
  unfold exp_squaring_call_with_mul_code
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- Bridge the post-call MUL result word at `evmSp + 32` into the
    unmarshal/restore block, producing the same word in the local EXP scratch
    frame at `sp`. -/
theorem exp_loop_un_marshal_and_restore_word_spec_within
    (sp evmSp tOld r0 r1 r2 r3 base : Word) (w : EvmWord) :
    cpsTripleWithin 9 base (base + 36)
      (CodeReq.ofProg base exp_loop_un_marshal_and_restore)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) w)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ w.getLimbN 3) **
       evmWordIs sp w ** evmWordIs (evmSp + 32) w) := by
  have h_unmarshal := exp_loop_un_marshal_and_restore_ofProg_spec_within
    sp (evmSp + 32) tOld r0 r1 r2 r3
    (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) base
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      have h0 : ((evmSp + 32) + signExtend12 (0 : BitVec 12) : Word) =
          evmSp + 32 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have h8 : ((evmSp + 32) + signExtend12 (8 : BitVec 12) : Word) =
          evmSp + 40 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have h16 : ((evmSp + 32) + signExtend12 (16 : BitVec 12) : Word) =
          evmSp + 48 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have h24 : ((evmSp + 32) + signExtend12 (24 : BitVec 12) : Word) =
          evmSp + 56 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      rw [h0, h8, h16, h24]
      unfold evmWordIs at hp
      have hSrc8 : ((evmSp + 32) + 8 : Word) = evmSp + 40 :=
        EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add8 evmSp
      have hSrc16 : ((evmSp + 32) + 16 : Word) = evmSp + 48 :=
        EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add16 evmSp
      have hSrc24 : ((evmSp + 32) + 24 : Word) = evmSp + 56 :=
        EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add24 evmSp
      rw [hSrc8, hSrc16, hSrc24] at hp
      xperm_hyp hp)
    (fun _ hp => by
      have hRestore : ((evmSp + 32) + signExtend12 (-32 : BitVec 12) : Word) =
          evmSp := by
        have : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by decide
        rw [this]; bv_omega
      have h0 : ((evmSp + 32) + signExtend12 (0 : BitVec 12) : Word) =
          evmSp + 32 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have h8 : ((evmSp + 32) + signExtend12 (8 : BitVec 12) : Word) =
          evmSp + 40 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have h16 : ((evmSp + 32) + signExtend12 (16 : BitVec 12) : Word) =
          evmSp + 48 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have h24 : ((evmSp + 32) + signExtend12 (24 : BitVec 12) : Word) =
          evmSp + 56 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      rw [hRestore, h0, h8, h16, h24] at hp
      have hSp0 : (sp + signExtend12 (0 : BitVec 12) : Word) = sp := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have hSp8 : (sp + signExtend12 (8 : BitVec 12) : Word) = sp + 8 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have hSp16 : (sp + signExtend12 (16 : BitVec 12) : Word) = sp + 16 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have hSp24 : (sp + signExtend12 (24 : BitVec 12) : Word) = sp + 24 := by
        simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
      have hSrc8 : ((evmSp + 32) + 8 : Word) = evmSp + 40 :=
        EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add8 evmSp
      have hSrc16 : ((evmSp + 32) + 16 : Word) = evmSp + 48 :=
        EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add16 evmSp
      have hSrc24 : ((evmSp + 32) + 24 : Word) = evmSp + 56 :=
        EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add24 evmSp
      rw [hSp0, hSp8, hSp16, hSp24] at hp
      unfold evmWordIs
      rw [hSrc8, hSrc16, hSrc24]
      xperm_hyp hp)
    h_unmarshal

/-- Weakened-pre variant of `exp_loop_un_marshal_and_restore_word_spec_within`:
    consumes `regOwn .x5` in place of a concrete `(.x5 ↦ᵣ tOld)`. The
    un_marshal block loads `w.getLimbN 3` into `.x5`, so it does not care
    about the prior value — any old value works. This bridges the seq
    composition with `mul_callable_spec_within`'s post (which carries
    `regOwn .x5` via `evmMulStackPost`) and the un_marshal entry. Slice 4
    micro evm-asm-xdmss. -/
theorem exp_loop_un_marshal_and_restore_word_spec_within_regOwn5
    (sp evmSp r0 r1 r2 r3 base : Word) (w : EvmWord) :
    cpsTripleWithin 9 base (base + 36)
      (CodeReq.ofProg base exp_loop_un_marshal_and_restore)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs (evmSp + 32) w) ** regOwn .x5)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ w.getLimbN 3) **
       evmWordIs sp w ** evmWordIs (evmSp + 32) w) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn (fun tOld =>
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => hp)
      (exp_loop_un_marshal_and_restore_word_spec_within sp evmSp tOld
        r0 r1 r2 r3 base w))

/-- Compose the squaring marshal pair (16 instr) plus its trailing JAL
    (1 instr) with `mul_callable_spec_within` (64 instr) at the JAL target.

    Pre-state (entry, at `base`):
    * Local scratch frame: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * LP64 frame for `mul_callable`: `(.x12 ↦ᵣ evmSp)`, with
      `evmSp[0..24]` and `evmSp[32..56]` holding any prior values
      `d_i / e_i` (overwritten by the marshal pair).
    * Caller-saved registers consumed by `mul_callable`:
      `(.x5 ↦ᵣ tOld)`, `(.x6 ↦ᵣ v6)`, `(.x7 ↦ᵣ v7)`,
      `(.x10 ↦ᵣ v10)`, `(.x11 ↦ᵣ v11)`.
    * Return-address slot: `(.x1 ↦ᵣ vOld)` — the JAL overwrites this
      with `base + 68`, which `mul_callable`'s `cc_ret` reads back.

    Post-state (exit, at `(base + 68) &&& ~~~1`):
    * Local scratch unchanged: `(.x2 ↦ᵣ sp)`, `sp[0..24] = r0..r3`.
    * `mul_callable`'s `evmMulStackPost evmSp w w` over
      `w := expResultWord r0 r1 r2 r3` (squaring of the limb-packed
      result word): `(.x12 ↦ᵣ evmSp + 32)`, `regOwn` on the
      caller-saved scratch registers, `memOwn` on the four bytes
      below the new LP64 sp, and `evmWordIs (evmSp + 32) squareW`.
    * `(.x1 ↦ᵣ (base + 68))` — `mul_callable` preserves `.x1`. -/
theorem exp_squaring_marshal_pair_then_mul_call_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mul_target : Word)
    (mulOff : BitVec 21) (base : Word)
    (hmt : mul_target = (base + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (exp_squaring_call_block_code base mulOff)
            (mul_callable_code mul_target)) :
    cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
      ((exp_squaring_call_block_code base mulOff).union
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmMulStackPost evmSp (expResultWord r0 r1 r2 r3)
                              (expResultWord r0 r1 r2 r3) **
       (.x1 ↦ᵣ (base + 68))) := by
  -- (1) Pair + JAL: 17 instructions, exit (base+64) + signExtend21 mulOff,
  --     code = exp_squaring_call_block_code base mulOff. Already proven.
  have hpair := exp_loop_squaring_marshal_pair_then_square_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff base
  -- Frame the four extra registers `(.x6, .x7, .x10, .x11)` consumed by
  -- `mul_callable_spec_within` on the right; the marshal pair never touches
  -- them, and the JAL only touches `.x1`.
  have hpairFramed :=
    cpsTripleWithin_frameR
      ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      (by pcFree) hpair
  -- (2) `mul_callable_spec_within` at `mul_target = (base+64)+signExtend21 mulOff`
  --     with `ra_val = base + 68`, working on the LP64 frame at `evmSp`,
  --     squaring `expResultWord r0..r3`.
  have hmul := mul_callable_spec_within
    evmSp mul_target (base + 68)
    (expResultWord r0 r1 r2 r3) (expResultWord r0 r1 r2 r3)
    r3 v6 v7 v10 v11
  -- Frame the local scratch frame `(.x2 ↦ᵣ sp) ** sp[0..24]` on the left;
  -- `mul_callable` does not touch any of those (its LP64 frame is `evmSp`
  -- via `x12`).
  have hmulFramed :=
    cpsTripleWithin_frameL
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))
      (by pcFree) hmul
  -- (3) Compose. The pair-then-JAL exits at `mul_target = (base+64) +
  --     signExtend21 mulOff` (rewrite via hmt to match the mul_callable
  --     entry). Midpoint permutation: re-associate the framed pair-post
  --     into the framed mul_callable pre, folding the 8-limb sub-tree at
  --     `evmSp[0..56]` into the two `evmWordIs` predicates.
  rw [← hmt] at hpairFramed
  have hseq :
      cpsTripleWithin (17 + 64) base ((base + 68) &&& ~~~1)
        ((exp_squaring_call_block_code base mulOff).union
          (mul_callable_code mul_target)) _ _ :=
    cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun h hp => by
          -- The pair-post has 8 explicit memIs atoms at
          --   `evmSp + signExtend12 N` for N = 0,8,..,56.
          -- The mul_callable pre has
          --   `evmWordIs evmSp w ** evmWordIs (evmSp+32) w`
          -- with `w := expResultWord r0 r1 r2 r3`. Expand each `evmWordIs`
          -- to its 4-memIs form (which uses literal `evmSp`, `evmSp+8`, ...
          -- offsets, no `signExtend12` wrapper), canonicalize the pair-post
          -- offsets to match, and permute atom-by-atom.
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
          have hR : evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3) = _ :=
            evmWordIs_sp32_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
              (expResultWord_getLimbN_0 r0 r1 r2 r3)
              (expResultWord_getLimbN_1 r0 r1 r2 r3)
              (expResultWord_getLimbN_2 r0 r1 r2 r3)
              (expResultWord_getLimbN_3 r0 r1 r2 r3)
          rw [hL, hR]
          xperm_hyp hp)
        hpairFramed)
      hmulFramed
  -- Re-associate entry pre and exit post into the natural shapes declared
  -- in the theorem's type.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

/-- Squaring full call-block: sequence the marshal-pair + JAL + mul_callable
    round-trip with `un_marshal_and_restore` to obtain a single
    `cpsTripleWithin` from `base` to `base + 104` over the disjoint union of
    `exp_squaring_call_block_code base mulOff` and `mul_callable_code
    mul_target`. The result word `squareW` (the squaring of `expResultWord
    r0..r3`) is delivered into the EXP-local scratch frame at `sp` and the
    LP64 frame at `evmSp + 32`. Slice 5 micro evm-asm-ifaon. -/
theorem exp_squaring_call_block_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mul_target : Word)
    (mulOff : BitVec 21) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mul_target = (base + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (exp_squaring_call_block_code base mulOff)
            (mul_callable_code mul_target)) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    cpsTripleWithin (17 + 64 + 9) base (base + 104)
      ((exp_squaring_call_block_code base mulOff).union
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ (base + 68))) := by
  intro squareW
  -- (1) Marshal-pair + JAL + mul_callable: 81 instrs, exit (base+68) &&& ~~~1.
  have h1 := exp_squaring_marshal_pair_then_mul_call_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mul_target mulOff base hmt hd
  -- (2) Alignment: under base &&& 1 = 0, (base+68) &&& ~~~1 = base+68.
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
  -- (3) un_marshal_and_restore_word at offset (base+68), with w' = squareW.
  have h2_raw := exp_loop_un_marshal_and_restore_word_spec_within_regOwn5
    sp evmSp r0 r1 r2 r3 (base + 68) squareW
  -- Lift code: ofProg (base+68) un_marshal_and_restore ⊆ union.
  have h2_lifted := cpsTripleWithin_extend_code
    (hmono := fun a i h =>
      exp_squaring_call_with_mul_code_block_sub base mul_target mulOff a i
        (exp_squaring_call_block_code_un_marshal_and_restore_sub base mulOff a i h))
    h2_raw
  -- Frame on the LEFT the extra atoms not consumed by un_marshal:
  --   regOwn .x6/.x7/.x10/.x11 ** memOwn evmSp[0..24] ** (.x1 ↦ (base+68)).
  have h2_framed :=
    cpsTripleWithin_frameL
      (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ (base + 68)))
      (by pcFree) h2_lifted
  -- Exit pcs: (base+68) + 36 = base + 104.
  have hexit : (base + 68 : Word) + 36 = base + 104 :=
    EvmAsm.Evm64.Exp.AddrNorm.expCallBlockRestoreExitPc base
  rw [hexit] at h2_framed
  -- (4) Compose with mid-point permutation: align h1's post with
  -- h2_framed's pre.
  have hpcFreeMulPost :
      (evmMulStackPost evmSp
        (expResultWord r0 r1 r2 r3) (expResultWord r0 r1 r2 r3)).pcFree := by
    delta evmMulStackPost; pcFree
  have hseq : cpsTripleWithin (17 + 64 + 9) base (base + 104)
      ((exp_squaring_call_block_code base mulOff).union
        (mul_callable_code mul_target)) _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        delta evmMulStackPost at hp
        xperm_hyp hp)
      h1 h2_framed
  -- Re-associate to the natural post shape.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hseq

end EvmAsm.Evm64
