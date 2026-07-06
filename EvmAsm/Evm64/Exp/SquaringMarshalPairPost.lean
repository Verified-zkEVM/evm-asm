/-
  EvmAsm.Evm64.Exp.SquaringMarshalPairPost

  Bridge: fold the 8 limb-level memIs atoms produced by the post-state of
  `exp_loop_squaring_marshal_pair_spec_within` (4 atoms in the LP64 factor-1
  slot at `evmSp[0..24]` plus 4 atoms in the factor-2 slot at `evmSp[32..56]`,
  all carrying the same scratch limbs `r0..r3`) into the two `evmWordIs`
  predicates expected by `mul_callable_spec_within` (a = b at `evmSp` and
  `evmSp + 32`).

  The packed EVM word is `expResultWord r0 r1 r2 r3` — i.e.
  `EvmWord.fromLimbs` over the four limbs in little-endian order.

  Sub-slice of evm-asm-nrfpf (#92 slice 4-squaring-call-spec): downstream
  `evm-asm-ct3ti` (the JAL-into-mul_callable round-trip composition) needs
  this bridge to shrink `mul_callable`'s `(evmWordIs sp a ** evmWordIs (sp+32) b)`
  pre into the marshal-pair post's flat 8-atom shape.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
  Refs: GH #92, parent evm-asm-mtj3, immediate parent evm-asm-nrfpf.
-/

import EvmAsm.Evm64.Exp.LimbSpec

namespace EvmAsm.Evm64

private theorem sepConjAssocEq (P Q R : EvmAsm.Rv64.Assertion) :
    ((P ** Q) ** R) = (P ** (Q ** R)) :=
  EvmAsm.Rv64.sepConj_assoc' P Q R

/-- Fold the 8-atom post-state of `exp_loop_squaring_marshal_pair_spec_within`
    (factor-1 slot at `evmSp[0..24]` and factor-2 slot at `evmSp[32..56]`,
    both holding limbs `r0..r3`) into two `evmWordIs` atoms over
    `expResultWord r0 r1 r2 r3`. -/
theorem exp_squaring_marshal_pair_post_evmWordIs
    (evmSp r0 r1 r2 r3 : Word) :
    (((evmSp + EvmAsm.Rv64.signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ r3)) =
    (evmWordIs evmSp (expResultWord r0 r1 r2 r3) **
      evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  -- Canonicalize all immediate offsets to their literal Word values.
  have h0  : (evmSp + EvmAsm.Rv64.signExtend12 (0  : BitVec 12) : Word) = evmSp       := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h8  : (evmSp + EvmAsm.Rv64.signExtend12 (8  : BitVec 12) : Word) = evmSp + 8   := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h16 : (evmSp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12) : Word) = evmSp + 16  := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h24 : (evmSp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12) : Word) = evmSp + 24  := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h32 : (evmSp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12) : Word) = evmSp + 32  := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h40 : (evmSp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12) : Word) = evmSp + 40  := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h48 : (evmSp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12) : Word) = evmSp + 48  := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h56 : (evmSp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12) : Word) = evmSp + 56  := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  rw [h0, h8, h16, h24, h32, h40, h48, h56]
  -- Now the LHS is the eight literal-offset atoms. Re-associate so that the
  -- first four atoms (factor-1 slot) and the last four (factor-2 slot) form
  -- distinct sub-trees, then fold each via `evmWordIs_sp_limbs_eq` and
  -- `evmWordIs_sp32_limbs_eq` instantiated with `expResultWord`.
  rw [evmWordIs_sp_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
        (expResultWord_getLimbN_0 r0 r1 r2 r3)
        (expResultWord_getLimbN_1 r0 r1 r2 r3)
        (expResultWord_getLimbN_2 r0 r1 r2 r3)
        (expResultWord_getLimbN_3 r0 r1 r2 r3)]
  rw [evmWordIs_sp32_limbs_eq evmSp (expResultWord r0 r1 r2 r3) r0 r1 r2 r3
        (expResultWord_getLimbN_0 r0 r1 r2 r3)
        (expResultWord_getLimbN_1 r0 r1 r2 r3)
        (expResultWord_getLimbN_2 r0 r1 r2 r3)
        (expResultWord_getLimbN_3 r0 r1 r2 r3)]
  -- Re-associate the right-leaning 8-atom chain into two right-leaning
  -- 4-atom chains separated at the factor-1/factor-2 boundary.
  rw [sepConjAssocEq]
  rw [sepConjAssocEq]
  rw [sepConjAssocEq]

/-- Mid-tree variant of `exp_squaring_marshal_pair_post_evmWordIs`: thread a
    remainder `Q` so callers (`evm-asm-ct3ti`, `evm-asm-nrfpf`) can fold the
    8-limb sub-tree even when it sits in the middle of a longer sepConj
    chain alongside frame slots like `(.x12 ↦ᵣ evmSp)`, `(.x1 ↦ᵣ ra_val)`,
    or the local-scratch `sp[0..24]` group. -/
theorem exp_squaring_marshal_pair_post_evmWordIs_right
    (evmSp r0 r1 r2 r3 : Word) (Q : EvmAsm.Rv64.Assertion) :
    (((evmSp + EvmAsm.Rv64.signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
     ((evmSp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ r3) ** Q) =
    (evmWordIs evmSp (expResultWord r0 r1 r2 r3) **
      evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3) ** Q) := by
  have h_assoc :
      (((evmSp + EvmAsm.Rv64.signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
       ((evmSp + EvmAsm.Rv64.signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
       ((evmSp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ r3) ** Q) =
      ((((evmSp + EvmAsm.Rv64.signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
        ((evmSp + EvmAsm.Rv64.signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
        ((evmSp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((evmSp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
        ((evmSp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
        ((evmSp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
        ((evmSp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ r3)) ** Q) := by
    simp only [sepConjAssocEq]
  rw [h_assoc]
  rw [exp_squaring_marshal_pair_post_evmWordIs]
  rw [sepConjAssocEq]

/-- Left-framed variant of `exp_squaring_marshal_pair_post_evmWordIs`: thread a
    leading frame `P` so callers can fold the 8-limb sub-tree when it follows
    already-framed registers or scratch slots. -/
theorem exp_squaring_marshal_pair_post_evmWordIs_left
    (evmSp r0 r1 r2 r3 : Word) (P : EvmAsm.Rv64.Assertion) :
    (P **
     (((evmSp + EvmAsm.Rv64.signExtend12 (0  : BitVec 12)) ↦ₘ r0) **
      ((evmSp + EvmAsm.Rv64.signExtend12 (8  : BitVec 12)) ↦ₘ r1) **
      ((evmSp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
      ((evmSp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
      ((evmSp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
      ((evmSp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
      ((evmSp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
      ((evmSp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ r3))) =
    (P **
      (evmWordIs evmSp (expResultWord r0 r1 r2 r3) **
        evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3))) := by
  rw [exp_squaring_marshal_pair_post_evmWordIs]

end EvmAsm.Evm64
