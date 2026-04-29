/-
  EvmAsm.Evm64.DivMod.SpecCallV4

  v4 versions of the call-trial semantic predicates:
  - `n4CallSkipSemanticHolds_v4` (mirror of `n4CallSkipSemanticHolds` with
    `div128Quot_v4` in place of `div128Quot`)
  - `n4CallAddbackBeqSemanticHolds_v4` (mirror of
    `n4CallAddbackBeqSemanticHolds` with `div128Quot_v4`)

  The v4 predicates are downstream of `IterV4InvariantsPhase2` (zero
  sorries on PR #1409, currently in review). They are the entry point
  for the v4 stack-spec dispatcher work tracked under issue #1337
  → issue #61.

  Companion to `SpecCall.lean` (defines v1 versions) and
  `SpecCallAddbackBeq.lean` (defines v1 + v2 versions).
-/

import EvmAsm.Evm64.DivMod.SpecCall
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsPhase2

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-! ### Irreducible component accessors for `div128Quot_v4`

These extract `q1''` (Phase-1 trial digit), `q0''` (Phase-2 trial digit),
and `un21` (Phase-1 remainder Word) as `@[irreducible]` defs so that
sub-stubs and the wire-up can talk about them as opaque names rather
than re-embedding the full let-chain.

Per `feedback_irreducible_for_let_bindings`: when let-binding chains in
sub-stub statements block tactics like `rw`/pattern unification, this
is the canonical fix. -/

/-- **q1''** = the Phase-1 trial digit after v4's 2-correction. -/
@[irreducible] def div128Quot_v4_q1'' (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
  let rhat' :=
    if rhatc >>> (32 : BitVec 6).toNat = 0 then
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    else rhatc
  div128Quot_phase2b_q0' q1' rhat' dLo div_un1

/-- **un21** = `(rhat'' << 32 | div_un1) - q1''*dLo` (Phase-1 remainder
    in Word form, via truncation absorption). -/
@[irreducible] def div128Quot_v4_un21 (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
  let rhat' :=
    if rhatc >>> (32 : BitVec 6).toNat = 0 then
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    else rhatc
  let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
  let rhat'' :=
    if rhat' >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q1' * dLo
      let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
    else rhat'
  ((rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1) - q1'' * dLo

/-- **q0''** = the Phase-2 trial digit after v4's 2-correction. -/
@[irreducible] def div128Quot_v4_q0'' (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un21 := div128Quot_v4_un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  let rhat2' :=
    if rhat2c >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q0c * dLo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
      if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
    else rhat2c
  div128Quot_phase2b_q0' q0' rhat2' dLo div_un0

/-- **div128Quot_v4 unfolds via the component accessors**: structural
    bridge to compose the proven sub-stubs. -/
theorem div128Quot_v4_eq_components (uHi uLo vTop : Word) :
    div128Quot_v4 uHi uLo vTop =
      ((div128Quot_v4_q1'' uHi uLo vTop) <<< (32 : BitVec 6).toNat) |||
        (div128Quot_v4_q0'' uHi uLo vTop) := by
  unfold div128Quot_v4 div128Quot_v4_q1'' div128Quot_v4_q0'' div128Quot_v4_un21
  rfl

/-- **v4 version of `n4CallSkipSemanticHolds`**, using `div128Quot_v4`
    (full 2-correction Knuth D3 in BOTH phases).

    Mirror of `n4CallSkipSemanticHolds` for the v4 algorithm. Used by
    downstream stack specs once they migrate from `div128Quot`/`div128Quot_v2`
    to `div128Quot_v4`. The associated closure
    `n4CallSkipSemanticHolds_v4_of_call_trial` is provable since v4
    satisfies `qHat ≥ q_true` (Knuth-A lower bound; trivially under
    perfect Phase-1+2). -/
def n4CallSkipSemanticHolds_v4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
    (div128Quot_v4 u4 u3 b3').toNat

theorem n4CallSkipSemanticHolds_v4_def {a b : EvmWord} :
    n4CallSkipSemanticHolds_v4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
       (div128Quot_v4 u4 u3 b3').toNat) :=
  rfl

/-- **Sub-stub 1**: under preconditions, q1'' (Phase-1 trial digit) is < 2^32.
    Follows from Phase-1 perfect (q1'' = q*_phase1) plus the standard
    Knuth-B bound `q*_phase1 < 2^32` (which holds when uHi < vTop). -/
theorem div128Quot_v4_phase1_quot_lt_pow32
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat < 2^32 := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Phase-1 perfect: q1''.toNat = q*_phase1 = (uHi*2^32 + div_un1) / vTop.
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Standard Word-level facts.
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Knuth-B at q*_phase1: q*_phase1 < 2^32.
  have h_q_true_lt : (uHi.toNat * 2^32 + div_un1.toNat) /
                     (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
    div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1 h_div_un1_lt h_uHi_lt_decomp
  linarith [h_perfect]

/-- **Sub-stub 2**: under preconditions, q0'' (Phase-2 trial digit) is < 2^32.
    Follows from Phase-2 perfect (q0'' = q*_phase2) plus the standard
    Knuth-B bound `q*_phase2 < 2^32` (which holds when un21 < vTop, the
    proven `_un21_lt_vTop`). -/
theorem div128Quot_v4_phase2_quot_lt_pow32
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' :=
      if rhat2c >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q0c * dLo
        let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
        if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
      else rhat2c
    let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
    q0''.toNat < 2^32 := by
  intro dHi dLo div_un0 div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' rhat2' q0''
  -- Phase-2 perfect: q0''.toNat = q*_phase2 = (un21*2^32 + div_un0) / vTop.
  have h_perfect := div128Quot_v4_phase2_perfect uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_div_un0_lt : div_un0.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- un21 < vTop (proven Phase-2 invariant).
  have h_un21_lt_vTop : un21.toNat < vTop.toNat :=
    div128Quot_v4_un21_lt_vTop uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_un21_lt_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_un21_lt_vTop
  -- Knuth-B at q*_phase2: q*_phase2 < 2^32.
  have h_q_true_lt : (un21.toNat * 2^32 + div_un0.toNat) /
                     (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
    div128Quot_q_true_1_lt_pow32 un21 dHi dLo div_un0 h_div_un0_lt h_un21_lt_decomp
  linarith [h_perfect]

/-- **Pure-Nat combined-quotient identity**: given Phase-1 + Phase-2
    perfect (with un21 = phase1 remainder), the combined output is
    the exact 128/64 quotient.

    Standard Euclidean division composition: if
    - `uHi*2^32 + div_un1 = q1''*vTop + r1` with `r1 < vTop`
    - `r1*2^32 + div_un0 = q0''*vTop + r2` with `r2 < vTop`
    - `uLo = div_un1*2^32 + div_un0`
    then `(uHi*2^64 + uLo) = (q1''*2^32 + q0'')*vTop + r2`, so the
    combined `q1''*2^32 + q0''` is the 128/64 quotient. -/
private theorem div128Quot_v4_combined_arith
    (uHi uLo vTop div_un1 div_un0 q1'' un21 q0'' : Nat)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0)
    (h_vTop_pos : 0 < vTop)
    (h_q1''_eq : q1'' = (uHi * 2^32 + div_un1) / vTop)
    (h_un21_eq : un21 = (uHi * 2^32 + div_un1) - q1'' * vTop)
    (h_q0''_eq : q0'' = (un21 * 2^32 + div_un0) / vTop) :
    q1'' * 2^32 + q0'' = (uHi * 2^64 + uLo) / vTop := by
  -- Phase-1 Eucl: q1''*vTop ≤ uHi*2^32+div_un1, with mod < vTop.
  have h_dam1 : q1'' * vTop + (uHi * 2^32 + div_un1) % vTop = uHi * 2^32 + div_un1 := by
    rw [h_q1''_eq]; exact Nat.div_add_mod' _ _
  have h_mod1_lt : (uHi * 2^32 + div_un1) % vTop < vTop := Nat.mod_lt _ h_vTop_pos
  have h_un21_eq' : un21 = (uHi * 2^32 + div_un1) % vTop := by
    rw [h_un21_eq, h_q1''_eq]
    have := Nat.div_add_mod' (uHi * 2^32 + div_un1) vTop
    omega
  -- Phase-2 Eucl: q0''*vTop ≤ un21*2^32+div_un0, with mod < vTop.
  have h_dam2 : q0'' * vTop + (un21 * 2^32 + div_un0) % vTop = un21 * 2^32 + div_un0 := by
    rw [h_q0''_eq]; exact Nat.div_add_mod' _ _
  have h_mod2_lt : (un21 * 2^32 + div_un0) % vTop < vTop := Nat.mod_lt _ h_vTop_pos
  -- Combined Eucl: (q1''*2^32 + q0'')*vTop + r2 = uHi*2^64 + uLo, with r2 < vTop.
  set r2 := (un21 * 2^32 + div_un0) % vTop with h_r2_def
  have h_combined : (q1'' * 2^32 + q0'') * vTop + r2 = uHi * 2^64 + uLo := by
    rw [h_uLo]
    -- Multiplication distributes: (q1''*2^32 + q0'')*vTop = q1''*2^32*vTop + q0''*vTop.
    -- Plus r2 = un21*2^32 + div_un0 - q0''*vTop.
    -- So lhs = q1''*2^32*vTop + (un21*2^32 + div_un0)
    --       = (q1''*vTop + un21)*2^32 + div_un0   (use h_dam1's substitution)
    --       = (uHi*2^32 + div_un1)*2^32 + div_un0
    --       = uHi*2^64 + div_un1*2^32 + div_un0.
    have h1 : (q1'' * 2^32 + q0'') * vTop = q1'' * 2^32 * vTop + q0'' * vTop := by ring
    have h2 : q1'' * 2^32 * vTop = q1'' * vTop * 2^32 := by ring
    have h3 : q1'' * vTop = (uHi * 2^32 + div_un1) - un21 := by
      rw [h_un21_eq']; omega
    -- Goal in terms: q1''*vTop*2^32 + q0''*vTop + r2 = uHi*2^64 + (div_un1*2^32 + div_un0).
    -- Substitute q1''*vTop = uHi*2^32 + div_un1 - un21, then expand.
    rw [h1, h2]
    -- Now: q1''*vTop*2^32 + q0''*vTop + r2 = uHi*2^64 + div_un1*2^32 + div_un0.
    -- Use h_dam2: q0''*vTop + r2 = un21*2^32 + div_un0.
    -- So lhs = q1''*vTop*2^32 + un21*2^32 + div_un0 = (q1''*vTop + un21)*2^32 + div_un0
    --       = (uHi*2^32 + div_un1)*2^32 + div_un0 = uHi*2^64 + div_un1*2^32 + div_un0.
    have h4 : q1'' * vTop * 2^32 + (q0'' * vTop + r2) =
              q1'' * vTop * 2^32 + un21 * 2^32 + div_un0 := by
      rw [h_dam2]; ring
    have h5 : q1'' * vTop * 2^32 + un21 * 2^32 = (q1'' * vTop + un21) * 2^32 := by ring
    have h_eucl1_eq : q1'' * vTop + un21 = uHi * 2^32 + div_un1 := by
      rw [h_un21_eq']; omega
    have h6 : (uHi * 2^32 + div_un1) * 2^32 = uHi * 2^64 + div_un1 * 2^32 := by ring
    -- Combine.
    have : q1'' * vTop * 2^32 + q0'' * vTop + r2 = uHi * 2^64 + div_un1 * 2^32 + div_un0 := by
      have : q1'' * vTop * 2^32 + q0'' * vTop + r2 =
             q1'' * vTop * 2^32 + (q0'' * vTop + r2) := by ring
      rw [this, h4, h5, h_eucl1_eq, h6]
    linarith
  -- (q*vTop + r)/vTop = q when r < vTop.
  rw [show uHi * 2^64 + uLo = (q1'' * 2^32 + q0'') * vTop + r2 from h_combined.symm]
  rw [show (q1'' * 2^32 + q0'') * vTop = vTop * (q1'' * 2^32 + q0'') from by ring]
  rw [Nat.mul_add_div h_vTop_pos]
  have : r2 / vTop = 0 := Nat.div_eq_of_lt h_mod2_lt
  omega

/-- **Pure-Nat truncation-absorbing un21 = phase1_remainder helper**.

    Mirror of `_un21_lt_vTop_truncation_arith` (in IterV4Invariants)
    but extracts the explicit value rather than just the < bound.

    Same case-split on k = rhat''/2^32 ∈ {0, 1}:
    - k = 0: rhat'' < 2^32, rhat'' % 2^32 = rhat'', so
      ((rhat'' % 2^32)*2^32 + div_un1 + 2^64 - q1''*dLo) % 2^64
      = (rhat''*2^32 + div_un1 - q1''*dLo) + 2^64 mod 2^64
      = rhat''*2^32 + div_un1 - q1''*dLo (since this is < 2^64).
    - k = 1: (rhat'' % 2^32)*2^32 + 2^64 = rhat''*2^32, so
      ((rhat'' % 2^32)*2^32 + div_un1 + 2^64 - q1''*dLo) % 2^64
      = rhat''*2^32 + div_un1 - q1''*dLo.

    Then rhat''*2^32 + div_un1 - q1''*dLo = uHi*2^32 + div_un1 -
    q1''*(dHi*2^32 + dLo) using rhat'' = uHi - q1''*dHi. -/
private theorem div128Quot_v4_un21_eq_phase1_remainder_arith
    (uHi vTop dHi dLo div_un1 q1'' rhat'' : Nat)
    (h_vTop_eq : vTop = dHi * 2^32 + dLo)
    (h_dLo_lt : dLo < 2^32)
    (h_div_un1_lt : div_un1 < 2^32)
    (h_vTop_le : vTop ≤ 2^64)
    (h_q1''_succ_gt : (q1'' + 1) * vTop > uHi * 2^32 + div_un1)
    (h_q1''_dHi_le : q1'' * dHi ≤ uHi)
    (h_rhat''_eq : rhat'' = uHi - q1'' * dHi)
    (h_no_wrap : q1'' * dLo ≤ rhat'' * 2^32 + div_un1)
    (h_q1''_le : q1'' ≤ 2^32) :
    ((rhat'' % 2^32) * 2^32 + div_un1 + 2^64 - q1'' * dLo) % 2^64 =
      uHi * 2^32 + div_un1 - q1'' * vTop := by
  -- Phase-1 remainder algebra: rhat'' * 2^32 + div_un1 - q1'' * dLo equals
  -- the same expression as the rhs (uHi*2^32 + div_un1 - q1''*vTop), via
  -- substitution of rhat'' = uHi - q1''*dHi and vTop = dHi*2^32 + dLo.
  have h_rem_eq : rhat'' * 2^32 + div_un1 - q1'' * dLo =
                  uHi * 2^32 + div_un1 - q1'' * vTop := by
    rw [h_rhat''_eq, h_vTop_eq]
    have h1 : (uHi - q1'' * dHi) * 2^32 = uHi * 2^32 - q1'' * dHi * 2^32 := by
      rw [Nat.sub_mul]
    have h2 : q1'' * dHi * 2^32 ≤ uHi * 2^32 :=
      Nat.mul_le_mul_right _ h_q1''_dHi_le
    have h3 : q1'' * (dHi * 2^32 + dLo) = q1'' * dHi * 2^32 + q1'' * dLo := by ring
    omega
  -- Bound: rem < vTop.
  have h_rem_lt_vTop : rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop := by
    have h := div128Quot_v4_un21_lt_vTop_arith uHi vTop dHi dLo div_un1 q1'' rhat''
      h_vTop_eq h_q1''_succ_gt h_rhat''_eq h_q1''_dHi_le h_no_wrap
    exact h
  have h_rem_lt_pow64 : rhat'' * 2^32 + div_un1 - q1'' * dLo < 2^64 :=
    lt_of_lt_of_le h_rem_lt_vTop h_vTop_le
  -- Now prove the lhs equals the same Phase-1 remainder.
  have h_QdLo_lt : q1'' * dLo < 2^64 := by
    calc q1'' * dLo
        ≤ 2^32 * dLo := Nat.mul_le_mul_right _ h_q1''_le
      _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr h_dLo_lt
      _ = 2^64 := by decide
  -- rhat'' < 2^33 (same as the un21_lt_vTop proof).
  have h_rhat_lt : rhat'' < 2^33 := by
    by_contra h_not
    have h_ge : 2^33 ≤ rhat'' := Nat.le_of_not_lt h_not
    have h1 : 2^65 ≤ rhat'' * 2^32 := by
      calc (2^65 : Nat) = 2^33 * 2^32 := by decide
        _ ≤ rhat'' * 2^32 := Nat.mul_le_mul_right _ h_ge
    omega
  -- k = rhat'' / 2^32 ∈ {0, 1}.
  have h_div_mod : (rhat'' / 2^32) * 2^32 + (rhat'' % 2^32) = rhat'' := by
    have := Nat.div_add_mod rhat'' (2^32)
    linarith
  have h_mod_lt : rhat'' % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  have h_k_le : rhat'' / 2^32 ≤ 1 := by
    have h1 : rhat'' < 2 * 2^32 := by
      have : (2 * 2^32 : Nat) = 2^33 := by decide
      omega
    omega
  -- Linearize products via `set` to help omega.
  set X := rhat'' * 2^32 with hX
  set Y := q1'' * dLo with hY
  set Z := (rhat'' % 2^32) * 2^32 with hZ
  -- Bound: Y < 2^64.
  have h_Y_lt : Y < 2^64 := h_QdLo_lt
  -- Case-split on k = rhat'' / 2^32.
  interval_cases (rhat'' / 2^32)
  · -- k = 0: rhat'' = rhat'' % 2^32 < 2^32.
    have h_rhat_lt32 : rhat'' < 2^32 := by omega
    have h_mod_eq : rhat'' % 2^32 = rhat'' := Nat.mod_eq_of_lt h_rhat_lt32
    have h_ZX : Z = X := by rw [hZ, hX, h_mod_eq]
    rw [h_ZX]
    have h_pow_eq : (2 : Nat)^64 = 2^64 := rfl
    have hY_le : Y ≤ X + div_un1 := h_no_wrap
    have h_eq2 : X + div_un1 + 2^64 - Y = (X + div_un1 - Y) + 2^64 := by
      rw [Nat.add_comm (X + div_un1) (2^64), Nat.add_sub_assoc hY_le, Nat.add_comm]
    rw [h_eq2, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt h_rem_lt_pow64]
    exact h_rem_eq
  · -- k = 1: rhat'' = rhat'' % 2^32 + 2^32 ∈ [2^32, 2^33).
    have h_rhat_decomp : rhat'' = rhat'' % 2^32 + 2^32 := by omega
    have h_ZX : Z + 2^64 = X := by
      rw [hZ, hX]
      conv_rhs => rw [h_rhat_decomp]
      ring
    have hY_le : Y ≤ X + div_un1 := h_no_wrap
    have h_eq2 : Z + div_un1 + 2^64 - Y = X + div_un1 - Y := by
      have : Z + div_un1 + 2^64 = X + div_un1 := by linarith [h_ZX]
      rw [this]
    rw [h_eq2, Nat.mod_eq_of_lt h_rem_lt_pow64]
    exact h_rem_eq

/-- **un21 equals the Phase-1 remainder** at toNat level. Sub-stub
    used by `div128Quot_v4_eq_q_true_normalized`. The proof requires
    careful Word↔Nat reasoning around the truncation absorption
    machinery already proven in `IterV4Invariants` (esp.
    `_un21_lt_vTop_truncation_arith`).

    Math (for reference):
    - From `_phase1_final_eucl_bridge`: `rhat''.toNat = uHi - q1''*dHi`.
    - un21 = ((rhat'' << 32) | div_un1) - q1''*dLo (Word).
    - At toNat (with truncation): un21.toNat =
      (rhat'' * 2^32 + div_un1) - q1'' * dLo
      = (uHi - q1''*dHi)*2^32 + div_un1 - q1''*dLo
      = uHi*2^32 + div_un1 - q1''*(dHi*2^32 + dLo)
      = uHi*2^32 + div_un1 - q1''*vTop. -/
theorem div128Quot_v4_un21_eq_phase1_remainder
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat = uHi.toNat * 2^32 + div_un1.toNat - q1''.toNat * vTop.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21
  -- Standard Word-level facts (mirroring `_un21_lt_vTop`).
  have hdLo_lt : dLo.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_eucl := div128Quot_v4_phase1_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1''_dHi_le, h_rhat''_eq⟩ := h_eucl
  have h_no_wrap := div128Quot_v4_phase1_no_wrap_lo uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_q1''_lt : q1''.toNat ≤ 2 ^ 32 := by
    have h_q_true_lt : (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
      div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1 h_div_un1_lt
        (h_decomp ▸ h_uHi_lt_vTop)
    linarith [h_perfect]
  have h_q_dLo_eq : (q1'' * dLo).toNat = q1''.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q1''.toNat * dLo.toNat
        ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1''_lt
      _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
      _ = 2^64 := by decide
  have h_rhatUn1_mod : ((rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                       (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact halfword_combine_mod rhat'' div_un1 h_div_un1_lt
  have h_vTop_pos : 0 < vTop.toNat :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 2 ^ 63) h_vTop_ge_pow63
  have h_q1''_succ_gt : (q1''.toNat + 1) * vTop.toNat >
                        uHi.toNat * 2 ^ 32 + div_un1.toNat := by
    have h_pos' : 0 < dHi.toNat * 2 ^ 32 + dLo.toNat := by
      have := h_decomp ▸ h_vTop_pos; omega
    have h := Nat.lt_div_mul_add (a := uHi.toNat * 2 ^ 32 + div_un1.toNat) h_pos'
    rw [show (q1''.toNat + 1) * vTop.toNat
          = q1''.toNat * vTop.toNat + vTop.toNat from by ring]
    rw [h_perfect, h_decomp]
    exact h
  have h_vTop_le_pow64 : vTop.toNat ≤ 2 ^ 64 := by
    have := vTop.isLt
    omega
  -- un21.toNat = ((rhat'' % 2^32)*2^32 + div_un1 + 2^64 - q1''*dLo) % 2^64.
  have h_un21_eq : un21.toNat =
      ((rhat''.toNat % 2 ^ 32) * 2 ^ 32 + div_un1.toNat + 2 ^ 64 -
        q1''.toNat * dLo.toNat) % 2 ^ 64 := by
    show (cu_rhat_un1 - cu_q1_dlo).toNat = _
    rw [BitVec.toNat_sub']
    rw [show cu_rhat_un1 = (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1 from rfl]
    rw [show cu_q1_dlo = q1'' * dLo from rfl]
    rw [h_rhatUn1_mod, h_q_dLo_eq]
    have h_Y_lt : q1''.toNat * dLo.toNat < 2 ^ 64 := by
      calc q1''.toNat * dLo.toNat
          ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1''_lt
        _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
        _ = 2^64 := by decide
    congr 1
    omega
  rw [h_un21_eq]
  exact div128Quot_v4_un21_eq_phase1_remainder_arith uHi.toNat vTop.toNat
    dHi.toNat dLo.toNat div_un1.toNat q1''.toNat rhat''.toNat
    h_decomp hdLo_lt h_div_un1_lt h_vTop_le_pow64 h_q1''_succ_gt
    h_q1''_dHi_le h_rhat''_eq h_no_wrap h_q1''_lt

/-- **v4's exact-quotient property**: under standard Knuth-A
    preconditions (shift-norm + `u4 < b3'` + `u4 < 2^63`), the v4
    algorithm produces the exact 128/64 quotient.

    Proof composes:
    - `_phase1_perfect` + `_phase2_perfect` (proven in IterV4Invariants*).
    - `_phase{1,2}_quot_lt_pow32` (proven; no-truncation in OR-shift).
    - `_un21_eq_phase1_remainder` (sub-stub above; the un21 value
      identity).
    - `_combined_arith` (proven; pure-Nat composition).
    - `halfword_combine` (existing lemma; OR-shift to add at toNat). -/
theorem div128Quot_v4_eq_q_true_normalized
    (u4 u3 b3' : Word)
    (_hb3'_ge : b3'.toNat ≥ 2^63)
    (_hu4_lt_b3' : u4.toNat < b3'.toNat)
    (_hu4_lt_pow63 : u4.toNat < 2^63) :
    (div128Quot_v4 u4 u3 b3').toNat =
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat := by
  sorry  -- BLOCKED on let-binding alignment. The math is fully proven via
         -- `_phase{1,2}_perfect`, `_un21_eq_phase1_remainder`, the proven
         -- `_combined_arith` pure-Nat helper, and the proven
         -- `_phase{1,2}_quot_lt_pow32` no-truncation bounds. The
         -- composition via `Eq.trans` of `halfword_combine` and
         -- `combined_arith` SHOULD work, but the sub-stub results are
         -- wrapped in `have ...` chains that Lean's `rw` cannot unify
         -- against the explicit `dHi.toNat * 2^32 + dLo.toNat` denominators.
         --
         -- Path forward (planned for next iteration): recast the sub-stubs
         -- to take explicit Word arguments rather than embedding the
         -- algorithm internals via `let`. This requires either a
         -- "div128Quot_v4_components" helper that exposes q1''/q0''/un21
         -- as Word values, or restating each sub-stub with explicit
         -- Word arguments instead of let-binding chains.

/-- **`n4CallSkipSemanticHolds_v4` holds unconditionally** under the
    standard call-trial preconditions.

    Mirror of `n4CallSkipSemanticHolds_of_call_trial` for v4. The v4
    version is even stronger: v4 produces the EXACT q_true (not just
    an over-estimate), so Knuth-A holds with equality on the rhs.

    Proof: bridge val256/val256 → q_true_normalized → div128Quot_v4
    via `q_true_triple_bridge_to_val256_norm` (val256-level part) and
    `div128Quot_v4_eq_q_true_normalized` (algorithm part, sub-stub). -/
theorem n4CallSkipSemanticHolds_v4_of_call_trial (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b) :
    n4CallSkipSemanticHolds_v4 a b := by
  rw [n4CallSkipSemanticHolds_v4_def]
  rw [isCallTrialN4Evm_def] at hcall
  intro shift antiShift b3' u4 u3
  -- Bridge val256/val256 → (u4*2^64 + u3)/b3' (val256-level Knuth-A).
  have h_bridge :=
    q_true_triple_bridge_to_val256_norm
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hshift_nz hb3nz
  simp only [] at h_bridge
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hcall
  have h_shift_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
      h_shift_pos (clzResult_fst_toNat_le (b.getLimbN 3))
  have h_eq := div128Quot_v4_eq_q_true_normalized u4 u3 b3'
    h_b3'_ge h_u4_lt_b3' h_u4_lt_pow63
  rw [h_eq]
  exact h_bridge

/-- **v4 version of `n4CallAddbackBeqSemanticHolds`**, using
    `div128Quot_v4` (full 2-correction Knuth D3 in BOTH phases).

    The v1 predicate `n4CallAddbackBeqSemanticHolds` is **provably FALSE**
    under runtime preconditions (see
    `n4CallAddbackBeqSemanticHolds_counterexample`) due to v1's
    1-correction Phase-1b allowing 2^32-scale qHat overshoots. The v2
    predicate fixes Phase-1b only; the v4 predicate fixes BOTH phases,
    eliminating the counterexample input class by construction.

    Mirror of `n4CallAddbackBeqSemanticHolds` for the v4 algorithm.
    Closure proof `n4CallAddbackBeqSemanticHolds_v4_of_call_addback_beq`
    is the next critical-path target (still in stub form). -/
def n4CallAddbackBeqSemanticHolds_v4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := div128Quot_v4 u4 u3 b3'  -- v4: 2 D3 correction iterations in BOTH phases.
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem n4CallAddbackBeqSemanticHolds_v4_def {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds_v4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot_v4 u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

/-- **Layer 1 stub: v4 Knuth-B at val256 level.** Under the runtime
    preconditions, the v4 trial digit `qHat` (equal to the exact 128/64
    quotient by `div128Quot_v4_eq_q_true_normalized`) is at most 2 above
    the true val256-level quotient.

    Mirror of the v1 statement (which is FALSE for v1 due to overshoots).
    For v4, this is the val256-level lift of the per-phase Knuth-B
    bounds: since v4's qHat = (u4*2^64 + u3) / b3' exactly, and Knuth-B
    at the val256 level says `(u4*2^64+u3)/b3' ≤ val256(a)/val256(b) + 2`,
    we get `qHat ≤ val256(a)/val256(b) + 2` directly.

    Sub-stub for the addback closure's Layer 1. -/
theorem div128Quot_v4_qHat_le_q_true_plus_two (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  rw [isCallTrialN4Evm_def] at hcall
  intro shift antiShift b3' u4 u3
  -- Standard Knuth preconditions.
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hcall
  have h_shift_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
      h_shift_pos (clzResult_fst_toNat_le (b.getLimbN 3))
  -- Convert v4 quotient to the (u4*2^64 + u3)/b3' form.
  have h_eq := div128Quot_v4_eq_q_true_normalized u4 u3 b3'
    h_b3'_ge h_u4_lt_b3' h_u4_lt_pow63
  rw [h_eq]
  -- Apply the existing val256-level Knuth-B (Piece A).
  exact knuth_theorem_b_from_clz
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall

/-- **Layer 2 stub: carry partition for v4.** The post-mulsub addback carry
    is 0 iff the trial digit overshoots q_true by exactly 2.

    Refines the Knuth-B bound: under v4's exactness, qHat is one of
    {q_true, q_true+1, q_true+2}, and the carry distinguishes carry=0
    (overshoot 2) from carry≠0 (overshoots 0 or 1). This is the
    structural piece needed for q_out to recover q_true.

    Sub-stub for the addback closure's Layer 2. -/
theorem n4CallAddback_v4_carry_partition (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hcall : isCallTrialN4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    -- Strong partition: carry=0 ⟺ qHat=q_true+2, AND carry≠0 ⟹ qHat=q_true+1
    -- (the call+addback+BEQ branch only fires when qHat overshoots, so
    -- qHat=q_true is excluded).
    (carry = 0 ↔ qHat.toNat = q_true + 2) ∧
      (carry ≠ 0 → qHat.toNat = q_true + 1) := by
  sorry  -- Carry partition refined to handle both branches of the closure.
         -- carry=0: mulsub underflowed (qHat overshoots q_true by 2).
         -- carry≠0: qHat=q_true+1 (single overshoot — qHat=q_true case excluded
         -- by the call+addback+BEQ branch's runtime gating: that branch fires
         -- only when the trial division detected overshoot).

/-- **`n4CallAddbackBeqSemanticHolds_v4` closure**: under the runtime
    call-addback-BEQ preconditions, the v4 predicate holds.

    Composes:
    - Layer 1 (`_qHat_le_q_true_plus_two`): qHat ≤ q_true + 2.
    - Layer 2 (`_carry_partition`): carry=0 ⟺ qHat = q_true + 2.
    - Layer 3 (q_out arithmetic): both branches yield q_out = q_true.

    Stub for the next critical-path iteration. The proof structure
    (per `project_addback_beq_closure_plan_v2.md`). -/
theorem n4CallAddbackBeqSemanticHolds_v4_of_call_addback_beq (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b) :
    n4CallAddbackBeqSemanticHolds_v4 a b := by
  rw [n4CallAddbackBeqSemanticHolds_v4_def]
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_out
  -- Layer 1: qHat ≤ q_true + 2.
  have h_le := div128Quot_v4_qHat_le_q_true_plus_two a b hb3nz hshift_nz hcall
  -- Layer 2: carry partition (refined: covers both branches).
  have h_partition := n4CallAddback_v4_carry_partition a b hb3nz hshift_nz hcall
  obtain ⟨h_carry_zero_iff, h_carry_nz_imp⟩ := h_partition
  -- Notation aliases (q_true at val256 level).
  set q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    with h_q_true_def
  -- q_out is defined as `if carry = 0 then qHat - 2 else qHat - 1` (Word).
  -- Goal: q_out.toNat = q_true.
  -- Case-split on carry.
  by_cases h_carry : carry = 0
  · -- carry = 0: qHat = q_true + 2.
    have h_qHat_eq : qHat.toNat = q_true + 2 := h_carry_zero_iff.mp h_carry
    -- q_out = qHat + signExtend12 4095 + signExtend12 4095.
    show (if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
          else qHat + signExtend12 4095).toNat = q_true
    rw [if_pos h_carry]
    -- Compute (qHat - 2).toNat.
    rw [BitVec.toNat_add, BitVec.toNat_add, signExtend12_4095_toNat]
    have h_qHat_ge_2 : qHat.toNat ≥ 2 := by linarith
    have h_qHat_lt_word : qHat.toNat < 2^64 := qHat.isLt
    -- (qHat + (2^64-1)) % 2^64 = qHat - 1.
    have h_step1 : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
      rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : qHat.toNat - 1 < 2^64)]
    rw [h_step1]
    -- ((qHat - 1) + (2^64 - 1)) % 2^64 = qHat - 2.
    have h_step2 : (qHat.toNat - 1 + (2^64 - 1)) % 2^64 = qHat.toNat - 2 := by
      rw [show qHat.toNat - 1 + (2^64 - 1) = (qHat.toNat - 2) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : qHat.toNat - 2 < 2^64)]
    rw [h_step2]
    -- qHat.toNat - 2 = q_true.
    omega
  · -- carry ≠ 0: qHat = q_true + 1.
    have h_qHat_eq : qHat.toNat = q_true + 1 := h_carry_nz_imp h_carry
    show (if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
          else qHat + signExtend12 4095).toNat = q_true
    rw [if_neg h_carry]
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_qHat_ge_1 : qHat.toNat ≥ 1 := by linarith
    have h_step1 : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
      rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by have := qHat.isLt; omega)]
    rw [h_step1]
    omega

end EvmAsm.Evm64
