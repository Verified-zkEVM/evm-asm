/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4

  v4 div128 trial quotient `div128Quot_v4` — the RV64 v4 program quotient.

  Bug history (v1, v2 deprecated; v3 removed in this PR):
  - `div128Quot` (v1): only 1 D3 correction in Phase-1b. Buggy on
    inputs where Knuth's classical D3 loop needs 2 iterations.
  - `div128Quot_v2`: added a 2nd Phase-1b correction.
  - (v3 was a half-step that fixed Phase-1b but kept 1-correction
    Phase-2; obsolete since `phase2_no_wrap_lo` sub-case b was proven
    FALSE under 1-correction Phase-2.)
  - `div128Quot_v4` (this file): keeps the v2 Phase-1b chain and adds the
    Phase-2 2nd D3 correction implemented by `divK_div128_v4`.

  Why v4 matters:
  - `phase2_no_wrap_lo_under_runtime` was sorry'd in v2/v3 because
    Phase-2 overshoot of 1 made the no-wrap claim false. With v4,
    q0'' = q*_phase2 exactly, so `phase2_no_wrap_lo` holds universally.
  - The chain `_no_wrap_under_call_addback_beq_untruncated` →
    `_le_val256_div_plus_two_untruncated` becomes provable.
  - `addback_carry_partition_v2_{zero,nonzero}_case` (deleted in
    PR #1393) can be re-derived for v4.

  Migration path: replace consumers of `div128Quot_v2` with
  `div128Quot_v4`. The actual RISC-V program needs the corresponding
  ~6 instructions added for the Phase-2 2nd D3 correction.

  Issue #1337 algorithm fix migration / Issue #61 stack spec closure.
-/

module

public import EvmAsm.Evm64.DivMod.LoopDefs.Iter

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **FULLY CORRECTED v4** trial quotient. Mirrors Knuth's classical
    Algorithm D Step D3 with up to 2 correction iterations in BOTH the
    high-half (Phase-1b) and low-half (Phase-2) trial divisions.

    Phase 1b is intentionally identical to the v2 executable/spec surface;
    the v4 change is the second Phase-2 D3 correction. -/
def div128Quot_v4 (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  -- Phase 1b: v2's first and second D3 corrections.
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
  let rhat'' :=
    if rhat' >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q1' * dLo
      let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
    else rhat'
  -- Phase 2 setup with q1''/rhat''.
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  -- Phase 2: 1st D3 correction (same as v3).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  -- Phase 2: 2nd D3 correction — NEW in v4. Mirror of Phase-1b's
  -- 2nd correction. Closes Knuth's classical 2-correction guarantee.
  let rhat2' :=
    if rhat2c >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q0c * dLo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
      if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
    else rhat2c
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
  (q1'' <<< (32 : BitVec 6).toNat) ||| q0''

/-- Borrow condition for n=1 call+skip with the fully-corrected v4
    trial quotient: mulsub does not overflow. -/
def isSkipBorrowN1CallV4 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot_v4 u1 u0 v0
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

end EvmAsm.Evm64
