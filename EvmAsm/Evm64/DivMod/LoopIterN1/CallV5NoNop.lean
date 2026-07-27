/-
  EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop

  v5 n=1 call+skip loop-body postcondition (j = 0), the target of brick 6
  (`divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop`).

  Mirror of `loopBodyN1CallSkipJ0PostV4` (LoopIterN1/Call.lean), with the trial
  quotient digit being the v5 trial `divKTrialCallV5QHat` (= `div128Quot_v5`,
  the exact floor) instead of the v4 trial.  The loop-body PRE
  (`loopBodyN1CallSkipJ0PreV4`) is version-agnostic (no `divKTrialCallV4*`
  references) and is reused directly for v5.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.N1CallBase
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 trial scratch-cell exit value (mirror of `divKTrialCallV4ScratchOut`):
    the Phase-2a capped remainder `rhat2c`, or the prior scratch when the
    high-correction guard fired. -/
def divKTrialCallV5ScratchOut (uHi uLo vTop scratchMem : Word) : Word :=
  let rhat2c := divKTrialCallV5Rhat2c uHi uLo vTop
  if rhat2c >>> (32 : BitVec 6).toNat ≠ 0 then scratchMem else rhat2c

/-- v5 trial `x7` exit value, in **compact** form over the irreducible v5
    sub-defs (`divKTrialCallV5Un21`/`Rhat2c`/`Q0c`).  Mirror of
    `divKTrialCallV4X7Exit`; needed for the compact NAMED trial-call-full post
    that resolves the brick-6 term-size wall (memory: v5-execlayer-termsize-wall). -/
def divKTrialCallV5X7Exit (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un0 := divKTrialCallV5Un0 uLo
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q0 := rv64_divu un21 dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let x7o := if hi2 = 0 then un21 else (q0 - cap) * dHi
  let rhat2c := divKTrialCallV5Rhat2c uHi uLo vTop
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0c := divKTrialCallV5Q0c uHi uLo vTop
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let bq0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
  let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := bq0' * dLo
  if rhat2cHi ≠ 0 then x7o else (if brhat2'Hi = 0 then q0Dlo2 else q0Dlo1)

/-- v5 trial `x9` exit value, compact form.  Mirror of `divKTrialCallV4X9Exit`. -/
def divKTrialCallV5X9Exit (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un0 := divKTrialCallV5Un0 uLo
  let rhat2c := divKTrialCallV5Rhat2c uHi uLo vTop
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0c := divKTrialCallV5Q0c uHi uLo vTop
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
  let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| un0
  if rhat2cHi ≠ 0 then rhat2cHi else (if brhat2'Hi = 0 then rhat2'Un0 else brhat2'Hi)

/-- v5 n=1 call+skip j=0 loop-body post: the digit `divKTrialCallV5QHat`
    (= exact `div128Quot_v5`) is stored, the dividend window updated by the
    no-borrow single-limb mulsub, and the div128 scratch cells settled. -/
@[irreducible]
def loopBodyN1CallSkipJ0PostV5
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  loopBodyN1SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  regOwn .x1

end EvmAsm.Evm64
