/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepCompare

  CPS scaffolding for the MULMOD reducer compare ladder.
-/

import EvmAsm.Evm64.MulMod.ReduceCompare

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The high-to-low compare ladder of `evm_mulmod_reduce512_inner_step`.

Entry is `base + 84` relative to the full inner step.  The ladder branches to
`base + 144` when the shifted remainder is at least the modulus, and to
`base + 248` when it is smaller. -/
def evm_mulmod_reduce512_inner_step_compare : Program :=
  LD .x6 .x12 248 ;;
  LD .x7 .x12 88 ;;
  BLTU .x7 .x6 (52 : BitVec 13) ;;
  BLTU .x6 .x7 (152 : BitVec 13) ;;
  LD .x6 .x12 240 ;;
  LD .x7 .x12 80 ;;
  BLTU .x7 .x6 (36 : BitVec 13) ;;
  BLTU .x6 .x7 (136 : BitVec 13) ;;
  LD .x6 .x12 232 ;;
  LD .x7 .x12 72 ;;
  BLTU .x7 .x6 (20 : BitVec 13) ;;
  BLTU .x6 .x7 (120 : BitVec 13) ;;
  LD .x6 .x12 224 ;;
  LD .x7 .x12 64 ;;
  BLTU .x6 .x7 (108 : BitVec 13)

abbrev evm_mulmod_reduce512_inner_step_compare_code (base : Word) : CodeReq :=
  CodeReq.ofProg (base + 84) evm_mulmod_reduce512_inner_step_compare

/-- Shared memory footprint for the reducer compare ladder. -/
@[irreducible]
def mulModReduceCompareMem (sp : Word) (r n : EvmWord) : Assertion :=
  ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded precondition for the reducer compare ladder. -/
@[irreducible]
def mulModReduceComparePre (sp x6Old x7Old : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
  mulModReduceCompareMem sp r n

/-- Folded postcondition for the reducer compare ladder.

The ladder leaves `x6` and `x7` with path-dependent comparison limbs, so this
post keeps ownership of those registers without committing to concrete values.
The Boolean selects the semantic branch result: `true` for the subtract entry
and `false` for the no-sub tail. -/
@[irreducible]
def mulModReduceComparePost (sp : Word) (r n : EvmWord) (willSubtract : Bool) : Assertion :=
  (.x12 ↦ᵣ sp) ** regOwn .x6 ** regOwn .x7 ** mulModReduceCompareMem sp r n **
  ⌜if willSubtract then mulModReduceRemGE r n else mulModReduceRemLT r n⌝

end EvmAsm.Evm64
