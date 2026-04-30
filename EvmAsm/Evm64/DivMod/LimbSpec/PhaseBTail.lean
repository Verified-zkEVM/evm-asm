/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseBTail

  CPS spec for the Knuth Algorithm D "phase B tail":
    * `divK_phaseB_tail_code` / `divK_phaseB_tail_spec_within` — 5-instruction
      block (SD n, ADDI n-1, SLLI ×8, ADD sp + offset, LD b[n-1]) that
      stores `n` to scratch and loads the leading limb of the divisor.

  Tenth chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev divK_phaseB_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.drop 16)

/-- Precondition for `divK_phaseB_tail_spec_within` (issue #433): the register
    and memory shape before the 5-instruction phase-B tail runs. Wrapped
    in an `@[irreducible] def` so the leading-limb address expression
    `sp + (n + signExtend12 4095) <<< 3 + signExtend12 32` doesn't appear
    in the theorem statement. Callers use
    `divK_phaseB_tail_pre_unfold` to peel it back when composing. -/
@[irreducible]
def divK_phaseB_tail_pre (sp n nMem leading_limb : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
  ((sp + signExtend12 3984) ↦ₘ nMem) **
  ((sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) ↦ₘ leading_limb)

/-- Unfold lemma for `divK_phaseB_tail_pre`. Callers rewrite with this
    before normalizing the concrete `n` into an sp-relative offset. -/
theorem divK_phaseB_tail_pre_unfold {sp n nMem leading_limb : Word} :
    divK_phaseB_tail_pre sp n nMem leading_limb =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
     ((sp + signExtend12 3984) ↦ₘ nMem) **
     ((sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) ↦ₘ leading_limb)) := by
  delta divK_phaseB_tail_pre; rfl

/-- Postcondition for `divK_phaseB_tail_spec_within` (issue #433): x5 now holds
    the leading limb, and the scratch slot at `sp + 3984` holds `n`.
    Wrapped in `@[irreducible]` for the same reason as `_pre`. -/
@[irreducible]
def divK_phaseB_tail_post (sp n leading_limb : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ leading_limb) **
  ((sp + signExtend12 3984) ↦ₘ n) **
  ((sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) ↦ₘ leading_limb)

/-- Unfold lemma for `divK_phaseB_tail_post`. -/
theorem divK_phaseB_tail_post_unfold {sp n leading_limb : Word} :
    divK_phaseB_tail_post sp n leading_limb =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ leading_limb) **
     ((sp + signExtend12 3984) ↦ₘ n) **
     ((sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) ↦ₘ leading_limb)) := by
  delta divK_phaseB_tail_post; rfl

/-- Phase B tail: store n to scratch, compute sp + (n-1)*8, load b[n-1].
    x5 = n on entry. On exit, x5 = leading limb b[n-1].

    Pre and post are wrapped in `@[irreducible] def`s
    (`divK_phaseB_tail_pre` / `_post`) so the leading-limb address
    expression stays hidden in the theorem statement (issue #433).
    Callers invoke `simp only [divK_phaseB_tail_pre_unfold,
    divK_phaseB_tail_post_unfold]` (or `delta ... ; rfl`) to peel back
    the wrappers before normalizing the concrete `n`. -/
theorem divK_phaseB_tail_spec_within (sp n leading_limb nMem : Word) (base : Word) :
    cpsTripleWithin 5 base (base + 20) (divK_phaseB_tail_code base)
      (divK_phaseB_tail_pre sp n nMem leading_limb)
      (divK_phaseB_tail_post sp n leading_limb) := by
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold]
  have I0 := sd_spec_gen_within .x12 .x5 sp n nMem 3984 base
  have I1 := addi_spec_gen_same_within .x5 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same_within .x5 (n + signExtend12 4095) 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2_within .x5 .x12 sp
    ((n + signExtend12 4095) <<< (3 : BitVec 6).toNat) (base + 12) (by nofun)
  have I4 := ld_spec_gen_same_within .x5
    (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat) leading_limb 32 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

end EvmAsm.Evm64
