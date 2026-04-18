/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseBTail

  CPS spec for the Knuth Algorithm D "phase B tail":
    * `divK_phaseB_tail_code` / `divK_phaseB_tail_spec` — 5-instruction
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

/-- Phase B tail: store n to scratch, compute sp + (n-1)*8, load b[n-1].
    x5 = n on entry. On exit, x5 = leading limb b[n-1]. -/
theorem divK_phaseB_tail_spec (sp n leading_limb n_mem : Word) (base : Word) :
    let nm1 := n + signExtend12 4095
    let nm1_x8 := nm1 <<< (3 : BitVec 6).toNat
    let addr_lead := sp + nm1_x8
    let cr := divK_phaseB_tail_code base
    cpsTriple base (base + 20) cr
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb))
      (
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ leading_limb) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((addr_lead + signExtend12 32) ↦ₘ leading_limb)) := by
  intro nm1 nm1_x8 addr_lead cr
  have I0 := sd_spec_gen .x12 .x5 sp n n_mem 3984 base
  have I1 := addi_spec_gen_same .x5 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x5 nm1 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x5 .x12 sp nm1_x8 (base + 12) (by nofun)
  have I4 := ld_spec_gen_same .x5 addr_lead leading_limb 32 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

end EvmAsm.Evm64
