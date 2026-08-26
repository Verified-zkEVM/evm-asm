/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5DenormPre

  The v5 n=1 denormalization-epilogue precondition shape `fullDivN1DenormPreV5`,
  the capped-loop analog of `fullDivN1DenormPre`: the four quotient digits land in
  the q-cells (`r0..r3 .1` at `sp+4088..4064`), the final normalized remainder in
  the u-cells (`r0 .2.*` at `sp+4056..4032`), and the normalized divisor `v` in the
  output slots (`sp+32..56`).  Built over the all-call v5 schoolbook digits
  `fullDivN1R{0,1,2,3}V5 true … true` / `fullDivN1C3V5`.  This is the target the
  loop-post → epilogue bridge reduces to; the bridge + full path land in a
  follow-up.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Defs
public import EvmAsm.Evm64.DivMod.Compose.Base

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 capped-loop analog of `fullDivN1DenormPre`: the denorm-epilogue entry shape
    for n=1, with the all-call schoolbook digits.  `x6 = sp+4056` (u-base),
    `x7 = sp+4088` (q-base), `x5 = 0`, `x10 = c3`, `x2 = un3`, `x11`/`x9` carry the
    loop-exit residue. -/
@[irreducible] def fullDivN1DenormPreV5 (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN1Shift b0
  let v := fullDivN1NormV b0 b1 b2 b3
  let r3 := fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) **
   (.x10 ↦ᵣ fullDivN1C3V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3) **
   ((sp + signExtend12 3992) ↦ₘ shift) **
   ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
   ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
   ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
   ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
   ((sp + signExtend12 4088) ↦ₘ r0.1) **
   ((sp + signExtend12 4080) ↦ₘ r1.1) **
   ((sp + signExtend12 4072) ↦ₘ r2.1) **
   ((sp + signExtend12 4064) ↦ₘ r3.1) **
   ((sp + signExtend12 32) ↦ₘ v.1) **
   ((sp + signExtend12 40) ↦ₘ v.2.1) **
   ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
   ((sp + signExtend12 56) ↦ₘ v.2.2.2))

theorem fullDivN1DenormPreV5_unfold {sp a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    fullDivN1DenormPreV5 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    let shift := fullDivN1Shift b0
    let v := fullDivN1NormV b0 b1 b2 b3
    let r3 := fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3
    let r2 := fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3
    let r1 := fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3
    let r0 := fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
     (.x2 ↦ᵣ r0.2.2.2.2.1) **
     (.x10 ↦ᵣ fullDivN1C3V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3) **
     ((sp + signExtend12 3992) ↦ₘ shift) **
     ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
     ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
     ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
     ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
     ((sp + signExtend12 4088) ↦ₘ r0.1) **
     ((sp + signExtend12 4080) ↦ₘ r1.1) **
     ((sp + signExtend12 4072) ↦ₘ r2.1) **
     ((sp + signExtend12 4064) ↦ₘ r3.1) **
     ((sp + signExtend12 32) ↦ₘ v.1) **
     ((sp + signExtend12 40) ↦ₘ v.2.1) **
     ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
     ((sp + signExtend12 56) ↦ₘ v.2.2.2)) := by
  delta fullDivN1DenormPreV5; rfl

end EvmAsm.Evm64
