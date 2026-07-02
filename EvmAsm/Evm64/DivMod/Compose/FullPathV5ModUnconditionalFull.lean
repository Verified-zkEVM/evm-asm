/-
  EvmAsm.Evm64.DivMod.Compose.FullPathV5ModUnconditionalFull

  The MOD capstone: the fully unconditional EVM-stack-level MOD dispatch triple,
  lifted from the no-NOP v5 surface (`evm_mod_stack_spec_unconditional_v5_mod`,
  FullPathV5ModAssembly) up through the production v5 bundle `modCode_v5` and then
  into the canonical v6 surface `modCodeV6`.

  MOD mirror of `evm_div_stack_spec_unconditional` (FullPathV5DivUnconditionalFull)
  + `evm_div_v5_unconditional_over_divCodeV6` (V5ReuseV6).  Two lifts:
  * `cpsTripleWithin_modCode_noNop_v5_to_modCode_v5` (V5Code2) — adds the entry-NOP
    block: no-NOP v5 → full v5 bundle;
  * `modCode_v5_sub_modCodeV6` (V5ReuseModV6) at offset `modV6V5Off` — embeds the
    reused v5 bundle into the v6 code.

  As with DIV, the unconditional spec is provable only at the v5/v6 surface (the
  legacy v4 `modCode_noNop_v4` carries the buggy ULTs).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathV5ModAssembly
import EvmAsm.Evm64.DivMod.Compose.V5Code2
import EvmAsm.Evm64.DivMod.Compose.V5ReuseModV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **The unconditional EVM-stack-level MOD spec** over the production v5 code
    surface `modCode_v5`, with the uniform dispatch shift `divDispatchShiftX2 b`
    in `x2` — the full MOD dispatch triple holds for every 256-bit divisor `b`
    (the `b = 0`, n=1, n=2, n=3 and n=4 divisor shapes are all discharged
    internally). -/
theorem evm_mod_stack_spec_unconditional
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) :=
  cpsTripleWithin_modCode_noNop_v5_to_modCode_v5
    (evm_mod_stack_spec_unconditional_v5_mod sp base a b
      raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign)

/-- The unconditional MOD dispatch triple over the canonical v6 code surface
    `modCodeV6`, entered at the embedded-v5 offset `modV6V5Off` and exiting at
    `modV6ExitOff`.  MOD mirror of `evm_div_v5_unconditional_over_divCodeV6`. -/
theorem evm_mod_v5_unconditional_over_modCodeV6
    (sp base : Word) (a b : EvmWord) (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : (((base + modV6V5Off) + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + modV6V5Off) + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound (base + modV6V5Off) (base + modV6ExitOff) (modCodeV6 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have h := evm_mod_stack_spec_unconditional sp (base + modV6V5Off) a b raVal v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign
  rw [show ((base + modV6V5Off) + nopOff : Word) = base + modV6ExitOff from by
    simp only [modV6V5Off, nopOff, modV6ExitOff]; bv_omega] at h
  exact cpsTripleWithin_extend_code (hmono := fun a i hh => modCode_v5_sub_modCodeV6 a i hh) h

end EvmAsm.Evm64
