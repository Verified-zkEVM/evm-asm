/-
  EvmAsm.Evm64.Eq.LimbSpec

  Per-limb EQ specs (XOR + OR accumulation).
-/

import EvmAsm.Evm64.Eq.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- EQ limb 0 spec (3 instructions): LD x7, LD x6, XOR x7 x7 x6. -/
theorem eq_limb0_spec (offA offB : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 offB))
       (CodeReq.singleton (base + 8) (.XOR .x7 .x7 .x6)))
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb)) := by
  runBlock

/-- EQ OR-limb spec (4 instructions): LD x6, LD x5, XOR x6 x6 x5, OR x7 x7 x6. -/
theorem eq_or_limb_spec (offA offB : BitVec 12)
    (sp a_limb b_limb v6 v5 acc : Word) (base : Word) :
    let memA := sp + signExtend12 offA
    let memB := sp + signExtend12 offB
    let xor_k := a_limb ^^^ b_limb
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x6 .x12 offA))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x5 .x12 offB))
      (CodeReq.union (CodeReq.singleton (base + 8) (.XOR .x6 .x6 .x5))
       (CodeReq.singleton (base + 12) (.OR .x7 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (acc ||| xor_k)) ** (.x6 ↦ᵣ xor_k) ** (.x5 ↦ᵣ b_limb) **
       (memA ↦ₘ a_limb) ** (memB ↦ₘ b_limb)) := by
  runBlock

end EvmAsm.Evm64
