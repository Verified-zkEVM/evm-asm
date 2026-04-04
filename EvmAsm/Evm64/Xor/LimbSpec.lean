/-
  EvmAsm.Evm64.Xor.LimbSpec

  Per-limb XOR spec.
-/

import EvmAsm.Evm64.Xor.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- Per-limb XOR spec (4 instructions: LD x7, LD x6, XOR x7 x7 x6, SD x12 x7). -/
theorem xor_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Word)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.XOR .x7 .x7 .x6))
       (CodeReq.singleton (base + 12) (.SD .x12 .x7 off_b))))
    cpsTriple base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ^^^ b_limb))) := by
  runBlock

end EvmAsm.Rv64
