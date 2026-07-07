/-
  EvmAsm.Evm64.ControlFlow.PcSpec

  Stack-level cpsTripleWithin specification for the EVM `PC` opcode
  (see `evm_pc` in `EvmAsm/Evm64/ControlFlow/Program.lean`).

  PC (0x58) pushes the byte offset of the PC opcode within the running
  bytecode. The dispatcher keeps the *absolute* code pointer of the opcode
  being executed in `x10`, and the running-code base in `codeBaseReg` (x21),
  so `pc = x10 - codeBaseReg`. The program computes that difference with a
  single `SUB` and pushes it zero-extended to 256 bits — the same push shape
  as CALLDATASIZE/CODESIZE/MSIZE, with the value coming from a register
  subtraction rather than a memory load.

  We state the spec over the dispatcher invariant `x10 = codeBase + pc`
  (universally quantified `pc`, so fully general): under it, PC pushes `pc`.
-/

import EvmAsm.Evm64.ControlFlow.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace ControlFlow

open EvmAsm.Rv64

/-- The `evm_pc` program placed in RV64 code memory at `base`. -/
abbrev evm_pc_code (codeBaseReg tmpReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_pc codeBaseReg tmpReg)

/-- Concretization of `evmWordIs nsp (BitVec.ofNat 256 v.toNat)` as four limb
    cells: low limb is `v`, upper three are zero. Generic over the pushed
    64-bit value; mirror of `evmWordIs_calldatasize_unfold`. -/
theorem evmWordIs_pc_unfold
    (nsp : Word) (v : Word) :
    evmWordIs nsp (BitVec.ofNat 256 v.toNat) =
      ((nsp ↦ₘ v) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have h_lt : v.toNat < 2 ^ 64 := v.isLt
  have hlow :
      EvmWord.getLimbN (BitVec.ofNat 256 v.toNat) 0 = v := by
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
               Nat.zero_mul]
    have h1 : v.toNat % 2 ^ 256 = v.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt (by norm_num))
    rw [h1, Nat.mod_eq_of_lt h_lt]
  have hhigh : ∀ k : Nat, k ≠ 0 → k < 4 →
      EvmWord.getLimbN (BitVec.ofNat 256 v.toNat) k = 0 := by
    intro k hk hk4
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
               Nat.shiftRight_eq_div_pow]
    have h1 : v.toNat % 2 ^ 256 = v.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt (by norm_num))
    rw [h1]
    have hp : 2 ^ 64 ≤ 2 ^ (k * 64) :=
      Nat.pow_le_pow_right (by norm_num) (by
        have : 0 < k := Nat.pos_of_ne_zero hk
        omega)
    have hdiv : v.toNat / 2 ^ (k * 64) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h_lt hp)
    simp [hdiv]
  unfold evmWordIs
  rw [hlow, hhigh 1 (by decide) (by decide),
      hhigh 2 (by decide) (by decide),
      hhigh 3 (by decide) (by decide)]

/-- Raw memory-cell-level PC spec: compute `x10 - codeBaseReg` into `tmpReg`,
    decrement EVM SP by 32, write it at the new top-of-stack low limb and zero
    the upper three limbs. The pushed low limb is `x10val - codeBase`; under
    the dispatcher invariant `x10 = codeBase + pc` this is exactly the EVM
    program counter `pc`. 6 instructions = 24 bytes. -/
theorem evm_pc_spec_within
    (codeBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base codeBase x10val tempOld : Word)
    (d0 d1 d2 d3 : Word) :
    let code := evm_pc_code codeBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((codeBaseReg ↦ᵣ codeBase) ** (.x10 ↦ᵣ x10val) **
       (tmpReg ↦ᵣ tempOld) ** (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      ((codeBaseReg ↦ᵣ codeBase) ** (.x10 ↦ᵣ x10val) **
       (tmpReg ↦ᵣ (x10val - codeBase)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (x10val - codeBase)) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  -- SUB tmpReg x10 codeBaseReg : tmpReg = x10val - codeBase.
  have LSUB := sub_spec_gen_within tmpReg .x10 codeBaseReg
                x10val codeBase tempOld base htmp_ne_x0
  -- ADDI x12 x12 -32 : decrement SP. Normalize (nsp+32) + (-32) = nsp.
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) (base + 4) (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- SD x12 tmpReg 0 : write the pc value at low limb (nsp).
  have LSD0 := sd_spec_gen_within .x12 tmpReg nsp (x10val - codeBase)
                  d0 (0 : BitVec 12) (base + 8)
  have LSD1 := sd_x0_spec_gen_within .x12 nsp d1 8 (base + 12)
  have LSD2 := sd_x0_spec_gen_within .x12 nsp d2 16 (base + 16)
  have LSD3 := sd_x0_spec_gen_within .x12 nsp d3 24 (base + 20)
  runBlock LSUB LADDI LSD0 LSD1 LSD2 LSD3

/-- PC stack spec: pops nothing, pushes the current program counter
    (`x10 - codeBaseReg`; under the dispatcher invariant `x10 = codeBase + pc`
    this is the EVM `pc`) zero-extended to 256 bits. The unconditional
    top-level triple witnessing PC `.proven`. -/
theorem evm_pc_stack_spec_within
    (codeBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base codeBase x10val tempOld : Word)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_pc_code codeBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((codeBaseReg ↦ᵣ codeBase) ** (.x10 ↦ᵣ x10val) **
       (tmpReg ↦ᵣ tempOld) ** (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmStackIs (nsp + 32) rest)
      ((codeBaseReg ↦ᵣ codeBase) ** (.x10 ↦ᵣ x10val) **
       (tmpReg ↦ᵣ (x10val - codeBase)) ** (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (BitVec.ofNat 256 (x10val - codeBase).toNat :: rest)) :=
  cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      rw [evmStackIs_cons, evmWordIs_pc_unfold]
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs (nsp + 32) rest)
      pcFree_evmStackIs
      (evm_pc_spec_within codeBaseReg tmpReg htmp_ne_x0
        nsp base codeBase x10val tempOld d0 d1 d2 d3))

end ControlFlow
end EvmAsm.Evm64
