/-
  EvmAsm.Evm64.GasOpcode.Spec

  Stack-level cpsTripleWithin specification for the EVM `GAS` opcode
  (see `EvmAsm/Evm64/GasOpcode/Program.lean`).

  GAS mirrors CODESIZE/CALLDATASIZE: it loads a 64-bit value from an env-block
  cell and pushes it zero-extended to 256 bits. The remaining-gas counter lives
  in a dispatcher-maintained cell at `gasRemainingOff = 568`, outside the typed
  `EvmEnv` struct, so the spec is stated against a raw `gasRemainingIs` cell
  rather than an `envIs` field split.
-/

import EvmAsm.Evm64.GasOpcode.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace GasOpcode

open EvmAsm.Rv64

/-- The env-block cell holding the remaining gas, at `envAddr + gasRemainingOff`.
    Maintained by the dispatcher's per-opcode gas loop. -/
def gasRemainingIs (envAddr : Word) (gas : Word) : Assertion :=
  (envAddr + BitVec.ofNat 64 gasRemainingOff) ↦ₘ gas

theorem pcFree_gasRemainingIs {envAddr gas : Word} :
    (gasRemainingIs envAddr gas).pcFree := by
  unfold gasRemainingIs; pcFree

instance (envAddr gas : Word) : Assertion.PCFree (gasRemainingIs envAddr gas) :=
  ⟨pcFree_gasRemainingIs⟩

/-- The `gasRemainingOff` immediate (568) sign-extends to itself as a 64-bit
    word, normalising the load address LD's spec produces. -/
private theorem signExtend12_gasRemainingOff :
    signExtend12 (BitVec.ofNat 12 gasRemainingOff) =
      BitVec.ofNat 64 gasRemainingOff := by
  rw [signExtend12_ofNat_small (by decide)]

/-- Raw memory-cell-level GAS spec: decrement EVM SP by 32, load `gas` from the
    env block at `envAddr + gasRemainingOff` into `tmpReg`, write it at the new
    top-of-stack low limb and zero the upper three limbs. 6 instructions =
    24 bytes. Mirror of `evm_codesize_spec_within`. -/
theorem evm_gas_spec_within
    (envBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld gas : Word)
    (d0 d1 d2 d3 : Word) :
    let code := evm_gas_code envBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((envAddr + BitVec.ofNat 64 gasRemainingOff) ↦ₘ gas))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ gas) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ gas) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
       ((envAddr + BitVec.ofNat 64 gasRemainingOff) ↦ₘ gas)) := by
  -- ADDI x12 x12 -32 : decrement SP first (matches the emitted handler order).
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- LD tmpReg envBaseReg gasRemainingOff : load env.gasRemaining.
  have LLD := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld
                gas (BitVec.ofNat 12 gasRemainingOff) (base + 4) htmp_ne_x0
  simp only [signExtend12_gasRemainingOff] at LLD
  have LSD0 := sd_spec_gen_within .x12 tmpReg nsp gas
                  d0 (0 : BitVec 12) (base + 8)
  have LSD1 := sd_x0_spec_gen_within .x12 nsp d1 8 (base + 12)
  have LSD2 := sd_x0_spec_gen_within .x12 nsp d2 16 (base + 16)
  have LSD3 := sd_x0_spec_gen_within .x12 nsp d3 24 (base + 20)
  runBlock LADDI LLD LSD0 LSD1 LSD2 LSD3

/-- Concretization of `evmWordIs nsp (BitVec.ofNat 256 gas.toNat)` as four limb
    cells: low limb is `gas`, upper three are zero. Mirror of
    `evmWordIs_calldatasize_unfold`. -/
theorem evmWordIs_gas_unfold
    (nsp : Word) (gas : Word) :
    evmWordIs nsp (BitVec.ofNat 256 gas.toNat) =
      ((nsp ↦ₘ gas) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have h_lt : gas.toNat < 2 ^ 64 := gas.isLt
  have hlow :
      EvmWord.getLimbN (BitVec.ofNat 256 gas.toNat) 0 = gas := by
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
               Nat.zero_mul]
    have h1 : gas.toNat % 2 ^ 256 = gas.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt (by norm_num))
    rw [h1, Nat.mod_eq_of_lt h_lt]
  have hhigh : ∀ k : Nat, k ≠ 0 → k < 4 →
      EvmWord.getLimbN (BitVec.ofNat 256 gas.toNat) k = 0 := by
    intro k hk hk4
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
               Nat.shiftRight_eq_div_pow]
    have h1 : gas.toNat % 2 ^ 256 = gas.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt (by norm_num))
    rw [h1]
    have hp : 2 ^ 64 ≤ 2 ^ (k * 64) :=
      Nat.pow_le_pow_right (by norm_num) (by
        have : 0 < k := Nat.pos_of_ne_zero hk
        omega)
    have hdiv : gas.toNat / 2 ^ (k * 64) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h_lt hp)
    simp [hdiv]
  unfold evmWordIs
  rw [hlow, hhigh 1 (by decide) (by decide),
      hhigh 2 (by decide) (by decide),
      hhigh 3 (by decide) (by decide)]

/-- GAS stack spec: pops nothing, pushes the remaining gas (held in the
    `gasRemainingIs` cell, already reflecting GAS's own base cost) zero-extended
    to 256 bits. The unconditional top-level triple witnessing GAS `.proven`. -/
theorem evm_gas_stack_spec_within
    (envBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld gas : Word)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_gas_code envBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       gasRemainingIs envAddr gas **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ gas) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (BitVec.ofNat 256 gas.toNat :: rest) **
       gasRemainingIs envAddr gas) :=
  cpsTripleWithin_weaken
    (fun _ hp => by
      unfold gasRemainingIs at hp
      xperm_hyp hp)
    (fun _ hq => by
      rw [evmStackIs_cons, evmWordIs_gas_unfold]
      unfold gasRemainingIs
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs (nsp + 32) rest)
      pcFree_evmStackIs
      (evm_gas_spec_within envBaseReg tmpReg htmp_ne_x0
        nsp base envAddr tempOld gas d0 d1 d2 d3))

end GasOpcode
end EvmAsm.Evm64
