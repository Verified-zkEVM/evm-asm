/-
  EvmAsm.Evm64.Calldata.SizeSpec

  Stack-level cpsTripleWithin specification for the EVM `CALLDATASIZE`
  opcode (see `EvmAsm/Evm64/Calldata/SizeProgram.lean`).

  Slice 3 of issue #104 (parent `evm-asm-xjk8`, this slice
  `evm-asm-8mp7`).  Authored by @pirapira; implemented by Hermes-bot
  (evm-hermes).
-/

module

public import EvmAsm.Evm64.Calldata.SizeProgram
public import EvmAsm.Evm64.Environment.Assertion
public import EvmAsm.Evm64.Stack
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.XSimp
public import EvmAsm.Rv64.Tactics.RunBlock

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv (callDataLenOff envIs envIs_callDataLen_split envIsCallDataLenRest)

/-- The on-disk `callDataLenOff` immediate (424) sign-extends to itself
    as a 64-bit word.  Used to normalise the load address that LD's
    spec produces (`v_addr + signExtend12 (BitVec.ofNat 12 424)`) so it
    matches the canonical `v_addr + BitVec.ofNat 64 callDataLenOff`
    spelling used by `envIs_callDataLen_split`. -/
private theorem signExtend12_callDataLenOff :
    signExtend12 (BitVec.ofNat 12 callDataLenOff) =
      BitVec.ofNat 64 callDataLenOff := by
  rw [signExtend12_ofNat_small (by decide)]

/-- Raw memory-cell-level CALLDATASIZE spec: load `callDataLen` from the
    env block at `envAddr + callDataLenOff` into `tmpReg`, decrement EVM
    SP by 32, write the loaded value at the new top-of-stack low limb
    and zero the upper three limbs.  6 instructions = 24 bytes. -/
theorem evm_calldatasize_spec_within
    (envBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld callDataLen : Word)
    (d0 d1 d2 d3 : Word) :
    let code := evm_calldatasize_code envBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ callDataLen) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ callDataLen) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
       ((envAddr + BitVec.ofNat 64 callDataLenOff) ↦ₘ callDataLen)) := by
  -- LD tmpReg envBaseReg callDataLenOff : load env.callDataLen.
  have LLD := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld
                callDataLen (BitVec.ofNat 12 callDataLenOff) base htmp_ne_x0
  simp only [signExtend12_callDataLenOff] at LLD
  -- ADDI x12 x12 -32 : decrement SP. Normalize (nsp+32) + (-32) = nsp.
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) (base + 4) (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- SD x12 tmpReg 0 : write callDataLen at low limb (nsp).
  have LSD0 := sd_spec_gen_within .x12 tmpReg nsp callDataLen
                  d0 (0 : BitVec 12) (base + 8)
  -- SD x12 x0 {8,16,24} : zero the upper three limbs.
  have LSD1 := sd_x0_spec_gen_within .x12 nsp d1 8 (base + 12)
  have LSD2 := sd_x0_spec_gen_within .x12 nsp d2 16 (base + 16)
  have LSD3 := sd_x0_spec_gen_within .x12 nsp d3 24 (base + 20)
  runBlock LLD LADDI LSD0 LSD1 LSD2 LSD3

/-! ## Stack-form lift

  Lift the raw spec to the EVM stack view.  The pushed word is the
  256-bit zero-extension of the 64-bit `callDataLen`, expressed as
  `BitVec.ofNat 256 callDataLen.toNat` so it matches the pure semantics
  in `EvmAsm/Evm64/Calldata/Size.lean`.
-/

/-- Concretization of `evmWordIs nsp (BitVec.ofNat 256 callDataLen.toNat)`
    as four limb cells: low limb is `callDataLen`, upper three are zero.
    Mirror of `evmWordIs_msize_unfold`. -/
theorem evmWordIs_calldatasize_unfold
    (nsp : Word) (callDataLen : Word) :
    evmWordIs nsp (BitVec.ofNat 256 callDataLen.toNat) =
      ((nsp ↦ₘ callDataLen) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have h_size_lt : callDataLen.toNat < 2 ^ 64 := callDataLen.isLt
  have hlow :
      EvmWord.getLimbN (BitVec.ofNat 256 callDataLen.toNat) 0 = callDataLen := by
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
               Nat.zero_mul]
    have h1 : callDataLen.toNat % 2 ^ 256 = callDataLen.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt (by norm_num))
    rw [h1, Nat.mod_eq_of_lt h_size_lt]
  have hhigh : ∀ k : Nat, k ≠ 0 → k < 4 →
      EvmWord.getLimbN (BitVec.ofNat 256 callDataLen.toNat) k = 0 := by
    intro k hk hk4
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
               Nat.shiftRight_eq_div_pow]
    have h1 : callDataLen.toNat % 2 ^ 256 = callDataLen.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt (by norm_num))
    rw [h1]
    have hp : 2 ^ 64 ≤ 2 ^ (k * 64) :=
      Nat.pow_le_pow_right (by norm_num) (by
        have : 0 < k := Nat.pos_of_ne_zero hk
        omega)
    have hdiv : callDataLen.toNat / 2 ^ (k * 64) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt hp)
    simp [hdiv]
  unfold evmWordIs
  rw [hlow, hhigh 1 (by decide) (by decide),
      hhigh 2 (by decide) (by decide),
      hhigh 3 (by decide) (by decide)]

/-- CALLDATASIZE stack spec: pops nothing, pushes the 64-bit
    `callDataLen` zero-extended to 256 bits onto the EVM stack.

    The callDataLen cell is exposed via `envIs_callDataLen_split`, which
    rotates that cell to the head of `envIs base env`; the remainder
    `envIsCallDataLenRest base env` is preserved by the spec. -/
theorem evm_calldatasize_stack_spec_within
    (envBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (env : EvmEnv)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_calldatasize_code envBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ env.callDataLen) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (BitVec.ofNat 256 env.callDataLen.toNat :: rest) **
       envIs envAddr env) :=
  cpsTripleWithin_weaken
    (fun _ hp => by
      rw [envIs_callDataLen_split envAddr env] at hp
      xperm_hyp hp)
    (fun _ hq => by
      rw [evmStackIs_cons, evmWordIs_calldatasize_unfold,
          envIs_callDataLen_split envAddr env]
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (envIsCallDataLenRest envAddr env ** evmStackIs (nsp + 32) rest)
      (pcFree_sepConj (by unfold envIsCallDataLenRest; pcFree)
        pcFree_evmStackIs)
      (evm_calldatasize_spec_within envBaseReg tmpReg htmp_ne_x0
        nsp base envAddr tempOld env.callDataLen d0 d1 d2 d3))

end Calldata
end EvmAsm.Evm64
