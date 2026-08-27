/-
  EvmAsm.Evm64.Env.StackSpec

  Stack-level cpsTripleWithin specification for the parameterized
  `evm_env_load envBaseReg tmpReg field` program (see
  `EvmAsm.Evm64.Env.Program`).

  Slice 5 of GH #103 (parent issue, this slice `evm-asm-3fvb`).
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  The 9-instruction `evm_env_load` program (one `ADDI x12 x12 -32`
  plus four `env_one_limb` blocks) is composed via `runBlock` from one
  ADDI spec plus four invocations of `env_one_limb_spec_within`
  (`EvmAsm/Evm64/Env/Spec.lean`). The stack-form lift uses
  `SimpleEnvField.envIs_split` to rotate the relevant env cell to the
  head of `envIs envAddr env`, then unfolds it to four limb cells via
  `evmWordIs_field_unfold`, parallel to
  `EvmAsm/Evm64/Calldata/SizeSpec.lean`.
-/

module

public import EvmAsm.Evm64.Env.Program
public import EvmAsm.Evm64.Env.Field
public import EvmAsm.Evm64.Environment.Assertion
public import EvmAsm.Evm64.Stack
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.RunBlock
public import EvmAsm.Rv64.Tactics.XSimp

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Env

open EvmAsm.Rv64
open SimpleEnvField

/-- Unfold `cellIs envAddr field env` into four limb-level memory atoms
    with the offset spelling `envAddr + ofNat 64 (field.offset + 8*i)`
    that `env_one_limb_spec_within` produces, so the stack-form lift
    can fan the envIs cell out into the four ↦ₘ atoms consumed by the
    raw memory-cell spec. -/
theorem evmWordIs_field_unfold
    (envAddr : Word) (field : SimpleEnvField) (env : EvmEnv) :
    cellIs envAddr field env =
      (((envAddr + BitVec.ofNat 64 (field.offset + 0))  ↦ₘ (field.value env).getLimbN 0) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8))  ↦ₘ (field.value env).getLimbN 1) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 16)) ↦ₘ (field.value env).getLimbN 2) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 24)) ↦ₘ (field.value env).getLimbN 3)) := by
  unfold cellIs slotAddr evmWordIs
  have h0 : envAddr + BitVec.ofNat 64 field.offset
              = envAddr + BitVec.ofNat 64 (field.offset + 0) := by bv_omega
  have h1 : envAddr + BitVec.ofNat 64 field.offset + 8
              = envAddr + BitVec.ofNat 64 (field.offset + 8) := by bv_omega
  have h2 : envAddr + BitVec.ofNat 64 field.offset + 16
              = envAddr + BitVec.ofNat 64 (field.offset + 16) := by bv_omega
  have h3 : envAddr + BitVec.ofNat 64 field.offset + 24
              = envAddr + BitVec.ofNat 64 (field.offset + 24) := by bv_omega
  rw [h1, h2, h3, h0]

/-- Bound on the per-limb load offset: the largest field offset is
    `chainIdOff = 384`, and `8*i ≤ 24`, so `field.offset + 8*i ≤ 408`,
    well under 2048.  Used to discharge `signExtend12_ofNat_small`. -/
theorem field_offset_add_lt_2048
    (field : SimpleEnvField) (i : Nat) (hi : i < 4) :
    field.offset + 8 * i < 2048 := by
  interval_cases i <;> cases field <;> decide

/-- Raw memory-cell-level spec for `evm_env_load envBaseReg tmpReg field`:
    the 9-instruction program decrements the EVM SP by 32 (`ADDI x12 x12 -32`)
    and writes the four 64-bit limbs of the field at the new top-of-stack
    cells.  Composed from 9 individual singleton instruction specs via
    `runBlock`.

    Note: this is the *raw* form of the spec, parameterised by four
    arbitrary limb values `v0..v3`, with memory cells at literal
    `field.offset + {0,8,16,24}` offsets.  It is a private internal
    helper for the stack-form lift below.  The end-user spec
    `evm_env_load_spec_within` (in `EvmAsm.Evm64.Env.Spec`) is the
    `EvmEnv`/`SimpleEnvField`-instantiated form, which is also what
    `evm_env_load_stack_spec_within` ultimately consumes via
    `cpsTripleWithin_frameR`. -/
private theorem evm_env_load_raw_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (field : SimpleEnvField)
    (v0 v1 v2 v3 : Word) (d0 d1 d2 d3 : Word) :
    let code := evm_env_load_code envBaseReg tmpReg field base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 0))  ↦ₘ v0) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8))  ↦ₘ v1) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 16)) ↦ₘ v2) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 24)) ↦ₘ v3))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ v3) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ v0) ** ((nsp + 8) ↦ₘ v1) **
       ((nsp + 16) ↦ₘ v2) ** ((nsp + 24) ↦ₘ v3) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 0))  ↦ₘ v0) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8))  ↦ₘ v1) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 16)) ↦ₘ v2) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 24)) ↦ₘ v3)) := by
  -- ADDI x12 x12 -32 : decrement EVM SP. Normalise (nsp+32)+(-32)=nsp.
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- Per-limb LD/SD specs at base+4, base+8, ..., base+32.
  have h0_se : signExtend12 (BitVec.ofNat 12 (field.offset + 0))
                  = BitVec.ofNat 64 (field.offset + 0) :=
    signExtend12_ofNat_small (field_offset_add_lt_2048 field 0 (by decide))
  have h1_se : signExtend12 (BitVec.ofNat 12 (field.offset + 8))
                  = BitVec.ofNat 64 (field.offset + 8) :=
    signExtend12_ofNat_small (field_offset_add_lt_2048 field 1 (by decide))
  have h2_se : signExtend12 (BitVec.ofNat 12 (field.offset + 16))
                  = BitVec.ofNat 64 (field.offset + 16) :=
    signExtend12_ofNat_small (field_offset_add_lt_2048 field 2 (by decide))
  have h3_se : signExtend12 (BitVec.ofNat 12 (field.offset + 24))
                  = BitVec.ofNat 64 (field.offset + 24) :=
    signExtend12_ofNat_small (field_offset_add_lt_2048 field 3 (by decide))
  -- Limb 0
  have LLD0 := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld v0
                  (BitVec.ofNat 12 (field.offset + 0)) (base + 4) htmp_ne_x0
  rw [h0_se] at LLD0
  have LSD0 := sd_spec_gen_within .x12 tmpReg nsp v0 d0
                  (BitVec.ofNat 12 0) (base + 8)
  rw [show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) from by decide] at LSD0
  rw [show (nsp + 0 : Word) = nsp from by bv_omega] at LSD0
  -- Limb 1
  have LLD1 := ld_spec_gen_within tmpReg envBaseReg envAddr v0 v1
                  (BitVec.ofNat 12 (field.offset + 8)) (base + 12) htmp_ne_x0
  rw [h1_se] at LLD1
  have LSD1 := sd_spec_gen_within .x12 tmpReg nsp v1 d1
                  (BitVec.ofNat 12 8) (base + 16)
  rw [show signExtend12 (BitVec.ofNat 12 8) = BitVec.ofNat 64 8 from
        signExtend12_ofNat_small (by decide)] at LSD1
  rw [show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at LSD1
  -- Limb 2
  have LLD2 := ld_spec_gen_within tmpReg envBaseReg envAddr v1 v2
                  (BitVec.ofNat 12 (field.offset + 16)) (base + 20) htmp_ne_x0
  rw [h2_se] at LLD2
  have LSD2 := sd_spec_gen_within .x12 tmpReg nsp v2 d2
                  (BitVec.ofNat 12 16) (base + 24)
  rw [show signExtend12 (BitVec.ofNat 12 16) = BitVec.ofNat 64 16 from
        signExtend12_ofNat_small (by decide)] at LSD2
  rw [show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at LSD2
  -- Limb 3
  have LLD3 := ld_spec_gen_within tmpReg envBaseReg envAddr v2 v3
                  (BitVec.ofNat 12 (field.offset + 24)) (base + 28) htmp_ne_x0
  rw [h3_se] at LLD3
  have LSD3 := sd_spec_gen_within .x12 tmpReg nsp v3 d3
                  (BitVec.ofNat 12 24) (base + 32)
  rw [show signExtend12 (BitVec.ofNat 12 24) = BitVec.ofNat 64 24 from
        signExtend12_ofNat_small (by decide)] at LSD3
  rw [show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at LSD3
  runBlock LADDI LLD0 LSD0 LLD1 LSD1 LLD2 LSD2 LLD3 LSD3

/-! ## Stack-form lift

  Lift the raw spec to the EVM stack view: pop nothing, push the
  256-bit `field.value env` onto the EVM stack.  Uses
  `SimpleEnvField.envIs_split` to rotate the relevant env cell to the
  head of `envIs envAddr env`; the remainder `field.rest envAddr env`
  is preserved by the spec.
-/

/-- `pcFree` for the residual `field.rest base env` after rotating one
    cell out of `envIs base env`.  Each per-field `envIs<F>Rest` is a
    sepConj of `evmWordIs`/`↦ₘ` cells, so `pcFree` discharges by
    unfolding and the standard atom lemmas. -/
private theorem pcFree_rest
    (base : Word) (field : SimpleEnvField) (env : EvmEnv) :
    (field.rest base env).pcFree := by
  cases field
  case address     => unfold rest EvmEnv.envIsAddressRest;         pcFree
  case caller      => unfold rest EvmEnv.envIsCallerRest;          pcFree
  case callValue   => unfold rest EvmEnv.envIsCallValueRest;       pcFree
  case origin      => unfold rest EvmEnv.envIsTxOriginRest;        pcFree
  case gasPrice    => unfold rest EvmEnv.envIsGasPriceRest;        pcFree
  case coinbase    => unfold rest EvmEnv.envIsBlockCoinbaseRest;   pcFree
  case timestamp   => unfold rest EvmEnv.envIsBlockTimestampRest;  pcFree
  case number      => unfold rest EvmEnv.envIsBlockNumberRest;     pcFree
  case prevrandao  => unfold rest EvmEnv.envIsBlockPrevrandaoRest; pcFree
  case gasLimit    => unfold rest EvmEnv.envIsBlockGasLimitRest;   pcFree
  case chainId     => unfold rest EvmEnv.envIsChainIdRest;         pcFree
  case baseFee     => unfold rest EvmEnv.envIsBlockBaseFeeRest;    pcFree
  case selfBalance => unfold rest EvmEnv.envIsSelfBalanceRest;     pcFree

/-- Stack-form spec for the parameterized environment-load opcode:
    pops nothing, pushes `field.value env` onto the EVM stack.
    The chosen env cell is exposed via `SimpleEnvField.envIs_split`,
    which rotates that cell to the head of `envIs envAddr env`;
    the remainder `field.rest envAddr env` is preserved. -/
theorem evm_env_load_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (field : SimpleEnvField)
    (env : EvmEnv) (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_env_load_code envBaseReg tmpReg field base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       EvmEnv.envIs envAddr env **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ (field.value env).getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (field.value env :: rest) **
       EvmEnv.envIs envAddr env) :=
  cpsTripleWithin_weaken
    (fun _ hp => by
      rw [SimpleEnvField.envIs_split envAddr field env,
          evmWordIs_field_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => by
      rw [evmStackIs_cons,
          show evmWordIs nsp (field.value env)
              = ((nsp ↦ₘ (field.value env).getLimbN 0) **
                 ((nsp + 8) ↦ₘ (field.value env).getLimbN 1) **
                 ((nsp + 16) ↦ₘ (field.value env).getLimbN 2) **
                 ((nsp + 24) ↦ₘ (field.value env).getLimbN 3)) from rfl,
          SimpleEnvField.envIs_split envAddr field env,
          evmWordIs_field_unfold]
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (field.rest envAddr env ** evmStackIs (nsp + 32) rest)
      (pcFree_sepConj (pcFree_rest envAddr field env) pcFree_evmStackIs)
      (evm_env_load_raw_spec_within envBaseReg tmpReg htmp_ne_x0
        nsp base envAddr tempOld field
        ((field.value env).getLimbN 0) ((field.value env).getLimbN 1)
        ((field.value env).getLimbN 2) ((field.value env).getLimbN 3)
        d0 d1 d2 d3))

end Env
end EvmAsm.Evm64
