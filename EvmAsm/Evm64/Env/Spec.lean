/-
  EvmAsm.Evm64.Env.Spec

  Per-limb cpsTripleWithin spec for the simple environment opcode load.

  Slice 5a-pre of GH #103 (parent `evm-asm-3jso`, this slice
  `evm-asm-ndsm`). The 9-instruction `evm_env_load` program decomposes
  into one `ADDI x12 x12 -32` allocator plus four `LD/SD` limb pairs
  (`env_one_limb`). This file lifts the 2-instruction limb pair to a
  reusable `cpsTripleWithin` spec so the eventual 5a low-level spec
  reuses it four times via `runBlock`, paralleling the structure of
  `EvmAsm/Evm64/Calldata/SizeSpec.lean`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Evm64.Env.Program
public import EvmAsm.Rv64.SyscallSpecs
public import EvmAsm.Rv64.Tactics.RunBlock
public import EvmAsm.Rv64.Tactics.XSimp
public import EvmAsm.Evm64.Stack

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Env

open EvmAsm.Rv64

/-- Code requirement for one `LD/SD` limb pair at byte address `base`.
    Matches the shape produced by the `env_one_limb` skeleton in
    `Env/Program.lean`. -/
abbrev env_one_limb_code
    (envBaseReg tmpReg : Reg) (loadOff storeOff : Nat) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (LD tmpReg envBaseReg (BitVec.ofNat 12 loadOff) ;;
     SD .x12 tmpReg (BitVec.ofNat 12 storeOff))

/-- Per-limb spec for `env_one_limb`: load a 64-bit limb from the
    environment block at `envAddr + loadOff` into `tmpReg`, then store
    it back at `nsp + storeOff` (above the new EVM SP `nsp`).

    Both offsets are required to be small (< 2048) so the 12-bit
    immediate sign-extends to itself.

    The spec exposes `nsp` directly (i.e. caller has already pre-bumped
    `x12`) and frames the source `envAddr` cell through unchanged.  -/
theorem env_one_limb_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (envAddr nsp memVal dOld tempOld : Word)
    (loadOff storeOff : Nat)
    (h_load : loadOff < 2048) (h_store : storeOff < 2048)
    (base : Word) :
    cpsTripleWithin 2 base (base + 8)
      (env_one_limb_code envBaseReg tmpReg loadOff storeOff base)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ nsp) **
       ((envAddr + BitVec.ofNat 64 loadOff) ↦ₘ memVal) **
       ((nsp + BitVec.ofNat 64 storeOff) ↦ₘ dOld))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ memVal) **
       (.x12 ↦ᵣ nsp) **
       ((envAddr + BitVec.ofNat 64 loadOff) ↦ₘ memVal) **
       ((nsp + BitVec.ofNat 64 storeOff) ↦ₘ memVal)) := by
  -- Normalise the 12-bit sign-extension so it matches the 64-bit
  -- offsets used by the `↦ₘ` cells.
  have h_load_se :
      signExtend12 (BitVec.ofNat 12 loadOff) = BitVec.ofNat 64 loadOff :=
    signExtend12_ofNat_small h_load
  have h_store_se :
      signExtend12 (BitVec.ofNat 12 storeOff) = BitVec.ofNat 64 storeOff :=
    signExtend12_ofNat_small h_store
  -- LD tmpReg envBaseReg loadOff : load the limb.
  have hLD := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld memVal
                (BitVec.ofNat 12 loadOff) base htmp_ne_x0
  rw [h_load_se] at hLD
  -- SD x12 tmpReg storeOff : write the limb to the new stack slot.
  have hSD := sd_spec_gen_within .x12 tmpReg nsp memVal dOld
                (BitVec.ofNat 12 storeOff) (base + 4)
  rw [h_store_se] at hSD
  runBlock hLD hSD

/-! ## Low-level cell spec for the full 9-instruction `evm_env_load`

  Slice 5a-low (`evm-asm-ibey`). Compose `env_one_limb_spec_within`
  four times with `addi_spec_gen_same_within` for the SP-bumping
  prologue, producing a single 9-instruction = 36-byte
  `cpsTripleWithin` for the parameterized `evm_env_load` program at
  `base`. The four memory source cells (env block) are framed
  through unchanged; the four target cells (above the new EVM SP
  `nsp`) are overwritten with the four 64-bit limbs of
  `field.value env`.

  Mirror of `evm_calldatasize_spec_within` (`Calldata/SizeSpec.lean`)
  but with four limbs instead of one + zero-fill.
-/

/-- Every `SimpleEnvField` has its 32-byte slot inside the 12-bit
    immediate range, so all four limb load offsets sign-extend to
    themselves. -/
private theorem field_offset_plus_24_lt_2048 (field : SimpleEnvField) :
    field.offset + 24 < 2048 := by
  cases field <;> decide

/-- Low-level (per-cell) spec for `evm_env_load envBaseReg tmpReg field`.

    Pre: registers `envBaseReg ↦ envAddr`, `tmpReg ↦ tempOld`,
    `x12 ↦ nsp + 32`; four env source cells at
    `envAddr + BitVec.ofNat 64 (field.offset + 8 * i)` carrying the
    four limbs of `field.value env`; four target cells at
    `nsp + BitVec.ofNat 64 (8 * i)` holding garbage `d_i`.

    Post: same source cells (frame-through); `tmpReg` now holds the
    high limb (`getLimbN 3`); `x12` decremented to `nsp`; the four
    target cells now hold the four limbs of `field.value env`. -/
theorem evm_env_load_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (envAddr nsp tempOld : Word) (env : EvmEnv) (field : SimpleEnvField)
    (d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 base (base + 36)
      (evm_env_load_code envBaseReg tmpReg field base)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 0)) ↦ₘ
          (field.value env).getLimbN 0) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 1)) ↦ₘ
          (field.value env).getLimbN 1) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 2)) ↦ₘ
          (field.value env).getLimbN 2) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 3)) ↦ₘ
          (field.value env).getLimbN 3) **
       ((nsp + BitVec.ofNat 64 (8 * 0)) ↦ₘ d0) **
       ((nsp + BitVec.ofNat 64 (8 * 1)) ↦ₘ d1) **
       ((nsp + BitVec.ofNat 64 (8 * 2)) ↦ₘ d2) **
       ((nsp + BitVec.ofNat 64 (8 * 3)) ↦ₘ d3))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ (field.value env).getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 0)) ↦ₘ
          (field.value env).getLimbN 0) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 1)) ↦ₘ
          (field.value env).getLimbN 1) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 2)) ↦ₘ
          (field.value env).getLimbN 2) **
       ((envAddr + BitVec.ofNat 64 (field.offset + 8 * 3)) ↦ₘ
          (field.value env).getLimbN 3) **
       ((nsp + BitVec.ofNat 64 (8 * 0)) ↦ₘ (field.value env).getLimbN 0) **
       ((nsp + BitVec.ofNat 64 (8 * 1)) ↦ₘ (field.value env).getLimbN 1) **
       ((nsp + BitVec.ofNat 64 (8 * 2)) ↦ₘ (field.value env).getLimbN 2) **
       ((nsp + BitVec.ofNat 64 (8 * 3)) ↦ₘ (field.value env).getLimbN 3)) := by
  -- ADDI x12 x12 -32 : decrement EVM SP by 32 (nsp + 32 ↦ nsp).
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- Bounds for the four limb-pair offsets.
  have h_off := field_offset_plus_24_lt_2048 field
  have h_l0 : field.offset + 8 * 0 < 2048 := by omega
  have h_l1 : field.offset + 8 * 1 < 2048 := by omega
  have h_l2 : field.offset + 8 * 2 < 2048 := by omega
  have h_l3 : field.offset + 8 * 3 < 2048 := by omega
  have h_s0 : (8 * 0 : Nat) < 2048 := by decide
  have h_s1 : (8 * 1 : Nat) < 2048 := by decide
  have h_s2 : (8 * 2 : Nat) < 2048 := by decide
  have h_s3 : (8 * 3 : Nat) < 2048 := by decide
  -- Sign-extension normalisations for the 8 limb addresses.
  have h_se_l0 : signExtend12 (BitVec.ofNat 12 (field.offset + 8 * 0))
                  = BitVec.ofNat 64 (field.offset + 8 * 0) :=
    signExtend12_ofNat_small h_l0
  have h_se_l1 : signExtend12 (BitVec.ofNat 12 (field.offset + 8 * 1))
                  = BitVec.ofNat 64 (field.offset + 8 * 1) :=
    signExtend12_ofNat_small h_l1
  have h_se_l2 : signExtend12 (BitVec.ofNat 12 (field.offset + 8 * 2))
                  = BitVec.ofNat 64 (field.offset + 8 * 2) :=
    signExtend12_ofNat_small h_l2
  have h_se_l3 : signExtend12 (BitVec.ofNat 12 (field.offset + 8 * 3))
                  = BitVec.ofNat 64 (field.offset + 8 * 3) :=
    signExtend12_ofNat_small h_l3
  have h_se_s0 : signExtend12 (BitVec.ofNat 12 (8 * 0))
                  = BitVec.ofNat 64 (8 * 0) :=
    signExtend12_ofNat_small h_s0
  have h_se_s1 : signExtend12 (BitVec.ofNat 12 (8 * 1))
                  = BitVec.ofNat 64 (8 * 1) :=
    signExtend12_ofNat_small h_s1
  have h_se_s2 : signExtend12 (BitVec.ofNat 12 (8 * 2))
                  = BitVec.ofNat 64 (8 * 2) :=
    signExtend12_ofNat_small h_s2
  have h_se_s3 : signExtend12 (BitVec.ofNat 12 (8 * 3))
                  = BitVec.ofNat 64 (8 * 3) :=
    signExtend12_ofNat_small h_s3
  -- Limb 0: LD + SD at base+4 / base+8.
  have L0LD := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld
                ((field.value env).getLimbN 0)
                (BitVec.ofNat 12 (field.offset + 8 * 0)) (base + 4) htmp_ne_x0
  rw [h_se_l0] at L0LD
  have L0SD := sd_spec_gen_within .x12 tmpReg nsp
                ((field.value env).getLimbN 0) d0
                (BitVec.ofNat 12 (8 * 0)) (base + 8)
  rw [h_se_s0] at L0SD
  -- Limb 1.
  have L1LD := ld_spec_gen_within tmpReg envBaseReg envAddr
                ((field.value env).getLimbN 0)
                ((field.value env).getLimbN 1)
                (BitVec.ofNat 12 (field.offset + 8 * 1)) (base + 12) htmp_ne_x0
  rw [h_se_l1] at L1LD
  have L1SD := sd_spec_gen_within .x12 tmpReg nsp
                ((field.value env).getLimbN 1) d1
                (BitVec.ofNat 12 (8 * 1)) (base + 16)
  rw [h_se_s1] at L1SD
  -- Limb 2.
  have L2LD := ld_spec_gen_within tmpReg envBaseReg envAddr
                ((field.value env).getLimbN 1)
                ((field.value env).getLimbN 2)
                (BitVec.ofNat 12 (field.offset + 8 * 2)) (base + 20) htmp_ne_x0
  rw [h_se_l2] at L2LD
  have L2SD := sd_spec_gen_within .x12 tmpReg nsp
                ((field.value env).getLimbN 2) d2
                (BitVec.ofNat 12 (8 * 2)) (base + 24)
  rw [h_se_s2] at L2SD
  -- Limb 3.
  have L3LD := ld_spec_gen_within tmpReg envBaseReg envAddr
                ((field.value env).getLimbN 2)
                ((field.value env).getLimbN 3)
                (BitVec.ofNat 12 (field.offset + 8 * 3)) (base + 28) htmp_ne_x0
  rw [h_se_l3] at L3LD
  have L3SD := sd_spec_gen_within .x12 tmpReg nsp
                ((field.value env).getLimbN 3) d3
                (BitVec.ofNat 12 (8 * 3)) (base + 32)
  rw [h_se_s3] at L3SD
  runBlock LADDI L0LD L0SD L1LD L1SD L2LD L2SD L3LD L3SD

end Env
end EvmAsm.Evm64
