/-
  EvmAsm.Evm64.BlobBaseFee.Spec

  Stack-level cpsTripleWithin specification for the EVM `BLOBBASEFEE` opcode
  (0x4a, EIP-7516; see `EvmAsm/Evm64/BlobBaseFee/Program.lean`).

  BLOBBASEFEE mirrors the simple environment loads (`evm_env_load`): it copies
  a full 256-bit value (four 64-bit limbs) from the env block onto the EVM
  stack. The blob base fee lives in a dispatcher-seeded region at
  `blobBaseFeeOff = 512`, outside the typed `EvmEnv` struct, so the spec is
  stated against a raw `blobBaseFeeIs` cell group rather than an `envIs` field
  split. The 256-bit push uses the definitional unfolding of `evmWordIs` into
  its four limb cells.
-/

import EvmAsm.Evm64.BlobBaseFee.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace BlobBaseFee

open EvmAsm.Rv64

/-- The env-block region holding the blob base fee: four 64-bit limbs of `w`
    at `envAddr + blobBaseFeeOff + {0,8,16,24}`. Seeded by the dispatcher. -/
def blobBaseFeeIs (envAddr : Word) (w : EvmWord) : Assertion :=
  ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 0))  ↦ₘ w.getLimbN 0) **
  ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 8))  ↦ₘ w.getLimbN 1) **
  ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 16)) ↦ₘ w.getLimbN 2) **
  ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 24)) ↦ₘ w.getLimbN 3)

theorem pcFree_blobBaseFeeIs {envAddr : Word} {w : EvmWord} :
    (blobBaseFeeIs envAddr w).pcFree := by
  unfold blobBaseFeeIs; pcFree

instance (envAddr : Word) (w : EvmWord) : Assertion.PCFree (blobBaseFeeIs envAddr w) :=
  ⟨pcFree_blobBaseFeeIs⟩

/-- Raw memory-cell-level BLOBBASEFEE spec: decrement EVM SP by 32, copy the
    four limbs from `envAddr + blobBaseFeeOff + {0,8,16,24}` into the freshly
    allocated stack slot. 9 instructions = 36 bytes. Mirror of
    `evm_env_load_raw_spec_within` at a raw offset. -/
theorem evm_blobbasefee_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word)
    (v0 v1 v2 v3 : Word) (d0 d1 d2 d3 : Word) :
    let code := evm_blobbasefee_code envBaseReg tmpReg base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 0))  ↦ₘ v0) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 8))  ↦ₘ v1) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 16)) ↦ₘ v2) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 24)) ↦ₘ v3))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ v3) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ v0) ** ((nsp + 8) ↦ₘ v1) **
       ((nsp + 16) ↦ₘ v2) ** ((nsp + 24) ↦ₘ v3) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 0))  ↦ₘ v0) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 8))  ↦ₘ v1) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 16)) ↦ₘ v2) **
       ((envAddr + BitVec.ofNat 64 (blobBaseFeeOff + 24)) ↦ₘ v3)) := by
  -- ADDI x12 x12 -32 : decrement EVM SP. Normalise (nsp+32)+(-32)=nsp.
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- Limb 0 (env offset 512, stack offset 0)
  have LLD0 := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld v0
                  (BitVec.ofNat 12 (blobBaseFeeOff + 0)) (base + 4) htmp_ne_x0
  rw [show signExtend12 (BitVec.ofNat 12 (blobBaseFeeOff + 0))
        = BitVec.ofNat 64 (blobBaseFeeOff + 0) from
        signExtend12_ofNat_small (by decide)] at LLD0
  have LSD0 := sd_spec_gen_within .x12 tmpReg nsp v0 d0
                  (BitVec.ofNat 12 0) (base + 8)
  rw [show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) from by decide] at LSD0
  rw [show (nsp + 0 : Word) = nsp from by bv_omega] at LSD0
  -- Limb 1 (env offset 520, stack offset 8)
  have LLD1 := ld_spec_gen_within tmpReg envBaseReg envAddr v0 v1
                  (BitVec.ofNat 12 (blobBaseFeeOff + 8)) (base + 12) htmp_ne_x0
  rw [show signExtend12 (BitVec.ofNat 12 (blobBaseFeeOff + 8))
        = BitVec.ofNat 64 (blobBaseFeeOff + 8) from
        signExtend12_ofNat_small (by decide)] at LLD1
  have LSD1 := sd_spec_gen_within .x12 tmpReg nsp v1 d1
                  (BitVec.ofNat 12 8) (base + 16)
  rw [show signExtend12 (BitVec.ofNat 12 8) = BitVec.ofNat 64 8 from
        signExtend12_ofNat_small (by decide)] at LSD1
  rw [show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at LSD1
  -- Limb 2 (env offset 528, stack offset 16)
  have LLD2 := ld_spec_gen_within tmpReg envBaseReg envAddr v1 v2
                  (BitVec.ofNat 12 (blobBaseFeeOff + 16)) (base + 20) htmp_ne_x0
  rw [show signExtend12 (BitVec.ofNat 12 (blobBaseFeeOff + 16))
        = BitVec.ofNat 64 (blobBaseFeeOff + 16) from
        signExtend12_ofNat_small (by decide)] at LLD2
  have LSD2 := sd_spec_gen_within .x12 tmpReg nsp v2 d2
                  (BitVec.ofNat 12 16) (base + 24)
  rw [show signExtend12 (BitVec.ofNat 12 16) = BitVec.ofNat 64 16 from
        signExtend12_ofNat_small (by decide)] at LSD2
  rw [show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at LSD2
  -- Limb 3 (env offset 536, stack offset 24)
  have LLD3 := ld_spec_gen_within tmpReg envBaseReg envAddr v2 v3
                  (BitVec.ofNat 12 (blobBaseFeeOff + 24)) (base + 28) htmp_ne_x0
  rw [show signExtend12 (BitVec.ofNat 12 (blobBaseFeeOff + 24))
        = BitVec.ofNat 64 (blobBaseFeeOff + 24) from
        signExtend12_ofNat_small (by decide)] at LLD3
  have LSD3 := sd_spec_gen_within .x12 tmpReg nsp v3 d3
                  (BitVec.ofNat 12 24) (base + 32)
  rw [show signExtend12 (BitVec.ofNat 12 24) = BitVec.ofNat 64 24 from
        signExtend12_ofNat_small (by decide)] at LSD3
  rw [show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at LSD3
  runBlock LADDI LLD0 LSD0 LLD1 LSD1 LLD2 LSD2 LLD3 LSD3

/-- BLOBBASEFEE stack spec: pops nothing, pushes the 256-bit blob base fee
    `w` (held in the `blobBaseFeeIs` cell group) onto the EVM stack. The
    unconditional top-level triple witnessing BLOBBASEFEE `.proven`. -/
theorem evm_blobbasefee_stack_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld : Word) (w : EvmWord)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_blobbasefee_code envBaseReg tmpReg base
    cpsTripleWithin 9 base (base + 36) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       blobBaseFeeIs envAddr w **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ w.getLimbN 3) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (w :: rest) **
       blobBaseFeeIs envAddr w) :=
  cpsTripleWithin_weaken
    (fun _ hp => by
      unfold blobBaseFeeIs at hp
      xperm_hyp hp)
    (fun _ hq => by
      rw [evmStackIs_cons,
          show evmWordIs nsp w
              = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                 ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl]
      unfold blobBaseFeeIs
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs (nsp + 32) rest)
      pcFree_evmStackIs
      (evm_blobbasefee_spec_within envBaseReg tmpReg htmp_ne_x0
        nsp base envAddr tempOld
        (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3)
        d0 d1 d2 d3))

end BlobBaseFee
end EvmAsm.Evm64
