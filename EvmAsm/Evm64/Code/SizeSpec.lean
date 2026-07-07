/-
  EvmAsm.Evm64.Code.SizeSpec

  Stack-level cpsTripleWithin specification for the EVM `CODESIZE` opcode
  (see `EvmAsm/Evm64/Code/SizeProgram.lean`).

  CODESIZE mirrors CALLDATASIZE (`Evm64/Calldata/SizeSpec.lean`): both load a
  64-bit length from an env-block cell and push it zero-extended to 256 bits.
  The difference is that CALLDATASIZE reads the typed `env.callDataLen` field
  exposed through `envIs`, whereas the running-code length lives in a
  dispatcher-seeded cell at `codeSizeOff = 496` that is *outside* the typed
  `EvmEnv` struct. We therefore specify it against a raw `codeSizeIs` cell
  rather than an `envIs` split, which makes the stack lift strictly simpler
  (no field rotation).
-/

import EvmAsm.Evm64.Code.SizeProgram
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Code

open EvmAsm.Rv64

/-- The env-block cell holding the running-bytecode length, at
    `envAddr + codeSizeOff`. Seeded by both dispatcher prologues. -/
def codeSizeIs (envAddr : Word) (codeSize : Word) : Assertion :=
  (envAddr + BitVec.ofNat 64 codeSizeOff) ↦ₘ codeSize

theorem pcFree_codeSizeIs {envAddr codeSize : Word} :
    (codeSizeIs envAddr codeSize).pcFree := by
  unfold codeSizeIs; pcFree

instance (envAddr codeSize : Word) : Assertion.PCFree (codeSizeIs envAddr codeSize) :=
  ⟨pcFree_codeSizeIs⟩

/-- The on-disk `codeSizeOff` immediate (496) sign-extends to itself as a
    64-bit word, normalising the load address LD's spec produces. -/
private theorem signExtend12_codeSizeOff :
    signExtend12 (BitVec.ofNat 12 codeSizeOff) =
      BitVec.ofNat 64 codeSizeOff := by
  rw [signExtend12_ofNat_small (by decide)]

/-- Raw memory-cell-level CODESIZE spec: load `codeSize` from the env block at
    `envAddr + codeSizeOff` into `tmpReg`, decrement EVM SP by 32, write the
    loaded value at the new top-of-stack low limb and zero the upper three
    limbs. 6 instructions = 24 bytes. Mirror of `evm_calldatasize_spec_within`. -/
theorem evm_codesize_spec_within
    (envBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld codeSize : Word)
    (d0 d1 d2 d3 : Word) :
    let code := evm_codesize_code envBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((envAddr + BitVec.ofNat 64 codeSizeOff) ↦ₘ codeSize))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ codeSize) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ codeSize) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
       ((envAddr + BitVec.ofNat 64 codeSizeOff) ↦ₘ codeSize)) := by
  -- ADDI x12 x12 -32 : decrement SP first (matches the emitted handler order).
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- LD tmpReg envBaseReg codeSizeOff : load env.codeSize.
  have LLD := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld
                codeSize (BitVec.ofNat 12 codeSizeOff) (base + 4) htmp_ne_x0
  simp only [signExtend12_codeSizeOff] at LLD
  have LSD0 := sd_spec_gen_within .x12 tmpReg nsp codeSize
                  d0 (0 : BitVec 12) (base + 8)
  have LSD1 := sd_x0_spec_gen_within .x12 nsp d1 8 (base + 12)
  have LSD2 := sd_x0_spec_gen_within .x12 nsp d2 16 (base + 16)
  have LSD3 := sd_x0_spec_gen_within .x12 nsp d3 24 (base + 20)
  runBlock LADDI LLD LSD0 LSD1 LSD2 LSD3

/-- Concretization of `evmWordIs nsp (BitVec.ofNat 256 codeSize.toNat)` as four
    limb cells: low limb is `codeSize`, upper three are zero. Mirror of
    `evmWordIs_calldatasize_unfold`. -/
theorem evmWordIs_codesize_unfold
    (nsp : Word) (codeSize : Word) :
    evmWordIs nsp (BitVec.ofNat 256 codeSize.toNat) =
      ((nsp ↦ₘ codeSize) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have h_size_lt : codeSize.toNat < 2 ^ 64 := codeSize.isLt
  have hlow :
      EvmWord.getLimbN (BitVec.ofNat 256 codeSize.toNat) 0 = codeSize := by
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
               Nat.zero_mul]
    have h1 : codeSize.toNat % 2 ^ 256 = codeSize.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt (by norm_num))
    rw [h1, Nat.mod_eq_of_lt h_size_lt]
  have hhigh : ∀ k : Nat, k ≠ 0 → k < 4 →
      EvmWord.getLimbN (BitVec.ofNat 256 codeSize.toNat) k = 0 := by
    intro k hk hk4
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
               Nat.shiftRight_eq_div_pow]
    have h1 : codeSize.toNat % 2 ^ 256 = codeSize.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt (by norm_num))
    rw [h1]
    have hp : 2 ^ 64 ≤ 2 ^ (k * 64) :=
      Nat.pow_le_pow_right (by norm_num) (by
        have : 0 < k := Nat.pos_of_ne_zero hk
        omega)
    have hdiv : codeSize.toNat / 2 ^ (k * 64) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt hp)
    simp [hdiv]
  unfold evmWordIs
  rw [hlow, hhigh 1 (by decide) (by decide),
      hhigh 2 (by decide) (by decide),
      hhigh 3 (by decide) (by decide)]

/-- CODESIZE stack spec: pops nothing, pushes the running-bytecode length
    (held in the `codeSizeIs` cell) zero-extended to 256 bits onto the EVM
    stack. The unconditional top-level triple witnessing CODESIZE `.proven`. -/
theorem evm_codesize_stack_spec_within
    (envBaseReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base envAddr tempOld codeSize : Word)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_codesize_code envBaseReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       codeSizeIs envAddr codeSize **
       evmStackIs (nsp + 32) rest)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ codeSize) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (BitVec.ofNat 256 codeSize.toNat :: rest) **
       codeSizeIs envAddr codeSize) :=
  cpsTripleWithin_weaken
    (fun _ hp => by
      unfold codeSizeIs at hp
      xperm_hyp hp)
    (fun _ hq => by
      rw [evmStackIs_cons, evmWordIs_codesize_unfold]
      unfold codeSizeIs
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs (nsp + 32) rest)
      pcFree_evmStackIs
      (evm_codesize_spec_within envBaseReg tmpReg htmp_ne_x0
        nsp base envAddr tempOld codeSize d0 d1 d2 d3))

end Code
end EvmAsm.Evm64
