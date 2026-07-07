/-
  EvmAsm.Evm64.ReturnData.SizeSpec

  Stack-level cpsTripleWithin specification for the EVM `RETURNDATASIZE` opcode
  (0x3d; see `EvmAsm/Evm64/ReturnData/SizeProgram.lean`).

  RETURNDATASIZE mirrors GAS/CODESIZE/CALLDATASIZE: it loads a 64-bit value from
  a dispatcher-seeded cell and pushes it zero-extended to 256 bits. The
  returndata size lives in the `evm_precompile_frame` region at
  `returnDataSizeOff = 8`, outside the typed `EvmEnv` struct, so the spec is
  stated against a raw `returnDataSizeIs` cell rather than an `envIs` field
  split. The instruction order is LD-then-ADDI to match the emitted handler.
-/

import EvmAsm.Evm64.ReturnData.SizeProgram
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace ReturnData

open EvmAsm.Rv64

/-- The `evm_precompile_frame` cell holding the returndata size, at
    `frameAddr + returnDataSizeOff`. Seeded by the dispatcher. -/
def returnDataSizeIs (frameAddr sz : Word) : Assertion :=
  (frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ sz

theorem pcFree_returnDataSizeIs {frameAddr sz : Word} :
    (returnDataSizeIs frameAddr sz).pcFree := by
  unfold returnDataSizeIs; pcFree

instance (frameAddr sz : Word) : Assertion.PCFree (returnDataSizeIs frameAddr sz) :=
  ⟨pcFree_returnDataSizeIs⟩

/-- The `returnDataSizeOff` immediate (8) sign-extends to itself as a 64-bit
    word, normalising the load address LD's spec produces. -/
private theorem signExtend12_returnDataSizeOff :
    signExtend12 (BitVec.ofNat 12 returnDataSizeOff) =
      BitVec.ofNat 64 returnDataSizeOff := by
  rw [signExtend12_ofNat_small (by decide)]

/-- Concretization of `evmWordIs nsp (BitVec.ofNat 256 sz.toNat)` as four limb
    cells: low limb is `sz`, upper three are zero. Clone of
    `evmWordIs_gas_unfold` (generic over any 64-bit `Word`). -/
theorem evmWordIs_size_unfold
    (nsp : Word) (sz : Word) :
    evmWordIs nsp (BitVec.ofNat 256 sz.toNat) =
      ((nsp ↦ₘ sz) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have h_lt : sz.toNat < 2 ^ 64 := sz.isLt
  have hlow :
      EvmWord.getLimbN (BitVec.ofNat 256 sz.toNat) 0 = sz := by
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
               Nat.zero_mul]
    have h1 : sz.toNat % 2 ^ 256 = sz.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt (by norm_num))
    rw [h1, Nat.mod_eq_of_lt h_lt]
  have hhigh : ∀ k : Nat, k ≠ 0 → k < 4 →
      EvmWord.getLimbN (BitVec.ofNat 256 sz.toNat) k = 0 := by
    intro k hk hk4
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
               Nat.shiftRight_eq_div_pow]
    have h1 : sz.toNat % 2 ^ 256 = sz.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt (by norm_num))
    rw [h1]
    have hp : 2 ^ 64 ≤ 2 ^ (k * 64) :=
      Nat.pow_le_pow_right (by norm_num) (by
        have : 0 < k := Nat.pos_of_ne_zero hk
        omega)
    have hdiv : sz.toNat / 2 ^ (k * 64) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h_lt hp)
    simp [hdiv]
  unfold evmWordIs
  rw [hlow, hhigh 1 (by decide) (by decide),
      hhigh 2 (by decide) (by decide),
      hhigh 3 (by decide) (by decide)]

/-- Raw memory-cell-level RETURNDATASIZE spec: load `sz` from the frame region
    at `frameAddr + returnDataSizeOff` into `tmpReg`, decrement EVM SP by 32,
    write it at the new top-of-stack low limb and zero the upper three limbs.
    6 instructions = 24 bytes. LD-first ordering (mirror of `evm_gas_spec_within`
    with LD and ADDI transposed to match the emitted handler). -/
theorem evm_returndatasize_spec_within
    (frameReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base frameAddr tempOld sz : Word)
    (d0 d1 d2 d3 : Word) :
    let code := evm_returndatasize_code frameReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((frameReg ↦ᵣ frameAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ sz))
      ((frameReg ↦ᵣ frameAddr) ** (tmpReg ↦ᵣ sz) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ sz) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
       ((frameAddr + BitVec.ofNat 64 returnDataSizeOff) ↦ₘ sz)) := by
  -- LD tmpReg frameReg returnDataSizeOff : load the returndata size first
  -- (matches the emitted handler order).
  have LLD := ld_spec_gen_within tmpReg frameReg frameAddr tempOld
                sz (BitVec.ofNat 12 returnDataSizeOff) base htmp_ne_x0
  simp only [signExtend12_returnDataSizeOff] at LLD
  -- ADDI x12 x12 -32 : decrement SP.
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) (base + 4) (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  have LSD0 := sd_spec_gen_within .x12 tmpReg nsp sz
                  d0 (0 : BitVec 12) (base + 8)
  have LSD1 := sd_x0_spec_gen_within .x12 nsp d1 8 (base + 12)
  have LSD2 := sd_x0_spec_gen_within .x12 nsp d2 16 (base + 16)
  have LSD3 := sd_x0_spec_gen_within .x12 nsp d3 24 (base + 20)
  runBlock LLD LADDI LSD0 LSD1 LSD2 LSD3

/-- RETURNDATASIZE stack spec: pops nothing, pushes the returndata size (held in
    the `returnDataSizeIs` cell) zero-extended to 256 bits. The unconditional
    top-level triple witnessing RETURNDATASIZE `.proven`. -/
theorem evm_returndatasize_stack_spec_within
    (frameReg tmpReg : Reg)
    (htmp_ne_x0 : tmpReg ≠ .x0)
    (nsp base frameAddr tempOld sz : Word)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_returndatasize_code frameReg tmpReg base
    cpsTripleWithin 6 base (base + 24) code
      ((frameReg ↦ᵣ frameAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       returnDataSizeIs frameAddr sz **
       evmStackIs (nsp + 32) rest)
      ((frameReg ↦ᵣ frameAddr) ** (tmpReg ↦ᵣ sz) **
       (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (BitVec.ofNat 256 sz.toNat :: rest) **
       returnDataSizeIs frameAddr sz) :=
  cpsTripleWithin_weaken
    (fun _ hp => by
      unfold returnDataSizeIs at hp
      xperm_hyp hp)
    (fun _ hq => by
      rw [evmStackIs_cons, evmWordIs_size_unfold]
      unfold returnDataSizeIs
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs (nsp + 32) rest)
      pcFree_evmStackIs
      (evm_returndatasize_spec_within frameReg tmpReg htmp_ne_x0
        nsp base frameAddr tempOld sz d0 d1 d2 d3))

end ReturnData
end EvmAsm.Evm64
