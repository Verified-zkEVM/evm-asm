/-
  EvmAsm.Evm64.MSize.Spec

  Slice 6 of issue #99 — MSIZE spec.

  MSIZE reads the EVM memory high-water mark (held in a single 8-byte
  cell at `sizeLoc`, owned by `evmMemSizeIs`) and pushes it as a 256-bit
  value onto the EVM stack. The pushed word has the size value in its
  LOW limb and zeros in the upper three limbs.

  This file proves the raw memory-cell-level spec
  `evm_msize_spec_within`. Lifting to the `evmStackIs / evmWordIs` stack
  view (`evm_msize_stack_spec_within`) is wired on top.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.MSize.Program
import EvmAsm.Evm64.Memory
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- MSIZE raw spec: load the size cell into `tempReg`, decrement SP by 32,
    then write low limb (size) and three zero upper limbs. 6 instructions
    = 24 bytes. -/
theorem evm_msize_spec_within
    (sizeReg tempReg : Reg)
    (htemp_ne_x0 : tempReg ≠ .x0)
    (nsp base sizeLoc tempOld : Word) (sizeBytes : Nat)
    (d0 d1 d2 d3 : Word) :
    let code := evm_msize_code sizeReg tempReg base
    cpsTripleWithin 6 base (base + 24) code
      ((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmMemSizeIs sizeLoc sizeBytes)
      ((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ BitVec.ofNat 64 sizeBytes) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ BitVec.ofNat 64 sizeBytes) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) **
       evmMemSizeIs sizeLoc sizeBytes) := by
  -- Unfold evmMemSizeIs so the size cell appears as a raw `↦ₘ` mapsto.
  simp only [evmMemSizeIs_unfold]
  -- LD tempReg sizeReg 0 : load size cell into tempReg.
  have LLD := ld_spec_gen_within tempReg sizeReg sizeLoc tempOld
                (BitVec.ofNat 64 sizeBytes) (0 : BitVec 12) base htemp_ne_x0
  -- ADDI x12 x12 -32 : decrement SP. Normalize (nsp+32) + (-32) = nsp.
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) (base + 4) (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  -- SD x12 tempReg 0 : write the size value at nsp.
  have LSD0 := sd_spec_gen_within .x12 tempReg nsp (BitVec.ofNat 64 sizeBytes)
                  d0 (0 : BitVec 12) (base + 8)
  -- SD x12 x0 {8,16,24} : zero the upper three limbs.
  have LSD1 := sd_x0_spec_gen_within .x12 nsp d1 8 (base + 12)
  have LSD2 := sd_x0_spec_gen_within .x12 nsp d2 16 (base + 16)
  have LSD3 := sd_x0_spec_gen_within .x12 nsp d3 24 (base + 20)
  runBlock LLD LADDI LSD0 LSD1 LSD2 LSD3

/-! ## Stack-form lift

  Lift `evm_msize_spec_within` to the EVM stack view: the post asserts
  `evmStackIs nsp (BitVec.ofNat 256 sizeBytes :: rest)` whenever the
  caller knows the size fits in 64 bits (which is true for any realistic
  EVM execution — gas costs bound `sizeBytes` well below `2^64`).
-/

private theorem evmWordIs_msize_unfold (nsp : Word) (sizeBytes : Nat)
    (h_size_lt : sizeBytes < 2 ^ 64) :
    evmWordIs nsp (BitVec.ofNat 256 sizeBytes) =
      ((nsp ↦ₘ BitVec.ofNat 64 sizeBytes) ** ((nsp + 8) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  -- Rewrite the four `getLimbN` applications using `getLimbN_eq_extractLsb'`
  -- and the algebraic identities for `extractLsb'` on `BitVec.ofNat 256 _`.
  have hlow : EvmWord.getLimbN (BitVec.ofNat 256 sizeBytes) 0 = BitVec.ofNat 64 sizeBytes := by
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
               Nat.zero_mul]
    have h1 : sizeBytes % 2 ^ 256 = sizeBytes :=
      Nat.mod_eq_of_lt (by
        have : sizeBytes < 2 ^ 256 :=
          Nat.lt_of_lt_of_le h_size_lt (by norm_num)
        exact this)
    rw [h1, Nat.mod_eq_of_lt h_size_lt]
  have hhigh : ∀ k : Nat, k ≠ 0 → k < 4 →
      EvmWord.getLimbN (BitVec.ofNat 256 sizeBytes) k = 0 := by
    intro k hk hk4
    rw [EvmWord.getLimbN_eq_extractLsb']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
               Nat.shiftRight_eq_div_pow]
    have h1 : sizeBytes % 2 ^ 256 = sizeBytes :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt (by norm_num))
    rw [h1]
    have hp : 2 ^ 64 ≤ 2 ^ (k * 64) :=
      Nat.pow_le_pow_right (by norm_num) (by
        have : 0 < k := Nat.pos_of_ne_zero hk
        omega)
    have hdiv : sizeBytes / 2 ^ (k * 64) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h_size_lt hp)
    simp [hdiv]
  unfold evmWordIs
  rw [hlow, hhigh 1 (by decide) (by decide),
      hhigh 2 (by decide) (by decide),
      hhigh 3 (by decide) (by decide)]

/-- Fold the four concrete MSIZE output limbs into the stack-word assertion. -/
theorem msizeWord_evmWordIs_fold (nsp : Word) (sizeBytes : Nat)
    (h_size_lt : sizeBytes < 2 ^ 64) :
    ((nsp ↦ₘ BitVec.ofNat 64 sizeBytes) ** ((nsp + 8) ↦ₘ 0) **
      ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) =
    evmWordIs nsp (BitVec.ofNat 256 sizeBytes) := by
  rw [evmWordIs_msize_unfold nsp sizeBytes h_size_lt]

/-- MSIZE stack spec: pushes `BitVec.ofNat 256 sizeBytes` (the EVM memory
    high-water mark) onto the EVM stack. Requires `sizeBytes < 2^64`,
    which always holds for realistic EVM executions. -/
theorem evm_msize_stack_spec_within
    (sizeReg tempReg : Reg)
    (htemp_ne_x0 : tempReg ≠ .x0)
    (nsp base sizeLoc tempOld : Word) (sizeBytes : Nat)
    (h_size_lt : sizeBytes < 2 ^ 64)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_msize_code sizeReg tempReg base
    cpsTripleWithin 6 base (base + 24) code
      ((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) **
       ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmMemSizeIs sizeLoc sizeBytes **
       evmStackIs (nsp + 32) rest)
      ((sizeReg ↦ᵣ sizeLoc) ** (tempReg ↦ᵣ BitVec.ofNat 64 sizeBytes) **
       (.x12 ↦ᵣ nsp) **
       evmWordIs nsp (BitVec.ofNat 256 sizeBytes) **
       evmMemSizeIs sizeLoc sizeBytes **
       evmStackIs (nsp + 32) rest) :=
  cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      rw [evmWordIs_msize_unfold nsp sizeBytes h_size_lt]
      xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs (nsp + 32) rest)
      pcFree_evmStackIs
      (evm_msize_spec_within sizeReg tempReg htemp_ne_x0
        nsp base sizeLoc tempOld sizeBytes d0 d1 d2 d3))

end EvmAsm.Evm64
