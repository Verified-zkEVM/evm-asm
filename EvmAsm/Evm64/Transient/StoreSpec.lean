/-
  EvmAsm.Evm64.Transient.StoreSpec

  Stack-level `cpsTripleWithin` specification for the EVM `TSTORE` opcode
  (0x5d, EIP-1153 transient storage; see `EvmAsm/Evm64/Transient/StoreProgram.lean`).

  TSTORE appends a fresh 128-byte transient-storage-log entry at
  `TRANSIENT_STORAGE_LOG_BASE + 128 * log_length`, keyed on the executing
  frame's `env.ADDRESS`; it bumps the length counter (`env+464`) and pops the
  two consumed stack words. `original` is written 0 (transient has no refunds).

  `evm_tstore_stack_spec_within` is the top-level witness. The raw
  `evm_tstore_spec_within` proves the 35-instruction body by composing two
  `runBlock` halves — `evm_tstore_p1` (24 instrs) and `evm_tstore_p2` (11) —
  each framed to its touched cells (`cpsTripleWithin_frameR`), extended to the
  full code (`cpsTripleWithin_extend_code` via `ofProg_mono_append_*`), and
  sequenced (`cpsTripleWithin_seq_perm_same_cr`). The second half is proved
  generic in its entry address and instantiated at the split point (`runBlock`
  closes a block at a variable entry, not `base + 96`); the code is passed as a
  named abbrev, not `CodeReq.ofProg` bare.
-/

import EvmAsm.Evm64.Transient.StoreProgram
import EvmAsm.Evm64.StorageAssertions
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Transient

open EvmAsm.Rv64
open EvmAsm.Evm64

/-! ## Bridging facts -/

theorem transientLogBaseImm_eq :
    transientLogBaseImm = TRANSIENT_STORAGE_LOG_BASE := rfl

theorem shift7_eq_mul128 (n : Nat) :
    (BitVec.ofNat 64 n) <<< (7 : BitVec 6).toNat = BitVec.ofNat 64 (n * 128) := by
  have h7 : (7 : BitVec 6).toNat = 7 := by decide
  rw [h7]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have e1 : (2 : Nat) ^ 7 = 128 := by norm_num
  rw [e1, Nat.mul_mod n 128 (2 ^ 64),
      Nat.mod_eq_of_lt (show (128 : Nat) < 2 ^ 64 by norm_num)]

/-- The runtime append target `transientLogBaseImm + (n <<< 7)`. -/
def tstoreTgt (n : Nat) : Word :=
  transientLogBaseImm + ((BitVec.ofNat 64 n) <<< (7 : BitVec 6).toNat)

/-- The append target equals `TRANSIENT_STORAGE_LOG_BASE + 128*n`. -/
theorem tstoreTgt_eq (n : Nat) :
    tstoreTgt n = TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (n * 128) := by
  rw [tstoreTgt, shift7_eq_mul128, transientLogBaseImm_eq]


/-- `storageSlotIs` unfolded to 16 flat doubleword cells at `base + 8·i`,
    matching the addresses the append `sd`s touch. -/
theorem storageSlotIs_eq_flat (base : Word) (e : StorageLogEntry) :
    storageSlotIs base e =
      ((base ↦ₘ e.addrHash.getLimbN 0) **
      ((base + 8) ↦ₘ e.addrHash.getLimbN 1) **
      ((base + 16) ↦ₘ e.addrHash.getLimbN 2) **
      ((base + 24) ↦ₘ e.addrHash.getLimbN 3) **
      ((base + 32) ↦ₘ e.slotKey.getLimbN 0) **
      ((base + 40) ↦ₘ e.slotKey.getLimbN 1) **
      ((base + 48) ↦ₘ e.slotKey.getLimbN 2) **
      ((base + 56) ↦ₘ e.slotKey.getLimbN 3) **
      ((base + 64) ↦ₘ e.original.getLimbN 0) **
      ((base + 72) ↦ₘ e.original.getLimbN 1) **
      ((base + 80) ↦ₘ e.original.getLimbN 2) **
      ((base + 88) ↦ₘ e.original.getLimbN 3) **
      ((base + 96) ↦ₘ e.current.getLimbN 0) **
      ((base + 104) ↦ₘ e.current.getLimbN 1) **
      ((base + 112) ↦ₘ e.current.getLimbN 2) **
      ((base + 120) ↦ₘ e.current.getLimbN 3)) := by
  unfold storageSlotIs evmWordIs
  rw [show (base + 32) + 8 = base + 40 from by bv_omega,
      show (base + 32) + 16 = base + 48 from by bv_omega,
      show (base + 32) + 24 = base + 56 from by bv_omega,
      show (base + 64) + 8 = base + 72 from by bv_omega,
      show (base + 64) + 16 = base + 80 from by bv_omega,
      show (base + 64) + 24 = base + 88 from by bv_omega,
      show (base + 96) + 8 = base + 104 from by bv_omega,
      show (base + 96) + 16 = base + 112 from by bv_omega,
      show (base + 96) + 24 = base + 120 from by bv_omega]
  simp only [sepConj_assoc']


/-! ## Raw cell-level spec (registers concrete: envReg = x20) -/

/-- Raw memory-cell-level TSTORE append spec (`envReg = x20`), 35 instructions
    = 140 bytes. Proven by composing two framed `runBlock` halves. -/
theorem evm_tstore_spec_within
    (n : Nat) (base envAddr sp : Word)
    (x14old x15old x16old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 c0 c1 c2 c3 : Word)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : Word) :
    cpsTripleWithin 35 base (base + 140) (evm_tstore_code .x20 base)
      (((((.x20) ↦ᵣ envAddr) **
        ((.x12) ↦ᵣ sp) **
        ((.x14) ↦ᵣ x14old) **
        ((.x15) ↦ᵣ x15old) **
        ((.x16) ↦ᵣ x16old) **
        ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n) **
        ((envAddr) ↦ₘ a0) **
        (((envAddr + 8)) ↦ₘ a1) **
        (((envAddr + 16)) ↦ₘ a2) **
        (((envAddr + 24)) ↦ₘ a3) **
        ((sp) ↦ₘ k0) **
        (((sp + 8)) ↦ₘ k1) **
        (((sp + 16)) ↦ₘ k2) **
        (((sp + 24)) ↦ₘ k3) **
        ((tstoreTgt n) ↦ₘ f0) **
        (((tstoreTgt n + 8)) ↦ₘ f1) **
        (((tstoreTgt n + 16)) ↦ₘ f2) **
        (((tstoreTgt n + 24)) ↦ₘ f3) **
        (((tstoreTgt n + 32)) ↦ₘ f4) **
        (((tstoreTgt n + 40)) ↦ₘ f5) **
        (((tstoreTgt n + 48)) ↦ₘ f6) **
        (((tstoreTgt n + 56)) ↦ₘ f7) **
        (((tstoreTgt n + 64)) ↦ₘ f8) **
        (((tstoreTgt n + 72)) ↦ₘ f9) **
        (((tstoreTgt n + 80)) ↦ₘ f10) **
        (((tstoreTgt n + 88)) ↦ₘ f11))) **
       (((((sp + 32)) ↦ₘ c0) **
        (((sp + 40)) ↦ₘ c1) **
        (((sp + 48)) ↦ₘ c2) **
        (((sp + 56)) ↦ₘ c3) **
        (((tstoreTgt n + 96)) ↦ₘ f12) **
        (((tstoreTgt n + 104)) ↦ₘ f13) **
        (((tstoreTgt n + 112)) ↦ₘ f14) **
        (((tstoreTgt n + 120)) ↦ₘ f15))))
      (((((.x20) ↦ᵣ envAddr) **
        ((.x12) ↦ᵣ (sp + 64)) **
        ((.x14) ↦ᵣ tstoreTgt n) **
        ((.x15) ↦ᵣ (BitVec.ofNat 64 n + 1)) **
        ((.x16) ↦ᵣ c3) **
        ((envAddr + 464) ↦ₘ (BitVec.ofNat 64 n + 1)) **
        (((sp + 32)) ↦ₘ c0) **
        (((sp + 40)) ↦ₘ c1) **
        (((sp + 48)) ↦ₘ c2) **
        (((sp + 56)) ↦ₘ c3) **
        (((tstoreTgt n + 96)) ↦ₘ c0) **
        (((tstoreTgt n + 104)) ↦ₘ c1) **
        (((tstoreTgt n + 112)) ↦ₘ c2) **
        (((tstoreTgt n + 120)) ↦ₘ c3))) **
       ((((envAddr) ↦ₘ a0) **
        (((envAddr + 8)) ↦ₘ a1) **
        (((envAddr + 16)) ↦ₘ a2) **
        (((envAddr + 24)) ↦ₘ a3) **
        ((sp) ↦ₘ k0) **
        (((sp + 8)) ↦ₘ k1) **
        (((sp + 16)) ↦ₘ k2) **
        (((sp + 24)) ↦ₘ k3) **
        ((tstoreTgt n) ↦ₘ a0) **
        (((tstoreTgt n + 8)) ↦ₘ a1) **
        (((tstoreTgt n + 16)) ↦ₘ a2) **
        (((tstoreTgt n + 24)) ↦ₘ a3) **
        (((tstoreTgt n + 32)) ↦ₘ k0) **
        (((tstoreTgt n + 40)) ↦ₘ k1) **
        (((tstoreTgt n + 48)) ↦ₘ k2) **
        (((tstoreTgt n + 56)) ↦ₘ k3) **
        (((tstoreTgt n + 64)) ↦ₘ (0 : Word)) **
        (((tstoreTgt n + 72)) ↦ₘ (0 : Word)) **
        (((tstoreTgt n + 80)) ↦ₘ (0 : Word)) **
        (((tstoreTgt n + 88)) ↦ₘ (0 : Word))))) := by
  have e0 : signExtend12 (BitVec.ofNat 12 0) = (0 : Word) := by decide
  have e1 : signExtend12 (BitVec.ofNat 12 1) = (1 : Word) := by decide
  have e8 : signExtend12 (BitVec.ofNat 12 8) = (8 : Word) := by decide
  have e16 : signExtend12 (BitVec.ofNat 12 16) = (16 : Word) := by decide
  have e24 : signExtend12 (BitVec.ofNat 12 24) = (24 : Word) := by decide
  have e32 : signExtend12 (BitVec.ofNat 12 32) = (32 : Word) := by decide
  have e40 : signExtend12 (BitVec.ofNat 12 40) = (40 : Word) := by decide
  have e48 : signExtend12 (BitVec.ofNat 12 48) = (48 : Word) := by decide
  have e56 : signExtend12 (BitVec.ofNat 12 56) = (56 : Word) := by decide
  have e64 : signExtend12 (BitVec.ofNat 12 64) = (64 : Word) := by decide
  have e72 : signExtend12 (BitVec.ofNat 12 72) = (72 : Word) := by decide
  have e80 : signExtend12 (BitVec.ofNat 12 80) = (80 : Word) := by decide
  have e88 : signExtend12 (BitVec.ofNat 12 88) = (88 : Word) := by decide
  have e96 : signExtend12 (BitVec.ofNat 12 96) = (96 : Word) := by decide
  have e104 : signExtend12 (BitVec.ofNat 12 104) = (104 : Word) := by decide
  have e112 : signExtend12 (BitVec.ofNat 12 112) = (112 : Word) := by decide
  have e120 : signExtend12 (BitVec.ofNat 12 120) = (120 : Word) := by decide
  have etl : signExtend12 (BitVec.ofNat 12 transientLogLengthOff) = (464 : Word) := by decide
  have block1_core :
      cpsTripleWithin 24 base (base + 96) (evm_tstore_p1_code base)
        (((.x20) ↦ᵣ envAddr) **
         ((.x12) ↦ᵣ sp) **
         ((.x14) ↦ᵣ x14old) **
         ((.x15) ↦ᵣ x15old) **
         ((.x16) ↦ᵣ x16old) **
         ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n) **
         ((envAddr) ↦ₘ a0) **
         (((envAddr + 8)) ↦ₘ a1) **
         (((envAddr + 16)) ↦ₘ a2) **
         (((envAddr + 24)) ↦ₘ a3) **
         ((sp) ↦ₘ k0) **
         (((sp + 8)) ↦ₘ k1) **
         (((sp + 16)) ↦ₘ k2) **
         (((sp + 24)) ↦ₘ k3) **
         ((tstoreTgt n) ↦ₘ f0) **
         (((tstoreTgt n + 8)) ↦ₘ f1) **
         (((tstoreTgt n + 16)) ↦ₘ f2) **
         (((tstoreTgt n + 24)) ↦ₘ f3) **
         (((tstoreTgt n + 32)) ↦ₘ f4) **
         (((tstoreTgt n + 40)) ↦ₘ f5) **
         (((tstoreTgt n + 48)) ↦ₘ f6) **
         (((tstoreTgt n + 56)) ↦ₘ f7) **
         (((tstoreTgt n + 64)) ↦ₘ f8) **
         (((tstoreTgt n + 72)) ↦ₘ f9) **
         (((tstoreTgt n + 80)) ↦ₘ f10) **
         (((tstoreTgt n + 88)) ↦ₘ f11))
        (((.x20) ↦ᵣ envAddr) **
         ((.x12) ↦ᵣ sp) **
         ((.x14) ↦ᵣ tstoreTgt n) **
         ((.x15) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x16) ↦ᵣ k3) **
         ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n) **
         ((envAddr) ↦ₘ a0) **
         (((envAddr + 8)) ↦ₘ a1) **
         (((envAddr + 16)) ↦ₘ a2) **
         (((envAddr + 24)) ↦ₘ a3) **
         ((sp) ↦ₘ k0) **
         (((sp + 8)) ↦ₘ k1) **
         (((sp + 16)) ↦ₘ k2) **
         (((sp + 24)) ↦ₘ k3) **
         ((tstoreTgt n) ↦ₘ a0) **
         (((tstoreTgt n + 8)) ↦ₘ a1) **
         (((tstoreTgt n + 16)) ↦ₘ a2) **
         (((tstoreTgt n + 24)) ↦ₘ a3) **
         (((tstoreTgt n + 32)) ↦ₘ k0) **
         (((tstoreTgt n + 40)) ↦ₘ k1) **
         (((tstoreTgt n + 48)) ↦ₘ k2) **
         (((tstoreTgt n + 56)) ↦ₘ k3) **
         (((tstoreTgt n + 64)) ↦ₘ (0 : Word)) **
         (((tstoreTgt n + 72)) ↦ₘ (0 : Word)) **
         (((tstoreTgt n + 80)) ↦ₘ (0 : Word)) **
         (((tstoreTgt n + 88)) ↦ₘ (0 : Word))) := by
    have hLD15 := ld_spec_gen_within .x15 .x20 envAddr x15old (BitVec.ofNat 64 n) (BitVec.ofNat 12 transientLogLengthOff) base (by decide)
    have hLI   := li_spec_gen_within .x14 x14old transientLogBaseImm (base + 4) (by decide)
    have hSLLI := slli_spec_gen_within .x16 .x15 x16old (BitVec.ofNat 64 n) (7 : BitVec 6) (base + 8) (by decide)
    have hADD  := add_spec_gen_rd_eq_rs1_within .x14 .x16 transientLogBaseImm ((BitVec.ofNat 64 n) <<< (7 : BitVec 6).toNat) (base + 12) (by decide)
    have hLDa0 := ld_spec_gen_within .x16 .x20 envAddr ((BitVec.ofNat 64 n) <<< (7 : BitVec 6).toNat) a0 (BitVec.ofNat 12 0) (base + 16) (by decide)
    have hSDa0 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) a0 f0 (BitVec.ofNat 12 0) (base + 20)
    have hLDa1 := ld_spec_gen_within .x16 .x20 envAddr a0 a1 (BitVec.ofNat 12 8) (base + 24) (by decide)
    have hSDa1 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) a1 f1 (BitVec.ofNat 12 8) (base + 28)
    have hLDa2 := ld_spec_gen_within .x16 .x20 envAddr a1 a2 (BitVec.ofNat 12 16) (base + 32) (by decide)
    have hSDa2 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) a2 f2 (BitVec.ofNat 12 16) (base + 36)
    have hLDa3 := ld_spec_gen_within .x16 .x20 envAddr a2 a3 (BitVec.ofNat 12 24) (base + 40) (by decide)
    have hSDa3 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) a3 f3 (BitVec.ofNat 12 24) (base + 44)
    have hLDk0 := ld_spec_gen_within .x16 .x12 sp a3 k0 (BitVec.ofNat 12 0) (base + 48) (by decide)
    have hSDk0 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) k0 f4 (BitVec.ofNat 12 32) (base + 52)
    have hLDk1 := ld_spec_gen_within .x16 .x12 sp k0 k1 (BitVec.ofNat 12 8) (base + 56) (by decide)
    have hSDk1 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) k1 f5 (BitVec.ofNat 12 40) (base + 60)
    have hLDk2 := ld_spec_gen_within .x16 .x12 sp k1 k2 (BitVec.ofNat 12 16) (base + 64) (by decide)
    have hSDk2 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) k2 f6 (BitVec.ofNat 12 48) (base + 68)
    have hLDk3 := ld_spec_gen_within .x16 .x12 sp k2 k3 (BitVec.ofNat 12 24) (base + 72) (by decide)
    have hSDk3 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) k3 f7 (BitVec.ofNat 12 56) (base + 76)
    have hz0 := sd_x0_spec_gen_within .x14 (tstoreTgt n) f8 (BitVec.ofNat 12 64) (base + 80)
    have hz1 := sd_x0_spec_gen_within .x14 (tstoreTgt n) f9 (BitVec.ofNat 12 72) (base + 84)
    have hz2 := sd_x0_spec_gen_within .x14 (tstoreTgt n) f10 (BitVec.ofNat 12 80) (base + 88)
    have hz3 := sd_x0_spec_gen_within .x14 (tstoreTgt n) f11 (BitVec.ofNat 12 88) (base + 92)
    simp only [etl, e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88] at hLD15 hLDa0 hSDa0 hLDa1 hSDa1 hLDa2 hSDa2 hLDa3 hSDa3 hLDk0 hSDk0 hLDk1 hSDk1 hLDk2 hSDk2 hLDk3 hSDk3 hz0 hz1 hz2 hz3
    rw [show transientLogBaseImm + ((BitVec.ofNat 64 n) <<< (7 : BitVec 6).toNat) = tstoreTgt n from rfl] at hADD
    runBlock hLD15 hLI hSLLI hADD hLDa0 hSDa0 hLDa1 hSDa1 hLDa2 hSDa2 hLDa3 hSDa3 hLDk0 hSDk0 hLDk1 hSDk1 hLDk2 hSDk2 hLDk3 hSDk3 hz0 hz1 hz2 hz3
  have block2_core_gen : ∀ b2 : Word,
      cpsTripleWithin 11 b2 (b2 + 44) (evm_tstore_p2_code b2)
        (((.x20) ↦ᵣ envAddr) **
         ((.x12) ↦ᵣ sp) **
         ((.x14) ↦ᵣ tstoreTgt n) **
         ((.x15) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x16) ↦ᵣ k3) **
         ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n) **
         (((sp + 32)) ↦ₘ c0) **
         (((sp + 40)) ↦ₘ c1) **
         (((sp + 48)) ↦ₘ c2) **
         (((sp + 56)) ↦ₘ c3) **
         (((tstoreTgt n + 96)) ↦ₘ f12) **
         (((tstoreTgt n + 104)) ↦ₘ f13) **
         (((tstoreTgt n + 112)) ↦ₘ f14) **
         (((tstoreTgt n + 120)) ↦ₘ f15))
        (((.x20) ↦ᵣ envAddr) **
         ((.x12) ↦ᵣ (sp + 64)) **
         ((.x14) ↦ᵣ tstoreTgt n) **
         ((.x15) ↦ᵣ (BitVec.ofNat 64 n + 1)) **
         ((.x16) ↦ᵣ c3) **
         ((envAddr + 464) ↦ₘ (BitVec.ofNat 64 n + 1)) **
         (((sp + 32)) ↦ₘ c0) **
         (((sp + 40)) ↦ₘ c1) **
         (((sp + 48)) ↦ₘ c2) **
         (((sp + 56)) ↦ₘ c3) **
         (((tstoreTgt n + 96)) ↦ₘ c0) **
         (((tstoreTgt n + 104)) ↦ₘ c1) **
         (((tstoreTgt n + 112)) ↦ₘ c2) **
         (((tstoreTgt n + 120)) ↦ₘ c3)) := by
    intro b2
    have hLDc0 := ld_spec_gen_within .x16 .x12 sp k3 c0 (BitVec.ofNat 12 32) b2 (by decide)
    have hSDc0 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) c0 f12 (BitVec.ofNat 12 96) (b2 + 4)
    have hLDc1 := ld_spec_gen_within .x16 .x12 sp c0 c1 (BitVec.ofNat 12 40) (b2 + 8) (by decide)
    have hSDc1 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) c1 f13 (BitVec.ofNat 12 104) (b2 + 12)
    have hLDc2 := ld_spec_gen_within .x16 .x12 sp c1 c2 (BitVec.ofNat 12 48) (b2 + 16) (by decide)
    have hSDc2 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) c2 f14 (BitVec.ofNat 12 112) (b2 + 20)
    have hLDc3 := ld_spec_gen_within .x16 .x12 sp c2 c3 (BitVec.ofNat 12 56) (b2 + 24) (by decide)
    have hSDc3 := sd_spec_gen_within .x14 .x16 (tstoreTgt n) c3 f15 (BitVec.ofNat 12 120) (b2 + 28)
    have hADDIlen := addi_spec_gen_same_within .x15 (BitVec.ofNat 64 n) (BitVec.ofNat 12 1) (b2 + 32) (by decide)
    have hSDlen := sd_spec_gen_within .x20 .x15 envAddr (BitVec.ofNat 64 n + signExtend12 (BitVec.ofNat 12 1)) (BitVec.ofNat 64 n) (BitVec.ofNat 12 transientLogLengthOff) (b2 + 36)
    have hADDIpop := addi_spec_gen_same_within .x12 sp (BitVec.ofNat 12 64) (b2 + 40) (by decide)
    simp only [etl, e1, e32, e40, e48, e56, e64, e96, e104, e112, e120] at hLDc0 hSDc0 hLDc1 hSDc1 hLDc2 hSDc2 hLDc3 hSDc3 hADDIlen hSDlen hADDIpop
    runBlock hLDc0 hSDc0 hLDc1 hSDc1 hLDc2 hSDc2 hLDc3 hSDc3 hADDIlen hSDlen hADDIpop
  have block2_core := block2_core_gen (base + 96)
  have block1 := cpsTripleWithin_frameR
    ((((sp + 32)) ↦ₘ c0) **
     (((sp + 40)) ↦ₘ c1) **
     (((sp + 48)) ↦ₘ c2) **
     (((sp + 56)) ↦ₘ c3) **
     (((tstoreTgt n + 96)) ↦ₘ f12) **
     (((tstoreTgt n + 104)) ↦ₘ f13) **
     (((tstoreTgt n + 112)) ↦ₘ f14) **
     (((tstoreTgt n + 120)) ↦ₘ f15)) (by pcFree) block1_core
  have block2 := cpsTripleWithin_frameR
    (((envAddr) ↦ₘ a0) **
     (((envAddr + 8)) ↦ₘ a1) **
     (((envAddr + 16)) ↦ₘ a2) **
     (((envAddr + 24)) ↦ₘ a3) **
     ((sp) ↦ₘ k0) **
     (((sp + 8)) ↦ₘ k1) **
     (((sp + 16)) ↦ₘ k2) **
     (((sp + 24)) ↦ₘ k3) **
     ((tstoreTgt n) ↦ₘ a0) **
     (((tstoreTgt n + 8)) ↦ₘ a1) **
     (((tstoreTgt n + 16)) ↦ₘ a2) **
     (((tstoreTgt n + 24)) ↦ₘ a3) **
     (((tstoreTgt n + 32)) ↦ₘ k0) **
     (((tstoreTgt n + 40)) ↦ₘ k1) **
     (((tstoreTgt n + 48)) ↦ₘ k2) **
     (((tstoreTgt n + 56)) ↦ₘ k3) **
     (((tstoreTgt n + 64)) ↦ₘ (0 : Word)) **
     (((tstoreTgt n + 72)) ↦ₘ (0 : Word)) **
     (((tstoreTgt n + 80)) ↦ₘ (0 : Word)) **
     (((tstoreTgt n + 88)) ↦ₘ (0 : Word))) (by pcFree) block2_core
  have hbound : 4 * (evm_tstore_p1 (.x20) ++ evm_tstore_p2 (.x20)).length < 2 ^ 64 := by decide
  have b1' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_append_left base (evm_tstore_p1 .x20) (evm_tstore_p2 .x20)) block1
  have b2' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_append_right base (evm_tstore_p1 .x20) (evm_tstore_p2 .x20) hbound) block2
  have composed := cpsTripleWithin_seq_perm_same_cr (fun h hq => by xperm_hyp hq) b1' b2'
  rw [show (base + 96) + (44 : Word) = base + 140 from by bv_omega] at composed
  exact composed

/-! ## Stack-level witness -/

/-- Top-level `TSTORE` witness (`.proven`). Given the transient log of length
    `n` (`transientLogLenIs`/`transientLogIs`), an uninitialised 128-byte slot at
    `TRANSIENT_STORAGE_LOG_BASE + 128*n`, the executing frame address, and the
    two stack words `slotKey :: current :: rest`, TSTORE extends the log to
    `entries ++ [⟨addrHash, slotKey, 0, current⟩]` (via `transientLogIs_snoc`),
    bumps the length to `n+1`, and pops the two consumed words. -/
theorem evm_tstore_stack_spec_within
    (n : Nat) (codeBase envAddr sp : Word)
    (x14old x15old x16old : Word)
    (addrHash slotKey current : EvmWord)
    (entries : List StorageLogEntry) (hlen : entries.length = n)
    (rest : List EvmWord) (freshEntry : StorageLogEntry) :
    cpsTripleWithin 35 codeBase (codeBase + 140) (evm_tstore_code .x20 codeBase)
      (((.x20) ↦ᵣ envAddr) ** ((.x12) ↦ᵣ sp) ** ((.x14) ↦ᵣ x14old) **
       ((.x15) ↦ᵣ x15old) ** ((.x16) ↦ᵣ x16old) **
       transientLogLenIs envAddr n **
       transientLogIs TRANSIENT_STORAGE_LOG_BASE entries **
       storageSlotIs (TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (n * 128)) freshEntry **
       evmWordIs envAddr addrHash **
       evmStackIs sp (slotKey :: current :: rest))
      (((.x20) ↦ᵣ envAddr) ** ((.x12) ↦ᵣ (sp + 64)) ** ((.x14) ↦ᵣ tstoreTgt n) **
       ((.x15) ↦ᵣ (BitVec.ofNat 64 n + 1)) ** ((.x16) ↦ᵣ current.getLimbN 3) **
       transientLogLenIs envAddr (n + 1) **
       transientLogIs TRANSIENT_STORAGE_LOG_BASE
         (entries ++ [(⟨addrHash, slotKey, 0, current⟩ : StorageLogEntry)]) **
       evmWordIs envAddr addrHash **
       evmWordIs sp slotKey ** evmWordIs (sp + 32) current ** evmStackIs (sp + 64) rest) := by
  have raw := evm_tstore_spec_within n codeBase envAddr sp x14old x15old x16old
    (addrHash.getLimbN 0) (addrHash.getLimbN 1) (addrHash.getLimbN 2) (addrHash.getLimbN 3) (slotKey.getLimbN 0) (slotKey.getLimbN 1) (slotKey.getLimbN 2) (slotKey.getLimbN 3) (current.getLimbN 0) (current.getLimbN 1) (current.getLimbN 2) (current.getLimbN 3) (freshEntry.addrHash.getLimbN 0) (freshEntry.addrHash.getLimbN 1) (freshEntry.addrHash.getLimbN 2) (freshEntry.addrHash.getLimbN 3) (freshEntry.slotKey.getLimbN 0) (freshEntry.slotKey.getLimbN 1) (freshEntry.slotKey.getLimbN 2) (freshEntry.slotKey.getLimbN 3) (freshEntry.original.getLimbN 0) (freshEntry.original.getLimbN 1) (freshEntry.original.getLimbN 2) (freshEntry.original.getLimbN 3) (freshEntry.current.getLimbN 0) (freshEntry.current.getLimbN 1) (freshEntry.current.getLimbN 2) (freshEntry.current.getLimbN 3)
  have framed := cpsTripleWithin_frameR
    (transientLogIs TRANSIENT_STORAGE_LOG_BASE entries ** evmStackIs (sp + 64) rest)
    (by pcFree) raw
  have hoff : (BitVec.ofNat 64 (EvmEnv.transientLogLengthOff)) = (464 : Word) := by decide
  have hsucc : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.add_mod]
  have s40 : (sp + 32) + 8 = sp + 40 := by bv_omega
  have s48 : (sp + 32) + 16 = sp + 48 := by bv_omega
  have s56 : (sp + 32) + 24 = sp + 56 := by bv_omega
  have s64 : sp + 32 + 32 = sp + 64 := by bv_omega
  refine cpsTripleWithin_weaken ?_ ?_ framed
  · intro h hp
    simp only [transientLogLenIs, hoff, evmWordIs, evmStackIs, storageSlotIs_eq_flat,
      tstoreTgt_eq, s40, s48, s56, s64] at hp ⊢
    xperm_hyp hp
  · intro h hq
    rw [transientLogIs_snoc, hlen]
    simp only [transientLogLenIs, hoff, hsucc, evmWordIs,
      storageSlotIs_eq_flat, EvmWord.getLimbN_zero, ← tstoreTgt_eq, s40, s48, s56] at hq ⊢
    xperm_hyp hq

end Transient
end EvmAsm.Evm64
