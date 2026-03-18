/-
  EvmAsm.Evm64.Not

  Full 256-bit EVM NOT spec composed from per-limb specs.
-/

import EvmAsm.Evm64.Bitwise

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Full NOT spec
-- ============================================================================

/-- CodeReq for the 256-bit EVM NOT operation.
    12 instructions = 48 bytes. 4 per-limb XORI(-1) blocks. -/
abbrev evm_not_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.XORI .x7 .x7 (-1)))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x7 0))
  (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x7 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 16) (.XORI .x7 .x7 (-1)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x7 8))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x7 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 28) (.XORI .x7 .x7 (-1)))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SD .x12 .x7 16))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x7 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 40) (.XORI .x7 .x7 (-1)))
   (CodeReq.singleton (base + 44) (.SD .x12 .x7 24))))))))))))

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM NOT: composes 4 per-limb NOT specs.
    12 instructions total. Unary: complements each limb in-place, sp unchanged. -/
theorem evm_not_spec (sp base : Addr)
    (a0 a1 a2 a3 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange sp 4) :
    let c := signExtend12 (-1 : BitVec 12)
    let code := evm_not_code base
    cpsTriple base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 ^^^ c)) **
       (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 8) ↦ₘ (a1 ^^^ c)) ** ((sp + 16) ↦ₘ (a2 ^^^ c)) ** ((sp + 24) ↦ₘ (a3 ^^^ c))) := by
  -- Compose 4 per-limb NOT specs via runBlock (manual mode with address normalization)
  have L0 := not_limb_spec 0 sp a0 v7 base (by validMem)
  have L1 := not_limb_spec 8 sp a1 (a0 ^^^ signExtend12 (-1 : BitVec 12)) (base + 12) (by validMem)
  have L2 := not_limb_spec 16 sp a2 (a1 ^^^ signExtend12 (-1 : BitVec 12)) (base + 24) (by validMem)
  have L3 := not_limb_spec 24 sp a3 (a2 ^^^ signExtend12 (-1 : BitVec 12)) (base + 36) (by validMem)
  runBlock L0 L1 L2 L3

-- ============================================================================
-- Stack-level NOT spec
-- ============================================================================

theorem signExtend12_neg1_eq_allOnes : signExtend12 (-1 : BitVec 12) = BitVec.allOnes 64 := by
  native_decide

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM NOT: complements an EvmWord in-place. -/
theorem evm_not_stack_spec (sp base : Addr)
    (a : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange sp 4) :
    let c := signExtend12 (-1 : BitVec 12)
    let code := evm_not_code base
    cpsTriple base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** evmWordIs sp a)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a.getLimb 3 ^^^ c)) ** evmWordIs sp (~~~a)) := by
  -- Helper: (~~~a).getLimb i = a.getLimb i ^^^ signExtend12 (-1)
  have not_limb_eq : ∀ i : Fin 4,
      (~~~a).getLimb i = a.getLimb i ^^^ signExtend12 (-1 : BitVec 12) := by
    intro i
    rw [EvmWord.getLimb_not, BitVec.not_def, BitVec.xor_comm, ← signExtend12_neg1_eq_allOnes]
  -- Apply evm_not_spec with individual limbs
  have h_main := evm_not_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    v7 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, not_limb_eq]
      xperm_hyp hq)
    h_main

end EvmAsm.Rv64
