/-
  EvmAsm.Evm64.Shift.ComposeBase

  Shared helper lemmas and SHR sub-program bridges used across the
  shift-opcode Compose modules (SHR `Compose.lean`, SHL `ShlCompose.lean`,
  SAR `SarCompose.lean`).

  Contents:
  - Generic helpers: `regIs_to_regOwn`, `CodeReq_union_sub_both`,
    `singleton_sub_ofProg`.
  - SHR sub-program length lemmas (`shr_phase_*_len`, `shr_zero_path_len`).
  - SHR Phase A / Phase C union-chain ⊆ ofProg bridges. These are shared by
    SHR and SHL (both programs reuse `shr_phase_a` / `shr_phase_c`
    verbatim). SAR uses its own phase lists with different constants and
    keeps its bridges locally.
-/

import EvmAsm.Evm64.Shift.LimbSpec
import EvmAsm.Rv64.AddrNorm

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Generic helpers
-- ============================================================================

/-- Weaken concrete register to existential ownership. -/
theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- If each half of a `CodeReq` union is subsumed by `target`, so is the union. -/
theorem CodeReq_union_sub_both {cr1 cr2 target : CodeReq}
    (h1 : ∀ a i, cr1 a = some i → target a = some i)
    (h2 : ∀ a i, cr2 a = some i → target a = some i) :
    ∀ a i, (cr1.union cr2) a = some i → target a = some i := by
  intro a i h
  simp only [CodeReq.union] at h
  cases h1a : cr1 a with
  | none => simp [h1a] at h; exact h2 a i h
  | some v => simp [h1a] at h; subst h; exact h1 a v h1a

/-- A singleton at instruction `k` of a small program is subsumed by its `ofProg`. -/
theorem singleton_sub_ofProg (base addr : Word) (prog : List Instr) (instr : Instr) (k : Nat)
    (hk : k < prog.length)
    (hbound : 4 * prog.length < 2 ^ 64)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : prog.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → (CodeReq.ofProg base prog) a = some i :=
  CodeReq.singleton_mono (h_instr ▸ CodeReq.ofProg_lookup_addr base prog k addr hk hbound h_addr)

-- ============================================================================
-- SHR sub-program length lemmas (shared with SHL)
-- ============================================================================

theorem shr_phase_a_len : shr_phase_a.length = 9 := by decide
theorem shr_phase_b_len : shr_phase_b.length = 7 := by decide
theorem shr_phase_c_len : shr_phase_c.length = 5 := by decide
theorem shr_zero_path_len : shr_zero_path.length = 5 := by decide

-- ============================================================================
-- SHR Phase A / Phase C union-chain ⊆ ofProg bridges (shared with SHL)
-- ============================================================================

/-- Bridge: `shr_phase_a_code` (union chain, 9 instrs) ⊆ `ofProg shr_phase_a`. -/
theorem shr_phase_a_code_sub_ofProg {base : Word} :
    ∀ a i, shr_phase_a_code base a = some i →
      (CodeReq.ofProg base shr_phase_a) a = some i := by
  unfold shr_phase_a_code shr_ld_or_acc_code
  apply CodeReq_union_sub_both
  · exact singleton_sub_ofProg base base shr_phase_a (.LD .x5 .x12 8) 0
      (by decide) (by decide) (by bv_omega) (by decide)
  · apply CodeReq_union_sub_both
    · exact CodeReq.ofProg_mono_sub base (base + 4) shr_phase_a (shr_ld_or_acc_prog 16) 1
        (by bv_omega) (by decide) (by decide) (by decide)
    · apply CodeReq_union_sub_both
      · exact CodeReq.ofProg_mono_sub base (base + 12) shr_phase_a (shr_ld_or_acc_prog 24) 3
          (by bv_omega) (by decide) (by decide) (by decide)
      · apply CodeReq_union_sub_both
        · exact singleton_sub_ofProg base (base + 20) shr_phase_a (.BNE .x5 .x0 320) 5
            (by decide) (by decide) (by bv_omega) (by decide)
        · apply CodeReq_union_sub_both
          · exact singleton_sub_ofProg base (base + 24) shr_phase_a (.LD .x5 .x12 0) 6
              (by decide) (by decide) (by bv_omega) (by decide)
          · apply CodeReq_union_sub_both
            · exact singleton_sub_ofProg base (base + 28) shr_phase_a (.SLTIU .x10 .x5 256) 7
                (by decide) (by decide) (by bv_omega) (by decide)
            · exact singleton_sub_ofProg base (base + 32) shr_phase_a (.BEQ .x10 .x0 308) 8
                (by decide) (by decide) (by bv_omega) (by decide)

/-- Bridge: `shr_phase_c_code` (union chain, 5 instrs) ⊆ `ofProg shr_phase_c`. -/
theorem shr_phase_c_code_sub_ofProg {base : Word} :
    ∀ a i, shr_phase_c_code base a = some i →
      (CodeReq.ofProg base shr_phase_c) a = some i := by
  unfold shr_phase_c_code shr_cascade_step_code
  apply CodeReq_union_sub_both
  · exact singleton_sub_ofProg base base shr_phase_c (.BEQ .x5 .x0 176) 0
      (by decide) (by decide) (by bv_omega) (by decide)
  · apply CodeReq_union_sub_both
    · exact CodeReq.ofProg_mono_sub base (base + 4) shr_phase_c (shr_cascade_step_prog 1 92) 1
        (by bv_omega) (by decide) (by decide) (by decide)
    · exact CodeReq.ofProg_mono_sub base (base + 12) shr_phase_c (shr_cascade_step_prog 2 32) 3
        (by bv_omega) (by decide) (by decide) (by decide)

end EvmAsm.Evm64
