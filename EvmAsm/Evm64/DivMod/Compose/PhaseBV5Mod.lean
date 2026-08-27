/-
  EvmAsm.Evm64.DivMod.Compose.PhaseBV5Mod

  v5 phase-B brick (21 steps, phaseBOff → clzOff, n=1 detection path) over
  `modCode_noNop_v5`.  Mirror of `evm_div_phaseB_n1_spec_within_v4_noNop`
  (PhaseABV4NoNop.lean): phase-B doesn't touch div128, so the same version-agnostic
  instruction bodies (init1/init2/tail + addi/bne singletons) extend to the v5 code
  via the v5 block subsumption `sharedNoNop_v5_b1_mod`.  Last leaf of the v5 n=1
  preloop.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.PhaseABV4NoNop
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divK_phaseB_init1_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseB_init1_code (base + phaseBOff)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b1_mod a i (CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBOff) divK_phaseB
    (divK_phaseB.take 7) 0 (by bv_addr) (by decide) (by decide) (by decide) a i h)

theorem divK_phaseB_init2_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseB_init2_code (base + phaseBInit2Off)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b1_mod a i (CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBInit2Off) divK_phaseB
    (divK_phaseB.drop 7 |>.take 2) 7 (by bv_addr) (by decide) (by decide) (by decide) a i h)

theorem divK_phaseB_tail_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseB_tail_code (base + phaseBTailOff)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b1_mod a i (CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBTailOff) divK_phaseB
    (divK_phaseB.drop 16) 16 (by bv_addr) (by decide) (by decide) (by decide) a i h)

theorem addi_x5_singleton_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBStep0Off) (.ADDI .x5 .x0 4)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 9 (by decide) (by decide)
  rw [show (base + phaseBOff : Word) + BitVec.ofNat 64 (4 * 9) = base + phaseBStep0Off from by bv_addr] at hlookup
  exact sharedNoNop_v5_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

theorem bne_x10_singleton_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBBneOff) (.BNE .x10 .x0 24)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 10 (by decide) (by decide)
  rw [show (base + phaseBOff : Word) + BitVec.ofNat 64 (4 * 10) = base + phaseBBneOff from by bv_addr] at hlookup
  exact sharedNoNop_v5_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

theorem addi_x5_3_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBStep1Off) (.ADDI .x5 .x0 3)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 11 (by decide) (by decide)
  rw [show (base + phaseBOff : Word) + BitVec.ofNat 64 (4 * 11) = base + phaseBStep1Off from by bv_addr] at hlookup
  exact sharedNoNop_v5_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

theorem bne_x7_16_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBBne2Off) (.BNE .x7 .x0 16)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 12 (by decide) (by decide)
  rw [show (base + phaseBOff : Word) + BitVec.ofNat 64 (4 * 12) = base + phaseBBne2Off from by bv_addr] at hlookup
  exact sharedNoNop_v5_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

theorem addi_x5_2_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBStep2Off) (.ADDI .x5 .x0 2)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 13 (by decide) (by decide)
  rw [show (base + phaseBOff : Word) + BitVec.ofNat 64 (4 * 13) = base + phaseBStep2Off from by bv_addr] at hlookup
  exact sharedNoNop_v5_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

theorem bne_x6_8_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBBne3Off) (.BNE .x6 .x0 8)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 14 (by decide) (by decide)
  rw [show (base + phaseBOff : Word) + BitVec.ofNat 64 (4 * 14) = base + phaseBBne3Off from by bv_addr] at hlookup
  exact sharedNoNop_v5_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

theorem addi_x5_1_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBStep3Off) (.ADDI .x5 .x0 1)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 15 (by decide) (by decide)
  rw [show (base + phaseBOff : Word) + BitVec.ofNat 64 (4 * 15) = base + phaseBStep3Off from by bv_addr] at hlookup
  exact sharedNoNop_v5_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

end EvmAsm.Evm64
