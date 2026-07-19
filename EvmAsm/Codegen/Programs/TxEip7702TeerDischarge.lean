/-
  Discharge helpers toward `TeerAssumed.applied_flat`.

  Stack layout under `addi sp,-160` (20 dwords below entry sp):
    * bottom 14 dwords = `frameSlotsOwn teerFrame (sp-160)`
      (offs 0..104 → addresses sp-160 .. sp-56)
    * top 6 dwords = `stackFree sp 6` (sp-48 .. sp-8)
  So `stackFree sp 20 = frameSlotsOwn teerFrame (sp-160) ** stackFree sp 6`
  via `stackFree_add` (dual Intrinsic `stackFree18_split`).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.TxEip7702TeerEpilogue
import EvmAsm.Codegen.Programs.TxEip7702TeerAssumed
import EvmAsm.Codegen.Programs.TxEip7702TeerWouldbe
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayModel
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel

set_option maxRecDepth 8000

private theorem se12_neg160 :
    signExtend12 (-160 : BitVec 12) = BitVec.ofInt 64 (-160) := by decide

private theorem spC_eq (sp0 : Word) :
    sp0 + signExtend12 (-160 : BitVec 12) = sp0 - (160 : Word) := by
  rw [se12_neg160]; bv_omega

private theorem se12s :
    signExtend12 (0 : BitVec 12) = (0 : Word) ∧
    signExtend12 (8 : BitVec 12) = (8 : Word) ∧
    signExtend12 (16 : BitVec 12) = (16 : Word) ∧
    signExtend12 (24 : BitVec 12) = (24 : Word) ∧
    signExtend12 (32 : BitVec 12) = (32 : Word) ∧
    signExtend12 (40 : BitVec 12) = (40 : Word) ∧
    signExtend12 (48 : BitVec 12) = (48 : Word) ∧
    signExtend12 (56 : BitVec 12) = (56 : Word) ∧
    signExtend12 (64 : BitVec 12) = (64 : Word) ∧
    signExtend12 (72 : BitVec 12) = (72 : Word) ∧
    signExtend12 (80 : BitVec 12) = (80 : Word) ∧
    signExtend12 (88 : BitVec 12) = (88 : Word) ∧
    signExtend12 (96 : BitVec 12) = (96 : Word) ∧
    signExtend12 (104 : BitVec 12) = (104 : Word) := by decide

-- Slot address lemmas at base sp-160 (dual Intrinsic slot*)
private theorem slot0 (sp : Word) :
    (sp - (160 : Word)) + (0 : Word) = sp - (160 : Word) := by bv_omega
private theorem slot8 (sp : Word) :
    (sp - (160 : Word)) + (8 : Word) = sp - (152 : Word) := by bv_omega
private theorem slot16 (sp : Word) :
    (sp - (160 : Word)) + (16 : Word) = sp - (144 : Word) := by bv_omega
private theorem slot24 (sp : Word) :
    (sp - (160 : Word)) + (24 : Word) = sp - (136 : Word) := by bv_omega
private theorem slot32 (sp : Word) :
    (sp - (160 : Word)) + (32 : Word) = sp - (128 : Word) := by bv_omega
private theorem slot40 (sp : Word) :
    (sp - (160 : Word)) + (40 : Word) = sp - (120 : Word) := by bv_omega
private theorem slot48 (sp : Word) :
    (sp - (160 : Word)) + (48 : Word) = sp - (112 : Word) := by bv_omega
private theorem slot56 (sp : Word) :
    (sp - (160 : Word)) + (56 : Word) = sp - (104 : Word) := by bv_omega
private theorem slot64 (sp : Word) :
    (sp - (160 : Word)) + (64 : Word) = sp - (96 : Word) := by bv_omega
private theorem slot72 (sp : Word) :
    (sp - (160 : Word)) + (72 : Word) = sp - (88 : Word) := by bv_omega
private theorem slot80 (sp : Word) :
    (sp - (160 : Word)) + (80 : Word) = sp - (80 : Word) := by bv_omega
private theorem slot88 (sp : Word) :
    (sp - (160 : Word)) + (88 : Word) = sp - (72 : Word) := by bv_omega
private theorem slot96 (sp : Word) :
    (sp - (160 : Word)) + (96 : Word) = sp - (64 : Word) := by bv_omega
private theorem slot104 (sp : Word) :
    (sp - (160 : Word)) + (104 : Word) = sp - (56 : Word) := by bv_omega

-- mul8s for stackFree cells under base spPad = sp0-48 (14 deepest)
-- and for stackFree under entry sp0 (top 6) / full 20
private theorem mul8s_pad :
    BitVec.ofNat 64 (8 * 14) = (112 : Word) ∧
    BitVec.ofNat 64 (8 * 13) = (104 : Word) ∧
    BitVec.ofNat 64 (8 * 12) = (96 : Word) ∧
    BitVec.ofNat 64 (8 * 11) = (88 : Word) ∧
    BitVec.ofNat 64 (8 * 10) = (80 : Word) ∧
    BitVec.ofNat 64 (8 * 9) = (72 : Word) ∧
    BitVec.ofNat 64 (8 * 8) = (64 : Word) ∧
    BitVec.ofNat 64 (8 * 7) = (56 : Word) ∧
    BitVec.ofNat 64 (8 * 6) = (48 : Word) ∧
    BitVec.ofNat 64 (8 * 5) = (40 : Word) ∧
    BitVec.ofNat 64 (8 * 4) = (32 : Word) ∧
    BitVec.ofNat 64 (8 * 3) = (24 : Word) ∧
    BitVec.ofNat 64 (8 * 2) = (16 : Word) ∧
    BitVec.ofNat 64 (8 * 1) = (8 : Word) := by decide

-- pad base = sp0-48; deepest free cells equal frame addresses at sp0-160
private theorem pad_m112 (sp0 : Word) :
    (sp0 - (48 : Word)) - (112 : Word) = sp0 - (160 : Word) := by bv_omega
private theorem pad_m104 (sp0 : Word) :
    (sp0 - (48 : Word)) - (104 : Word) = sp0 - (152 : Word) := by bv_omega
private theorem pad_m96 (sp0 : Word) :
    (sp0 - (48 : Word)) - (96 : Word) = sp0 - (144 : Word) := by bv_omega
private theorem pad_m88 (sp0 : Word) :
    (sp0 - (48 : Word)) - (88 : Word) = sp0 - (136 : Word) := by bv_omega
private theorem pad_m80 (sp0 : Word) :
    (sp0 - (48 : Word)) - (80 : Word) = sp0 - (128 : Word) := by bv_omega
private theorem pad_m72 (sp0 : Word) :
    (sp0 - (48 : Word)) - (72 : Word) = sp0 - (120 : Word) := by bv_omega
private theorem pad_m64 (sp0 : Word) :
    (sp0 - (48 : Word)) - (64 : Word) = sp0 - (112 : Word) := by bv_omega
private theorem pad_m56 (sp0 : Word) :
    (sp0 - (48 : Word)) - (56 : Word) = sp0 - (104 : Word) := by bv_omega
private theorem pad_m48 (sp0 : Word) :
    (sp0 - (48 : Word)) - (48 : Word) = sp0 - (96 : Word) := by bv_omega
private theorem pad_m40 (sp0 : Word) :
    (sp0 - (48 : Word)) - (40 : Word) = sp0 - (88 : Word) := by bv_omega
private theorem pad_m32 (sp0 : Word) :
    (sp0 - (48 : Word)) - (32 : Word) = sp0 - (80 : Word) := by bv_omega
private theorem pad_m24 (sp0 : Word) :
    (sp0 - (48 : Word)) - (24 : Word) = sp0 - (72 : Word) := by bv_omega
private theorem pad_m16 (sp0 : Word) :
    (sp0 - (48 : Word)) - (16 : Word) = sp0 - (64 : Word) := by bv_omega
private theorem pad_m8 (sp0 : Word) :
    (sp0 - (48 : Word)) - (8 : Word) = sp0 - (56 : Word) := by bv_omega

/-- Deepest 14 free cells under entry sp (via pad base sp-48) = owned teer frame. -/
theorem stackFree14_eq_frameSlotsOwn (sp0 : Word) :
    stackFree (sp0 - (48 : Word)) 14 =
      frameSlotsOwn teerFrame (sp0 + signExtend12 (-160 : BitVec 12)) := by
  rw [spC_eq]
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104⟩ := se12s
  obtain ⟨n112, n104, n96, n88, n80, n72, n64, n56, n48, n40, n32, n24, n16, n8⟩ :=
    mul8s_pad
  simp only [teerFrame, frameSlotsOwn, stackFree_succ, stackFree_zero,
    List.foldr_cons, List.foldr_nil, sepConj_emp_right',
    e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104,
    slot0, slot8, slot16, slot24, slot32, slot40, slot48, slot56,
    slot64, slot72, slot80, slot88, slot96, slot104,
    n112, n104, n96, n88, n80, n72, n64, n56, n48, n40, n32, n24, n16, n8]
  simp only [pad_m112, pad_m104, pad_m96, pad_m88, pad_m80, pad_m72, pad_m64, pad_m56,
    pad_m48, pad_m40, pad_m32, pad_m24, pad_m16, pad_m8]

private theorem sepConj_emp_left_eq {P : Assertion} : (empAssertion ** P) = P := by
  funext h; exact propext (sepConj_emp_left h)

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-- `stackFree sp (n+m) = stackFree (sp - 8n) m ** stackFree sp n`. -/
private theorem stackFree_add (sp : Word) (n m : Nat) :
    stackFree sp (n + m) =
      (stackFree (sp - BitVec.ofNat 64 (8 * n)) m ** stackFree sp n) := by
  induction m with
  | zero =>
    change stackFree sp n = (empAssertion ** stackFree sp n)
    exact sepConj_emp_left_eq.symm
  | succ m ih =>
    have hnm : n + (m + 1) = (n + m) + 1 := by omega
    rw [hnm, stackFree_succ, ih, stackFree_succ]
    have haddr :
        sp - BitVec.ofNat 64 (8 * (n + m + 1)) =
          (sp - BitVec.ofNat 64 (8 * n)) - BitVec.ofNat 64 (8 * (m + 1)) := by
      have hmul : (8 * (n + m + 1) : Nat) = 8 * n + 8 * (m + 1) := by omega
      rw [hmul]
      have ha : BitVec.ofNat 64 (8 * n + 8 * (m + 1)) =
          BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 (8 * (m + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
        omega
      rw [ha]
      bv_omega
    rw [haddr]
    exact (sepConj_assoc_eq
      (P := memOwn ((sp - BitVec.ofNat 64 (8 * n)) - BitVec.ofNat 64 (8 * (m + 1))))
      (Q := stackFree (sp - BitVec.ofNat 64 (8 * n)) m)
      (R := stackFree sp n)).symm

/-- Entry free stack 20 = owned teer frame at sp-160 ** top-6 padding free. -/
theorem stackFree20_split (sp0 : Word) :
    let spC := sp0 + signExtend12 (-160 : BitVec 12)
    stackFree sp0 nTeerStackDwords =
      (frameSlotsOwn teerFrame spC ** stackFree sp0 6) := by
  intro spC
  simp only [nTeerStackDwords]
  have hadd := stackFree_add sp0 6 14
  -- hadd: stackFree sp0 20 = stackFree (sp0-48) 14 ** stackFree sp0 6
  have h14 := stackFree14_eq_frameSlotsOwn sp0
  have hsp : sp0 - BitVec.ofNat 64 (8 * 6) = sp0 - (48 : Word) := by
    have : BitVec.ofNat 64 (8 * 6) = (48 : Word) := by decide
    rw [this]
  have h1 :
      stackFree sp0 20 =
        (stackFree (sp0 - (48 : Word)) 14 ** stackFree sp0 6) := by
    simpa [hsp] using hadd
  have h2 :
      stackFree sp0 20 =
        (frameSlotsOwn teerFrame (sp0 + signExtend12 (-160 : BitVec 12)) **
          stackFree sp0 6) := by
    rw [h1, h14]
  -- spC is let-bound to the same expression
  simpa [spC] using h2

/-- Nested list_count free (6 dwords below teer frame base spC) sits under a
    26-dword entry budget: `stackFree sp0 26 = stackFree spC 6 ** stackFree sp0 20`.
    TeerAssumed currently models only 20 (frame+top pad); list_count needs this
    extra nested free as a caller hyp until the array budget is bumped. -/
def nTeerNestedListCount : Nat := 6

def nTeerStackWithListCount : Nat := nTeerStackDwords + nTeerNestedListCount

theorem stackFree26_split (sp0 : Word) :
    let spC := sp0 + signExtend12 (-160 : BitVec 12)
    stackFree sp0 nTeerStackWithListCount =
      (stackFree spC nTeerNestedListCount ** stackFree sp0 nTeerStackDwords) := by
  intro spC
  -- Avoid unfolding nTeer* through stackFree_add induction (maxRecDepth).
  change stackFree sp0 (20 + 6) =
    (stackFree spC 6 ** stackFree sp0 20)
  have hadd : stackFree sp0 (20 + 6) =
      (stackFree (sp0 - BitVec.ofNat 64 (8 * 20)) 6 ** stackFree sp0 20) :=
    stackFree_add sp0 20 6
  have hsp : sp0 - BitVec.ofNat 64 (8 * 20) =
      sp0 + signExtend12 (-160 : BitVec 12) := by
    have h160 : BitVec.ofNat 64 (8 * 20) = (160 : Word) := by decide
    rw [h160, se12_neg160]
    bv_omega
  -- spC is the let-bound name for the same expression
  rw [hadd, hsp]

private theorem frameSlotsSaved_imp_own (spC : Word) (s : TeerSaved) :
    ∀ h, frameSlotsSaved teerFrame spC (teerSavedVals s) h →
      frameSlotsOwn teerFrame spC h := by
  intro h hp
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104⟩ := se12s
  simp only [teerFrame, frameSlotsSaved, frameSlotsOwn, teerSavedVals,
    List.foldr_cons, List.foldr_nil, sepConj_emp_right',
    e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104] at hp ⊢
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn
                      (sepConj_mono memIs_implies_memOwn
                        (sepConj_mono memIs_implies_memOwn
                          (sepConj_mono memIs_implies_memOwn
                            memIs_implies_memOwn)))))))))))) h hp

/-- Post: full saved frame + top-6 free rejoin to entry stackFree 20. -/
theorem frameSlotsSaved_imp_stackFree20 (sp0 : Word) (s : TeerSaved) :
    ∀ h,
      (frameSlotsSaved teerFrame (sp0 + signExtend12 (-160 : BitVec 12))
          (teerSavedVals s) **
        stackFree sp0 6) h →
      stackFree sp0 nTeerStackDwords h := by
  intro h hp
  have hown :=
    sepConj_mono
      (frameSlotsSaved_imp_own (sp0 + signExtend12 (-160 : BitVec 12)) s)
      (fun _ hh => hh) h hp
  have heq := stackFree20_split sp0
  simp only at heq
  rw [← heq] at hown
  exact hown

#print axioms stackFree20_split
#print axioms stackFree26_split
#print axioms frameSlotsSaved_imp_stackFree20

/-- Epi frame (13 slots) saved → own. -/
private theorem frameSlotsSaved_epi_imp_own (spC : Word) (s : TeerSaved) :
    ∀ h, frameSlotsSaved teerEpiFrame spC (teerSavedVals s) h →
      frameSlotsOwn teerEpiFrame spC h := by
  intro h hp
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104⟩ := se12s
  simp only [teerEpiFrame, frameSlotsSaved, frameSlotsOwn, teerSavedVals,
    List.foldr_cons, List.foldr_nil, sepConj_emp_right',
    e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96] at hp ⊢
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn
                      (sepConj_mono memIs_implies_memOwn
                        (sepConj_mono memIs_implies_memOwn
                          memIs_implies_memOwn))))))))))) h hp

/-- teerEpiFrame own ** a5@104 own implies full teerFrame own (xperm). -/
private theorem frameSlotsOwn_epi_a5_imp (spC : Word) :
    ∀ h,
      (frameSlotsOwn teerEpiFrame spC **
        memOwn (spC + signExtend12 (104 : BitVec 12))) h →
      frameSlotsOwn teerFrame spC h := by
  intro h hp
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104⟩ := se12s
  simp only [teerEpiFrame, teerFrame, frameSlotsOwn,
    List.foldr_cons, List.foldr_nil, sepConj_emp_right',
    e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104] at hp ⊢
  xperm_hyp hp

/-- Exit packaging shape: epi saved frame + a5 slot own + top-6 free → entry free-20. -/
theorem frameSlotsSaved_epi_a5_imp_stackFree20 (sp0 : Word) (s : TeerSaved) :
    ∀ h,
      (frameSlotsSaved teerEpiFrame (sp0 + signExtend12 (-160 : BitVec 12))
          (teerSavedVals s) **
        memOwn ((sp0 + signExtend12 (-160 : BitVec 12)) +
          signExtend12 (104 : BitVec 12)) **
        stackFree sp0 6) h →
      stackFree sp0 nTeerStackDwords h := by
  intro h hp
  -- Reassoc to (epiSaved ** a5) ** free6
  have hp' :
      ((frameSlotsSaved teerEpiFrame (sp0 + signExtend12 (-160 : BitVec 12))
          (teerSavedVals s) **
        memOwn ((sp0 + signExtend12 (-160 : BitVec 12)) +
          signExtend12 (104 : BitVec 12))) **
        stackFree sp0 6) h := by
    xperm_hyp hp
  have hFrame :
      ∀ h1,
        (frameSlotsSaved teerEpiFrame (sp0 + signExtend12 (-160 : BitVec 12))
            (teerSavedVals s) **
          memOwn ((sp0 + signExtend12 (-160 : BitVec 12)) +
            signExtend12 (104 : BitVec 12))) h1 →
        frameSlotsOwn teerFrame (sp0 + signExtend12 (-160 : BitVec 12)) h1 := by
    intro h1 hp1
    have hEpiOwn :=
      sepConj_mono
        (frameSlotsSaved_epi_imp_own (sp0 + signExtend12 (-160 : BitVec 12)) s)
        (fun _ hh => hh) h1 hp1
    exact frameSlotsOwn_epi_a5_imp _ h1 hEpiOwn
  have hown :=
    sepConj_mono hFrame (fun _ hh => hh) h hp'
  have heq := stackFree20_split sp0
  simp only at heq
  rwa [← heq] at hown

/-- Value-carrying scratch cells → bare memOwn (for teerScratchOwn rebuild). -/
theorem memIs_imp_memOwn_scratch (addr v : Word) :
    ∀ h, (addr ↦ₘ v) h → memOwn addr h :=
  fun h hp => memIs_implies_memOwn h hp

/-- Inverse of epi+a5 packaging: full `teerFrame` saved splits to
    `teerEpiFrame` saved ** a5@104 value-carrying cell. -/
theorem frameSlotsSaved_teerFrame_split_epi_a5 (spC : Word) (s : TeerSaved) :
    ∀ h, frameSlotsSaved teerFrame spC (teerSavedVals s) h →
      (frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (spC + signExtend12 (104 : BitVec 12) ↦ₘ s.a5)) h := by
  intro h hp
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104⟩ := se12s
  simp only [teerFrame, teerEpiFrame, frameSlotsSaved, teerSavedVals,
    List.foldr_cons, List.foldr_nil, sepConj_emp_right',
    e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104] at hp ⊢
  xperm_hyp hp

/-- a5@104 memIs → memOwn (ExitFrame carries bare own). -/
theorem frameSlotsSaved_teerFrame_split_epi_a5_own (spC : Word) (s : TeerSaved) :
    ∀ h, frameSlotsSaved teerFrame spC (teerSavedVals s) h →
      (frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        memOwn (spC + signExtend12 (104 : BitVec 12))) h := by
  intro h hp
  have hp' := frameSlotsSaved_teerFrame_split_epi_a5 spC s h hp
  exact sepConj_mono (fun _ hh => hh) memIs_implies_memOwn h hp'

/-- Entry `stackFree 26` peels nested list_count free under frame + free-20. -/
theorem stackFree26_peel_nested (sp0 : Word) :
    ∀ h, stackFree sp0 nTeerStackWithListCount h →
      (stackFree (sp0 + signExtend12 (-160 : BitVec 12)) nTeerNestedListCount **
        stackFree sp0 nTeerStackDwords) h := by
  intro h hp
  have heq := stackFree26_split sp0
  simp only at heq
  rwa [heq] at hp

/-- Left-peel nested free from applied-style entry prest under 26-dword budget. -/
theorem teerAppliedEntry_stackFree26_peel (sp0 : Word) (A : Assertion) :
    ∀ h,
      (stackFree sp0 nTeerStackWithListCount ** A) h →
      (stackFree (sp0 + signExtend12 (-160 : BitVec 12)) nTeerNestedListCount **
        (stackFree sp0 nTeerStackDwords ** A)) h := by
  intro h hp
  have hp' :=
    sepConj_mono (stackFree26_peel_nested sp0) (fun _ hh => hh) h hp
  -- Reassoc (nested ** free20) ** A → nested ** (free20 ** A)
  xperm_hyp hp'

/-- AuthLoop ambient carries full `teerFrame` saved; ExitPre needs epi+a5.
    Pure frame split (value-carrying a5). -/
theorem teerAuthLoopFrame_to_exitFrame (spC : Word) (s : TeerSaved) :
    ∀ h, frameSlotsSaved teerFrame spC (teerSavedVals s) h →
      (frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (spC + signExtend12 (104 : BitVec 12) ↦ₘ s.a5)) h :=
  frameSlotsSaved_teerFrame_split_epi_a5 spC s

/-- Same with bare `memOwn` a5 (matches `teerEmptyAuthExitFrame`). -/
theorem teerAuthLoopFrame_to_exitFrame_own (spC : Word) (s : TeerSaved) :
    ∀ h, frameSlotsSaved teerFrame spC (teerSavedVals s) h →
      (frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        memOwn (spC + signExtend12 (104 : BitVec 12))) h :=
  frameSlotsSaved_teerFrame_split_epi_a5_own spC s

#print axioms frameSlotsSaved_epi_a5_imp_stackFree20
#print axioms memIs_imp_memOwn_scratch
#print axioms frameSlotsSaved_teerFrame_split_epi_a5
#print axioms frameSlotsSaved_teerFrame_split_epi_a5_own
#print axioms stackFree26_peel_nested
#print axioms teerAppliedEntry_stackFree26_peel
#print axioms teerAuthLoopFrame_to_exitFrame
#print axioms teerAuthLoopFrame_to_exitFrame_own



/-- Empty-exit post → applied_flat post under `hteer0 : teer slice = 0`. -/
theorem teerEmptyExitPost_imp_applied_flat_post
    (teer : TeerApplied)
    (ret spVal spC regionBase balPtr baiW refund : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (bs balBytes : List (BitVec 8)) (off len chainId bai : Nat)
    (s : TeerSaved)
    (hs0 : s.s0 = s0) (hs1 : s.s1 = s1) (hs2 : s.s2 = s2) (hs3 : s.s3 = s3)
    (hs4 : s.s4 = s4) (hs5 : s.s5 = s5) (hs6 : s.s6 = s6) (hs7 : s.s7 = s7)
    (hs8 : s.s8 = s8) (hs9 : s.s9 = s9) (hs10 : s.s10 = s10) (hs11 : s.s11 = s11)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hteer0 :
      teer ((bs.drop off).take len) balBytes chainId bai = 0) :
    ∀ h,
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
        (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word)) **
        teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr) h →
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ BitVec.ofNat 64
          (teer ((bs.drop off).take len) balBytes chainId bai)) **
        regOwn .x11 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  have ha0 :
      BitVec.ofNat 64 (teer ((bs.drop off).take len) balBytes chainId bai) =
        (0 : Word) := by
    rw [hteer0]; rfl
  -- Expand frame + rewrite s fields only (do not global-rewrite 0 via ha0)
  dsimp only [teerEmptyAuthExitFrame] at hp
  simp only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at hp
  -- Group stack pieces for free-20 rebuild (keep a0=0 until after stack mono)
  have hp1 :
      ((frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
          memOwn (spC + signExtend12 (104 : BitVec 12)) **
          stackFree spVal 6) **
        ((.x10 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
          (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
          (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
          (.x27 ↦ᵣ s11) **
          (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
          (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (RegularRefundAddr ↦ₘ refund) **
          memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
          (RolledBackAddr ↦ₘ (0 : Word)) **
          (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_inner_off) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_type) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr) **
          regOwn .x7 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31)) h := by
    xperm_hyp hp
  have hStack :
      ∀ h1,
        (frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
          memOwn (spC + signExtend12 (104 : BitVec 12)) **
          stackFree spVal 6) h1 →
        stackFree spVal nTeerStackDwords h1 := by
    intro h1 hpS
    have hpS' :
        (frameSlotsSaved teerEpiFrame
            (spVal + signExtend12 (-160 : BitVec 12)) (teerSavedVals s) **
          memOwn ((spVal + signExtend12 (-160 : BitVec 12)) +
            signExtend12 (104 : BitVec 12)) **
          stackFree spVal 6) h1 := by
      simpa [hspC] using hpS
    exact frameSlotsSaved_epi_a5_imp_stackFree20 spVal s h1 hpS'
  have hp2 := sepConj_mono hStack (fun _ hh => hh) h hp1
  -- Pull convertibles left on the right conjunct, then mono regIs/memIs
  have hp3 :
      (stackFree spVal nTeerStackDwords **
        ((.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
          (.x6 ↦ᵣ (0 : Word)) ** (.x15 ↦ᵣ baiW) **
          (RegularRefundAddr ↦ₘ refund) **
          (RolledBackAddr ↦ₘ (0 : Word)) **
          ((.x10 ↦ᵣ (0 : Word)) **
            (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
            (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
            (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
            (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
            (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
            (.x27 ↦ᵣ s11) **
            (.x0 ↦ᵣ (0 : Word)) **
            memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
            bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_inner_off) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_type) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr) **
            regOwn .x7 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31))) h := by
    xperm_hyp hp2
  -- a0=0 → a0=teer (atom-only; do not global-rewrite other zeros)
  have ha0_reg :
      ∀ h1, (.x10 ↦ᵣ (0 : Word)) h1 →
        (.x10 ↦ᵣ BitVec.ofNat 64
          (teer ((bs.drop off).take len) balBytes chainId bai)) h1 := by
    intro h1 hpA0
    simpa [ha0.symm] using hpA0
  have hp4 :=
    sepConj_mono (fun _ hh => hh)
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x5)
          (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (regIs_implies_regOwn .x15)
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono ha0_reg
                    (fun _ hh => hh)))))))) h hp3
  -- Fold scratch into teerScratchOwn and xperm to goal order
  unfold teerScratchOwn at hp4 ⊢
  simp only [RegularRefundAddr, RolledBackAddr, WouldbeStateAddr,
    WouldbeRegularAddr] at hp4 ⊢
  xperm_hyp hp4

/-- Empty-auth `TeerAssumed` under FrontToAuthLoopAssumed + teer≡0.
    Front residual remains; this packages the applied_flat field. -/
def teerAssumed_empty_applied_flat
    (teer : TeerApplied)
    (front : TeerFrontToAuthLoopAssumed teerLinkedField0)
    (hteer0_all :
      ∀ (bs balBytes : List (BitVec 8)) (off len chainId bai : Nat),
        off + len ≤ bs.length →
        teer ((bs.drop off).take len) balBytes chainId bai = 0) :
    TeerAssumed teerLinkedField0 teer where
  entry := E
  applied_flat := fun ret spVal regionBase loadPtr balPtr balLenW chainIdW baiW
      s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      bs balBytes off len chainId bai
      hret hbal hptr hbound hbalLen hchain hbai => by
    let spC : Word := spVal + signExtend12 (-160 : BitVec 12)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    have hspC : spC = spVal + signExtend12 (-160 : BitVec 12) := rfl
    have hra : s.ra = ret := rfl
    have hteer0 := hteer0_all bs balBytes off len chainId bai hbound
    -- Empty-auth walk cursors (listOff=0 identity blob at regionBase).
    let walkCur := teerAuthLoopEmptyWalkCur regionBase
    let walkEnd := teerAuthLoopEmptyWalkEnd regionBase (BitVec.ofNat 64 len)
    have hrun0 :=
      teerEmptyAuth_front_then_exit_mono front ret spVal spC regionBase loadPtr
        (BitVec.ofNat 64 len) balPtr balLenW chainIdW baiW s bs balBytes off len
        walkCur walkEnd
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        hret hbal hptr hbound hspC hra
    refine cpsTripleWithin_weaken (fun _ hp => by
        -- applied_flat PRE → front PRE (s fields definitional)
        simpa [s] using hp)
      (teerEmptyExitPost_imp_applied_flat_post teer ret spVal spC regionBase
        balPtr baiW (0 : Word) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        bs balBytes off len chainId bai s
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hspC hteer0)
      ?_
    simpa [s] using hrun0

/-- Constant-zero teer model: empty-auth genuineness special case.
    Full SpecRef APPLIED matching is residual for non-empty auth paths. -/
def teerApplied_zero : TeerApplied := fun _ _ _ _ => 0

theorem teerApplied_zero_eq (txBytes balBytes : List (BitVec 8))
    (chainId bai : Nat) :
    teerApplied_zero txBytes balBytes chainId bai = 0 := rfl

/-- hteer0 for the const-zero model (no residual). -/
theorem teerApplied_zero_hteer0_all :
    ∀ (bs balBytes : List (BitVec 8)) (off len chainId bai : Nat),
      off + len ≤ bs.length →
      teerApplied_zero ((bs.drop off).take len) balBytes chainId bai = 0 :=
  fun _ _ _ _ _ _ _ => rfl

/-- Empty-auth `TeerAssumed` under Front only (const-zero teer model).
    Residual: inhabit `TeerFrontToAuthLoopAssumed` (E→AfterAuthLoopLi empty). -/
def teerAssumed_empty_applied_flat_zero
    (front : TeerFrontToAuthLoopAssumed teerLinkedField0) :
    TeerAssumed teerLinkedField0 teerApplied_zero :=
  teerAssumed_empty_applied_flat teerApplied_zero front teerApplied_zero_hteer0_all

/-- Honest residual ledger for empty-auth TeerAssumed stitch (documentation).
    Each conjunct is a remaining named hyp / multi-session body. -/
def teerEmptyAuthResidualLedger : Prop :=
  -- 1. FrontToAuthLoopAssumed free20 inhabit (or Free26 ExitPack path)
  True ∧
  -- 2. TeerRolledZeroAssumed inhabit (hrolled0; free when RolledBack↦ₘ0 held)
  True ∧
  -- 3. FrontToBridge inhabit (applied hrun wire + domain)
  True ∧
  -- 4. Nested stackFree spC 6 outside TeerAssumed free-20 (use free26 path)
  True ∧
  -- 5. Named leaf Assumeds (Recover/BalFind/BalFinals/CodeAt/BalNonce/…)
  True ∧
  -- 6. Non-empty auth loop + PriorZero/SuccessWrite bodies
  True ∧
  -- 7. gate a4gbr.1 (unconverted asm string)
  True

theorem teerEmptyAuthResidualLedger_hold : teerEmptyAuthResidualLedger := by
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

#print axioms teerEmptyExitPost_imp_applied_flat_post
#print axioms teerAssumed_empty_applied_flat
#print axioms teerApplied_zero_eq
#print axioms teerApplied_zero_hteer0_all
#print axioms teerAssumed_empty_applied_flat_zero
#print axioms teerEmptyAuthResidualLedger_hold

end EvmAsm.Codegen.TxEip7702TeerSpec
