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
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

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
#print axioms frameSlotsSaved_imp_stackFree20

end EvmAsm.Codegen.TxEip7702TeerSpec
