/-
  Shared declaration home for the first two ADDMOD carry stages.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryPipeline
import EvmAsm.Evm64.AddMod.Compose.CarryBranch
import EvmAsm.Evm64.EvmWordArith.Arithmetic
import Mathlib.Data.Fin.VecNotation

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

namespace EvmAsm.Evm64.AddMod.Compose

/-- Registers untouched by both `save_operands` and `minus_one_args`, carried at
    generic `regIs` values so the MOD-call adapter can consume them directly.
    `x0` is kept separate (constant 0). -/
def addmodLaRegTail (x1v x2v x6v x7v x9v x10v x11v : Word) : Assertion :=
  (.x1 ↦ᵣ x1v) ** (.x2 ↦ᵣ x2v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) **
  (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v)

theorem addmodLaRegTail_pcFree (x1v x2v x6v x7v x9v x10v x11v : Word) :
    (addmodLaRegTail x1v x2v x6v x7v x9v x10v x11v).pcFree := by
  unfold addmodLaRegTail; pcFree

/-- The S3 park cells (F − 256 .. −232) plus the MOD callable scratch band and
    its `F − 160` cell — all untouched by `save_operands` / `minus_one_args`,
    carried as the value-agnostic tail so they slot into the adapter's pre. -/
def addmodLaScratchTail (F : Word)
    (m0 m1 m2 m3 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    Assertion :=
  ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ m0) **
  ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ m1) **
  ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ m2) **
  ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ m3) **
  divScratchValuesCallNoX1 F q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
  ((F + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)

theorem addmodLaScratchTail_pcFree (F : Word)
    (m0 m1 m2 m3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (addmodLaScratchTail F m0 m1 m2 m3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  unfold addmodLaScratchTail divScratchValuesCallNoX1
  pcFree

/-- Combined value-agnostic tail framed through both `save_operands` and
    `minus_one_args`: the constant `x0`, the generic register tail, and the
    scratch/S3 tail. -/
def addmodLaTail (F : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (m0 m1 m2 m3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** addmodLaRegTail x1v x2v x6v x7v x9v x10v x11v **
  addmodLaScratchTail F m0 m1 m2 m3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem

theorem addmodLaTail_pcFree (F : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (m0 m1 m2 m3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
      m0 m1 m2 m3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  unfold addmodLaTail addmodLaRegTail addmodLaScratchTail divScratchValuesCallNoX1
  pcFree

/-- Link 1 of La: `save_operands` framed with the carry tail, over the common
    region `C`. Parks `N` into S1 and `r` into S2. -/
theorem la_save_in_C
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 16 (bt + 160) ((bt + 160) + 64)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ r3) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem) := by
  refine carry_block_in_C
    (fun a i h => evm_addmod_total_program_code_carry_save_operands_sub a i
      (by rw [← evm_addmod_carry_save_operands_code_eq_ofProg]; exact h))
    (cpsTripleWithin_frameR _
      (addmodLaTail_pcFree F x1v x2v x6v x7v x9v x10v x11v
        sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (evm_addmod_carry_save_operands_spec_within F (bt + 160) x5Old
        n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3))

/-- Frame carried through `minus_one_args`: the register tail, the modulus `N`
    cells (untouched), the S1 (=N) / S2 (=r) park cells, and the scratch tail. -/
def addmodLaMinusOneFrame (F : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    Assertion :=
  addmodLaRegTail x1v x2v x6v x7v x9v x10v x11v **
  ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
  ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
  ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
  ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
  ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
  ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
  ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
  ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
  addmodLaScratchTail F sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem

theorem addmodLaMinusOneFrame_pcFree (F : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word) :
    (addmodLaMinusOneFrame F x1v x2v x6v x7v x9v x10v x11v n0 n1 n2 n3 r0 r1 r2 r3
      sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem).pcFree := by
  unfold addmodLaMinusOneFrame addmodLaRegTail addmodLaScratchTail divScratchValuesCallNoX1
  pcFree

/-- Link 2 of La: `minus_one_args` framed, over `C`. Writes the all-ones
    dividend into F+0..24. -/
theorem la_minus_one_in_C
    (bt F : Word) (x1v x2v x6v x7v x9v x10v x11v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 5 (bt + 224) ((bt + 224) + 20)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ r3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) **
       addmodLaMinusOneFrame F x1v x2v x6v x7v x9v x10v x11v n0 n1 n2 n3 r0 r1 r2 r3
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (((.x12 ↦ᵣ F) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12))) **
       addmodLaMinusOneFrame F x1v x2v x6v x7v x9v x10v x11v n0 n1 n2 n3 r0 r1 r2 r3
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem) := by
  refine carry_block_in_C
    (fun a i h => evm_addmod_total_program_code_carry_minus_one_args_sub a i
      (by rw [← evm_addmod_carry_minus_one_args_code_eq_ofProg]; exact h))
    (cpsTripleWithin_frameR _
      (addmodLaMinusOneFrame_pcFree F x1v x2v x6v x7v x9v x10v x11v n0 n1 n2 n3 r0 r1 r2 r3
        sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (evm_addmod_carry_minus_one_args_spec_within F (bt + 224) r3 r0 r1 r2 r3))

/-- La12: `save_operands ;; minus_one_args` over `C`, from carry entry (byte 160)
    to byte 244 (the first MOD-call JAL site). Parks N→S1, r→S2, writes the
    all-ones dividend into F+0..24; N still lives at F+32..56. -/
theorem la12_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 21 (bt + 160) ((bt + 224) + 20)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (((.x12 ↦ᵣ F) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12))) **
       addmodLaMinusOneFrame F x1v x2v x6v x7v x9v x10v x11v n0 n1 n2 n3 r0 r1 r2 r3
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem) := by
  have hs := la_save_in_C bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry
  rw [show (bt + 160) + 64 = bt + 224 from by bv_omega] at hs
  exact cpsTripleWithin_seq_perm_same_cr
    (by
      intro h hp
      simp only [addmodLaTail, addmodLaMinusOneFrame, addmodLaRegTail,
        addmodLaScratchTail] at hp ⊢
      xperm_hyp hp)
    hs
    (la_minus_one_in_C bt F x1v x2v x6v x7v x9v x10v x11v n0 n1 n2 n3 r0 r1 r2 r3
      sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry)

/-- The park cells S1 (=N), S2 (=r), S3 (=m-slot, still stale) — untouched by
    the first MOD call, framed around the adapter. -/
def addmodCall1Frame (F : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) : Assertion :=
  ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
  ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
  ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
  ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
  ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3)

theorem addmodCall1Frame_pcFree (F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) :
    (addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3).pcFree := by
  unfold addmodCall1Frame; pcFree

/-- Link 3 of La: the first MOD near-call (`JAL@244 → evm_mod_callable_v5 →
    ret@248`), discharged by the adapter, framed with the untouched park cells.
    Divisor `divr` is the modulus assembled from its limbs. -/
theorem la_call1_in_C
    (bt F calleeEntry : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word)
    (dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21)
    (hoffset : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin (1 + (unifiedDivBound + 1)) (bt + 244) ((bt + 244) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((divModStackDispatchPreNoX1 F (-1 : EvmWord)
          (EvmWord.fromLimbs ![n0, n1, n2, n3])
          x9v x1v x2v (signExtend12 (4095 : BitVec 12)) x6v x7v x10v x11v
          dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0) **
        ((F + signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      ((modStackDispatchPostCallableX9Owned F (-1 : EvmWord)
          (EvmWord.fromLimbs ![n0, n1, n2, n3]) ((bt + 244) + 4) **
        memOwn (F + signExtend12 (3936 : BitVec 12))) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  refine cpsTripleWithin_frameR _
    (addmodCall1Frame_pcFree F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
    (evm_addmod_v5_call_adapter_in_C (bt + 244) F calleeEntry mo1
      (-1 : EvmWord) (EvmWord.fromLimbs ![n0, n1, n2, n3])
      x9v x1v x2v (signExtend12 (4095 : BitVec 12)) x6v x7v x10v x11v
      dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
      hoffset callerAlign retAlign hdisj
      (fun a i h => evm_addmod_total_program_code_carry_call1_sub a i h)
      hdisjTC)

/-- La123: `save_operands ;; minus_one_args ;; [call1]` over `C`, from carry
    entry (byte 160) to the first MOD-call return (byte 248). Leaves
    `EvmWord.mod (-1) N` at F+32..56 with `x12 = F+32`, `x1 = bt+248`. -/
theorem la123_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hoffset : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin (21 + (1 + (unifiedDivBound + 1))) (bt + 160) ((bt + 244) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      ((modStackDispatchPostCallableX9Owned F (-1 : EvmWord)
          (EvmWord.fromLimbs ![n0, n1, n2, n3]) ((bt + 244) + 4) **
        memOwn (F + signExtend12 (3936 : BitVec 12))) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  have h12 := la12_spec_within bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem mo1 mo2 mo3 moNC calleeEntry
  rw [show (bt + 224) + 20 = bt + 244 from by bv_omega] at h12
  refine cpsTripleWithin_seq_perm_same_cr ?_ h12
    (la_call1_in_C bt F calleeEntry x1v x2v x6v x7v x9v x10v x11v
      n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3
      dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem
      mo1 mo2 mo3 moNC hoffset callerAlign retAlign hdisj hdisjTC)
  intro h hp
  have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
  have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
  have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
  have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
  simp only [addmodLaMinusOneFrame, addmodLaRegTail, addmodLaScratchTail,
    addmodCall1Frame, divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold,
    evmWordIs, EvmWord.getLimbN_fromLimbs_gen_0, EvmWord.getLimbN_fromLimbs_gen_1,
    EvmWord.getLimbN_fromLimbs_gen_2, EvmWord.getLimbN_fromLimbs_gen_3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    show (-1 : EvmWord).getLimbN 0 = signExtend12 (4095 : BitVec 12) from by decide,
    show (-1 : EvmWord).getLimbN 1 = signExtend12 (4095 : BitVec 12) from by decide,
    show (-1 : EvmWord).getLimbN 2 = signExtend12 (4095 : BitVec 12) from by decide,
    show (-1 : EvmWord).getLimbN 3 = signExtend12 (4095 : BitVec 12) from by decide,
    e0, e8, e16, e24, e32, e40, e48, e56,
    BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp ⊢
  xperm_hyp hp

-- ============================================================================
-- La link 4: call_mod_restore, and the full La sub-chain (byte 160 → 252)
-- ============================================================================

/-- The La post minus `x12`: the callable's x9-owned return frame (with `x12`
    peeled off), the scratch cell, and the S1/S2/S3 park cells. This is exactly
    `la123`'s post with the `.x12` atom removed, so it frames straight through
    the `call_mod_restore` ADDI (which touches only `x12`). -/
def addmodAfterCall1Rest (F raVal : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) : Assertion :=
  (regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
   evmWordIs F (-1 : EvmWord) **
   evmWordIs (F + 32) (EvmWord.mod (-1 : EvmWord) (EvmWord.fromLimbs ![n0, n1, n2, n3])) **
   divScratchOwnCallNoX1 F ** (.x1 ↦ᵣ raVal) ** regOwn .x9) **
  memOwn (F + signExtend12 (3936 : BitVec 12)) **
  addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3

theorem addmodAfterCall1Rest_pcFree (F raVal : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) :
    (addmodAfterCall1Rest F raVal n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3).pcFree := by
  unfold addmodAfterCall1Rest addmodCall1Frame divScratchOwnCallNoX1 divScratchOwn
  pcFree

/-- The full La post bundle: after the first MOD call and the frame-pointer
    restore, `x12 = F`, the first remainder `EvmWord.mod (-1) N` sits at F+32..56,
    with N/r/(stale m) parked at S1/S2/S3 and the callable frame shed. -/
def addmodCarryAfterCall1 (F raVal : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) : Assertion :=
  (.x12 ↦ᵣ F) **
  addmodAfterCall1Rest F raVal n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3

/-- Link 4 of La: `call_mod_restore` (`ADDI x12 x12 −32` at byte 248) framed with
    the callable return frame, over `C`. Restores `x12 = F+32 → F`. -/
theorem la_restore_in_C
    (bt F raVal : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 1 (bt + 248) ((bt + 248) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((.x12 ↦ᵣ (F + 32)) **
       addmodAfterCall1Rest F raVal n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodCarryAfterCall1 F raVal n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  have hsubRestore : ∀ a i,
      CodeReq.singleton (bt + 248) (.ADDI .x12 .x12 (4064 : BitVec 12)) a = some i →
      (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC) a = some i := by
    intro a i ha
    refine evm_addmod_total_program_code_carry_call1_sub a i ?_
    rw [← evm_addmod_carry_call_mod_code_eq_ofProg]
    show (CodeReq.union (CodeReq.singleton (bt + 244) (.JAL .x1 mo1))
        (CodeReq.singleton ((bt + 244) + 4) (.ADDI .x12 .x12 (4064 : BitVec 12)))) a = some i
    refine CodeReq.mono_union_right
      (CodeReq.Disjoint.singleton (by
        rw [show (bt + 244) + 4 = bt + 248 from by bv_omega]; bv_omega))
      (fun a' i' h => h) a i ?_
    rw [show (bt + 244) + 4 = bt + 248 from by bv_omega]; exact ha
  have hrestore := cpsTripleWithin_frameR
    (addmodAfterCall1Rest F raVal n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
    (addmodAfterCall1Rest_pcFree F raVal n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
    (evm_addmod_carry_call_mod_restore_spec_within (F + 32) (bt + 248))
  rw [show (F + 32) + signExtend12 (4064 : BitVec 12) = F from by
    rw [show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide]
    bv_omega] at hrestore
  exact carry_block_in_C hsubRestore hrestore

/-- **La complete**: `save_operands ;; minus_one_args ;; [call1] ;; restore`
    over `C`, carry entry (byte 160) → byte 252. Post `addmodCarryAfterCall1`:
    `x12 = F`, `EvmWord.mod (-1) N` at F+32..56, N@S1, r@S2. -/
theorem la_spec_within
    (bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3 : Word)
    (x1v x2v x6v x7v x9v x10v x11v : Word)
    (sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7 : Word)
    (shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hoffset : (bt + 244) + signExtend21 mo1 = calleeEntry)
    (callerAlign : ((bt + 244) + 4) &&& ~~~(1 : Word) = (bt + 244) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 244) (.JAL .x1 mo1)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin ((21 + (1 + (unifiedDivBound + 1))) + 1) (bt + 160) ((bt + 248) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ x5Old) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ sp0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ sp1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ sp2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ sp3) **
        ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ sq0) **
        ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ sq1) **
        ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ sq2) **
        ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ sq3)) **
       addmodLaTail F x1v x2v x6v x7v x9v x10v x11v
         sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem)
      (addmodCarryAfterCall1 F (bt + 248) n0 n1 n2 n3 r0 r1 r2 r3
         sm0 sm1 sm2 sm3) := by
  have h123 := la123_spec_within bt F x5Old n0 n1 n2 n3 r0 r1 r2 r3 sp0 sp1 sp2 sp3 sq0 sq1 sq2 sq3
    x1v x2v x6v x7v x9v x10v x11v
    sm0 sm1 sm2 sm3 dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 scratchMem
    mo1 mo2 mo3 moNC calleeEntry hoffset callerAlign retAlign hdisj hdisjTC
  rw [show (bt + 244) + 4 = bt + 248 from by bv_omega] at h123
  refine cpsTripleWithin_seq_perm_same_cr ?_ h123
    (la_restore_in_C bt F (bt + 248) n0 n1 n2 n3 r0 r1 r2 r3
      sm0 sm1 sm2 sm3 mo1 mo2 mo3 moNC calleeEntry)
  intro h hp
  simp only [modStackDispatchPostCallableX9Owned_unfold, modStackDispatchPostCallable_unfold,
    addmodAfterCall1Rest] at hp ⊢
  xperm_hyp hp

/-- The `plus_one_args` block's four-limb increment carry-chain, applied to the
    limbs of an `EvmWord` `w`, reassembles to `w + 1`. Matches the block's
    `SLTIU`/`SLTU` idiom against the general `add_carry_chain_correct` at
    `b = 1` (whose higher limbs are 0, collapsing the combined carries). -/
theorem addOne_via_incr_chain (w : EvmWord) :
    let m0 := w.getLimbN 0
    let m1 := w.getLimbN 1
    let m2 := w.getLimbN 2
    let m3 := w.getLimbN 3
    let q0 := m0 + (1 : Word)
    let k0 := if BitVec.ult q0 (1 : Word) then (1 : Word) else 0
    let q1 := m1 + k0
    let k1 := if BitVec.ult q1 k0 then (1 : Word) else 0
    let q2 := m2 + k1
    let k2 := if BitVec.ult q2 k1 then (1 : Word) else 0
    let q3 := m3 + k2
    EvmWord.fromLimbs ![q0, q1, q2, q3] = w + 1 := by
  intro m0 m1 m2 m3 q0 k0 q1 k1 q2 k2 q3
  have h := EvmWord.add_carry_chain_correct w (1 : EvmWord)
  have e0 : (1 : EvmWord).getLimb 0 = (1 : Word) := by decide
  have e1 : (1 : EvmWord).getLimb 1 = (0 : Word) := by decide
  have e2 : (1 : EvmWord).getLimb 2 = (0 : Word) := by decide
  have e3 : (1 : EvmWord).getLimb 3 = (0 : Word) := by decide
  simp only [e0, e1, e2, e3,
    show ∀ x : Word, x + (0 : Word) = x from fun x => by simp,
    show ∀ x : Word, BitVec.ult x (0 : Word) = false from fun x => by simp [BitVec.ult]] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hfun : (![q0, q1, q2, q3] : Fin 4 → Word) = (w + 1).getLimb := by
    funext i
    fin_cases i
    · simpa [q0, m0, EvmWord.getLimb_eq_getLimbN] using h0.symm
    · simpa [q1, k0, q0, m0, m1, EvmWord.getLimb_eq_getLimbN] using h1.symm
    · simpa [q2, k1, q1, k0, q0, m0, m1, m2, EvmWord.getLimb_eq_getLimbN] using h2.symm
    · simpa [q3, k2, q2, k1, q1, k0, q0, m0, m1, m2, m3, EvmWord.getLimb_eq_getLimbN]
        using h3.symm
  calc EvmWord.fromLimbs ![q0, q1, q2, q3]
      = EvmWord.fromLimbs (w + 1).getLimb := by rw [hfun]
    _ = w + 1 := EvmWord.fromLimbs_getLimb (w + 1)

-- ============================================================================
-- Own → generic-valued conversion for memory cells (Lb needs this: between the
-- MOD calls the div-scratch band is only OWNED, but the next call's adapter
-- pre wants it VALUED; the adapter is generic in every scratch value, so we
-- ∃-eliminate the owned cells and instantiate). Mirror of
-- `cpsTripleWithin_pre_regOwn` / `_under` for `memOwn`.
-- ============================================================================

/-- Choose the concrete value of a leading `memOwn a` in a `cpsTripleWithin`
    precondition. -/
theorem cpsTripleWithin_pre_memOwn
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {a : Word} {B Q : Assertion}
    (h : ∀ v, cpsTripleWithin nSteps entry exit_ cr ((a ↦ₘ v) ** B) Q) :
    cpsTripleWithin nSteps entry exit_ cr (memOwn a ** B) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hst, hcompat, hP⟩ := hPR
  have hP' : (memOwn a ** (B ** R)) hst := (sepConj_assoc hst).mp hP
  obtain ⟨v, hv⟩ := sepConj_choose_memOwn hP'
  have hv' : (((a ↦ₘ v) ** B) ** R) hst := (sepConj_assoc hst).mpr hv
  exact h v R hR s hcr ⟨hst, hcompat, hv'⟩ hpc

/-- Choose the concrete value of a `memOwn a` sitting in the SECOND position of a
    precondition (behind a leading `A`). Peels several `memOwn`s out of a chain
    one at a time via `sepConj_left_comm'`. -/
theorem cpsTripleWithin_pre_memOwn_under
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {A : Assertion} {a : Word} {B Q : Assertion}
    (h : ∀ v, cpsTripleWithin nSteps entry exit_ cr (A ** ((a ↦ₘ v) ** B)) Q) :
    cpsTripleWithin nSteps entry exit_ cr (A ** (memOwn a ** B)) Q := by
  rw [sepConj_left_comm']
  refine cpsTripleWithin_pre_memOwn (fun v => ?_)
  rw [sepConj_left_comm']
  exact h v

/-- Convert an OWNED div-scratch call band in a `cpsTripleWithin` precondition
    into the generic-VALUED form the MOD-call adapter needs. The 19 scratch
    cells are ∃-eliminated (the adapter is universally generic in every scratch
    value). Peel pattern: `pre_memOwn` for the leading cell, then
    `rw [← sepConj_assoc']; pre_memOwn_under` for each of the remaining 18
    (folding the growing valued prefix into one left-nested block so the next
    owned cell sits in the second slot `_under` can reach). -/
theorem cpsTripleWithin_pre_divScratchValued
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq} {F : Word} {B Q : Assertion}
    (h : ∀ q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratch_un0,
      cpsTripleWithin nSteps entry exit_ cr
        (divScratchValuesCallNoX1 F q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 ** B) Q) :
    cpsTripleWithin nSteps entry exit_ cr (divScratchOwnCallNoX1 F ** B) Q := by
  rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold]
  simp only [sepConj_assoc']
  refine cpsTripleWithin_pre_memOwn (fun q0 => ?_)
  refine cpsTripleWithin_pre_memOwn_under (fun q1 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun q2 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun q3 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u0 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u1 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u2 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u3 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u4 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u5 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u6 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun u7 => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun shiftMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun nMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun jMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun retMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun dMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun dloMem => ?_)
  rw [← sepConj_assoc']; refine cpsTripleWithin_pre_memOwn_under (fun scratch_un0 => ?_)
  have hh := h q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hh
  simp only [sepConj_assoc'] at hh ⊢
  exact hh

-- ============================================================================
-- Lb link 1: plus_one_args (byte 252 → 348)
-- ============================================================================

/-- Frame carried through `plus_one_args`: `x0`, the return address, the
    registers untouched by the block (`x2/x9/x10/x11`, still owned from the
    callable return), the S2 (=r) / S3 (=stale m) park cells, and the owned
    div-scratch band + its `F−160` cell. -/
def addmodLbPlusOneFrame (F raVal x2v x9v x10v x11v : Word)
    (r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
  (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
  ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ sm0) **
  ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ sm1) **
  ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ sm2) **
  ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ sm3) **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12))

theorem addmodLbPlusOneFrame_pcFree (F raVal x2v x9v x10v x11v
    r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) :
    (addmodLbPlusOneFrame F raVal x2v x9v x10v x11v
      r0 r1 r2 r3 sm0 sm1 sm2 sm3).pcFree := by
  unfold addmodLbPlusOneFrame divScratchOwnCallNoX1 divScratchOwn
  pcFree

/-- Link 1 of Lb: `plus_one_args` framed, over `C`. Consumes the (owned from
    the callable return) `x5/x6/x7` at generic values, reads the call-1
    remainder limbs `m0..m3` at F+32..56 and the all-ones `w0..w3` at F+0..24,
    reloads `N` from S1, and writes the `+1` increment `q0..q3` into F+0..24. -/
theorem lb_plus_one_in_C
    (bt F raVal x2v x9v x10v x11v : Word)
    (m0 m1 m2 m3 w0 w1 w2 w3 n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    let q0 := m0 + signExtend12 (1 : BitVec 12)
    let k0 := if BitVec.ult q0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
    let q1 := m1 + k0
    let k1 := if BitVec.ult q1 k0 then (1 : Word) else 0
    let q2 := m2 + k1
    let k2 := if BitVec.ult q2 k1 then (1 : Word) else 0
    let q3 := m3 + k2
    let k3 := if BitVec.ult q3 k2 then (1 : Word) else 0
    cpsTripleWithin 24 (bt + 252) ((bt + 252) + 96)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ m3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ w0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ w1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ w2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ w3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLbPlusOneFrame F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ n3) ** (.x6 ↦ᵣ q3) ** (.x7 ↦ᵣ k3) **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ q0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ q1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ q2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ q3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLbPlusOneFrame F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  intro q0 k0 q1 k1 q2 k2 q3 k3
  simp only [sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x5o => ?_)
  rw [← sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x6o => ?_)
  rw [← sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x7o => ?_)
  have hblk := carry_block_in_C
    (blockCode := evm_addmod_carry_plus_one_args_code (bt + 252))
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun a i h => evm_addmod_total_program_code_carry_plus_one_args_sub a i
      (by rw [← evm_addmod_carry_plus_one_args_code_eq_ofProg]; exact h))
    (cpsTripleWithin_frameR
      (addmodLbPlusOneFrame F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodLbPlusOneFrame_pcFree F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (evm_addmod_carry_plus_one_args_spec_within F (bt + 252) x5o x6o x7o
        m0 m1 m2 m3 w0 w1 w2 w3 n0 n1 n2 n3))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hblk
  · simp only [addmodLbPlusOneFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp
  · simp only [addmodLbPlusOneFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp

-- ============================================================================
-- Lb link 2: the second MOD near-call (byte 348 → 352)
-- ============================================================================

/-- Link 2 of Lb: the second MOD near-call (`JAL@348 → evm_mod_callable_v5 →
    ret@352`), discharged by the adapter. Dividend is the `+1` increment
    `fromLimbs ![q0,q1,q2,q3]`, divisor is the modulus `fromLimbs ![n0..n3]`.
    Between calls the div-scratch band arrives OWNED (from the callable return);
    it is `∃`-eliminated to the generic-valued form the adapter needs via
    `cpsTripleWithin_pre_divScratchValued`. The registers `x2/x9/x10/x11` are
    already carried as generic values (untouched by `plus_one_args`). -/
theorem lb_call2_in_C
    (bt F calleeEntry raVal x2v x9v x10v x11v x5v x6v x7v : Word)
    (q0 q1 q2 q3 n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21)
    (hoffset : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    cpsTripleWithin (1 + (unifiedDivBound + 1)) (bt + 348) ((bt + 348) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((divScratchOwnCallNoX1 F **
        memOwn (F + signExtend12 (3936 : BitVec 12)) **
        (.x12 ↦ᵣ F) ** (.x9 ↦ᵣ x9v) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ x2v) **
        (.x5 ↦ᵣ x5v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) **
        (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) ** (.x0 ↦ᵣ (0 : Word)) **
        evmWordIs F (EvmWord.fromLimbs ![q0, q1, q2, q3]) **
        evmWordIs (F + 32) (EvmWord.fromLimbs ![n0, n1, n2, n3])) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      ((modStackDispatchPostCallableX9Owned F (EvmWord.fromLimbs ![q0, q1, q2, q3])
          (EvmWord.fromLimbs ![n0, n1, n2, n3]) ((bt + 348) + 4) **
        memOwn (F + signExtend12 (3936 : BitVec 12))) **
       addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  refine cpsTripleWithin_frameR _
    (addmodCall1Frame_pcFree F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) ?_
  refine cpsTripleWithin_pre_divScratchValued (fun dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0 => ?_)
  refine cpsTripleWithin_pre_memOwn_under (fun scratchMem => ?_)
  have hadapter := evm_addmod_v5_call_adapter_in_C (bt + 348) F calleeEntry mo2
    (EvmWord.fromLimbs ![q0, q1, q2, q3]) (EvmWord.fromLimbs ![n0, n1, n2, n3])
    x9v raVal x2v x5v x6v x7v x10v x11v
    dq0 dq1 dq2 dq3 du0 du1 du2 du3 du4 du5 du6 du7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    hoffset callerAlign retAlign hdisj
    (fun a i h => evm_addmod_total_program_code_carry_call2_sub a i h)
    hdisjTC
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => hp) hadapter
  rw [divModStackDispatchPreNoX1_unfold]
  simp only [sepConj_assoc'] at hp ⊢
  xperm_hyp hp

-- ============================================================================
-- Lb link 3: call_mod_restore (byte 352 → 356), and the full Lb sub-chain
-- ============================================================================

/-- The call-2 post minus `x12`: the callable's x9-owned return frame (x12
    peeled), the scratch cell, and the S1/S2/S3 park cells. `d` is the
    preserved dividend `fromLimbs ![q..]`; `v` is the F+32 remainder value
    (kept generic so the pow256 rewrite happens once, in `lb_spec_within`). -/
def addmodAfterCall2Rest (F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) : Assertion :=
  (regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
   evmWordIs F d ** evmWordIs (F + 32) v **
   divScratchOwnCallNoX1 F ** (.x1 ↦ᵣ raVal) ** regOwn .x9) **
  memOwn (F + signExtend12 (3936 : BitVec 12)) **
  addmodCall1Frame F n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3

theorem addmodAfterCall2Rest_pcFree (F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) :
    (addmodAfterCall2Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3).pcFree := by
  unfold addmodAfterCall2Rest addmodCall1Frame divScratchOwnCallNoX1 divScratchOwn evmWordIs
  pcFree

/-- Full Lb post bundle: after the second MOD call and the frame-pointer restore,
    `x12 = F`, the `2^256 mod N` carry contribution `pow256ModN N` sits at
    F+32..56, with N/r/(stale m) parked at S1/S2/S3 and the callable frame shed. -/
def addmodCarryAfterCall2 (F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word) : Assertion :=
  (.x12 ↦ᵣ F) **
  addmodAfterCall2Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3

/-- Link 3 of Lb: `call_mod_restore` (`ADDI x12 x12 −32` at byte 352) framed with
    the callable return frame, over `C`. Restores `x12 = F+32 → F`. Mirror of
    `la_restore_in_C`. -/
theorem lb_restore_in_C
    (bt F raVal : Word) (d v : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 1 (bt + 352) ((bt + 352) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      ((.x12 ↦ᵣ (F + 32)) **
       addmodAfterCall2Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodCarryAfterCall2 F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  have hsubRestore : ∀ a i,
      CodeReq.singleton (bt + 352) (.ADDI .x12 .x12 (4064 : BitVec 12)) a = some i →
      (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC) a = some i := by
    intro a i ha
    refine evm_addmod_total_program_code_carry_call2_sub a i ?_
    rw [← evm_addmod_carry_call_mod_code_eq_ofProg]
    show (CodeReq.union (CodeReq.singleton (bt + 348) (.JAL .x1 mo2))
        (CodeReq.singleton ((bt + 348) + 4) (.ADDI .x12 .x12 (4064 : BitVec 12)))) a = some i
    refine CodeReq.mono_union_right
      (CodeReq.Disjoint.singleton (by
        rw [show (bt + 348) + 4 = bt + 352 from by bv_omega]; bv_omega))
      (fun a' i' h => h) a i ?_
    rw [show (bt + 348) + 4 = bt + 352 from by bv_omega]; exact ha
  have hrestore := cpsTripleWithin_frameR
    (addmodAfterCall2Rest F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
    (addmodAfterCall2Rest_pcFree F raVal d v n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3)
    (evm_addmod_carry_call_mod_restore_spec_within (F + 32) (bt + 352))
  rw [show (F + 32) + signExtend12 (4064 : BitVec 12) = F from by
    rw [show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide]
    bv_omega] at hrestore
  exact carry_block_in_C hsubRestore hrestore

/-- **Lb complete** (chain form): `plus_one_args ;; [call2] ;; restore` over `C`,
    byte 252 → 356. Kept with generic `m`/`w` (the call-1 remainder / all-ones
    dividend limbs) and the F+32 remainder value left as
    `EvmWord.mod (fromLimbs ![q..]) N`; the `pow256ModN` value-fold lands in the
    La;;Lb compose, where `m` becomes `getLimbN (EvmWord.mod (-1) N)`. -/
theorem lb_spec_within
    (bt F raVal x2v x9v x10v x11v : Word)
    (m0 m1 m2 m3 w0 w1 w2 w3 n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word)
    (hoffset : (bt + 348) + signExtend21 mo2 = calleeEntry)
    (callerAlign : ((bt + 348) + 4) &&& ~~~(1 : Word) = (bt + 348) + 4)
    (retAlign : ((calleeEntry + div128CallRetOff) + signExtend12 (0 : BitVec 12))
        &&& ~~~(1 : Word) = calleeEntry + div128CallRetOff)
    (hdisj : (CodeReq.singleton (bt + 348) (.JAL .x1 mo2)).Disjoint
      (evm_mod_callable_code_v5 calleeEntry))
    (hdisjTC : (evm_addmod_total_program_code bt mo1 mo2 mo3 moNC).Disjoint
      (evm_mod_callable_code_v5 calleeEntry)) :
    let q0 := m0 + signExtend12 (1 : BitVec 12)
    let k0 := if BitVec.ult q0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
    let q1 := m1 + k0
    let k1 := if BitVec.ult q1 k0 then (1 : Word) else 0
    let q2 := m2 + k1
    let k2 := if BitVec.ult q2 k1 then (1 : Word) else 0
    let q3 := m3 + k2
    cpsTripleWithin ((24 + (1 + (unifiedDivBound + 1))) + 1) (bt + 252) (((bt + 348) + 4) + 4)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        ((F + signExtend12 (32 : BitVec 12)) ↦ₘ m0) **
        ((F + signExtend12 (40 : BitVec 12)) ↦ₘ m1) **
        ((F + signExtend12 (48 : BitVec 12)) ↦ₘ m2) **
        ((F + signExtend12 (56 : BitVec 12)) ↦ₘ m3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ w0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ w1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ w2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ w3) **
        ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
        ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
        ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
        ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)) **
       addmodLbPlusOneFrame F raVal x2v x9v x10v x11v r0 r1 r2 r3 sm0 sm1 sm2 sm3)
      (addmodCarryAfterCall2 F ((bt + 348) + 4)
        (EvmWord.fromLimbs ![q0, q1, q2, q3])
        (EvmWord.mod (EvmWord.fromLimbs ![q0, q1, q2, q3])
          (EvmWord.fromLimbs ![n0, n1, n2, n3]))
        n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3) := by
  intro q0 k0 q1 k1 q2 k2 q3
  -- link 1: plus_one (252→348)
  have hp := lb_plus_one_in_C bt F raVal x2v x9v x10v x11v
    m0 m1 m2 m3 w0 w1 w2 w3 n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3
    mo1 mo2 mo3 moNC calleeEntry
  simp only at hp
  rw [show (bt + 252) + 96 = bt + 348 from by bv_omega] at hp
  -- link 2: call2 (348→352); plus_one leaves x5=n3, x6=q3, x7=k3
  have hc := lb_call2_in_C bt F calleeEntry raVal x2v x9v x10v x11v
    n3 q3 (if BitVec.ult q3 k2 then (1 : Word) else 0)
    q0 q1 q2 q3 n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3
    mo1 mo2 mo3 moNC hoffset callerAlign retAlign hdisj hdisjTC
  -- link 3: restore (352→356)
  have hr := lb_restore_in_C bt F ((bt + 348) + 4)
    (EvmWord.fromLimbs ![q0, q1, q2, q3])
    (EvmWord.mod (EvmWord.fromLimbs ![q0, q1, q2, q3]) (EvmWord.fromLimbs ![n0, n1, n2, n3]))
    n0 n1 n2 n3 r0 r1 r2 r3 sm0 sm1 sm2 sm3 mo1 mo2 mo3 moNC calleeEntry
  rw [show bt + 352 = (bt + 348) + 4 from by bv_omega] at hr
  have e0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have e8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have e16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have e24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  have e32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
  have e40 : signExtend12 (40 : BitVec 12) = 40#64 := by decide
  have e48 : signExtend12 (48 : BitVec 12) = 48#64 := by decide
  have e56 : signExtend12 (56 : BitVec 12) = 56#64 := by decide
  refine cpsTripleWithin_seq_perm_same_cr ?_
    (cpsTripleWithin_seq_perm_same_cr ?_ hp hc) hr
  · -- call2 post → restore pre
    intro h hp2
    simp only [addmodCall1Frame, addmodAfterCall2Rest,
      modStackDispatchPostCallableX9Owned_unfold, modStackDispatchPostCallable_unfold] at hp2 ⊢
    xperm_hyp hp2
  · -- plus_one post → call2 pre (fold q/n cells → fromLimbs, permute scratch to lead)
    intro h hp1
    simp only [addmodLbPlusOneFrame, addmodCall1Frame,
      evmWordIs, EvmWord.getLimbN_fromLimbs_gen_0, EvmWord.getLimbN_fromLimbs_gen_1,
      EvmWord.getLimbN_fromLimbs_gen_2, EvmWord.getLimbN_fromLimbs_gen_3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      e0, e8, e16, e24, e32, e40, e48, e56,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero] at hp1 ⊢
    xperm_hyp hp1

end EvmAsm.Evm64.AddMod.Compose
