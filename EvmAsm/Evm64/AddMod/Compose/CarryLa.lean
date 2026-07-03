/-
  EvmAsm.Evm64.AddMod.Compose.CarryLa

  Phase-3 M3d for total ADDMOD (issue #9704): the first carry-branch sub-chain.

  La runs from the carry-path entry (byte 160, taken when N ≠ 0 and the ADD
  carry bit is 1) through the first MOD call:

    save_operands (160,16) ;; minus_one_args (224,5) ;;
    [adapter call1 : JAL@244 → evm_mod_callable_v5 → ret@248] ;;
    call_mod_restore (248,1)

  ending at byte 252 with `EvmWord.mod (-1) N` in the dividend/divisor work
  window at F+32..56 (F = sp+32), N parked at S1, r parked at S2.

  Built via the FullPath pattern: each block is framed with the complement of
  the shared carry invariant, extended onto the common region
  `C = addmodCarryCode …`, then chained with `cpsTripleWithin_seq_perm_same_cr`.

  The register tail x1/x2/x6/x7/x9/x10/x11 is carried as GENERIC `regIs`
  values (threaded params), so at the call1 boundary they slot straight into
  the MOD-callable adapter's `divModStackDispatchPreNoX1` pre (which pins them
  at generic values) with no own→generic conversion.
-/

import EvmAsm.Evm64.AddMod.Compose.CarryPipeline
import Mathlib.Data.Fin.VecNotation

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

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

end EvmAsm.Evm64.AddMod.Compose
