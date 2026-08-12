/-
  EvmAsm.Codegen.Programs.WitnessCodesLookupEnabledSpec

  The enabled=1 prefix of `witness_codes_lookup_by_hash`.  The builder
  success post supplies the dispatch and telemetry cells used here, but its
  return register x10 is zero; loading the lookup arguments is therefore an
  explicit caller adapter, not a direct triple composition.
-/

import EvmAsm.Codegen.Programs.WitnessCodesIndexBuildSpec

namespace EvmAsm.Codegen.WitnessCodesLookupSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Evm64
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## The builder-success source -/

def wcbBuilderSuccessLookupCells : Assertion :=
  (CallsLoc ↦ₘ (0 : Word)) ** (WcidxEnLoc ↦ₘ (1 : Word)) **
  (WcbIndexedCallsLoc ↦ₘ (0 : Word))

/- The three atoms above are the cells inherited from `wcbBuilderPost 0`:
   `wcbEmptySuccessPost` supplies enabled=1 and `wcbBuilderBranchFrame 0`
   supplies the two zero counters.  They are kept as a named source fact so
   the lookup precondition cannot silently drift from the builder post. -/

theorem wcb_builder_post_zero_lookup_values (s : MachineState)
    (hs : (wcbBuilderPost 0).holdsFor s) :
    s.getMem CallsLoc = 0 ∧ s.getMem WcidxEnLoc = 1 ∧
      s.getMem WcbIndexedCallsLoc = 0 := by
  simp only [wcbBuilderPost, ↓reduceIte] at hs
  have hsucc := holdsFor_sepConj_elim_left hs
  have hframe := holdsFor_sepConj_elim_right hs
  have he1 := holdsFor_sepConj_elim_right hsucc
  have he2 := holdsFor_sepConj_elim_right he1
  have he3 := holdsFor_sepConj_elim_right he2
  have he4 := holdsFor_sepConj_elim_right he3
  have he5 := holdsFor_sepConj_elim_right he4
  have he6 := holdsFor_sepConj_elim_right he5
  have he7 := holdsFor_sepConj_elim_right he6
  have he8 := holdsFor_sepConj_elim_right he7
  have he9 := holdsFor_sepConj_elim_right he8
  have he10 := holdsFor_sepConj_elim_right he9
  have hf1 := holdsFor_sepConj_elim_right hframe
  have hf2 := holdsFor_sepConj_elim_right hf1
  have hf3 := holdsFor_sepConj_elim_right hf2
  have hf4 := holdsFor_sepConj_elim_right hf3
  have hcalls := holdsFor_sepConj_elim_left hf4
  have hindexed := holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hf4)
  exact ⟨by simpa [CallsLoc, WcbLookupCallsLoc] using holdsFor_memIs_getMem hcalls,
    by simpa [WcidxEnLoc, WcbEnabledLoc] using holdsFor_memIs_getMem he10,
    by simpa [WcbIndexedCallsLoc] using holdsFor_memIs_getMem hindexed⟩

/-! ## The caller-loaded argument adapter -/

def wclhEnabledArgs (secPtr len hashPtr outOffP outLenP : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ secPtr) **
  ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
  ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
  (WcidxEnLoc ↦ₘ (1 : Word))

/-! ## The argument moves, with arbitrary incoming callee-saved registers -/

private theorem wclhArgMoves_own_spec (secPtr len hashPtr outOffP outLenP : Word)
    (a8 a9 a18 a19 a20 : Word) :
    cpsTripleWithin 5 (wclhB + 36) (wclhB + 56) wclhCr
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
        ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x8 : Reg) ↦ᵣ a8) **
        ((.x9 : Reg) ↦ᵣ a9) ** ((.x18 : Reg) ↦ᵣ a18) **
        ((.x19 : Reg) ↦ᵣ a19) ** ((.x20 : Reg) ↦ᵣ a20))
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
        ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
        ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP)) := by
  exact wclhArgMoves_spec secPtr len hashPtr outOffP outLenP a8 a9 a18 a19 a20

/-! ## Enabled dispatch prefix -/

private theorem wclh_enabled_dispatch_spec (v5 v6 : Word) :
    cpsTripleWithin 4 (wclhB + 76) (wclhB + 92) wclhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        (WcidxEnLoc ↦ₘ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x6 : Reg) ↦ᵣ v6) **
        (WcidxEnLoc ↦ₘ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hla := la_materialize_within .x5 v5 (wclhB + 76) WcidxEnLoc
    (cr := wclhCr) (by decide) (by decide)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 76 : Word) + 8 = wclhB + 84 from by bv_omega] at hla
  have hld := liftCode (cr' := wclhCr)
    (ld_spec_gen_same_within .x5 WcidxEnLoc (1 : Word) (0 : BitVec 12)
      (wclhB + 84) (by decide)) (by unfold wclhCr; code_mem)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show WcidxEnLoc + (0 : Word) = WcidxEnLoc from by bv_omega,
    show (wclhB + 84 : Word) + 4 = wclhB + 88 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := wclhCr)
    (by unfold wclhCr; code_mem)
    (beq_spec_gen_within .x5 .x0
      (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220)
        (GuestAddrs.witness_codes_lookup_by_hash + 88))
      (1 : Word) (0 : Word) (wclhB + 88))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hP⟩ := hQt
    exact (by decide : (1 : Word) ≠ (0 : Word))
      ((sepConj_pure_right _).1 hP).2)
  rw [show (wclhB + 88 : Word) + 4 = wclhB + 92 from by bv_omega] at hnt
  have f1 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** (WcidxEnLoc ↦ₘ (1 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcf) hla
  have f2 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hld
  have f3 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** (WcidxEnLoc ↦ₘ (1 : Word))) (by pcf) hnt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 1 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

private theorem wclh_enabled_section_ptr_spec (secPtr v5 : Word) :
    cpsTripleWithin 4 (wclhB + 92) (wclhB + 108) wclhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        (WcbSectionPtrLoc ↦ₘ secPtr))
      (((.x5 : Reg) ↦ᵣ secPtr) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        (WcbSectionPtrLoc ↦ₘ secPtr)) := by
  have hla := la_materialize_within .x5 v5 (wclhB + 92) WcbSectionPtrLoc
    (cr := wclhCr) (by decide) (by decide)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 92 : Word) + 8 = wclhB + 100 from by bv_omega] at hla
  have hld := liftCode (cr' := wclhCr)
    (ld_spec_gen_same_within .x5 WcbSectionPtrLoc secPtr (0 : BitVec 12)
      (wclhB + 100) (by decide)) (by unfold wclhCr; code_mem)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show WcbSectionPtrLoc + (0 : Word) = WcbSectionPtrLoc from by bv_omega,
    show (wclhB + 100 : Word) + 4 = wclhB + 104 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := wclhCr)
    (by unfold wclhCr; code_mem)
    (bne_spec_gen_within .x8 .x5
      (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220)
        (GuestAddrs.witness_codes_lookup_by_hash + 104))
      secPtr secPtr (wclhB + 104))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hP⟩ := hQt
    exact ((sepConj_pure_right _).1 hP).2 rfl)
  rw [show (wclhB + 104 : Word) + 4 = wclhB + 108 from by bv_omega] at hnt
  have f1 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr) ** (WcbSectionPtrLoc ↦ₘ secPtr)) (by pcf) hla
  have f2 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ secPtr)) (by pcf) hld
  have f3 := cpsTripleWithin_frameR
    (WcbSectionPtrLoc ↦ₘ secPtr) (by pcf) hnt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 1 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

private theorem wclh_enabled_section_len_spec (len v5 : Word) :
    cpsTripleWithin 4 (wclhB + 108) (wclhB + 124) wclhCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x9 : Reg) ↦ᵣ len) **
        (WcbSectionLenLoc ↦ₘ len))
      (((.x5 : Reg) ↦ᵣ len) ** ((.x9 : Reg) ↦ᵣ len) **
        (WcbSectionLenLoc ↦ₘ len)) := by
  have hla := la_materialize_within .x5 v5 (wclhB + 108) WcbSectionLenLoc
    (cr := wclhCr) (by decide) (by decide)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
  rw [show (wclhB + 108 : Word) + 8 = wclhB + 116 from by bv_omega] at hla
  have hld := liftCode (cr' := wclhCr)
    (ld_spec_gen_same_within .x5 WcbSectionLenLoc len (0 : BitVec 12)
      (wclhB + 116) (by decide)) (by unfold wclhCr; code_mem)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show WcbSectionLenLoc + (0 : Word) = WcbSectionLenLoc from by bv_omega,
    show (wclhB + 116 : Word) + 4 = wclhB + 120 from by bv_omega] at hld
  have hbr := cpsBranchWithin_extend_code (cr' := wclhCr)
    (by unfold wclhCr; code_mem)
    (bne_spec_gen_within .x9 .x5
      (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220)
        (GuestAddrs.witness_codes_lookup_by_hash + 120))
      len len (wclhB + 120))
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hP⟩ := hQt
    exact ((sepConj_pure_right _).1 hP).2 rfl)
  rw [show (wclhB + 120 : Word) + 4 = wclhB + 124 from by bv_omega] at hnt
  have f1 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ len) ** (WcbSectionLenLoc ↦ₘ len)) (by pcf) hla
  have f2 := cpsTripleWithin_frameR (((.x9 : Reg) ↦ᵣ len)) (by pcf) hld
  have f3 := cpsTripleWithin_frameR
    (WcbSectionLenLoc ↦ₘ len) (by pcf) hnt
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 1 ≤ 4 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

private theorem wclh_enabled_result_moves_spec
    (secPtr hashPtr outOffP outLenP a10 a11 a12 a13 a14 : Word) :
    cpsTripleWithin 5 (wclhB + 124) (wclhB + 144) wclhCr
      (((.x10 : Reg) ↦ᵣ a10) ** ((.x11 : Reg) ↦ᵣ a11) **
        ((.x12 : Reg) ↦ᵣ a12) ** ((.x13 : Reg) ↦ᵣ a13) **
        ((.x14 : Reg) ↦ᵣ a14) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
        ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP))
      (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
        ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x8 : Reg) ↦ᵣ secPtr) **
        ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
        ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP)) := by
  have h10 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x10 .x8 secPtr a10 (wclhB + 124) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 124 : Word) + 4 = wclhB + 128 from by bv_omega] at h10
  have h11 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x11 .x9 (0 : Word) a11 (wclhB + 128) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 128 : Word) + 4 = wclhB + 132 from by bv_omega] at h11
  have h12 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x12 .x18 hashPtr a12 (wclhB + 132) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 132 : Word) + 4 = wclhB + 136 from by bv_omega] at h12
  have h13 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x13 .x19 outOffP a13 (wclhB + 136) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 136 : Word) + 4 = wclhB + 140 from by bv_omega] at h13
  have h14 := liftCode (cr' := wclhCr)
    (mv_spec_gen_within .x14 .x20 outLenP a14 (wclhB + 140) (by decide))
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 140 : Word) + 4 = wclhB + 144 from by bv_omega] at h14
  have f10 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ a11) ** ((.x12 : Reg) ↦ᵣ a12) **
      ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP)) (by pcf) h10
  have f11 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x12 : Reg) ↦ᵣ a12) **
      ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
      ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP)) (by pcf) h11
  have f12 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP)) (by pcf) h12
  have f13 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x14 : Reg) ↦ᵣ a14) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x20 : Reg) ↦ᵣ outLenP)) (by pcf) h13
  have f14 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ secPtr) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
      ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP)) (by pcf) h14
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f10 f11
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f12
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f13
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f14
  exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 + 1 + 1 ≤ 5 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c4)

/-! ## The enabled=1 prefix, ending at the indexed `JAL` -/

def wclhEnabledPrefixPre (v5 v6 a10 a11 a12 a13 a14 hashPtr outOffP outLenP : Word) :
    Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) **
  ((.x6 : Reg) ↦ᵣ v6) ** ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
  ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ a10) **
  ((.x11 : Reg) ↦ᵣ a11) ** ((.x12 : Reg) ↦ᵣ a12) **
  ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14) **
  ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
  ((.x20 : Reg) ↦ᵣ outLenP) ** wcbBuilderSuccessLookupCells **
  (WcbSectionPtrLoc ↦ₘ (0x40000030 : Word)) **
  (WcbSectionLenLoc ↦ₘ (0 : Word))

def wclhEnabledPrefixPost (hashPtr outOffP outLenP : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x5 : Reg) ↦ᵣ WcbIndexedCallsLoc) ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
  ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
  ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOffP) **
  ((.x14 : Reg) ↦ᵣ outLenP) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
  ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
  (CallsLoc ↦ₘ (1 : Word)) ** (WcidxEnLoc ↦ₘ (1 : Word)) **
  (WcbSectionPtrLoc ↦ₘ (0x40000030 : Word)) **
  (WcbSectionLenLoc ↦ₘ (0 : Word)) ** (WcbIndexedCallsLoc ↦ₘ (1 : Word))

theorem wclh_enabled_indexed_prefix_spec
    (v5 v6 a10 a11 a12 a13 a14 hashPtr outOffP outLenP : Word) :
    cpsTripleWithin 27 (wclhB + 56) (wclhB + 164) wclhCr
      (wclhEnabledPrefixPre v5 v6 a10 a11 a12 a13 a14 hashPtr outOffP outLenP)
      (wclhEnabledPrefixPost hashPtr outOffP outLenP) := by
  have h0 := wclhCounterBump_spec (wclhB + 56) CallsLoc v5 v6 0 (by decide)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 56 : Word) + 20 = wclhB + 76 from by bv_omega] at h0
  rw [show (0 : Word) + 1 = 1 from by decide] at h0
  have h1 := wclh_enabled_dispatch_spec CallsLoc 1
  have h2 := wclh_enabled_section_ptr_spec (0x40000030 : Word) 1
  have h3 := wclh_enabled_section_len_spec 0 (0x40000030 : Word)
  have h4 := wclh_enabled_result_moves_spec (0x40000030 : Word)
    hashPtr outOffP outLenP a10 a11 a12 a13 a14
  have h5 := wclhCounterBump_spec (wclhB + 144) WcbIndexedCallsLoc
    (0 : Word) 1 0 (by decide)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
    (by unfold wclhCr; code_mem) (by unfold wclhCr; code_mem)
    (by unfold wclhCr; code_mem)
  rw [show (wclhB + 144 : Word) + 20 = wclhB + 164 from by bv_omega] at h5
  rw [show (0 : Word) + 1 = 1 from by decide] at h5
  have f0 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ a10) **
      ((.x11 : Reg) ↦ᵣ a11) ** ((.x12 : Reg) ↦ᵣ a12) **
      ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (WcidxEnLoc ↦ₘ (1 : Word)) **
      (WcbSectionPtrLoc ↦ₘ (0x40000030 : Word)) **
      (WcbSectionLenLoc ↦ₘ (0 : Word)) ** (WcbIndexedCallsLoc ↦ₘ (0 : Word)))
    (by pcf) h0
  have f1 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ a10) **
      ((.x11 : Reg) ↦ᵣ a11) ** ((.x12 : Reg) ↦ᵣ a12) **
      ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (1 : Word)) **
      (WcbSectionPtrLoc ↦ₘ (0x40000030 : Word)) **
      (WcbSectionLenLoc ↦ₘ (0 : Word)) ** (WcbIndexedCallsLoc ↦ₘ (0 : Word)))
    (by pcf) h1
  have f2 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ a10) **
      ((.x11 : Reg) ↦ᵣ a11) ** ((.x12 : Reg) ↦ᵣ a12) **
      ((.x13 : Reg) ↦ᵣ a13) ** ((.x14 : Reg) ↦ᵣ a14) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (1 : Word)) **
      (WcidxEnLoc ↦ₘ (1 : Word)) ** (WcbSectionLenLoc ↦ₘ (0 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word))) (by pcf) h2
  have f3 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ (1 : Word)) **
      ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
      ((.x10 : Reg) ↦ᵣ a10) ** ((.x11 : Reg) ↦ᵣ a11) **
      ((.x12 : Reg) ↦ᵣ a12) ** ((.x13 : Reg) ↦ᵣ a13) **
      ((.x14 : Reg) ↦ᵣ a14) ** ((.x18 : Reg) ↦ᵣ hashPtr) **
      ((.x19 : Reg) ↦ᵣ outOffP) ** ((.x20 : Reg) ↦ᵣ outLenP) **
      (CallsLoc ↦ₘ (1 : Word)) ** (WcidxEnLoc ↦ₘ (1 : Word)) **
      (WcbSectionPtrLoc ↦ₘ (0x40000030 : Word)) **
      (WcbIndexedCallsLoc ↦ₘ (0 : Word))) (by pcf) h3
  have f4 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ (1 : Word)) ** (CallsLoc ↦ₘ (1 : Word)) **
      (WcidxEnLoc ↦ₘ (1 : Word)) **
      (WcbSectionPtrLoc ↦ₘ (0x40000030 : Word)) **
      (WcbSectionLenLoc ↦ₘ (0 : Word)) ** (WcbIndexedCallsLoc ↦ₘ (0 : Word)))
    (by pcf) h4
  have f5 := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ (0x40000030 : Word)) **
      ((.x9 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0x40000030 : Word)) **
      ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ hashPtr) **
      ((.x13 : Reg) ↦ᵣ outOffP) ** ((.x14 : Reg) ↦ᵣ outLenP) **
      ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOffP) **
      ((.x20 : Reg) ↦ᵣ outLenP) ** (CallsLoc ↦ₘ (1 : Word)) **
      (WcidxEnLoc ↦ₘ (1 : Word)) **
      (WcbSectionPtrLoc ↦ₘ (0x40000030 : Word)) **
      (WcbSectionLenLoc ↦ₘ (0 : Word))) (by pcf) h5
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f0 f1
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 f2
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c02 f3
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c03 f4
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c04 f5
  exact cpsTripleWithin_mono_nSteps (show 5 + 4 + 4 + 4 + 5 + 5 ≤ 27 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by
      simp only [wclhEnabledPrefixPre, wcbBuilderSuccessLookupCells] at hp ⊢
      xperm_chunked hp) (fun _ hq => by
      simp only [wclhEnabledPrefixPost] at hq ⊢
      xperm_chunked hq) c05)

end EvmAsm.Codegen.WitnessCodesLookupSpec
