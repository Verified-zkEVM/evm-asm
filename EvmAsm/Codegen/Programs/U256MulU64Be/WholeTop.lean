import EvmAsm.Codegen.Programs.U256MulU64Be.WholeOverflow

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm Rv64.SAsm.Stmt

/-! Composition seam for the complete post-zero-fill body.  The copy phase is
    framed by the caller-owned output region; the overflow init then consumes
    only `x6` and `x10`, while `mulTailExtra` carries the unrelated caller
    resources through the hand-managed scan and epilogue. -/
theorem mulCore_spec
    (aBytes outBytes : List (BitVec 8))
    (hlenA : aBytes.length = 32) (hout : outBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old5 : Word)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (aPtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true)
    (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 3810 (mulBase + 76) vRa mulCR
      (outerHeaderInitPre empAssertion aBytes spNew vRa v8 v9 v18 v19 v20
        aPtr b outPtr old5 ** bytesRegion outPtr outBytes)
      (mulWholeBodyPost spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr aBytes
        (mulState aBytes b 32) (copyState (mulState aBytes b 32) outBytes 32)) := by
  let F : Assertion := empAssertion
  have hF : F.pcFree := by pcf
  have hinit := outerHeaderInit_spec F hF aBytes
    spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old5
  have hloop := outerLoop_spec F hF aBytes hlenA
    spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr halignA hoverA hvalidA
  have houter := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hinit hloop
  have houtPc : (bytesRegion outPtr outBytes).pcFree := by pcf
  have houterF := cpsTripleWithin_frameR (bytesRegion outPtr outBytes)
    houtPc houter
  have hstate : (mulState aBytes b 32).length = 40 :=
    mulState_len aBytes b 32
  have hcopyInitRaw : cpsTripleWithin 3 (mulBase + 240) (mulBase + 252) mulCR
      ((((.x5 : Reg) ↦ᵣ (32 : Word)) **
        copyInitP F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          (mulState aBytes b 32) outBytes) ** regOwn .x6 ** regOwn .x7)
      (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr)
          (mulState aBytes b 32) outBytes outPtr 0) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2
      (nSteps := 3) (entry := mulBase + 240) (exit_ := mulBase + 252)
      (cr := mulCR) (r1 := .x6) (r2 := .x7)
      (P := ((.x5 : Reg) ↦ᵣ (32 : Word)) **
        copyInitP F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          (mulState aBytes b 32) outBytes)
      (Q := ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr)
          (mulState aBytes b 32) outBytes outPtr 0)
      ?_
    intro old6 old7
    have h := copyInit_exact_spec F hF aBytes (mulState aBytes b 32) outBytes
      spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr old6 old7
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [copyInitP] at hp ⊢
      xperm_hyp hp)
      (fun _ hq => hq) h
  have hcopyInit : cpsTripleWithin 3 (mulBase + 240) (mulBase + 252) mulCR
      (((.x5 : Reg) ↦ᵣ (32 : Word)) ** regOwn .x6 ** regOwn .x7 **
        copyInitP F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr
          (mulState aBytes b 32) outBytes)
      (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr)
          (mulState aBytes b 32) outBytes outPtr 0) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [copyInitP] at hp ⊢
      xperm_hyp hp)
      (fun _ hq => hq) hcopyInitRaw
  have hcopyLoop := copyLoop_spec
    (copyStable F aBytes spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr)
    (by dsimp [copyStable, F]; pcf)
    (mulState aBytes b 32) outBytes outPtr hstate hout halignOut hoverOut hvalidOut
  have hcopy := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hcopyInit hcopyLoop
  let F0 : Assertion :=
    mulEpiloguePre spNew vRa v8 v9 v18 v19 v20
      vRa aPtr b outPtr accBase (32 : Word) **
      bytesRegion outPtr (copyState (mulState aBytes b 32) outBytes 32)
  let Fextra : Assertion := mulTailExtra aPtr b outPtr aBytes
  let Finit : Assertion :=
    Fextra ** F0 ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 32)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
      bytesRegion accBase (mulState aBytes b 32)
  have hFextra : Fextra.pcFree := by dsimp [Fextra, mulTailExtra]; pcf
  have hFinit : Finit.pcFree := by dsimp [Finit]; pcf
  have hoverflow := overflowInit_spec Finit hFinit outPtr aPtr
  have hcopyOverflow := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Finit, Fextra, F0, mulTailExtra, mulEpiloguePre, copyInv, copyStable, F] at hp ⊢
      simp only [BitVec.add_zero] at hp ⊢
      simp only [sepConj_emp_left'] at hp ⊢
      xperm_hyp hp)
    hcopy hoverflow
  have htail := overflowTail_epilogue_spec
    spNew vRa v8 v9 v18 v19 v20 vRa aPtr b outPtr accBase (32 : Word)
    outPtr (mulState aBytes b 32)
      (copyState (mulState aBytes b 32) outBytes 32) hstate hret
  have htailF := cpsTripleWithin_frameR Fextra hFextra htail
  have hbeforeTail := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [outerHeaderInv, outerLoopInv, copyInitP, copyStable, copyInv, F] at hp ⊢
      xperm_hyp hp) houterF hcopyOverflow
  have hfinal := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Finit, Fextra, F0, mulTailExtra, mulEpiloguePre,
        overflowZeroInv, overflowZeroCore] at hp ⊢
      xperm_hyp hp)
    hbeforeTail htailF
  simpa [mulWholeBodyPost, Fextra, mulTailExtra, F, sepConj_assoc',
    sepConj_comm', sepConj_left_comm'] using hfinal

end EvmAsm.Codegen.U256MulU64Be
