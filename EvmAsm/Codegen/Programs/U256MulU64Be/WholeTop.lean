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

/-! ## Whole-routine entry

The component above starts after the prologue and accumulator zero-fill.  This
contract restores those two pieces without taking ownership of caller state
twice: `x13` is an exact incoming value because the K70/K73 call sites pass it
through, while the scratch registers are caller-owned. -/

def mulWholePre
    (F : Assertion) (spOld vRa v8 v9 v18 v19 v20 aPtr b outPtr v13 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (aBytes accBytes outBytes : List (BitVec 8)) : Assertion :=
  ((.x2 : Reg) ↦ᵣ spOld) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
    ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
    ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
    ((.x13 : Reg) ↦ᵣ v13) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    frameSlots (spOld + Rv64.signExtend12 (-48 : BitVec 12))
      f0 f1 f2 f3 f4 f5 ** bytesRegion aPtr aBytes **
    bytesRegion accBase accBytes ** bytesRegion outPtr outBytes ** F

theorem mulWhole_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes accBytes outBytes : List (BitVec 8))
    (hlenA : aBytes.length = 32) (hlenAcc : accBytes.length = 40)
    (hout : outBytes.length = 32)
    (spOld vRa v8 v9 v18 v19 v20 aPtr b outPtr v13 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (aPtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true)
    (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 3850 mulBase vRa mulCR
      (mulWholePre F spOld vRa v8 v9 v18 v19 v20 aPtr b outPtr v13
        f0 f1 f2 f3 f4 f5 aBytes accBytes outBytes)
      (mulWholeBodyPost (spOld + Rv64.signExtend12 (-48 : BitVec 12))
        vRa v8 v9 v18 v19 v20 aPtr b outPtr aBytes
        (mulState aBytes b 32)
        (copyState (mulState aBytes b 32) outBytes 32) ** F) := by
  let spNew := spOld + Rv64.signExtend12 (-48 : BitVec 12)
  let extra : Assertion :=
    ((.x13 : Reg) ↦ᵣ v13) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion aPtr aBytes ** bytesRegion accBase accBytes **
      bytesRegion outPtr outBytes ** F
  let extra0 : Assertion :=
    ((.x13 : Reg) ↦ᵣ v13) **
      regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion aPtr aBytes ** bytesRegion outPtr outBytes ** F
  have hextra : extra.pcFree := by
    dsimp [extra]
    pcf
    exact hF
  have hpro := prologue_spec spOld vRa v8 v9 v18 v19 v20 aPtr b outPtr
    f0 f1 f2 f3 f4 f5
  have hproF := cpsTripleWithin_frameR extra hextra hpro
  let Pzero : Assertion :=
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
      ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
      ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes **
      frameSlots spNew vRa v8 v9 v18 v19 v20 ** extra0
  let Qzero : Assertion :=
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
      ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
      ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 40)) **
      ((.x6 : Reg) ↦ᵣ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
      frameSlots spNew vRa v8 v9 v18 v19 v20 ** extra0
  have hzeroAny : ∀ old5 old6, cpsTripleWithin 28 (mulBase + 48)
      (mulBase + 76) mulCR (Pzero ** ((.x5 : Reg) ↦ᵣ old5) **
        ((.x6 : Reg) ↦ᵣ old6)) Qzero := by
    intro old5 old6
    have hz := zeroLoop_spec spNew vRa v20 aPtr b outPtr v8 v9 v18 v19
      old5 old6 accBytes hlenAcc
    have hzF := cpsTripleWithin_frameR extra0 (by
      dsimp [extra0]
      pcf
      exact hF) hz
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Pzero, extra0] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Qzero, extra0] at hq ⊢
      xperm_hyp hq) hzF
  have hzeroOwn := cpsTripleWithin_of_forall_regIs_to_regOwn2
    (nSteps := 28) (entry := mulBase + 48) (exit_ := mulBase + 76)
    (cr := mulCR) (r1 := .x5) (r2 := .x6) (P := Pzero) (Q := Qzero)
    hzeroAny
  have hproZero : cpsTripleWithin 12 mulBase (mulBase + 48) mulCR
      (mulWholePre F spOld vRa v8 v9 v18 v19 v20 aPtr b outPtr v13
        f0 f1 f2 f3 f4 f5 aBytes accBytes outBytes)
      (Pzero ** regOwn .x5 ** regOwn .x6) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [mulWholePre, extra, extra0, Pzero, spNew, frameSlots] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Pzero, extra, extra0, spNew, frameSlots] at hq ⊢
      xperm_hyp hq) hproF
  have hzeroCore : cpsTripleWithin 28 (mulBase + 48) (mulBase + 76) mulCR
      (Pzero ** regOwn .x5 ** regOwn .x6)
      (outerHeaderInitPre empAssertion aBytes spNew vRa v8 v9 v18 v19 v20
        aPtr b outPtr (accBase + BitVec.ofNat 64 40) ** bytesRegion outPtr outBytes ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) hzeroOwn
    simp only [Qzero, outerHeaderInitPre, outerLoopInv, spNew,
      sepConj_emp_left'] at hq ⊢
    have hq' := sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono_right
                        (sepConj_mono_right
                          (sepConj_mono_left (regIs_to_regOwn .x6 _)))))))))))) _ hq
    let Prefix : Assertion :=
      ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
        ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
        ((.x18 : Reg) ↦ᵣ outPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 40)) **
        regOwn .x6 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
        frameSlots spNew vRa v8 v9 v18 v19 v20
    let extraOwn : Assertion :=
      regOwn .x13 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** bytesRegion aPtr aBytes **
        bytesRegion outPtr outBytes ** F
    have hqPrefix : (Prefix ** extra0) s := by
      dsimp [Prefix, spNew] at hq' ⊢
      xperm_hyp hq'
    have hextraOwn : ∀ h, extra0 h → extraOwn h := by
      intro h hs
      dsimp [extra0, extraOwn] at hs ⊢
      exact sepConj_mono_left (regIs_to_regOwn .x13 v13) _ hs
    have hqOwn : (Prefix ** extraOwn) s :=
      sepConj_mono_right (P := Prefix) (Q := extra0) (Q' := extraOwn)
        hextraOwn s hqPrefix
    simp only [Prefix, extraOwn, spNew, accBase] at hqOwn ⊢
    change _ at hqOwn
    rw [show mulState aBytes b 0 = List.replicate 40 (0 : BitVec 8) from rfl]
    xperm_hyp hqOwn
  have hcore := mulCore_spec aBytes outBytes hlenA hout spNew vRa v8 v9 v18 v19 v20
    aPtr b outPtr (accBase + BitVec.ofNat 64 40)
    halignA hoverA hvalidA halignOut hoverOut hvalidOut hret
  have hcoreF := cpsTripleWithin_frameR F hF hcore
  have hbody := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hzeroCore hcoreF
  have hwhole := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hproZero hbody
  exact hwhole

end EvmAsm.Codegen.U256MulU64Be
