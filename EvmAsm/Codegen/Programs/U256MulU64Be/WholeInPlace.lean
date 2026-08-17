/-
  In-place entry contract for `u256_mul_u64_be`.

  The ordinary whole-routine contract keeps the source and result windows
  disjoint.  Amsterdam's arm 2 passes the same pointer in `a0` and `a2`.
  That is safe for this implementation: the outer loop reads the source
  through `x8` and writes only the separate accumulator; the reverse copy is
  the first phase that writes the result window.  This file records that
  stronger call-site contract without weakening the ordinary one.  The
  ordering is load-bearing in the statement: the outer-loop pre owns
  `bytesRegion aPtr aBytes`, its post carries that window through all 32
  source reads, and `copyInv` consumes the same window as the output region;
  the final `copyState (mulState aBytes b 32) aBytes 32` therefore relates the
  written bytes to the bytes read before the copy.  A re-emission that fuses
  the copy into the multiply loop, writes the output before the corresponding
  source read, or changes the traversal order would invalidate this theorem
  and must be checked before reusing the variant.
-/
import EvmAsm.Codegen.Programs.U256MulU64Be.WholeTop

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm Rv64.SAsm.Stmt

def mulInPlaceBodyPost
    (spNew vRa v8 v9 v18 v19 v20 aPtr b : Word)
    (accBytes outBytes : List (BitVec 8)) : Assertion :=
  mulTailExtra aPtr b aPtr [] **
    overflowTailPost spNew vRa v8 v9 v18 v19 v20 aPtr accBytes outBytes

theorem mulCore_inPlace_spec
    (aBytes : List (BitVec 8))
    (hlenA : aBytes.length = 32)
    (spNew vRa v8 v9 v18 v19 v20 aPtr b old5 : Word)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (aPtr + BitVec.ofNat 64 j) = true)
    (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 3810 (mulBase + 76) vRa mulCR
      (outerHeaderInitPre empAssertion aBytes spNew vRa v8 v9 v18 v19 v20
        aPtr b aPtr old5)
      (mulInPlaceBodyPost spNew vRa v8 v9 v18 v19 v20 aPtr b
        (mulState aBytes b 32)
        (copyState (mulState aBytes b 32) aBytes 32)) := by
  let F : Assertion := empAssertion
  have hF : F.pcFree := by pcf
  have hinit := outerHeaderInit_spec F hF aBytes
    spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr old5
  have hloop := outerLoop_spec F hF aBytes hlenA
    spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr halignA hoverA hvalidA
  have houter := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hinit hloop
  have hstate : (mulState aBytes b 32).length = 40 :=
    mulState_len aBytes b 32
  /- The source is no longer read after the outer loop.  Use `[]` for the
     copy helper's historical source parameter, leaving the one live region
     as the caller-owned output/source window. -/
  have hcopyInitRaw : cpsTripleWithin 3 (mulBase + 240) (mulBase + 252) mulCR
      ((((.x5 : Reg) ↦ᵣ (32 : Word)) **
        copyInitP F [] spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr
          (mulState aBytes b 32) aBytes) ** regOwn .x6 ** regOwn .x7)
      (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F [] spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr)
          (mulState aBytes b 32) aBytes aPtr 0) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2
      (nSteps := 3) (entry := mulBase + 240) (exit_ := mulBase + 252)
      (cr := mulCR) (r1 := .x6) (r2 := .x7)
      (P := ((.x5 : Reg) ↦ᵣ (32 : Word)) **
        copyInitP F [] spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr
          (mulState aBytes b 32) aBytes)
      (Q := ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F [] spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr)
          (mulState aBytes b 32) aBytes aPtr 0)
      ?_
    intro old6 old7
    have h := copyInit_exact_spec F hF [] (mulState aBytes b 32) aBytes
      spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr old6 old7
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [copyInitP] at hp ⊢
      xperm_hyp hp)
      (fun _ hq => hq) h
  have hcopyInit : cpsTripleWithin 3 (mulBase + 240) (mulBase + 252) mulCR
      (((.x5 : Reg) ↦ᵣ (32 : Word)) ** regOwn .x6 ** regOwn .x7 **
        copyInitP F [] spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr
          (mulState aBytes b 32) aBytes)
      (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInv (copyStable F [] spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr)
          (mulState aBytes b 32) aBytes aPtr 0) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [copyInitP] at hp ⊢
      xperm_hyp hp)
      (fun _ hq => hq) hcopyInitRaw
  have hcopyLoop := copyLoop_spec
    (copyStable F [] spNew vRa v8 v9 v18 v19 v20 aPtr b aPtr)
    (by dsimp [copyStable, F]; pcf)
    (mulState aBytes b 32) aBytes aPtr hstate hlenA halignA hoverA hvalidA
  have hcopy := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hcopyInit hcopyLoop
  let F0 : Assertion :=
    mulEpiloguePre spNew vRa v8 v9 v18 v19 v20
      vRa aPtr b aPtr accBase (32 : Word) **
      bytesRegion aPtr (copyState (mulState aBytes b 32) aBytes 32)
  let Fextra : Assertion := mulTailExtra aPtr b aPtr []
  let Finit : Assertion :=
    Fextra ** F0 ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 32)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
      bytesRegion accBase (mulState aBytes b 32)
  have hFextra : Fextra.pcFree := by dsimp [Fextra, mulTailExtra]; pcf
  have hFinit : Finit.pcFree := by dsimp [Finit]; pcf
  have hoverflow := overflowInit_spec Finit hFinit aPtr aPtr
  have hcopyOverflow := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Finit, Fextra, F0, mulTailExtra, mulEpiloguePre, copyInv,
        copyStable, F] at hp ⊢
      simp only [BitVec.add_zero, sepConj_emp_left'] at hp ⊢
      xperm_hyp hp)
    hcopy hoverflow
  have htail := overflowTail_epilogue_spec
    spNew vRa v8 v9 v18 v19 v20 vRa aPtr b aPtr accBase (32 : Word)
    aPtr (mulState aBytes b 32)
      (copyState (mulState aBytes b 32) aBytes 32) hstate hret
  have htailF := cpsTripleWithin_frameR Fextra hFextra htail
  have hbeforeTail := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [outerHeaderInv, outerLoopInv, copyInitP, copyStable, copyInv, F] at hp ⊢
      simp only [sepConj_emp_left'] at hp ⊢
      xperm_hyp hp) houter hcopyOverflow
  have hfinal := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [Finit, Fextra, F0, mulTailExtra, mulEpiloguePre,
        overflowZeroInv, overflowZeroCore] at hp ⊢
      simp only [sepConj_emp_left'] at hp ⊢
      xperm_hyp hp)
    hbeforeTail htailF
  simpa [mulInPlaceBodyPost, Fextra, mulTailExtra, F, sepConj_assoc',
    sepConj_comm', sepConj_left_comm'] using hfinal

def mulWholeInPlacePre
    (F : Assertion) (spOld vRa v8 v9 v18 v19 v20 aPtr b v13 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (aBytes accBytes : List (BitVec 8)) : Assertion :=
  ((.x2 : Reg) ↦ᵣ spOld) ** ((.x1 : Reg) ↦ᵣ vRa) **
    ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
    ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) **
    ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ aPtr) **
    ((.x13 : Reg) ↦ᵣ v13) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    frameSlots (spOld + Rv64.signExtend12 (-48 : BitVec 12))
      f0 f1 f2 f3 f4 f5 ** bytesRegion aPtr aBytes **
    bytesRegion accBase accBytes ** F

theorem mulWhole_inPlace_spec
    (F : Assertion) (hF : F.pcFree)
    (aBytes accBytes : List (BitVec 8))
    (hlenA : aBytes.length = 32) (hlenAcc : accBytes.length = 40)
    (spOld vRa v8 v9 v18 v19 v20 aPtr b v13 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (aPtr + BitVec.ofNat 64 j) = true)
    (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 3850 mulBase vRa mulCR
      (mulWholeInPlacePre F spOld vRa v8 v9 v18 v19 v20 aPtr b v13
        f0 f1 f2 f3 f4 f5 aBytes accBytes)
      (mulInPlaceBodyPost (spOld + Rv64.signExtend12 (-48 : BitVec 12))
        vRa v8 v9 v18 v19 v20 aPtr b
        (mulState aBytes b 32)
        (copyState (mulState aBytes b 32) aBytes 32) ** F) := by
  let spNew := spOld + Rv64.signExtend12 (-48 : BitVec 12)
  let extra : Assertion :=
    ((.x13 : Reg) ↦ᵣ v13) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion aPtr aBytes ** bytesRegion accBase accBytes ** F
  let extra0 : Assertion :=
    ((.x13 : Reg) ↦ᵣ v13) ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** bytesRegion aPtr aBytes ** F
  have hextra : extra.pcFree := by
    dsimp [extra]; pcf; exact hF
  have hpro := prologue_spec spOld vRa v8 v9 v18 v19 v20 aPtr b aPtr
    f0 f1 f2 f3 f4 f5
  have hproF := cpsTripleWithin_frameR extra hextra hpro
  let Pzero : Assertion :=
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
      ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x18 : Reg) ↦ᵣ aPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
      ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ aPtr) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes **
      frameSlots spNew vRa v8 v9 v18 v19 v20 ** extra0
  let Qzero : Assertion :=
    ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
      ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
      ((.x18 : Reg) ↦ᵣ aPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
      ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ aPtr) **
      ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 40)) **
      ((.x6 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
      frameSlots spNew vRa v8 v9 v18 v19 v20 ** extra0
  have hzeroAny : ∀ old5 old6, cpsTripleWithin 28 (mulBase + 48)
      (mulBase + 76) mulCR (Pzero ** ((.x5 : Reg) ↦ᵣ old5) **
        ((.x6 : Reg) ↦ᵣ old6)) Qzero := by
    intro old5 old6
    have hz := zeroLoop_spec spNew vRa v20 aPtr b aPtr v8 v9 v18 v19
      old5 old6 accBytes hlenAcc
    have hzF := cpsTripleWithin_frameR extra0 (by dsimp [extra0]; pcf; exact hF) hz
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Pzero, extra0] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by dsimp [Qzero, extra0] at hq ⊢; xperm_hyp hq) hzF
  have hzeroOwn := cpsTripleWithin_of_forall_regIs_to_regOwn2
    (nSteps := 28) (entry := mulBase + 48) (exit_ := mulBase + 76)
    (cr := mulCR) (r1 := .x5) (r2 := .x6) (P := Pzero) (Q := Qzero)
    hzeroAny
  have hproZero : cpsTripleWithin 12 mulBase (mulBase + 48) mulCR
      (mulWholeInPlacePre F spOld vRa v8 v9 v18 v19 v20 aPtr b v13
        f0 f1 f2 f3 f4 f5 aBytes accBytes)
      (Pzero ** regOwn .x5 ** regOwn .x6) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [mulWholeInPlacePre, extra, extra0, Pzero, spNew, frameSlots] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Pzero, extra, extra0, spNew, frameSlots] at hq ⊢
      xperm_hyp hq) hproF
  have hzeroCore : cpsTripleWithin 28 (mulBase + 48) (mulBase + 76) mulCR
      (Pzero ** regOwn .x5 ** regOwn .x6)
      (outerHeaderInitPre empAssertion aBytes spNew vRa v8 v9 v18 v19 v20
        aPtr b aPtr (accBase + BitVec.ofNat 64 40) ** F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) hzeroOwn
    simp only [Qzero, outerHeaderInitPre, outerLoopInv, spNew,
      sepConj_emp_left'] at hq ⊢
    have hq' := sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left
              (regIs_to_regOwn .x6 _)))))))))))) _ hq
    let Prefix : Assertion :=
      ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ vRa) **
        ((.x8 : Reg) ↦ᵣ aPtr) ** ((.x9 : Reg) ↦ᵣ b) **
        ((.x18 : Reg) ↦ᵣ aPtr) ** ((.x19 : Reg) ↦ᵣ accBase) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x10 : Reg) ↦ᵣ aPtr) **
        ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ aPtr) **
        ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 40)) ** regOwn .x6 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion accBase (List.replicate 40 (0 : BitVec 8)) **
        frameSlots spNew vRa v8 v9 v18 v19 v20
    let extraOwn : Assertion :=
      regOwn .x13 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** bytesRegion aPtr aBytes ** F
    have hqPrefix : (Prefix ** extra0) s := by
      dsimp [Prefix, spNew] at hq' ⊢; xperm_hyp hq'
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
  have hcore := mulCore_inPlace_spec aBytes hlenA spNew vRa v8 v9 v18 v19 v20
    aPtr b (accBase + BitVec.ofNat 64 40) halignA hoverA hvalidA hret
  have hcoreF := cpsTripleWithin_frameR F hF hcore
  have hbody := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hzeroCore hcoreF
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hproZero hbody

end EvmAsm.Codegen.U256MulU64Be
