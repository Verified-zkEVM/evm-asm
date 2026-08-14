import EvmAsm.Codegen.Programs.RlpListCountItemsSAsm

/-!
  Flat caller contract for the strict `rlp_list_count_items` routine.

  The emitted K47 program is unchanged.  This file only releases its private
  48-byte ABI frame as six free stack dwords (five saved-register slots plus
  the shallow unused slot), so callers can compose it through `callWithin_spec`.
-/

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

private theorem savedSlotAddr0 (sp : Word) :
    sp + signExtend12 (-48 : BitVec 12) =
      sp - BitVec.ofNat 64 (8 * 6) := by
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
    show BitVec.ofNat 64 (8 * 6) = (48 : Word) from by decide]
  bv_omega

private theorem savedSlotAddr8 (sp : Word) :
    sp + signExtend12 (-48 : BitVec 12) + 8 =
      sp - BitVec.ofNat 64 (8 * 5) := by
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
    show BitVec.ofNat 64 (8 * 5) = (40 : Word) from by decide]
  bv_omega

private theorem savedSlotAddr16 (sp : Word) :
    sp + signExtend12 (-48 : BitVec 12) + 16 =
      sp - BitVec.ofNat 64 (8 * 4) := by
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
    show BitVec.ofNat 64 (8 * 4) = (32 : Word) from by decide]
  bv_omega

private theorem savedSlotAddr24 (sp : Word) :
    sp + signExtend12 (-48 : BitVec 12) + 24 =
      sp - BitVec.ofNat 64 (8 * 3) := by
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
    show BitVec.ofNat 64 (8 * 3) = (24 : Word) from by decide]
  bv_omega

private theorem savedSlotAddr32 (sp : Word) :
    sp + signExtend12 (-48 : BitVec 12) + 32 =
      sp - BitVec.ofNat 64 (8 * 2) := by
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide,
    show BitVec.ofNat 64 (8 * 2) = (16 : Word) from by decide]
  bv_omega

def flatResult
    (sp0 listBase outPtr : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status result v11 v12 : Word,
    ((((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals saved) **
       stackFree sp0 6) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (outPtr ↦ₘ result))) **
     ⌜Result bytes listBase listLen status result⌝) h

/-- Release K47's private frame as six free stack dwords for a caller. -/
theorem rlpListCountItems_flat_spec_within
    (sp0 newSp listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin
      (8 + (85 + (93 * (listLen + 1) + 3) + 7))
      B saved.ra code
      ((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals saved) **
       stackFree sp0 6 **
       entryRest listBase listLenW outPtr oldCount bytes)
      (flatResult sp0 listBase outPtr saved bytes listLen) := by
  let extra : Assertion := memOwn (sp0 - BitVec.ofNat 64 (8 * 1))
  have hbase := rlp_list_count_items_spec_within
    sp0 newSp listBase listLenW outPtr oldCount saved bytes listLen
    hlistLenW hsalign hslack hover hvalid hnewSp hret
  have hframed := cpsTripleWithin_frameR extra (by unfold extra; pcf) hbase
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hframed
  · unfold extra
    rw [hnewSp]
    rw [regsAt_countFrame] at hp ⊢
    simp only [frameSlotsOwn, countFrame,
      List.foldr_cons, List.foldr_nil, sepConj_emp_right',
      signExtend12_0, signExtend12_8, signExtend12_16,
      signExtend12_24, signExtend12_32,
      savedSlotAddr0]
    simp only [stackFree_succ, stackFree_zero, sepConj_emp_right'] at hp
    rw [show sp0 - BitVec.ofNat 64 (8 * 6) + (0 : Word) =
      sp0 - BitVec.ofNat 64 (8 * 6) by bv_omega]
    rw [show sp0 - BitVec.ofNat 64 (8 * 6) + (8 : Word) =
      sp0 - BitVec.ofNat 64 (8 * 5) by bv_omega,
      show sp0 - BitVec.ofNat 64 (8 * 6) + (16 : Word) =
        sp0 - BitVec.ofNat 64 (8 * 4) by bv_omega,
      show sp0 - BitVec.ofNat 64 (8 * 6) + (24 : Word) =
        sp0 - BitVec.ofNat 64 (8 * 3) by bv_omega,
      show sp0 - BitVec.ofNat 64 (8 * 6) + (32 : Word) =
        sp0 - BitVec.ofNat 64 (8 * 2) by bv_omega]
    xperm_hyp hp
  · change (finalResult sp0 newSp listBase outPtr saved bytes listLen **
      memOwn (sp0 - BitVec.ofNat 64 (8 * 1))) h at hq
    unfold finalResult at hq
    unfold flatResult
    obtain ⟨hLeft, hExtra, hdisj, hunion, hret, hextra⟩ := hq
    obtain ⟨status, result, v11, v12, hcore⟩ := hret
    refine ⟨status, result, v11, v12, ?_⟩
    let Tail : Assertion :=
      ((((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals saved)) **
        ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes ** (outPtr ↦ₘ result)))) **
       ⌜Result bytes listBase listLen status result⌝
    have hslots :
        (((newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
          ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2) **
          ((newSp + 32) ↦ₘ saved.s3) ** Tail) hLeft) := by
      unfold savedFrame at hcore
      unfold Tail
      xperm_hyp hcore
    have howns := sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn (fun _ ht => ht)))))
      hLeft hslots
    let Owned : Assertion :=
      memOwn newSp ** memOwn (newSp + 8) ** memOwn (newSp + 16) **
      memOwn (newSp + 24) ** memOwn (newSp + 32) ** Tail
    have hq1 : (Owned ** memOwn (sp0 - BitVec.ofNat 64 (8 * 1))) h :=
      ⟨hLeft, hExtra, hdisj, hunion, howns, hextra⟩
    unfold Owned Tail at hq1
    rw [hnewSp] at hq1
    rw [savedSlotAddr32, savedSlotAddr24, savedSlotAddr16,
      savedSlotAddr8, savedSlotAddr0] at hq1
    simp only [stackFree_succ, stackFree_zero, sepConj_emp_right']
    xperm_hyp hq1



end EvmAsm.Codegen.RlpListCountItemsSAsm
