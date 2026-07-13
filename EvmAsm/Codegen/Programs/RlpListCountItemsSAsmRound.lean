import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmNext

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

/-- The six concrete WalkNext exits collapsed to the semantic distinction the
    count loop needs. -/
def normalizedNext (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) : Assertion := fun h =>
  rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
  ∃ status : Word,
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
      (.x12 ↦ᵣ (0 : Word))) **
     ⌜status ≠ 0 ∧
       WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h

theorem failureRegs_mono (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) (status : Word) (P : Prop)
    (h_status : status ≠ 0)
    (h_imp : P → WalkFailure bytes off
      (listBase + BitVec.ofNat 64 off) endPtr) : ∀ h,
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) ** ⌜P⌝) h) →
      ((((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word))) **
        ⌜status ≠ 0 ∧ WalkFailure bytes off
          (listBase + BitVec.ofNat 64 off) endPtr⌝) h) := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, h10, hp⟩ := hp
  obtain ⟨h3, h4, hd2, hu2, h11, hp⟩ := hp
  obtain ⟨h12, hP⟩ := (sepConj_pure_right h4).1 hp
  exact (sepConj_pure_right h).2
    ⟨⟨h1, h2, hd, hu, h10, ⟨h3, h4, hd2, hu2, h11, h12⟩⟩,
      h_status, h_imp hP⟩

theorem nextOutcome_to_normalized (listBase endPtr : Word)
    (bytes : List (BitVec 8)) (off : Nat) : ∀ h,
    nextOutcome listBase endPtr bytes off h →
      normalizedNext listBase endPtr bytes off h := by
  intro h h_out
  unfold nextOutcome at h_out
  unfold normalizedNext
  rcases h_out with hs | h2 | h3 | h4 | h5 | h6
  · exact Or.inl hs
  · exact Or.inr ⟨2, failureRegs_mono listBase endPtr bytes off 2 _ (by decide) Or.inl h h2⟩
  · exact Or.inr ⟨3, failureRegs_mono listBase endPtr bytes off 3 _ (by decide) Or.inr h h3⟩
  · exact Or.inr ⟨4, failureRegs_mono listBase endPtr bytes off 4 _ (by decide) Or.inr h h4⟩
  · exact Or.inr ⟨5, failureRegs_mono listBase endPtr bytes off 5 _ (by decide) Or.inr h h5⟩
  · exact Or.inr ⟨6, failureRegs_mono listBase endPtr bytes off 6 _ (by decide) Or.inr h h6⟩

theorem nextCallNormalized (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off listLen : Nat) (v5 v6 v7 v11 v12 v28 v29 v30 v31 oldRa : Word)
    (F : Assertion) (h_F : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_off : off ≤ listLen) :
    cpsTripleWithin 89 (B + 52) (B + 60) code
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x18 ↦ᵣ endPtr) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** F)
      ((nextCommon listBase bytes **
        normalizedNext listBase endPtr bytes off) **
       ((.x18 ↦ᵣ endPtr) ** F)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp =>
    sepConj_mono_left (sepConj_mono_right
      (nextOutcome_to_normalized listBase endPtr bytes off)) h hp)
    (nextCallBlock listBase endPtr bytes off listLen v5 v6 v7 v11 v12 v28 v29
      v30 v31 oldRa F h_F h_align h_slack h_over h_valid h_off)

#print axioms failureRegs_mono
#print axioms nextOutcome_to_normalized
#print axioms nextCallNormalized

end EvmAsm.Codegen.RlpListCountItemsSAsm
