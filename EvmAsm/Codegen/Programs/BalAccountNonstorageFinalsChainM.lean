/- Top-level station composition for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainL

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP
namespace BalAccountNonstorageFinalsSpec

/-- Persistent balance result carried unchanged through nonce and code stations. -/
def balResult (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) : Assertion := fun h =>
  ((((oB ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
      ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
      ((oB + 32) ↦ₘ (0 : Word))) **
     ⌜FieldFinal acctBytes aB fOff fSpanN none⌝) h) ∨
  (∃ vNext vLen : Word,
    (((oB ↦ₘ (1 : Word)) **
      bytesRegion (oB + 8) (copyN (List.replicate 32 (0 : BitVec 8))
        acctBytes (32 - vLen.toNat) ((vNext - vLen - aB).toNat) vLen.toNat)) **
     ⌜FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen)) ∧
       vLen.toNat ≤ 32⌝) h)

/-- Split a balance-station success into its persistent result and reusable
    scratch frame. -/
theorem balStationPost_to_resultFrame
    (aB newSp oB n3 : Word) (aLen fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) :
    ∀ h, balStationPost aB newSp oB aLen fOff fSpanN n3 acctBytes F h →
      (balResult aB oB fOff fSpanN acctBytes **
       (((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
  intro h hp
  unfold balStationPost at hp
  unfold balResult
  rcases hp with hp | hp
  · refine sepConj_mono_left (fun h' hp' => Or.inl hp') h ?_
    xperm_hyp hp
  · obtain ⟨vNext, vLen, hp⟩ := hp
    refine sepConj_mono_left (fun h' hp' => Or.inr ⟨vNext, vLen, hp'⟩) h ?_
    xperm_hyp hp

#print axioms balStationPost_to_resultFrame

/-- Persistent balance+nonce result carried unchanged through code station. -/
def nonceResult (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G : Assertion) : Assertion := fun h =>
  (((G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word))) **
    ⌜FieldFinal acctBytes aB fOff fSpanN none⌝) h) ∨
  (∃ vNext vLen : Word,
    (((G ** ((oB + 40) ↦ₘ (1 : Word)) **
        ((oB + 48) ↦ₘ BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
          ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat)))) **
      ⌜FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen)) ∧
        vLen.toNat ≤ 8⌝) h))

/-- Split a nonce-station success into its persistent result and the frame
    consumed by code station. -/
theorem nonceStationPost_to_resultFrame
    (aB newSp oB n4 : Word) (aLen fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h, nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F h →
      (nonceResult aB oB fOff fSpanN acctBytes G **
       (((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
  intro h hp
  unfold nonceStationPost at hp
  unfold nonceResult
  rcases hp with hp | hp
  · refine sepConj_mono_left (fun h' hp' => Or.inl hp') h ?_
    xperm_hyp hp
  · obtain ⟨vNext, vLen, hp⟩ := hp
    refine sepConj_mono_left (fun h' hp' => Or.inr ⟨vNext, vLen, hp'⟩) h ?_
    xperm_pure hp

#print axioms nonceStationPost_to_resultFrame

/-- Persistent balance+nonce+code result carried into the verdict tail. -/
def codeResult (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G : Assertion) : Assertion := fun h =>
  (((G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word))) **
    ⌜FieldFinal acctBytes aB fOff fSpanN none⌝) h) ∨
  (∃ vNext vLen : Word,
    (((G ** ((oB + 56) ↦ₘ (1 : Word)) **
        ((oB + 64) ↦ₘ BitVec.ofNat 64 ((vNext - vLen - aB).toNat)) **
        ((oB + 72) ↦ₘ BitVec.ofNat 64 vLen.toNat)) **
      ⌜FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))⌝) h))

/-- Split a code-station success into its persistent result and verdict frame. -/
theorem codeStationPost_to_resultFrame
    (aB newSp oB n5 : Word) (aLen fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h, codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F h →
      (codeResult aB oB fOff fSpanN acctBytes G **
       (((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
  intro h hp
  unfold codeStationPost at hp
  unfold codeResult
  rcases hp with hp | hp
  · refine sepConj_mono_left (fun h' hp' => Or.inl hp') h ?_
    xperm_hyp hp
  · obtain ⟨vNext, vLen, hp⟩ := hp
    refine sepConj_mono_left (fun h' hp' => Or.inr ⟨vNext, vLen, hp'⟩) h ?_
    xperm_pure hp

#print axioms codeStationPost_to_resultFrame

/-- The abstract result represented by three optional final value windows. -/
def finalsOutOf (acctBytes : List (BitVec 8)) (aB : Word)
    (bal nonce code : Option (Word × Word)) : FinalsOut :=
  { hasBalance := bal.isSome
    balanceBE := match bal with
      | none => List.replicate 32 0
      | some (vNext, vLen) => copyN (List.replicate 32 (0 : BitVec 8))
          acctBytes (32 - vLen.toNat) (vNext - vLen - aB).toNat vLen.toNat
    hasNonce := nonce.isSome
    nonce := match nonce with
      | none => 0
      | some (vNext, vLen) => BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
          ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat))
    hasCode := code.isSome
    codeOff := match code with
      | none => 0
      | some (vNext, vLen) => vNext - vLen - aB
    codeLen := match code with
      | none => 0
      | some (_, vLen) => vLen }

/-- Six outer decodes plus the three station-final facts entail the genuine
    account-finals derivation for the result represented by those windows. -/
theorem fieldFinals_to_finalsDerivation
    (acctBytes : List (BitVec 8)) (aB : Word) (aLen : Nat) (b0 : BitVec 8)
    (n0 l0 n1 l1 n2 l2 n3 l3 n4 l4 n5 l5 : Word)
    (bal nonce code : Option (Word × Word))
    (h0 : acctBytes[0]? = some b0)
    (hd0 : rlpItemDecode acctBytes (listHeaderSize b0)
      (aB + BitVec.ofNat 64 (listHeaderSize b0))
      (aB + BitVec.ofNat 64 aLen) n0 l0)
    (hd1 : rlpItemDecode acctBytes (n0 - aB).toNat n0
      (aB + BitVec.ofNat 64 aLen) n1 l1)
    (hd2 : rlpItemDecode acctBytes (n1 - aB).toNat n1
      (aB + BitVec.ofNat 64 aLen) n2 l2)
    (hd3 : rlpItemDecode acctBytes (n2 - aB).toNat n2
      (aB + BitVec.ofNat 64 aLen) n3 l3)
    (hd4 : rlpItemDecode acctBytes (n3 - aB).toNat n3
      (aB + BitVec.ofNat 64 aLen) n4 l4)
    (hd5 : rlpItemDecode acctBytes (n4 - aB).toNat n4
      (aB + BitVec.ofNat 64 aLen) n5 l5)
    (hbal : FieldFinal acctBytes aB (n3 - l3 - aB).toNat l3.toNat bal)
    (hnonce : FieldFinal acctBytes aB (n4 - l4 - aB).toNat l4.toNat nonce)
    (hcode : FieldFinal acctBytes aB (n5 - l5 - aB).toNat l5.toNat code)
    (hbalBound : ∀ vNext vLen, bal = some (vNext, vLen) → vLen.toNat ≤ 32)
    (hnonceBound : ∀ vNext vLen, nonce = some (vNext, vLen) → vLen.toNat ≤ 8) :
    FinalsDerivation acctBytes aB aLen (finalsOutOf acctBytes aB bal nonce code) := by
  refine ⟨b0, h0, n0, l0, n1, l1, n2, l2, n3, l3, n4, l4, n5, l5,
    hd0, hd1, hd2, hd3, hd4, hd5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases bal with
    | none => exact Or.inl ⟨rfl, hbal⟩
    | some p =>
        obtain ⟨vNext, vLen⟩ := p
        exact Or.inr ⟨rfl, vNext, vLen, hbal, rfl, hbalBound _ _ rfl⟩
  · cases bal <;> simp [finalsOutOf]
  · cases nonce with
    | none => exact Or.inl ⟨rfl, hnonce⟩
    | some p =>
        obtain ⟨vNext, vLen⟩ := p
        exact Or.inr ⟨rfl, vNext, vLen, hnonce, rfl, hnonceBound _ _ rfl⟩
  · cases nonce <;> simp [finalsOutOf]
  · cases code with
    | none => exact Or.inl ⟨rfl, hcode⟩
    | some p =>
        obtain ⟨vNext, vLen⟩ := p
        exact Or.inr ⟨rfl, vNext, vLen, hcode, rfl, rfl⟩
  · cases code <;> simp [finalsOutOf]

#print axioms fieldFinals_to_finalsDerivation

/-- Expose the optional balance window encoded by `balResult`, while retaining
    the complete owned balance footprint. -/
theorem balResult_attachFinal
    (aB oB : Word) (fOff fSpanN : Nat) (acctBytes : List (BitVec 8)) :
    ∀ h, balResult aB oB fOff fSpanN acctBytes h →
      ∃ bal : Option (Word × Word),
        (balResult aB oB fOff fSpanN acctBytes **
          ⌜FieldFinal acctBytes aB fOff fSpanN bal ∧
            ∀ vNext vLen, bal = some (vNext, vLen) → vLen.toNat ≤ 32⌝) h := by
  intro h hp
  have hpKeep := hp
  unfold balResult at hp
  rcases hp with hp | hp
  · refine ⟨none, (sepConj_pure_right h).2 ⟨hpKeep, ?_⟩⟩
    exact ⟨((sepConj_pure_right h).1 hp).2, by simp⟩
  · obtain ⟨vNext, vLen, hp⟩ := hp
    refine ⟨some (vNext, vLen), (sepConj_pure_right h).2 ⟨hpKeep, ?_⟩⟩
    exact ⟨((sepConj_pure_right h).1 hp).2.1, by
      intro vNext' vLen' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact ((sepConj_pure_right h).1 hp).2.2⟩

#print axioms balResult_attachFinal

/-- Pure semantic witnesses accumulated after balance and nonce stations. -/
def balNonceFinals (acctBytes : List (BitVec 8)) (aB : Word)
    (balOff balSpan nonceOff nonceSpan : Nat)
    (bal nonce : Option (Word × Word)) : Prop :=
  FieldFinal acctBytes aB balOff balSpan bal ∧
  (∀ vNext vLen, bal = some (vNext, vLen) → vLen.toNat ≤ 32) ∧
  FieldFinal acctBytes aB nonceOff nonceSpan nonce ∧
  (∀ vNext vLen, nonce = some (vNext, vLen) → vLen.toNat ≤ 8)

/-- Lift the balance witness through `nonceResult` and expose the nonce
    witness, retaining the complete nested owned footprint. -/
theorem nonceResult_attachFinals
    (aB oB : Word) (balOff balSpan nonceOff nonceSpan : Nat)
    (acctBytes : List (BitVec 8)) :
    ∀ h,
      nonceResult aB oB nonceOff nonceSpan acctBytes
        (balResult aB oB balOff balSpan acctBytes) h →
      ∃ bal nonce : Option (Word × Word),
        (nonceResult aB oB nonceOff nonceSpan acctBytes
            (balResult aB oB balOff balSpan acctBytes) **
          ⌜balNonceFinals acctBytes aB balOff balSpan nonceOff nonceSpan
            bal nonce⌝) h := by
  intro h hp
  have hpKeep := hp
  unfold nonceResult at hp
  rcases hp with hp | hp
  · have hCore := ((sepConj_pure_right h).1 hp).1
    obtain ⟨hBal, hRest, _, _, hBalResult, _⟩ := hCore
    obtain ⟨bal, hAttached⟩ :=
      balResult_attachFinal aB oB balOff balSpan acctBytes hBal hBalResult
    have hBalFacts := ((sepConj_pure_right hBal).1 hAttached).2
    have hNonce := ((sepConj_pure_right h).1 hp).2
    refine ⟨bal, none, (sepConj_pure_right h).2 ⟨hpKeep, ?_⟩⟩
    exact ⟨hBalFacts.1, hBalFacts.2, hNonce, by simp⟩
  · obtain ⟨vNext, vLen, hp⟩ := hp
    have hCore := ((sepConj_pure_right h).1 hp).1
    obtain ⟨hBal, hRest, _, _, hBalResult, _⟩ := hCore
    obtain ⟨bal, hAttached⟩ :=
      balResult_attachFinal aB oB balOff balSpan acctBytes hBal hBalResult
    have hBalFacts := ((sepConj_pure_right hBal).1 hAttached).2
    have hNonce := ((sepConj_pure_right h).1 hp).2
    refine ⟨bal, some (vNext, vLen),
      (sepConj_pure_right h).2 ⟨hpKeep, ?_⟩⟩
    refine ⟨hBalFacts.1, hBalFacts.2, hNonce.1, ?_⟩
    intro vNext' vLen' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact hNonce.2

#print axioms nonceResult_attachFinals

/-- Pure semantic witnesses accumulated after all three value stations. -/
def allFieldFinals (acctBytes : List (BitVec 8)) (aB : Word)
    (balOff balSpan nonceOff nonceSpan codeOff codeSpan : Nat)
    (bal nonce code : Option (Word × Word)) : Prop :=
  balNonceFinals acctBytes aB balOff balSpan nonceOff nonceSpan bal nonce ∧
  FieldFinal acctBytes aB codeOff codeSpan code

/-- Lift the balance and nonce witnesses through `codeResult`, expose the code
    witness, and retain the complete nested owned output footprint. -/
theorem codeResult_attachFinals
    (aB oB : Word)
    (balOff balSpan nonceOff nonceSpan codeOff codeSpan : Nat)
    (acctBytes : List (BitVec 8)) :
    ∀ h,
      codeResult aB oB codeOff codeSpan acctBytes
        (nonceResult aB oB nonceOff nonceSpan acctBytes
          (balResult aB oB balOff balSpan acctBytes)) h →
      ∃ bal nonce code : Option (Word × Word),
        (codeResult aB oB codeOff codeSpan acctBytes
            (nonceResult aB oB nonceOff nonceSpan acctBytes
              (balResult aB oB balOff balSpan acctBytes)) **
          ⌜allFieldFinals acctBytes aB balOff balSpan nonceOff nonceSpan
            codeOff codeSpan bal nonce code⌝) h := by
  intro h hp
  have hpKeep := hp
  unfold codeResult at hp
  rcases hp with hp | hp
  · have hCore := ((sepConj_pure_right h).1 hp).1
    obtain ⟨hBN, hRest, _, _, hBNResult, _⟩ := hCore
    obtain ⟨bal, nonce, hAttached⟩ := nonceResult_attachFinals aB oB
      balOff balSpan nonceOff nonceSpan acctBytes hBN hBNResult
    have hBNFacts := ((sepConj_pure_right hBN).1 hAttached).2
    have hCode := ((sepConj_pure_right h).1 hp).2
    refine ⟨bal, nonce, none,
      (sepConj_pure_right h).2 ⟨hpKeep, hBNFacts, hCode⟩⟩
  · obtain ⟨vNext, vLen, hp⟩ := hp
    have hCore := ((sepConj_pure_right h).1 hp).1
    obtain ⟨hBN, hRest, _, _, hBNResult, _⟩ := hCore
    obtain ⟨bal, nonce, hAttached⟩ := nonceResult_attachFinals aB oB
      balOff balSpan nonceOff nonceSpan acctBytes hBN hBNResult
    have hBNFacts := ((sepConj_pure_right hBN).1 hAttached).2
    have hCode := ((sepConj_pure_right h).1 hp).2
    refine ⟨bal, nonce, some (vNext, vLen),
      (sepConj_pure_right h).2 ⟨hpKeep, hBNFacts, hCode⟩⟩

#print axioms codeResult_attachFinals

/-- The complete six-item outer AccountChanges decode chain. -/
def outerDecodes (acctBytes : List (BitVec 8)) (aB : Word) (aLen : Nat)
    (b0 : BitVec 8) (n0 l0 n1 l1 n2 l2 n3 l3 n4 l4 n5 l5 : Word) : Prop :=
  acctBytes[0]? = some b0 ∧
  rlpItemDecode acctBytes (listHeaderSize b0)
    (aB + BitVec.ofNat 64 (listHeaderSize b0))
    (aB + BitVec.ofNat 64 aLen) n0 l0 ∧
  rlpItemDecode acctBytes (n0 - aB).toNat n0
    (aB + BitVec.ofNat 64 aLen) n1 l1 ∧
  rlpItemDecode acctBytes (n1 - aB).toNat n1
    (aB + BitVec.ofNat 64 aLen) n2 l2 ∧
  rlpItemDecode acctBytes (n2 - aB).toNat n2
    (aB + BitVec.ofNat 64 aLen) n3 l3 ∧
  rlpItemDecode acctBytes (n3 - aB).toNat n3
    (aB + BitVec.ofNat 64 aLen) n4 l4 ∧
  rlpItemDecode acctBytes (n4 - aB).toNat n4
    (aB + BitVec.ofNat 64 aLen) n5 l5

/-- Convert the packaged outer chain and three packaged station finals into
    the genuine semantic derivation used by the capstone postcondition. -/
theorem outerAndFieldFinals_to_derivation
    (acctBytes : List (BitVec 8)) (aB : Word) (aLen : Nat)
    (b0 : BitVec 8) (n0 l0 n1 l1 n2 l2 n3 l3 n4 l4 n5 l5 : Word)
    (bal nonce code : Option (Word × Word))
    (hOuter : outerDecodes acctBytes aB aLen b0
      n0 l0 n1 l1 n2 l2 n3 l3 n4 l4 n5 l5)
    (hFinals : allFieldFinals acctBytes aB
      (n3 - l3 - aB).toNat l3.toNat
      (n4 - l4 - aB).toNat l4.toNat
      (n5 - l5 - aB).toNat l5.toNat bal nonce code) :
    FinalsDerivation acctBytes aB aLen (finalsOutOf acctBytes aB bal nonce code) := by
  rcases hOuter with ⟨h0, hd0, hd1, hd2, hd3, hd4, hd5⟩
  rcases hFinals with ⟨⟨hbal, hbalBound, hnonce, hnonceBound⟩, hcode⟩
  exact fieldFinals_to_finalsDerivation acctBytes aB aLen b0
    n0 l0 n1 l1 n2 l2 n3 l3 n4 l4 n5 l5 bal nonce code
    h0 hd0 hd1 hd2 hd3 hd4 hd5 hbal hnonce hcode hbalBound hnonceBound

#print axioms outerAndFieldFinals_to_derivation

/-- Reframe the successful outer nonce item as a persistent nonce result,
    reusable code-station frame, and its retained outer decode. -/
theorem nonceStationOuterPost_to_resultFrame
    (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h, nonceStationOuterPost aB newSp oB aLen off acctBytes G F h →
      ∃ n4 l4 : Word,
        ((nonceResult aB oB (n4 - l4 - aB).toNat l4.toNat acctBytes G **
          (((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
           ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           memOwn (newSp + 64) ** memOwn (newSp + 72) **
           ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
           ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
           regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x19 **
           regOwn .x20 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
           bytesRegion aB acctBytes ** F)) **
         ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
           (aB + BitVec.ofNat 64 aLen) n4 l4⌝) h := by
  intro h hp
  unfold nonceStationOuterPost at hp
  obtain ⟨n4, l4, hp⟩ := hp
  obtain ⟨hStation, hDecode⟩ := (sepConj_pure_right h).1 hp
  refine ⟨n4, l4, (sepConj_pure_right h).2 ⟨?_, hDecode⟩⟩
  exact nonceStationPost_to_resultFrame aB newSp oB n4 aLen
    (n4 - l4 - aB).toNat l4.toNat acctBytes G F h hStation

#print axioms nonceStationOuterPost_to_resultFrame

/-- Reframe the successful outer code item as the complete persistent result,
    verdict frame, and its retained outer decode. -/
theorem codeStationOuterPost_to_resultFrame
    (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h, codeStationOuterPost aB newSp oB aLen off acctBytes G F h →
      ∃ n5 l5 : Word,
        ((codeResult aB oB (n5 - l5 - aB).toNat l5.toNat acctBytes G **
          (((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           memOwn (newSp + 64) ** memOwn (newSp + 72) **
           ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
           ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
           regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x19 **
           regOwn .x20 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
           bytesRegion aB acctBytes ** F)) **
         ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
           (aB + BitVec.ofNat 64 aLen) n5 l5⌝) h := by
  intro h hp
  unfold codeStationOuterPost at hp
  obtain ⟨n5, l5, hp⟩ := hp
  obtain ⟨hStation, hDecode⟩ := (sepConj_pure_right h).1 hp
  refine ⟨n5, l5, (sepConj_pure_right h).2 ⟨?_, hDecode⟩⟩
  have hResult := codeStationPost_to_resultFrame aB newSp oB
    (aB + BitVec.ofNat 64 off) aLen (n5 - l5 - aB).toNat l5.toNat
    acctBytes G F h hStation
  exact hResult

#print axioms codeStationOuterPost_to_resultFrame

/-- Existential code-station entry obtained from a successful nonce station;
    the item-4 decode is retained in the ambient assertion. -/
def nonceToCodePre (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion := fun h =>
  ∃ n4 l4 : Word,
    ((codeStationOuterBase aB newSp oB aLen (n4 - aB).toNat acctBytes
        (nonceResult aB oB (n4 - l4 - aB).toNat l4.toNat acctBytes G)
        (F ** ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
          (aB + BitVec.ofNat 64 aLen) n4 l4⌝) **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** regOwn .x1) h)

/-- A successful nonce-station outer post satisfies the existential entry
    assertion consumed by the code station. -/
theorem nonceStationOuterPost_to_codePre
    (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h, nonceStationOuterPost aB newSp oB aLen off acctBytes G F h →
      nonceToCodePre aB newSp oB aLen off acctBytes G F h := by
  intro h hp
  obtain ⟨n4, l4, hp⟩ := nonceStationOuterPost_to_resultFrame
    aB newSp oB aLen off acctBytes G F h hp
  refine ⟨n4, l4, ?_⟩
  have hrep : n4 = aB + BitVec.ofNat 64 (n4 - aB).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  unfold codeStationOuterBase
  rw [← hrep]
  xperm_hyp hp

#print axioms nonceStationOuterPost_to_codePre

/-- The persistent balance result owns only memory and pure facts. -/
theorem balResult_pcFree (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) :
    (balResult aB oB fOff fSpanN acctBytes).pcFree := by
  intro h hp
  unfold balResult at hp
  rcases hp with hp | hp
  · exact (inferInstance : Assertion.PCFree _).proof h hp
  · obtain ⟨vNext, vLen, hp⟩ := hp
    exact (inferInstance : Assertion.PCFree _).proof h hp

#print axioms balResult_pcFree

/-- The persistent nonce result is PC-free when its preserved footprint is. -/
theorem nonceResult_pcFree (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G : Assertion) (hG : G.pcFree) :
    (nonceResult aB oB fOff fSpanN acctBytes G).pcFree := by
  letI : Assertion.PCFree G := ⟨hG⟩
  intro h hp
  unfold nonceResult at hp
  rcases hp with hp | hp
  · exact (inferInstance : Assertion.PCFree _).proof h hp
  · obtain ⟨vNext, vLen, hp⟩ := hp
    exact (inferInstance : Assertion.PCFree _).proof h hp

#print axioms nonceResult_pcFree

/-- The complete persistent code result is PC-free when its preserved
    balance+nonce footprint is. -/
theorem codeResult_pcFree (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G : Assertion) (hG : G.pcFree) :
    (codeResult aB oB fOff fSpanN acctBytes G).pcFree := by
  letI : Assertion.PCFree G := ⟨hG⟩
  intro h hp
  unfold codeResult at hp
  rcases hp with hp | hp
  · exact (inferInstance : Assertion.PCFree _).proof h hp
  · obtain ⟨vNext, vLen, hp⟩ := hp
    exact (inferInstance : Assertion.PCFree _).proof h hp

#print axioms codeResult_pcFree

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
