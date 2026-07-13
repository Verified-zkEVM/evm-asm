/- ABI post normalization for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainN

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP
namespace BalAccountNonstorageFinalsSpec

/-- Common conservative result footprint of every parse-reject path. -/
def bansfRejectResult (aB newSp oB : Word) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  memOwn oB ** memOwn (oB + 8) ** memOwn (oB + 16) **
  memOwn (oB + 24) ** memOwn (oB + 32) ** memOwn (oB + 40) **
  memOwn (oB + 48) ** memOwn (oB + 56) ** memOwn (oB + 64) **
  memOwn (oB + 72) ** regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F

private def zeroOutBlock (oB : Word) : Assertion :=
  (oB ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
  ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
  ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
  ((oB + 48) ↦ₘ (0 : Word)) ** ((oB + 56) ↦ₘ (0 : Word)) **
  ((oB + 64) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word))

private def ownOutBlock (oB : Word) : Assertion :=
  memOwn oB ** memOwn (oB + 8) ** memOwn (oB + 16) **
  memOwn (oB + 24) ** memOwn (oB + 32) ** memOwn (oB + 40) **
  memOwn (oB + 48) ** memOwn (oB + 56) ** memOwn (oB + 64) **
  memOwn (oB + 72)

private def earlyRejectRest (aB newSp : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  regOwn .x19 ** regOwn .x20 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- SEG-B's earliest reject factors into the ABI-restorable register set and
    the common conservative reject result. -/
theorem chainRejB_to_abiReject
    (aB newSp oB : Word) (aLen : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) :
    ∀ h, chainRejB aB newSp oB aLen acctBytes
        (memOwn (newSp + 64) ** memOwn (newSp + 72) **
         regOwn .x19 ** regOwn .x20 ** F) h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfRejectResult aB newSp oB acctBytes F) h := by
  intro h hp
  unfold chainRejB at hp
  have hq :
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) **
       (zeroOutBlock oB ** earlyRejectRest aB newSp acctBytes F)) h := by
    unfold zeroOutBlock earlyRejectRest
    xperm_hyp hp
  have hAnchors : ∀ h',
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) h') →
      (((regOwn .x8 ** regOwn .x9) ** regOwn .x18) h') :=
    sepConj_mono (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) (regIs_implies_regOwn .x18)
  have hOut : ∀ h',
      zeroOutBlock oB h' → ownOutBlock oB h' := by
    unfold zeroOutBlock ownOutBlock
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn
                      memIs_implies_memOwn))))))))
  have hq' := sepConj_mono hAnchors
    (sepConj_mono hOut (fun _ hx => hx)) h hq
  unfold earlyRejectRest ownOutBlock at hq'
  unfold bansfRejectResult
  simp only [regsOwnAt, bansfFrame, List.foldr, sepConj_emp_right']
  xperm_hyp hq'

#print axioms chainRejB_to_abiReject

/-- An item-walk reject carries the same ABI anchors and conservative result;
    the successful outer-header fact is irrelevant once rejection is chosen. -/
theorem itemRejAmbient_to_abiReject
    (aB newSp oB : Word) (aLen off0 : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) :
    ∀ h,
      (itemRej aB newSp acctBytes
          (valueEntryAmbient aB newSp oB aLen F) **
        ⌜OuterInitOk acctBytes aLen off0⌝) h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfRejectResult aB newSp oB acctBytes F) h := by
  intro h hp
  obtain ⟨hp, _⟩ := (sepConj_pure_right h).1 hp
  unfold itemRej valueEntryAmbient at hp
  have hq :
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) **
       (zeroOutBlock oB ** earlyRejectRest aB newSp acctBytes F)) h := by
    unfold zeroOutBlock earlyRejectRest
    xperm_hyp hp
  have hAnchors : ∀ h',
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) h') →
      (((regOwn .x8 ** regOwn .x9) ** regOwn .x18) h') :=
    sepConj_mono (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) (regIs_implies_regOwn .x18)
  have hOut : ∀ h', zeroOutBlock oB h' → ownOutBlock oB h' := by
    unfold zeroOutBlock ownOutBlock
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn
                      memIs_implies_memOwn))))))))
  have hq' := sepConj_mono hAnchors
    (sepConj_mono hOut (fun _ hx => hx)) h hq
  unfold earlyRejectRest ownOutBlock at hq'
  unfold bansfRejectResult
  simp only [regsOwnAt, bansfFrame, List.foldr, sepConj_emp_right']
  xperm_hyp hq'

#print axioms itemRejAmbient_to_abiReject

private def lateZeroBlock (oB : Word) : Assertion :=
  ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
  ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
  ((oB + 72) ↦ₘ (0 : Word))

private def lateOwnBlock (oB : Word) : Assertion :=
  memOwn (oB + 40) ** memOwn (oB + 48) ** memOwn (oB + 56) **
  memOwn (oB + 64) ** memOwn (oB + 72)

/-- A balance-station reject, including the still-zero nonce/code cells,
    factors into the common ABI reject result. -/
theorem balStationRej_to_abiReject
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) :
    ∀ h, balStationRej aB newSp oB aLen acctBytes
        (laterFieldZeros oB F) h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfRejectResult aB newSp oB acctBytes F) h := by
  intro h hp
  unfold balStationRej laterFieldZeros at hp
  have hq :
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) **
       (lateZeroBlock oB **
        (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
         memOwn (newSp + 48) ** memOwn (newSp + 56) **
         memOwn (newSp + 64) ** memOwn (newSp + 72) **
         memOwn oB ** memOwnU256 (oB + 8) **
         regOwn .x19 ** regOwn .x20 ** regOwn .x11 ** regOwn .x12 **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
         bytesRegion aB acctBytes ** F))) h := by
    unfold lateZeroBlock
    xperm_hyp hp
  have hAnchors : ∀ h',
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) h') →
      (((regOwn .x8 ** regOwn .x9) ** regOwn .x18) h') :=
    sepConj_mono (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) (regIs_implies_regOwn .x18)
  have hLate : ∀ h', lateZeroBlock oB h' → lateOwnBlock oB h' := by
    unfold lateZeroBlock lateOwnBlock
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))
  have hq' := sepConj_mono hAnchors
    (sepConj_mono hLate (fun _ hx => hx)) h hq
  unfold lateOwnBlock memOwnU256 at hq'
  rw [show (oB + 8) + 8 = oB + 16 from by bv_omega,
      show (oB + 8) + 16 = oB + 24 from by bv_omega,
      show (oB + 8) + 24 = oB + 32 from by bv_omega] at hq'
  unfold bansfRejectResult
  simp only [regsOwnAt, bansfFrame, List.foldr, sepConj_emp_right']
  xperm_hyp hq'

#print axioms balStationRej_to_abiReject

private def balOwnBlock (oB : Word) : Assertion :=
  memOwn oB ** memOwn (oB + 8) ** memOwn (oB + 16) **
  memOwn (oB + 24) ** memOwn (oB + 32)

private def codeZeroBlock (oB : Word) : Assertion :=
  ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
  ((oB + 72) ↦ₘ (0 : Word))

private def codeOwnBlock (oB : Word) : Assertion :=
  memOwn (oB + 56) ** memOwn (oB + 64) ** memOwn (oB + 72)

private def balanceNonceOwnBlock (oB : Word) : Assertion :=
  memOwn oB ** memOwn (oB + 8) ** memOwn (oB + 16) **
  memOwn (oB + 24) ** memOwn (oB + 32) ** memOwn (oB + 40) **
  memOwn (oB + 48)

/-- A byte region of exactly 32 bytes can be conservatively forgotten to the
    four-dword ownership token used by the balance result. -/
theorem bytesRegion32_to_memOwnU256 (base : Word) (bs : List (BitVec 8))
    (h_len : bs.length = 32) :
    ∀ h, bytesRegion base bs h → memOwnU256 base h := by
  intro h hp
  have hne0 : bs ≠ [] := by
    apply List.ne_nil_of_length_pos
    omega
  have hne1 : bs.drop 8 ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_drop]
    omega
  have hne2 : (bs.drop 8).drop 8 ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_drop]
    omega
  have hne3 : ((bs.drop 8).drop 8).drop 8 ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_drop]
    omega
  rw [bytesRegion_eq_cons base bs hne0,
      bytesRegion_eq_cons (base + 8) (bs.drop 8) hne1,
      bytesRegion_eq_cons (base + 8 + 8) ((bs.drop 8).drop 8) hne2,
      bytesRegion_eq_cons (base + 8 + 8 + 8) (((bs.drop 8).drop 8).drop 8) hne3]
      at hp
  have hdrop : ((((bs.drop 8).drop 8).drop 8).drop 8) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_drop]
    omega
  rw [hdrop, bytesRegion_nil, sepConj_emp_right',
      show base + 8 + 8 = base + 16 from by bv_omega,
      show base + 16 + 8 = base + 24 from by bv_omega] at hp
  unfold memOwnU256
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)) h hp

#print axioms bytesRegion32_to_memOwnU256

/-- Either semantic balance result owns exactly the five balance output cells,
    independently of whether the field was absent or materialized. -/
theorem balResult_to_balOwnBlock
    (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) :
    ∀ h, balResult aB oB fOff fSpanN acctBytes h → balOwnBlock oB h := by
  intro h hp
  unfold balResult at hp
  rcases hp with hp | hp
  · obtain ⟨hCells, _⟩ := (sepConj_pure_right h).1 hp
    unfold balOwnBlock
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))) h hCells
  · obtain ⟨vNext, vLen, hp⟩ := hp
    obtain ⟨hCells, _⟩ := (sepConj_pure_right h).1 hp
    have h_len : (copyN (List.replicate 32 (0 : BitVec 8)) acctBytes
        (32 - vLen.toNat) (vNext - vLen - aB).toNat vLen.toNat).length = 32 := by
      rw [copyN_length]
      simp
    have hOwned := sepConj_mono memIs_implies_memOwn
      (bytesRegion32_to_memOwnU256 (oB + 8) _ h_len) h hCells
    unfold memOwnU256 at hOwned
    rw [show (oB + 8) + 8 = oB + 16 from by bv_omega,
        show (oB + 8) + 16 = oB + 24 from by bv_omega,
        show (oB + 8) + 24 = oB + 32 from by bv_omega] at hOwned
    unfold balOwnBlock
    exact hOwned

#print axioms balResult_to_balOwnBlock

/-- A code-station reject normalizes to the common ABI reject result whenever
    the already-materialized balance and nonce footprint owns its cells. -/
theorem codeStationRej_to_abiReject
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : ∀ h, G h → balanceNonceOwnBlock oB h) :
    ∀ h, codeStationRej aB newSp oB aLen acctBytes G F h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfRejectResult aB newSp oB acctBytes F) h := by
  intro h hp
  unfold codeStationRej at hp
  have hq :
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) **
       (G **
        (memOwn (oB + 56) ** memOwn (oB + 64) ** memOwn (oB + 72) **
         memOwn (newSp + 48) ** memOwn (newSp + 56) **
         memOwn (newSp + 64) ** memOwn (newSp + 72) **
         ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
         regOwn .x11 ** regOwn .x12 ** regOwn .x19 ** regOwn .x20 **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
         bytesRegion aB acctBytes ** F))) h := by
    xperm_hyp hp
  have hAnchors : ∀ h',
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) h') →
      (((regOwn .x8 ** regOwn .x9) ** regOwn .x18) h') :=
    sepConj_mono (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) (regIs_implies_regOwn .x18)
  have hq' := sepConj_mono hAnchors
    (sepConj_mono hG (fun _ hx => hx)) h hq
  unfold balanceNonceOwnBlock at hq'
  unfold bansfRejectResult
  simp only [regsOwnAt, bansfFrame, List.foldr, sepConj_emp_right']
  xperm_hyp hq'

#print axioms codeStationRej_to_abiReject

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
