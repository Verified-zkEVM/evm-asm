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


/-- Either semantic nonce result extends an owned balance footprint with the
    two owned nonce output cells. -/
theorem nonceResult_to_balanceNonceOwnBlock
    (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G : Assertion)
    (hG : ∀ h, G h → balOwnBlock oB h) :
    ∀ h, nonceResult aB oB fOff fSpanN acctBytes G h →
      balanceNonceOwnBlock oB h := by
  intro h hp
  unfold nonceResult at hp
  rcases hp with hp | hp
  · obtain ⟨hCells, _⟩ := (sepConj_pure_right h).1 hp
    have hOwned := sepConj_mono hG
      (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn) h hCells
    unfold balOwnBlock at hOwned
    unfold balanceNonceOwnBlock
    xperm_hyp hOwned
  · obtain ⟨vNext, vLen, hp⟩ := hp
    obtain ⟨hCells, _⟩ := (sepConj_pure_right h).1 hp
    have hOwned := sepConj_mono hG
      (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn) h hCells
    unfold balOwnBlock at hOwned
    unfold balanceNonceOwnBlock
    xperm_hyp hOwned


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


/-- A nonce-station reject normalizes to the common ABI reject result whenever
    the already-materialized balance footprint owns its output cells. -/
theorem nonceStationRej_to_abiReject
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : ∀ h, G h → balOwnBlock oB h) :
    ∀ h, nonceStationRej aB newSp oB aLen acctBytes G F h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfRejectResult aB newSp oB acctBytes F) h := by
  intro h hp
  unfold nonceStationRej at hp
  have hAnchors : ∀ h',
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) h') →
      (((regOwn .x8 ** regOwn .x9) ** regOwn .x18) h') :=
    sepConj_mono (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) (regIs_implies_regOwn .x18)
  have hp' := sepConj_mono hG
    (sepConj_mono (fun _ hx => hx)
      (sepConj_mono (fun _ hx => hx)
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono_left memIs_implies_memOwn))))) h hp
  let R : Assertion :=
    memOwn (oB + 40) ** memOwn (oB + 48) **
    memOwn (oB + 56) ** memOwn (oB + 64) ** memOwn (oB + 72) **
    memOwn (newSp + 48) ** memOwn (newSp + 56) **
    memOwn (newSp + 64) ** memOwn (newSp + 72) **
    ((.x2 : Reg) ↦ᵣ newSp) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
    regOwn .x11 ** regOwn .x12 ** regOwn .x19 ** regOwn .x20 **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
    bytesRegion aB acctBytes ** F
  have hq :
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) ** (balOwnBlock oB ** R)) h := by
    dsimp only [R]
    xperm_hyp hp'
  have hq' := sepConj_mono hAnchors (fun _ hx => hx) h hq
  dsimp only [R] at hq'
  unfold balOwnBlock at hq'
  unfold bansfRejectResult
  simp only [regsOwnAt, bansfFrame, List.foldr, sepConj_emp_right']
  xperm_hyp hq'


/-- The existential code reject reached after a successful nonce station also
    normalizes to the common ABI reject result. -/
theorem nonceCodeRej_to_abiReject
    (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : ∀ h, G h → balOwnBlock oB h) :
    ∀ h, nonceCodeRej aB newSp oB aLen off acctBytes G F h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfRejectResult aB newSp oB acctBytes F) h := by
  intro h hp
  unfold nonceCodeRej at hp
  obtain ⟨n4, l4, hp⟩ := hp
  obtain ⟨hRej, _⟩ := (sepConj_pure_right h).1 hp
  exact codeStationRej_to_abiReject aB newSp oB aLen acctBytes
    (nonceResult aB oB (n4 - l4 - aB).toNat l4.toNat acctBytes G) F
    (nonceResult_to_balanceNonceOwnBlock aB oB
      (n4 - l4 - aB).toNat l4.toNat acctBytes G hG) h hRej


/-- Semantic success result after factoring out the stack pointer and the
    callee-saved registers consumed by `abiFrame_spec_own`. -/
def bansfSuccessResult (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion := fun h =>
  ∃ out : FinalsOut, ∃ spill : Word,
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** finalOutBlock acctBytes aB oB out **
      ((newSp + 48) ↦ₘ spill) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aB acctBytes ** F **
      ⌜FinalsDerivation acctBytes aB aLen out⌝) h

/-- Factor a genuine semantic success verdict into the ABI body-post shape. -/
theorem bansfSuccessVerdict_to_abiSuccess
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) :
    ∀ h, bansfSuccessVerdictPost aB newSp oB aLen acctBytes F h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfSuccessResult aB newSp oB aLen acctBytes F) h := by
  intro h hp
  unfold bansfSuccessVerdictPost bansfSuccessRest at hp
  obtain ⟨out, hp⟩ := sepConj_exists_right h hp
  obtain ⟨spill, hp⟩ := sepConj_exists_right h hp
  unfold bansfSuccessResult
  refine sepConj_mono_right
    (sepConj_mono_right (fun _ hp' => ⟨out, spill, hp'⟩)) h ?_
  let Q : Assertion :=
    ((.x2 : Reg) ↦ᵣ newSp) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    finalOutBlock acctBytes aB oB out ** ((newSp + 48) ↦ₘ spill) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    memOwn (newSp + 64) ** memOwn (newSp + 72) **
    regOwn .x11 ** regOwn .x12 ** regOwn .x19 ** regOwn .x20 **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
    bytesRegion aB acctBytes ** F **
    ⌜FinalsDerivation acctBytes aB aLen out⌝
  have hq :
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) ** Q) h := by
    dsimp only [Q]
    xperm_hyp hp
  have hAnchors : ∀ h',
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) h') →
      (((regOwn .x8 ** regOwn .x9) ** regOwn .x18) h') :=
    sepConj_mono (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) (regIs_implies_regOwn .x18)
  have hq' := sepConj_mono hAnchors (fun _ hx => hx) h hq
  dsimp only [Q] at hq'
  simp only [regsOwnAt, bansfFrame, List.foldr, sepConj_emp_right']
  xperm_hyp hq'


/-- Observable result of the body: exact rejection status, or exact success
    status together with the window-anchored semantic derivation. -/
def bansfVerdictResult (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion := fun h =>
  bansfRejectResult aB newSp oB acctBytes F h ∨
  bansfSuccessResult aB newSp oB aLen acctBytes F h

/-- Normalize every nested body verdict into the common ABI body-post shape. -/
theorem chainAVerdictPost_to_abiVerdict
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) :
    ∀ h, chainAVerdictPost aB newSp oB aLen acctBytes F h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfVerdictResult aB newSp oB aLen acctBytes F) h := by
  intro h hp
  have reject (hr : (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
      bansfRejectResult aB newSp oB acctBytes F) h) :
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfVerdictResult aB newSp oB aLen acctBytes F) h := by
    unfold bansfVerdictResult
    exact sepConj_mono_right (sepConj_mono_right (fun _ hx => Or.inl hx)) h hr
  have success (hs : (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
      bansfSuccessResult aB newSp oB aLen acctBytes F) h) :
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfVerdictResult aB newSp oB aLen acctBytes F) h := by
    unfold bansfVerdictResult
    exact sepConj_mono_right (sepConj_mono_right (fun _ hx => Or.inr hx)) h hs
  unfold chainAVerdictPost at hp
  rcases hp with hp | hp
  · exact reject (chainRejB_to_abiReject aB newSp oB aLen acctBytes F h hp)
  · unfold chainMidVerdictPost at hp
    obtain ⟨off0, hp⟩ := hp
    unfold itemsVerdictPost at hp
    rcases hp with hp | hp
    · exact reject (itemRejAmbient_to_abiReject aB newSp oB aLen off0
        acctBytes F h hp)
    · unfold valueStationsFromAcc3Post at hp
      obtain ⟨n3, l3, hp⟩ := hp
      unfold valueStationsVerdictPost at hp
      rcases hp with hp | hp
      · unfold valueStationsRej at hp
        rcases hp with hp | hp
        · exact reject (balStationRej_to_abiReject aB newSp oB aLen
            acctBytes F h hp)
        · unfold nonceCodeChainRej at hp
          rcases hp with hp | hp
          · exact reject (nonceStationRej_to_abiReject aB newSp oB aLen
              acctBytes
              (balResult aB oB (n3 - l3 - aB).toNat l3.toNat acctBytes)
              F (balResult_to_balOwnBlock aB oB
                (n3 - l3 - aB).toNat l3.toNat acctBytes) h hp)
          · exact reject (nonceCodeRej_to_abiReject aB newSp oB aLen
              (n3 - aB).toNat acctBytes
              (balResult aB oB (n3 - l3 - aB).toNat l3.toNat acctBytes)
              F (balResult_to_balOwnBlock aB oB
                (n3 - l3 - aB).toNat l3.toNat acctBytes) h hp)
      · exact success (bansfSuccessVerdict_to_abiSuccess aB newSp oB aLen
          acctBytes F h hp)


/-- Pull an ambient assertion out of either observable verdict arm. -/
theorem bansfVerdictResult_frame_out
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (A F : Assertion) :
    ∀ h, bansfVerdictResult aB newSp oB aLen acctBytes (A ** F) h →
      (A ** bansfVerdictResult aB newSp oB aLen acctBytes F) h := by
  intro h hp
  unfold bansfVerdictResult at hp ⊢
  rcases hp with hp | hp
  · refine sepConj_mono_right (fun _ hx => Or.inl hx) h ?_
    unfold bansfRejectResult at hp ⊢
    xperm_hyp hp
  · refine sepConj_mono_right (fun _ hx => Or.inr hx) h ?_
    unfold bansfSuccessResult at hp ⊢
    obtain ⟨out, spill, hp⟩ := hp
    refine sepConj_mono_right (fun _ hp' => ⟨out, spill, hp'⟩) h ?_
    xperm_hyp hp


/-- Caller-owned resources used by the body, excluding the ABI frame itself. -/
def bansfCallerPre (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ aB) **
  ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x12 : Reg) ↦ᵣ oB) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  memOwn oB ** memOwn (oB + 8) ** memOwn (oB + 16) **
  memOwn (oB + 24) ** memOwn (oB + 32) ** memOwn (oB + 40) **
  memOwn (oB + 48) ** memOwn (oB + 56) ** memOwn (oB + 64) **
  memOwn (oB + 72) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F

/-- Complete 177-instruction body triple in `abiFrame_spec_own` shape. -/
theorem bansf_body_spec
    (sp0 aB oB : Word) (aLen : Nat) (vals : Reg → Word)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 →
      isValidByteAccess (oB + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (101 + (372 + (((98 * (aLen + 1) + 700) +
        2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2)))
      (B + 28) (B + 736) bansfCR
      (((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-80 : BitVec 12))) **
       regsAt bansfFrame vals **
       frameSlotsSaved bansfFrame
         (sp0 + signExtend12 (-80 : BitVec 12)) vals **
       bansfCallerPre aB (sp0 + signExtend12 (-80 : BitVec 12)) oB
         aLen acctBytes F)
      (((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-80 : BitVec 12))) **
       regsOwnAt bansfFrame **
       frameSlotsSaved bansfFrame
         (sp0 + signExtend12 (-80 : BitVec 12)) vals **
       bansfVerdictResult aB (sp0 + signExtend12 (-80 : BitVec 12)) oB
         aLen acctBytes F) := by
  let newSp := sp0 + signExtend12 (-80 : BitVec 12)
  let FS := frameSlotsSaved bansfFrame newSp vals
  have hFS : FS.pcFree := by
    dsimp only [FS]
    exact pcFree_frameSlotsSaved bansfFrame newSp vals
  have hAmbient : (FS ** F).pcFree := by
    letI : Assertion.PCFree FS := ⟨hFS⟩
    letI : Assertion.PCFree F := ⟨hF⟩
    exact (inferInstance : Assertion.PCFree (FS ** F)).proof
  have ht := bansf_chainAVerdict_concrete1920 aB newSp oB aLen acctBytes
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20) (FS ** F)
    hAmbient hsalign hoalign hslack hover hvalid hovout hovalid
  exact cpsTripleWithin_weaken (by
    intro h hp
    dsimp only [newSp, FS] at hp ⊢
    unfold bansfCallerPre at hp
    unfold chainAConcretePre
    have hRegs : ∀ h',
        regsAt bansfFrame vals h' →
        (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ vals .x8) **
          ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
          ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20)) h' := by
      simp only [regsAt, bansfFrame, List.foldr, sepConj_emp_right']
      exact sepConj_mono (regIs_implies_regOwn .x1) (fun _ hx => hx)
    have hp' := sepConj_mono (fun _ hx => hx)
      (sepConj_mono hRegs (fun _ hx => hx)) h hp
    xperm_hyp hp') (by
    intro h hp
    have hpAbi := chainAVerdictPost_to_abiVerdict aB newSp oB aLen
      acctBytes (FS ** F) h hp
    have hpOut := sepConj_mono_right (sepConj_mono_right
      (bansfVerdictResult_frame_out aB newSp oB aLen acctBytes FS F)) h hpAbi
    simpa only [newSp, FS] using hpOut) ht


/-- The caller-owned body footprint is PC-free when its ambient frame is. -/
theorem bansfCallerPre_pcFree
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (bansfCallerPre aB newSp oB aLen acctBytes F).pcFree := by
  letI : Assertion.PCFree F := ⟨hF⟩
  unfold bansfCallerPre
  exact (inferInstance : Assertion.PCFree _).proof


/-- Both exact verdict arms are PC-free when the ambient assertion is. -/
theorem bansfVerdictResult_pcFree
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (bansfVerdictResult aB newSp oB aLen acctBytes F).pcFree := by
  letI : Assertion.PCFree F := ⟨hF⟩
  intro h hp
  unfold bansfVerdictResult at hp
  rcases hp with hp | hp
  · unfold bansfRejectResult at hp
    exact (inferInstance : Assertion.PCFree _).proof h hp
  · unfold bansfSuccessResult at hp
    obtain ⟨out, spill, hp⟩ := hp
    letI : Assertion.PCFree (finalOutBlock acctBytes aB oB out) :=
      ⟨finalOutBlock_pcFree acctBytes aB oB out⟩
    exact (inferInstance : Assertion.PCFree _).proof h hp


/-- Static account/output geometry required by the verified memory model.
    It contains no decode result or branch outcome. -/
def BansfRegionInvariant (aB oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) : Prop :=
  aB.toNat % 8 = 0 ∧ oB.toNat % 8 = 0 ∧
  aLen + 9 ≤ acctBytes.length ∧
  aB.toNat + acctBytes.length < 2 ^ 64 ∧
  (∀ k, k < acctBytes.length →
    isValidByteAccess (aB + BitVec.ofNat 64 k) = true) ∧
  oB.toNat + 80 ≤ 2 ^ 64 ∧
  (∀ k, k < 80 →
    isValidByteAccess (oB + BitVec.ofNat 64 k) = true)

/-- Whole-routine capstone: from a standard ABI frame and static region
    invariant, return with the frame restored and an exact reject/success
    verdict.  The success arm retains a window-anchored `FinalsDerivation`. -/
theorem bansf_spec_within
    (sp0 ret aB oB : Word) (aLen : Nat) (vals : Reg → Word)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hret : vals .x1 = ret)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hRegions : BansfRegionInvariant aB oB aLen acctBytes) :
    cpsTripleWithin
      (1 + bansfFrame.length +
        (101 + (372 + (((98 * (aLen + 1) + 700) +
          2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2))) +
        bansfFrame.length + 1 + 1)
      B ret bansfCR
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt bansfFrame vals **
       frameSlotsOwn bansfFrame
         (sp0 + signExtend12 (-80 : BitVec 12)) **
       bansfCallerPre aB (sp0 + signExtend12 (-80 : BitVec 12)) oB
         aLen acctBytes F)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt bansfFrame vals **
       frameSlotsSaved bansfFrame
         (sp0 + signExtend12 (-80 : BitVec 12)) vals **
       bansfVerdictResult aB (sp0 + signExtend12 (-80 : BitVec 12)) oB
         aLen acctBytes F) := by
  rcases hRegions with
    ⟨hsalign, hoalign, hslack, hover, hvalid, hovout, hovalid⟩
  have hbody := bansf_body_spec sp0 aB oB aLen vals acctBytes F hF
    hsalign hoalign hslack hover hvalid hovout hovalid
  have hBodyLen : bansfBody.length = 177 := by decide +kernel
  apply abiFrame_spec_own B sp0 ret (-80 : BitVec 12) (80 : BitVec 12)
    bansfFrame (0 : BitVec 12)
    [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]
    vals bansfBody
    (101 + (372 + (((98 * (aLen + 1) + 700) +
      2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2)))
    (bansfCallerPre aB (sp0 + signExtend12 (-80 : BitVec 12)) oB
      aLen acctBytes F)
    (bansfVerdictResult aB (sp0 + signExtend12 (-80 : BitVec 12)) oB
      aLen acctBytes F) bansfCR
  · rfl
  · decide
  · decide
  · rw [← bansf_prog_eq_abiFrame]
    decide +kernel
  · exact hret
  · exact halignRet
  · rw [show signExtend12 (-80 : BitVec 12) = (-80 : Word) by decide,
        show signExtend12 (80 : BitVec 12) = (80 : Word) by decide]
    bv_omega
  · exact bansfCallerPre_pcFree aB
      (sp0 + signExtend12 (-80 : BitVec 12)) oB aLen acctBytes F hF
  · exact bansfVerdictResult_pcFree aB
      (sp0 + signExtend12 (-80 : BitVec 12)) oB aLen acctBytes F hF
  · intro a i hi
    rw [← bansf_prog_eq_abiFrame] at hi
    unfold bansfCR
    exact CodeReq.union_mono_left a i hi
  · simpa only [bansfFrame, List.length_cons, List.length_nil, hBodyLen,
      Nat.reduceAdd, Nat.reduceMul] using hbody


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
