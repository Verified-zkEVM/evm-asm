import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmFrame

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

theorem nthFailure_to_countFailure {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat}
    (h_failure : RlpListNthItemSAsm.Failure bytes base listLen index) :
    Failure bytes base listLen := by
  cases h_failure with
  | init h_invalid => exact .init h_invalid
  | walk cursorOff count off endPtr h_list _ h_prefix h_fail =>
      exact .walk cursorOff count off endPtr h_list h_prefix h_fail

def initStable (newSp listBase outPtr oldCount : Word) (saved : Saved) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** savedFrame newSp saved **
  (outPtr ↦ₘ oldCount)

def initCommon (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 36)) ** bytesRegion listBase bytes

def initNormalized (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) : Assertion := fun h =>
  (∃ cursorOff endPtr,
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      ⌜RlpListNthItemSAsm.StrictListPayload bytes listBase listLen
        cursorOff endPtr⌝) h)) ∨
  (∃ status cursor endPtr,
    (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
      ⌜status ≠ 0 ∧ Failure bytes listBase listLen⌝) h))

theorem initOutcome_to_normalized (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (hoff : 0 < bytes.length)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64) : ∀ h,
    RlpListNthItemSAsm.initOutcome listBase bytes listLen hoff h →
      initNormalized listBase bytes listLen h := by
  intro h h_outcome
  have h_norm := RlpListNthItemSAsm.initOutcome_to_normalized
    listBase bytes listLen 0 hoff h_slack h_over h h_outcome
  unfold RlpListNthItemSAsm.initNormalized at h_norm
  unfold initNormalized
  rcases h_norm with h_success | h_failure
  · exact Or.inl h_success
  · rcases h_failure with ⟨status, cursor, endPtr, h_body⟩
    refine Or.inr ⟨status, cursor, endPtr, ?_⟩
    exact RlpListNthItemSAsm.threeRegs_pure_mono
      (fun hp => ⟨hp.1, nthFailure_to_countFailure hp.2⟩) h h_body

theorem initCallExact (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (outPtr : Word)
    (v5 v6 v7 v28 v29 v30 v31 oldRa : Word)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 82 (B + 32) (B + 36) code
      ((.x1 ↦ᵣ oldRa) **
       ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
        (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes))
      ((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        RlpListNthItemSAsm.initOutcome listBase bytes listLen (by omega)) := by
  have hoff : 0 < bytes.length := by omega
  have hwi := rlp_walk_init_spec_within WI listBase (B + 36)
    (BitVec.ofNat 64 listLen) outPtr v5 v6 v7 v28 v29 v30 v31 bytes 0
    h_align hoff (by omega) (h_valid 0 hoff)
    (fun h_f8 _ => by
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 _ => by
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 _ => by
      intro k hk
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      exact h_valid _ (by omega))
  rw [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at hwi
  let Prest : Assertion :=
    (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
    (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion listBase bytes
  let Q : Assertion :=
    (initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
      RlpListNthItemSAsm.initOutcome listBase bytes listLen hoff
  have hwi' : cpsTripleWithin 81 WI ((B + 36) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 36)) ** Prest) Q :=
    cpsTripleWithin_weaken
      (fun h hp => by unfold Prest at hp; xperm_hyp hp)
      (fun h hp => by
        unfold Q initCommon RlpListNthItemSAsm.initOutcome
        simp only [Nat.zero_add] at hp ⊢
        xperm_hyp hp) hwi
  have hc := callWalkInit oldRa (by unfold Prest; pcf) hwi'
  simpa [Prest, Q] using hc


end EvmAsm.Codegen.RlpListCountItemsSAsm
