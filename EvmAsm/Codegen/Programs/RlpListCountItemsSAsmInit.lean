import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmFrame

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-- Nth `.init` → count `.init`. -/
theorem nthFailure_init_to_countFailure {bytes : List (BitVec 8)} {base : Word}
    {listLen : Nat}
    (h_invalid : ¬ ∃ cursorOff endPtr,
      RlpListNthItemSAsm.StrictListPayload bytes base listLen cursorOff endPtr) :
    Failure bytes base listLen :=
  .init h_invalid

/-- Still-inside nth walk → count walk Failure. -/
theorem nthFailure_walk_to_countFailure {bytes : List (BitVec 8)} {base : Word}
    {listLen cursorOff count off : Nat} {endPtr : Word}
    (h_list : RlpListNthItemSAsm.StrictListPayload bytes base listLen cursorOff endPtr)
    (h_prefix : RlpListNthItemSAsm.StrictPrefix bytes base endPtr cursorOff count off)
    (h_inside : BitVec.ult (base + BitVec.ofNat 64 off) endPtr = true)
    (h_fail : RlpListNthItemSAsm.WalkFailure bytes off
      (base + BitVec.ofNat 64 off) endPtr) :
    Failure bytes base listLen :=
  .walk cursorOff count off endPtr h_list h_prefix h_inside h_fail

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

/-- Map walk_init initOutcome → count initNormalized.
    Fail arms rebuild `Failure.init` from the same pure facts as nth
    (no `.walk` — walk_init never produces nth Failure.walk). -/
theorem initOutcome_to_normalized (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (hoff : 0 < bytes.length)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64) : ∀ h,
    RlpListNthItemSAsm.initOutcome listBase bytes listLen hoff h →
      initNormalized listBase bytes listLen h := by
  intro h hp
  unfold RlpListNthItemSAsm.initOutcome at hp
  unfold initNormalized
  rcases hp with h0 | h1 | hs | h3 | h4 | h5 | h6 | h7 | hl
  · have hword : BitVec.ofNat 64 listLen = (0 : Word) :=
      RlpListNthItemSAsm.threeRegs_pure h h0
    have hlen : listLen = 0 := by
      have hw := congrArg BitVec.toNat hword
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hw
      simpa using hw
    refine Or.inr ⟨2, listBase, 0, ?_⟩
    have hf : Failure bytes listBase listLen := by
      subst listLen
      exact .init (RlpListNthItemSAsm.noStrictList_of_empty bytes listBase)
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h0
  · have hc : BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
        BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true :=
      RlpListNthItemSAsm.threeRegs_pure h h1
    refine Or.inr ⟨1, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen :=
      .init (RlpListNthItemSAsm.noStrictList_of_notlist bytes listBase listLen hoff hc.2)
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h1
  · have hc := RlpListNthItemSAsm.threeRegs_pure h hs
    obtain ⟨_, hnot, hshort, hend⟩ := hc
    have hlist := RlpListNthItemSAsm.shortInit_to_strict bytes listBase listLen hoff
      (by omega) hnot hshort hend
    refine Or.inl ⟨1, listBase + BitVec.ofNat 64 listLen, ?_⟩
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 by decide] at hs
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => hlist) h hs
  · have hc := RlpListNthItemSAsm.threeRegs_pure h h3
    obtain ⟨_, _, hshort, hm⟩ := hc
    refine Or.inr ⟨3, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen := .init
      (RlpListNthItemSAsm.noStrictList_of_short_mismatch bytes listBase listLen hoff
        (by omega) hshort hm)
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h3
  · have hc := RlpListNthItemSAsm.threeRegs_pure h h4
    obtain ⟨_, _, hlong, htrunc⟩ := hc
    refine Or.inr ⟨4, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen := .init
      (RlpListNthItemSAsm.noStrictList_of_long_header_truncated bytes listBase listLen
        hoff h_slack h_over hlong htrunc)
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h4
  · have hc := RlpListNthItemSAsm.threeRegs_pure h h5
    obtain ⟨_, _, hlong, _, hzero⟩ := hc
    refine Or.inr ⟨5, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen := .init
      (RlpListNthItemSAsm.noStrictList_of_long_leading_zero bytes listBase listLen
        hoff hlong hzero)
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h5
  · have hc := RlpListNthItemSAsm.threeRegs_pure h h6
    obtain ⟨_, _, hlong, _, _, hmin⟩ := hc
    refine Or.inr ⟨6, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen := .init
      (RlpListNthItemSAsm.noStrictList_of_long_nonminimal bytes listBase listLen
        hoff hlong hmin)
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h6
  · have hc := RlpListNthItemSAsm.threeRegs_pure h h7
    obtain ⟨_, _, hlong, _, _, _, hm⟩ := hc
    refine Or.inr ⟨7, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen := .init
      (RlpListNthItemSAsm.noStrictList_of_long_mismatch bytes listBase listLen
        hoff hlong hm)
    exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h7
  · -- long success (dual nth initOutcome_to_normalized long arm)
    have hc := RlpListNthItemSAsm.threeRegs_pure h hl
    obtain ⟨_, _, hlong, hfit, hbNZ, hmin, hend⟩ := hc
    have hoff1 : 1 < bytes.length := by omega
    have hfirst : bytes[1]? = some (bytes[1]'hoff1) := List.getElem?_eq_getElem hoff1
    have hnz : bytes[1]'hoff1 ≠ 0 := by
      intro hz
      apply hbNZ
      rw [hfirst, hz]
    have hminimal :=
      RlpListNthItemSAsm.longDecode_minimal_of_not_ult bytes hoff hlong hmin
    let cursorOff := 1 +
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
    have hlist := RlpListNthItemSAsm.longInit_to_strict bytes listBase listLen hoff
      h_slack h_over hlong hfit hfirst hnz hminimal hend
    have hcursor : listBase +
        (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = listBase + BitVec.ofNat 64 cursorOff := by
      unfold cursorOff
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
      have hb := (bytes[0]'hoff).isLt
      have hge := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le hlong
      bv_omega
    rw [hcursor] at hl
    exact Or.inl ⟨cursorOff, listBase + BitVec.ofNat 64 listLen, by
      exact RlpListNthItemSAsm.threeRegs_pure_mono (fun _ => hlist) h hl⟩


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
    (fun h_f8 => by
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 => by
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 => by
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
