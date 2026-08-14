/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashMismatch

  Dword0-mismatch residual + adapter for `header_validate_parent_hash`
  (status = 2). Same namespace as `HeaderValidateParentHashSpec`.
-/

import EvmAsm.Codegen.Programs.HeaderValidateParentHashKeccak

namespace EvmAsm.Codegen.HeaderValidateParentHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)

set_option maxRecDepth 8000 in
/-- Concrete-scratch helper for `hvphFromCompareSetupMismatch0`. -/
theorem hvphFromCompareSetupMismatch0_vals
    (sp0 spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (old5 old6 v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    let saved := hvphFrameVals ret vals
    cpsTripleWithin 14 (H + 72) (saved .x1) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  intro saved
  let cur : Reg → Word := fun r =>
    if r = .x1 then link else if r = .x8 then parentPtr else
    if r = .x9 then parentLen else if r = .x18 then vals .x18 else (0 : Word)
  have hsetup0 := hvphCompareSetup spC ret link parentPtr parentLen vals old5 old6
  have hsetup := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hsetup0
  have hexit := hvphCompareMismatch0Exit sp0 spC ret saved cur
    claimedBytes computedBytes v7 v28 o10 G hG hspC
    (by simpa [saved, hvphFrameVals] using hret) hclen hcdlen h_ne
  have hregs : regsAt hvphFrame cur =
      ((.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
        (.x18 ↦ᵣ vals .x18)) := by
    simp [cur, hvphFrame, regsAt, sepConj_emp_right']
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [hregs]
    xperm_hyp hp) hsetup hexit
  have hn : 4 + 10 = 14 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [saved, hvphFrameVals] at hq ⊢
      xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- From `H+72`: `la` ptrs ;; first-dword mismatch ;; status-2. Cost `14`.
    Scratch `x5/x6/x7/x28` are `regOwn`. -/
theorem hvphFromCompareSetupMismatch0
    (sp0 spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    let saved := hvphFrameVals ret vals
    cpsTripleWithin 14 (H + 72) (saved .x1) hvphCode
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
          (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
          (.x10 ↦ᵣ o10) **
          frameSlotsSaved hvphFrame spC saved **
          claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G **
          regOwn .x5 ** regOwn .x6) **
        regOwn .x7 ** regOwn .x28)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  intro saved
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x28)
    (fun v7 v28 => ?_)
  refine cpsTripleWithin_weaken
    (P := (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ o10) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
      regOwn .x5 ** regOwn .x6))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x5) (r2 := .x6)
    (fun old5 old6 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
      (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
      (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
      (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
      frameSlotsSaved hvphFrame spC saved **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  simpa [saved] using
    hvphFromCompareSetupMismatch0_vals sp0 spC ret link parentPtr parentLen vals
      claimedBytes computedBytes old5 old6 v7 v28 o10 G hG hspC hret
      hclen hcdlen h_ne


set_option maxRecDepth 8000 in
/-- Keccak setup+call (`H+52`) ;; first-dword mismatch exit. Cost `19+nK`. -/
theorem hvphKeccakThenMismatch0
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (old10 old11 old12 v20 v28 v29 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    cpsTripleWithin (19 + nKeccak N rem) (H + 52) (saved .x1) fullCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (H + 40)) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x20 ↦ᵣ v20) **
        frameSlotsSaved hvphFrame spC saved **
        stackFree spC 4 **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
        bytesRegion parentPtr parentBytes **
        bytesRegion Computed out0 **
        claimedOwn claimedBytes ** F)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion ** F)) := by
  intro digest kvals out0 saved
  have hcdlen : digest.length = 32 := by
    simp only [digest, keccakBodyDigest]
    exact keccakDigestCopy_length _
  have hcall := hvphKeccakSetupAndCall spC ret (H + 40) parentPtr parentLen vals
    old10 old11 old12 v20 v28 v29 parentBytes N rem os
    (claimedOwn claimedBytes ** F)
    (by refine pcFree_sepConj ?_ hF; exact bytesRegion_pcFree _ _)
    hplen hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  set Gmm : Assertion :=
    (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
      (.x20 ↦ᵣ v20) **
      bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
        (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
          (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
      keccakCallerFreeA parentPtr parentBytes N empAssertion ** F)
  have hG : Gmm.pcFree := by
    unfold Gmm
    refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj (bytesRegion_pcFree _ _)
      (pcFree_sepConj ?_ (pcFree_sepConj (pcFree_regOwns _)
        (pcFree_sepConj (keccakCallerFreeA_pcFree _ _ _ _ (by pcf)) hF)))))
      <;> pcf
  have hmm0 := hvphFromCompareSetupMismatch0 sp0 spC ret (H + 72) parentPtr parentLen vals
    claimedBytes digest (0 : Word) Gmm hG hspC hret hclen hcdlen h_ne
  have hmm := cpsTripleWithin_extend_code hvph_mono hmm0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold keccakCallerPost at hp
    have hregs : regsAt keccakFrame kvals =
        ((.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
          (.x20 ↦ᵣ v20)) := by
      simp [kvals, keccakEntryVals, keccakFrame, regsAt, sepConj_emp_right']
    rw [hregs] at hp
    have hcsrs :
        regOwns keccakCsrsRestNoX5 =
          (regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]) := by
      simp only [regOwns, keccakCsrsRestNoX5, sepConj_emp_right']
    rw [hcsrs] at hp
    unfold Gmm
    xperm_hyp hp) hcall hmm
  have hn : (5 + nKeccak N rem) + 14 = 19 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [saved, out0] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest, Gmm] at hq ⊢
    xperm_hyp hq) hall


set_option maxRecDepth 8000 in
/-- Concrete-scratch helper: `H+40` beq-ok ;; keccak ;; dword0-mismatch. Cost `20+nK`. -/
theorem hvphFromHeadersMismatch0_vals
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (old11 old12 v20 v28 v29 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (thisPtr : Word) (thisBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0
      (bytesRegion thisPtr thisBytes ** F)
    cpsTripleWithin (20 + nKeccak N rem) (H + 40) (saved .x1) fullCode
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedBytes **
        headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  have hAmb : Amb.pcFree :=
    hvphSuccKeccakAmb_pcFree spC v20 os out0 _
      (by refine pcFree_sepConj (bytesRegion_pcFree _ _) hF)
  have hbeq0 := hvphBeqExtractOk
  have hbeq := cpsTripleWithin_extend_code hvph_mono hbeq0
  have hbeqF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** claimedOwn claimedBytes **
      headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb)
    (by
      refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
        (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hAmb))))))
      · pcf
      · exact bytesRegion_pcFree _ _
      · unfold headersCallFrameSuccCore; pcf
      · pcf
      · pcf
      · pcf
      · pcf) hbeq
  have hkm := hvphKeccakThenMismatch0 sp0 spC ret parentPtr parentLen vals
    (0 : Word) old11 old12 v20 v28 v29 parentBytes claimedBytes N rem os
    (bytesRegion thisPtr thisBytes ** F)
    (by refine pcFree_sepConj (bytesRegion_pcFree _ _) hF)
    hspC hret hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h_ne
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold headersCallFrameSuccCore Amb hvphSuccKeccakAmb at hp
    simp only [out0, regOwns, keccakBodyFreeTemps, sepConj_emp_right'] at hp ⊢
    xperm_hyp hp) hbeqF hkm
  have hn : 1 + (19 + nKeccak N rem) = 20 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [Amb] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest] at hq ⊢
    xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- From `H+40` with status 0: beq-ok ;; keccak ;; dword0-mismatch. Cost `20+nK`. -/
theorem hvphFromHeadersMismatch0
    (sp0 spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (thisPtr : Word) (thisBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0
      (bytesRegion thisPtr thisBytes ** F)
    cpsTripleWithin (20 + nKeccak N rem) (H + 40) (saved .x1) fullCode
      ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn claimedBytes **
            headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
            Amb) **
          regOwn .x11 ** regOwn .x12) **
        regOwn .x28 ** regOwn .x29)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x28) (r2 := .x29)
    (fun v28 v29 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          claimedOwn claimedBytes **
          headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
          Amb) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29)) **
      regOwn .x11 ** regOwn .x12))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x11) (r2 := .x12)
    (fun old11 old12 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      claimedOwn claimedBytes **
      headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) ** Amb))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  simpa [digest, kvals, out0, saved, Amb] using
    hvphFromHeadersMismatch0_vals sp0 spC ret parentPtr parentLen vals
      old11 old12 v20 v28 v29 parentBytes claimedBytes N rem os
      thisPtr thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hclen h_ne


set_option maxRecDepth 8000 in
/-- Full dword0-mismatch residual: prologue+headers ;; beq-ok ;; keccak ;; mismatch0.
    Cost `30+nH+nK`. Requires `statusHdr = 0` and claimed dword0 ≠ digest. -/
theorem hvphMismatch0_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_headers : headersCallPremise nH (H + 40) (0 : Word) thisPtr thisLen
      thisBytes claimedBytes claimedBytes
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes))
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    let out0 := List.replicate 32 (0 : BitVec 8)
    let saved := hvphFrameVals ret vals
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + nH + nKeccak N rem) H (saved .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
  intro digest kvals out0 saved Amb
  have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
  have hph0 := hvphPrologueHeaders nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    (0 : Word) vals thisBytes parentBytes claimedBytes claimedBytes hspC h_headers
  have hph := cpsTripleWithin_frameR Amb hAmb hph0
  have hmm := hvphFromHeadersMismatch0 sp0 spC ret parentPtr parentLen vals
    v20 parentBytes claimedBytes N rem os thisPtr thisBytes F hF
    hspC hret hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h_ne
  have hphW :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
      unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
      let Rest : Assertion :=
        (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          claimedOwn claimedBytes ** bytesRegion thisPtr thisBytes **
          (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x30 ** regOwn .x31 **
          (.x20 ↦ᵣ v20) ** stackFree spC 4 **
          regOwns [.x14, .x15, .x16, .x17] **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
          bytesRegion Computed out0 ** F **
          regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
      have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
        simp only [Rest]
        xperm_hyp hq
      have hqOwn : (Rest ** regOwn .x13) s :=
        sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
      change
        (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              claimedOwn claimedBytes **
              headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
              hvphSuccKeccakAmb spC v20 os out0
                (bytesRegion thisPtr thisBytes ** F)) **
            regOwn .x11 ** regOwn .x12) **
          regOwn .x28 ** regOwn .x29) s)
      · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
        simp only [Rest] at hqOwn
        xperm_hyp hqOwn) hph
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [out0] at hp ⊢
    xperm_hyp hp) hphW hmm
  have hn : (9 + (1 + nH)) + (20 + nKeccak N rem) = 30 + nH + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [Amb] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [saved, digest] at hq ⊢
    xperm_hyp hq) hall


set_option maxRecDepth 8000 in
/-- Dword0-mismatch path in adapter shape. Cost `30+nH+nK`. Status `2`. -/
theorem header_validate_parent_hash_mismatch0_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
    (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes claimedBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_headers : headersCallPremise nH (H + 40) (0 : Word) thisPtr thisLen
      thisBytes claimedBytes claimedBytes
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes))
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (hclen : claimedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + nH + nKeccak N rem) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn claimedBytes ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (2 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals
          parentBytes claimedBytes digest N rem F) := by
  intro digest out0 Amb
  have hmm := hvphMismatch0_spec_within nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    vals v20 thisBytes parentBytes claimedBytes N rem os F hF
    hspC hret h_headers hplen hlen hrem_le hos
    halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
    hclen h_ne
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hmm
  · unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · simpa [digest, Amb] using
      hvphKeccakExit_post_to_adapter sp0 spC ret parentPtr parentLen v20
        (2 : Word) (dwordAt claimedBytes 0) (dwordAt digest 0) vals
        thisPtr thisBytes parentBytes claimedBytes N rem F hspC hlen s hq

end EvmAsm.Codegen.HeaderValidateParentHashSpec
