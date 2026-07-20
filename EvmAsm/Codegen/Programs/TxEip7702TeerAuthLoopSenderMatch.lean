/-
  Teer auth-loop AfterLi20Nj (E+2040): 20B authority==sender memcmp
  (fail-fast) + addi x6,x6,1 on full match → AfterAuthSenderInc (E+2076).

  Dual OrZero body×20 under bytesRegion; success path only (authBytes=senderBytes).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopNonceJoin
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopOrZero
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SAsm.MeasureLoop

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Rv64.AddrNorm (se12_1)
open EvmAsm.Rv64.SAsm (cpsTripleWithin_of_forall_regIs_to_regOwn2)

set_option maxRecDepth 8000

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

abbrev AfterSmBeqNtaken : Word := E + 2044
abbrev AfterSmLbuAuth : Word := E + 2048
abbrev AfterSmLbuSend : Word := E + 2052
abbrev AfterSmBneNtaken : Word := E + 2056
abbrev AfterSmAddiAuth : Word := E + 2060
abbrev AfterSmAddiSend : Word := E + 2064
abbrev AfterSmAddiCnt : Word := E + 2068
abbrev AfterSmAddiNonce : Word := E + 2072

abbrev teerSmCntBeqOff : BitVec 13 := (32 : BitVec 13)
abbrev teerSmBneOff : BitVec 13 := (24 : BitVec 13)
abbrev teerSmJalBack : BitVec 21 := (-28 : BitVec 21)

theorem teerSmCntBeqOff_taken :
    AfterLi20Nj + signExtend13 teerSmCntBeqOff = AfterSmAddiNonce := by
  simp only [AfterLi20Nj, AfterSmAddiNonce, teerSmCntBeqOff, E]; decide

theorem teerSmBneOff_taken :
    AfterSmLbuSend + signExtend13 teerSmBneOff = AfterAuthSenderInc := by
  simp only [AfterSmLbuSend, AfterAuthSenderInc, teerSmBneOff, E]; decide

theorem teerSmJalBack_eq :
    AfterSmAddiCnt + signExtend21 teerSmJalBack = AfterLi20Nj := by
  simp only [AfterSmAddiCnt, AfterLi20Nj, teerSmJalBack, E]; decide

/-- Loop ambient: dual ptrs + temps + two blobs. -/
def teerSmInvAmb (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  (.x6 ↦ᵣ nonceVal) **
    (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
    (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
    regOwn .x30 ** regOwn .x31 **
    bytesRegion authPtr authBytes **
    bytesRegion sendPtr senderBytes

/-- Inv at header: (cnt ** x0) left for BEQ. -/
def teerSmInv (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  (((.x29 ↦ᵣ BitVec.ofNat 64 (authBytes.length - i)) ** (.x0 ↦ᵣ (0 : Word))) **
    teerSmInvAmb authPtr sendPtr nonceVal authBytes senderBytes i)

/-- Counter BEQ taken (cnt=0) → AfterSmAddiNonce. -/
theorem teerSmCntBeqTaken :
    cpsTripleWithin 1 AfterLi20Nj AfterSmAddiNonce teerLinkedField0
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerSmCntBeqOff
    (0 : Word) (0 : Word) AfterLi20Nj
  rw [teerSmCntBeqOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLi20Nj teerProg 510
          (.BEQ .x29 .x0 teerSmCntBeqOff)
          (by simp only [AfterLi20Nj]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- Counter BEQ ntaken (cnt≠0) → AfterSmBeqNtaken. -/
theorem teerSmCntBeqNtaken (cnt : Word) (hne : cnt ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterLi20Nj AfterSmBeqNtaken teerLinkedField0
      ((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerSmCntBeqOff
    cnt (0 : Word) AfterLi20Nj
  change cpsBranchWithin _ _ _ _ _ _ (AfterLi20Nj + 4) _ at hbr
  have hnt := cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLi20Nj teerProg 510
          (.BEQ .x29 .x0 teerSmCntBeqOff)
          (by simp only [AfterLi20Nj]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)
  have hpc : (AfterLi20Nj + 4 : Word) = AfterSmBeqNtaken := by
    simp only [AfterLi20Nj, AfterSmBeqNtaken]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- BNE ntaken when bytes equal (success continue). -/
theorem teerSmBneNtaken (b : Word) :
    cpsTripleWithin 1 AfterSmLbuSend AfterSmBneNtaken teerLinkedField0
      ((.x30 ↦ᵣ b) ** (.x31 ↦ᵣ b))
      ((.x30 ↦ᵣ b) ** (.x31 ↦ᵣ b)) := by
  have hbr := bne_spec_gen_within .x30 .x31 teerSmBneOff b b AfterSmLbuSend
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSmLbuSend teerProg 513
        (.BNE .x30 .x31 teerSmBneOff)
        (by simp only [AfterSmLbuSend]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterSmLbuSend + 4 = AfterSmBneNtaken := by
    simp only [AfterSmLbuSend, AfterSmBneNtaken]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- Body: LBU auth, LBU send, BNE ntaken, ADDI×3 (6 steps, equal bytes). -/
theorem teerSmBody6
    (authPtr sendPtr nonceVal baOld bsOld cnt : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat)
    (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hi : i < authBytes.length)
    (hoverA : authPtr.toNat + i < 2 ^ 64)
    (hoverS : sendPtr.toNat + i < 2 ^ 64)
    (hvalidA : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true)
    (hvalidS : isValidByteAccess (sendPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 6 AfterSmBeqNtaken AfterSmAddiCnt teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ baOld) ** (.x31 ↦ᵣ bsOld) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
        (.x29 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
        (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
        (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) := by
  set byteZ := (authBytes[i]'hi).zeroExtend 64
  have hiS : i < senderBytes.length := by simpa [heq] using hi
  have hbyteS : (senderBytes[i]'hiS).zeroExtend 64 = byteZ := by
    simp only [byteZ]
    have : senderBytes[i]'hiS = authBytes[i]'hi := by
      simp only [heq]
    simp only [this]
  -- LBU auth x30
  have lbuA := bytesRegion_lbu_within .x30 .x7 authPtr baOld AfterSmBeqNtaken
    authBytes i (by decide) halignA hi hoverA hvalidA
  have s1 : cpsTripleWithin 1 AfterSmBeqNtaken AfterSmLbuAuth teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ baOld) ** (.x31 ↦ᵣ bsOld) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ bsOld) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ nonceVal) ** (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) ** (.x31 ↦ᵣ bsOld) ** bytesRegion sendPtr senderBytes)
      (by pcf) lbuA
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterSmBeqNtaken teerProg 511
          (.LBU .x30 .x7 (0 : BitVec 12))
          (by simp only [AfterSmBeqNtaken]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterSmBeqNtaken + 4 : Word) = AfterSmLbuAuth := by
      simp only [AfterSmBeqNtaken, AfterSmLbuAuth]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  -- LBU send x31
  have lbuS := bytesRegion_lbu_within .x31 .x28 sendPtr bsOld AfterSmLbuAuth
    senderBytes i (by decide) halignS hiS hoverS hvalidS
  have s2 : cpsTripleWithin 1 AfterSmLbuAuth AfterSmLbuSend teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ bsOld) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** bytesRegion authPtr authBytes)
      (by pcf) lbuS
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterSmLbuAuth teerProg 512
          (.LBU .x31 .x28 (0 : BitVec 12))
          (by simp only [AfterSmLbuAuth]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterSmLbuAuth + 4 : Word) = AfterSmLbuSend := by
      simp only [AfterSmLbuAuth, AfterSmLbuSend]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
        have hq2 :
            ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
              (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** bytesRegion authPtr authBytes **
              (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
              (.x31 ↦ᵣ ((senderBytes[i]'hiS).zeroExtend 64)) **
              bytesRegion sendPtr senderBytes) s := by xperm_hyp hq
        have hq3 :
            ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
              (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** bytesRegion authPtr authBytes **
              (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
              (.x31 ↦ᵣ byteZ) **
              bytesRegion sendPtr senderBytes) s := by
          simpa only [hbyteS] using hq2
        xperm_hyp hq3) h1
  -- BNE ntaken
  have s3 : cpsTripleWithin 1 AfterSmLbuSend AfterSmBneNtaken teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) ** (.x29 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes)
      (by pcf) (teerSmBneNtaken byteZ)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  -- ADDI x7 +1
  have addiA := addi_spec_gen_same_within .x7 (authPtr + BitVec.ofNat 64 i)
    1 AfterSmBneNtaken (by nofun)
  have hptrA : (authPtr + BitVec.ofNat 64 i) + (1 : Word) =
      authPtr + BitVec.ofNat 64 (i + 1) := by
    rw [teer_word_ofNat_add_one i]; bv_omega
  have s4 : cpsTripleWithin 1 AfterSmBneNtaken AfterSmAddiAuth teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ nonceVal) ** (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes)
      (by pcf) addiA
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterSmBneNtaken teerProg 514
          (.ADDI .x7 .x7 (1 : BitVec 12))
          (by simp only [AfterSmBneNtaken]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterSmBneNtaken + 4 : Word) = AfterSmAddiAuth := by
      simp only [AfterSmBneNtaken, AfterSmAddiAuth]; bv_omega
    rw [hpc, se12_1] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
        have hq2 :
            ((.x6 ↦ᵣ nonceVal) ** (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
              (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
              bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes **
              (.x7 ↦ᵣ ((authPtr + BitVec.ofNat 64 i) + (1 : Word)))) s := by
          xperm_hyp hq
        have hq3 :
            ((.x6 ↦ᵣ nonceVal) ** (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
              (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
              bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes **
              (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1)))) s := by
          simpa only [hptrA] using hq2
        xperm_hyp hq3) h1
  -- ADDI x28 +1
  have addiS := addi_spec_gen_same_within .x28 (sendPtr + BitVec.ofNat 64 i)
    1 AfterSmAddiAuth (by nofun)
  have hptrS : (sendPtr + BitVec.ofNat 64 i) + (1 : Word) =
      sendPtr + BitVec.ofNat 64 (i + 1) := by
    rw [teer_word_ofNat_add_one i]; bv_omega
  have s5 : cpsTripleWithin 1 AfterSmAddiAuth AfterSmAddiSend teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes)
      (by pcf) addiS
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterSmAddiAuth teerProg 515
          (.ADDI .x28 .x28 (1 : BitVec 12))
          (by simp only [AfterSmAddiAuth]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterSmAddiAuth + 4 : Word) = AfterSmAddiSend := by
      simp only [AfterSmAddiAuth, AfterSmAddiSend]; bv_omega
    rw [hpc, se12_1] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
        have hq2 :
            ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
              (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
              bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes **
              (.x28 ↦ᵣ ((sendPtr + BitVec.ofNat 64 i) + (1 : Word)))) s := by
          xperm_hyp hq
        have hq3 :
            ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
              (.x29 ↦ᵣ cnt) ** (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
              bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes **
              (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1)))) s := by
          simpa only [hptrS] using hq2
        xperm_hyp hq3) h1
  -- ADDI x29 -1
  have addiC := addi_spec_gen_same_within .x29 cnt (-1) AfterSmAddiSend (by nofun)
  have s6 : cpsTripleWithin 1 AfterSmAddiSend AfterSmAddiCnt teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
        (.x29 ↦ᵣ cnt) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
        (.x29 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
        (.x30 ↦ᵣ byteZ) ** (.x31 ↦ᵣ byteZ) **
        bytesRegion authPtr authBytes ** bytesRegion sendPtr senderBytes)
      (by pcf) addiC
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterSmAddiSend teerProg 516
          (.ADDI .x29 .x29 (-1 : BitVec 12))
          (by simp only [AfterSmAddiSend]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterSmAddiSend + 4 : Word) = AfterSmAddiCnt := by
      simp only [AfterSmAddiSend, AfterSmAddiCnt]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 s2
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 s3
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 s4
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 s5
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c45 s6

/-- Body6 with x30/x31 owned via of_forall2 (P ** r1 ** r2). -/
theorem teerSmBody6_own
    (authPtr sendPtr nonceVal cnt : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat)
    (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hi : i < authBytes.length)
    (hoverA : authPtr.toNat + i < 2 ^ 64)
    (hoverS : sendPtr.toNat + i < 2 ^ 64)
    (hvalidA : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true)
    (hvalidS : isValidByteAccess (sendPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 6 AfterSmBeqNtaken AfterSmAddiCnt teerLinkedField0
      (((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
        (.x29 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes) ** regOwn .x30 ** regOwn .x31)
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
        (.x29 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes **
        (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
        (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64))) := by
  exact cpsTripleWithin_of_forall_regIs_to_regOwn2
    (r1 := .x30) (r2 := .x31)
    (P := (.x6 ↦ᵣ nonceVal) **
      (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
      (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
      (.x29 ↦ᵣ cnt) **
      bytesRegion authPtr authBytes **
      bytesRegion sendPtr senderBytes)
    (fun baOld bsOld =>
      cpsTripleWithin_weaken
        (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq)
        (teerSmBody6 authPtr sendPtr nonceVal baOld bsOld cnt
          authBytes senderBytes i heq halignA halignS hi hoverA hoverS
          hvalidA hvalidS))

/-- JAL x0 -28: AfterSmAddiCnt → AfterLi20Nj. -/
theorem teerSmJalBackTrip (P : Assertion) (hpc : P.pcFree) :
    cpsTripleWithin 1 AfterSmAddiCnt AfterLi20Nj teerLinkedField0 P P := by
  have h0 := jal_x0_spec_gen_within teerSmJalBack AfterSmAddiCnt
  rw [teerSmJalBack_eq] at h0
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSmAddiCnt teerProg 517
        (.JAL .x0 teerSmJalBack)
        (by simp only [AfterSmAddiCnt]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 := cpsTripleWithin_frameR P hpc h1
  exact cpsTripleWithin_weaken
    (fun s hp => (sepConj_emp_left _).2 hp)
    (fun s hq => (sepConj_emp_left _).1 hq) h2

/-- One full iteration: BEQ ntaken + body6 + JAL → inv i → inv (i+1). -/
theorem teerSmBodyIter
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat)
    (hlen : authBytes.length = 20) (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hi : i < authBytes.length)
    (hoverA : authPtr.toNat + i < 2 ^ 64)
    (hoverS : sendPtr.toNat + i < 2 ^ 64)
    (hvalidA : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true)
    (hvalidS : isValidByteAccess (sendPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 8 AfterLi20Nj AfterLi20Nj teerLinkedField0
      (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes i)
      (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes (i + 1)) := by
  set cnt := BitVec.ofNat 64 (authBytes.length - i)
  have hne : cnt ≠ (0 : Word) := by
    intro hc
    have hlt : authBytes.length - i < 2 ^ 64 := by omega
    have ht : cnt.toNat = authBytes.length - i := by
      simp only [cnt, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
    have ht0 : (0 : Word).toNat = 0 := rfl
    simp only [hc] at ht
    rw [ht0] at ht
    omega
  have hbneF : cpsTripleWithin 1 AfterLi20Nj AfterSmBeqNtaken teerLinkedField0
      (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes i)
      (((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) **
        teerSmInvAmb authPtr sendPtr nonceVal authBytes senderBytes i) := by
    have h0 := cpsTripleWithin_frameR
      (teerSmInvAmb authPtr sendPtr nonceVal authBytes senderBytes i)
      (by simp only [teerSmInvAmb]; pcf)
      (teerSmCntBeqNtaken cnt hne)
    exact cpsTripleWithin_weaken
      (fun s hp => by
        change (((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) **
          teerSmInvAmb authPtr sendPtr nonceVal authBytes senderBytes i) s
        dsimp only [teerSmInv, cnt] at hp
        exact hp)
      (fun _ hq => hq) h0
  have hbodyF : cpsTripleWithin 6 AfterSmBeqNtaken AfterSmAddiCnt teerLinkedField0
      (((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) **
        teerSmInvAmb authPtr sendPtr nonceVal authBytes senderBytes i)
      (((.x29 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ nonceVal) **
          (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
          (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
          (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
          (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes)) := by
    have hraw := teerSmBody6_own authPtr sendPtr nonceVal cnt
      authBytes senderBytes i heq halignA halignS hi hoverA hoverS hvalidA hvalidS
    have h0 := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hraw
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [teerSmInvAmb] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  have hjal := teerSmJalBackTrip
    (((.x29 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x6 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
        (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
        (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
        bytesRegion authPtr authBytes **
        bytesRegion sendPtr senderBytes))
    (by pcf)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbneF hbodyF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hjal
  have hcnt : cnt + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (authBytes.length - (i + 1)) := by
    have hk : 0 < authBytes.length - i := by omega
    simp only [cnt]
    have hrem : authBytes.length - (i + 1) = (authBytes.length - i) - 1 := by omega
    rw [hrem, teer_cnt_pred (authBytes.length - i) hk]
  have hpost :
      ∀ s,
        (((.x29 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x6 ↦ᵣ nonceVal) **
            (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
            (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
            (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
            (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
            bytesRegion authPtr authBytes **
            bytesRegion sendPtr senderBytes)) s →
        teerSmInv authPtr sendPtr nonceVal authBytes senderBytes (i + 1) s := by
    intro s hq
    have hq1 :
        (((.x29 ↦ᵣ BitVec.ofNat 64 (authBytes.length - (i + 1))) **
            (.x0 ↦ᵣ (0 : Word))) **
          ((.x6 ↦ᵣ nonceVal) **
            (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
            (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
            (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
            (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
            bytesRegion authPtr authBytes **
            bytesRegion sendPtr senderBytes)) s := by
      simpa only [hcnt] using hq
    have hq2 :
        (((.x29 ↦ᵣ BitVec.ofNat 64 (authBytes.length - (i + 1))) **
            (.x0 ↦ᵣ (0 : Word))) **
          ((.x6 ↦ᵣ nonceVal) **
            (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
            (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
            regOwn .x30 ** regOwn .x31 **
            bytesRegion authPtr authBytes **
            bytesRegion sendPtr senderBytes)) s := by
      refine sepConj_mono_right ?_ s hq1
      intro sR hR
      have hR1 :
          (((.x6 ↦ᵣ nonceVal) **
              (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
              (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
              bytesRegion authPtr authBytes **
              bytesRegion sendPtr senderBytes) **
            ((.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
              (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)))) sR := by
        xperm_hyp hR
      have hR2 :
          (((.x6 ↦ᵣ nonceVal) **
              (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
              (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
              bytesRegion authPtr authBytes **
              bytesRegion sendPtr senderBytes) **
            (regOwn .x30 ** regOwn .x31)) sR := by
        refine sepConj_mono_right ?_ sR hR1
        intro s2 h2
        have h2a :
            ((.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
              (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64))) s2 := h2
        have h2b :
            (regOwn .x30 ** (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64))) s2 :=
          sepConj_mono_left (regIs_implies_regOwn .x30) s2 h2a
        exact sepConj_mono_right (fun s3 h3 => regIs_implies_regOwn .x31 s3 h3) s2 h2b
      xperm_hyp hR2
    simpa only [teerSmInv, teerSmInvAmb] using hq2
  exact cpsTripleWithin_weaken (fun _ hp => hp) hpost c2

/-- Loop with remaining fuel `k` starting at index `20-k`. -/
theorem teerSmLoop_fuel
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8)) (k : Nat)
    (hlen : authBytes.length = 20) (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hk : k ≤ 20)
    (hvalidA : ∀ j, j < 20 →
      isValidByteAccess (authPtr + BitVec.ofNat 64 j) = true)
    (hvalidS : ∀ j, j < 20 →
      isValidByteAccess (sendPtr + BitVec.ofNat 64 j) = true)
    (hoverA : authPtr.toNat + 20 ≤ 2 ^ 64)
    (hoverS : sendPtr.toNat + 20 ≤ 2 ^ 64) :
    cpsTripleWithin (8 * k + 1) AfterLi20Nj AfterSmAddiNonce teerLinkedField0
      (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes (20 - k))
      (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes 20) := by
  induction k with
  | zero =>
      have h0 := cpsTripleWithin_frameR
        (teerSmInvAmb authPtr sendPtr nonceVal authBytes senderBytes 20)
        (by simp only [teerSmInvAmb]; pcf)
        teerSmCntBeqTaken
      exact cpsTripleWithin_weaken
        (fun s hp => by
          change (((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            teerSmInvAmb authPtr sendPtr nonceVal authBytes senderBytes 20) s
          dsimp only [teerSmInv] at hp
          simpa only [Nat.sub_zero, hlen, Nat.sub_self, teer_ofNat_zero_eq] using hp)
        (fun s hq => by
          change teerSmInv authPtr sendPtr nonceVal authBytes senderBytes 20 s
          dsimp only [teerSmInv]
          simpa only [hlen, Nat.sub_self, teer_ofNat_zero_eq] using hq)
        (by simpa only [Nat.mul_zero, Nat.zero_add] using h0)
  | succ m ih =>
      have hm : m ≤ 20 := by omega
      have hi : 20 - (m + 1) < authBytes.length := by omega
      have hoverAi : authPtr.toNat + (20 - (m + 1)) < 2 ^ 64 := by omega
      have hoverSi : sendPtr.toNat + (20 - (m + 1)) < 2 ^ 64 := by omega
      have hva := hvalidA (20 - (m + 1)) (by omega)
      have hvs := hvalidS (20 - (m + 1)) (by omega)
      have hstep := teerSmBodyIter authPtr sendPtr nonceVal authBytes senderBytes
        (20 - (m + 1)) hlen heq halignA halignS hi hoverAi hoverSi hva hvs
      have hidx : (20 - (m + 1)) + 1 = 20 - m := by omega
      have hstep' : cpsTripleWithin 8 AfterLi20Nj AfterLi20Nj teerLinkedField0
          (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes (20 - (m + 1)))
          (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes (20 - m)) := by
        simpa only [hidx] using hstep
      have hrest := ih hm
      have hseq := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hstep' hrest
      have hn : 8 + (8 * m + 1) = 8 * (m + 1) + 1 := by omega
      simpa only [hn] using hseq

/-- Full 20-iter memcmp under inv: AfterLi20Nj → AfterSmAddiNonce. -/
theorem teerSmLoop20
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8))
    (hlen : authBytes.length = 20) (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hoverA : authPtr.toNat + 20 ≤ 2 ^ 64)
    (hoverS : sendPtr.toNat + 20 ≤ 2 ^ 64)
    (hvalidA : ∀ k, k < 20 →
      isValidByteAccess (authPtr + BitVec.ofNat 64 k) = true)
    (hvalidS : ∀ k, k < 20 →
      isValidByteAccess (sendPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 161 AfterLi20Nj AfterSmAddiNonce teerLinkedField0
      (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes 0)
      (teerSmInv authPtr sendPtr nonceVal authBytes senderBytes 20) := by
  have hloop := teerSmLoop_fuel authPtr sendPtr nonceVal authBytes senderBytes 20
    hlen heq halignA halignS (by omega) hvalidA hvalidS hoverA hoverS
  have hn : 8 * 20 + 1 = 161 := by decide
  simpa only [Nat.sub_self, hn] using hloop

/-- `addi x6,x6,1` AfterSmAddiNonce → AfterAuthSenderInc. -/
theorem teerSmAddiNonce (nonceVal : Word) :
    cpsTripleWithin 1 AfterSmAddiNonce AfterAuthSenderInc teerLinkedField0
      (.x6 ↦ᵣ nonceVal)
      (.x6 ↦ᵣ (nonceVal + (1 : Word))) := by
  have h0 := addi_spec_gen_same_within .x6 nonceVal 1 AfterSmAddiNonce (by nofun)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSmAddiNonce teerProg 518
        (.ADDI .x6 .x6 (1 : BitVec 12))
        (by simp only [AfterSmAddiNonce]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterSmAddiNonce + 4 : Word) = AfterAuthSenderInc := by
    simp only [AfterSmAddiNonce, AfterAuthSenderInc]; bv_omega
  rw [hpc, se12_1] at h1
  exact h1

private theorem teerSmAssumedPre_to_inv0
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8))
    (hlen : authBytes.length = 20) :
    ∀ s,
      (((.x29 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ authPtr) ** (.x28 ↦ᵣ sendPtr) **
          regOwn .x30 ** regOwn .x31 **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes)) s →
      teerSmInv authPtr sendPtr nonceVal authBytes senderBytes 0 s := by
  intro s hp
  dsimp only [teerSmInv, teerSmInvAmb]
  have h20 : BitVec.ofNat 64 20 = (20 : Word) := rfl
  simpa only [hlen, Nat.sub_zero, teer_add_ofNat_zero, h20] using hp

private theorem teerSmInv20_to_loopPost
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8))
    (hlen : authBytes.length = 20) :
    ∀ s, teerSmInv authPtr sendPtr nonceVal authBytes senderBytes 20 s →
      (((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ nonceVal) **
          (.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x28 ↦ᵣ (sendPtr + (20 : Word))) **
          regOwn .x30 ** regOwn .x31 **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes)) s := by
  intro s hq
  dsimp only [teerSmInv, teerSmInvAmb] at hq
  have h20 : BitVec.ofNat 64 20 = (20 : Word) := rfl
  simpa only [hlen, Nat.sub_self, teer_ofNat_zero_eq, h20] using hq

/-- Loop20 + ADDI x6 under Assumed prest/post shape (value-carrying ptrs). -/
theorem teerSmLoop20_thenAddi
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8))
    (hlenA : authBytes.length = 20) (hlenS : senderBytes.length = 20) -- used via heq/domain
    (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hoverA : authPtr.toNat + 20 ≤ 2 ^ 64)
    (hoverS : sendPtr.toNat + 20 ≤ 2 ^ 64)
    (hvalidA : ∀ k, k < 20 →
      isValidByteAccess (authPtr + BitVec.ofNat 64 k) = true)
    (hvalidS : ∀ k, k < 20 →
      isValidByteAccess (sendPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 162 AfterLi20Nj AfterAuthSenderInc teerLinkedField0
      (((.x29 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ authPtr) ** (.x28 ↦ᵣ sendPtr) **
          regOwn .x30 ** regOwn .x31 **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes))
      (((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ (nonceVal + (1 : Word))) **
          (.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x28 ↦ᵣ (sendPtr + (20 : Word))) **
          regOwn .x30 ** regOwn .x31 **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes)) := by
  have hlen : authBytes.length = 20 := hlenA
  have _hlenS : senderBytes.length = 20 := by simpa [heq] using hlenA
  have hloop := teerSmLoop20 authPtr sendPtr nonceVal authBytes senderBytes
    hlen heq halignA halignS hoverA hoverS hvalidA hvalidS
  have hloopW := cpsTripleWithin_weaken
    (teerSmAssumedPre_to_inv0 authPtr sendPtr nonceVal authBytes senderBytes hlen)
    (teerSmInv20_to_loopPost authPtr sendPtr nonceVal authBytes senderBytes hlen)
    hloop
  have haddiF : cpsTripleWithin 1 AfterSmAddiNonce AfterAuthSenderInc teerLinkedField0
      (((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ nonceVal) **
          (.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x28 ↦ᵣ (sendPtr + (20 : Word))) **
          regOwn .x30 ** regOwn .x31 **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes))
      (((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ (nonceVal + (1 : Word))) **
          (.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x28 ↦ᵣ (sendPtr + (20 : Word))) **
          regOwn .x30 ** regOwn .x31 **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes)) := by
    have h0 := cpsTripleWithin_frameR
      (((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x28 ↦ᵣ (sendPtr + (20 : Word))) **
          regOwn .x30 ** regOwn .x31 **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes))
      (by pcf) (teerSmAddiNonce nonceVal)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hloopW haddiF
  have hn : 161 + 1 = 162 := by decide
  simpa only [hn] using hseq

/-- Fill TeerAuthSenderMatchAssumed under teerLinkedField0. -/
def teerAuthSenderMatchAssumed_teerLinked :
    TeerAuthSenderMatchAssumed teerLinkedField0 where
  nSteps := 162
  match_flat := fun nonceVal authBytes senderBytes hlenA hlenS heq
      halignA halignS hoverA hoverS hvalidA hvalidS =>
    teerSmLoop20_thenAddi AuthorityAddr SenderAddr nonceVal
      authBytes senderBytes hlenA hlenS heq
      halignA halignS hoverA hoverS hvalidA hvalidS

#print axioms teerSmBody6
#print axioms teerSmBodyIter
#print axioms teerSmLoop20
#print axioms teerSmLoop20_thenAddi
#print axioms teerAuthSenderMatchAssumed_teerLinked

end EvmAsm.Codegen.TxEip7702TeerSpec
