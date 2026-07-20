/-
  Teer PriorZero auth==sender memcmp (AfterLi20Pz E+2228 → AfterPriorJoin).
  Dual SenderMatch; success path authBytes=senderBytes only.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerPriorZero
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

/-- Loop header BEQ (after `li x29, 20`). -/
abbrev AfterLi20Pz : Word := E + 2232
abbrev AfterPzBeqNtaken : Word := E + 2236
abbrev AfterPzLbuAuth : Word := E + 2240
abbrev AfterPzLbuSend : Word := E + 2244
abbrev AfterPzBneNtaken : Word := E + 2248
abbrev AfterPzAddiAuth : Word := E + 2252
abbrev AfterPzAddiSend : Word := E + 2256
abbrev AfterPzAddiCnt : Word := E + 2260

abbrev teerPzCntBeqOff : BitVec 13 := (152 : BitVec 13)
abbrev teerPzBneOff : BitVec 13 := (20 : BitVec 13)
abbrev teerPzJalBack : BitVec 21 := (-28 : BitVec 21)

theorem teerPzCntBeqOff_taken :
    AfterLi20Pz + signExtend13 teerPzCntBeqOff = AfterPriorJoin := by
  simp only [AfterLi20Pz, AfterPriorJoin, teerPzCntBeqOff, E]; decide

theorem teerPzJalBack_eq :
    AfterPzAddiCnt + signExtend21 teerPzJalBack = AfterLi20Pz := by
  simp only [AfterPzAddiCnt, AfterLi20Pz, teerPzJalBack, E]; decide

/-- Keep x6 ghost (unused) so dual of SenderMatch inv stays mechanical. -/
def teerPzInvAmb (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  (.x6 ↦ᵣ nonceVal) **
    (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
    (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 i)) **
    regOwn .x30 ** regOwn .x31 **
    bytesRegion authPtr authBytes **
    bytesRegion sendPtr senderBytes

def teerPzInv (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  (((.x29 ↦ᵣ BitVec.ofNat 64 (authBytes.length - i)) ** (.x0 ↦ᵣ (0 : Word))) **
    teerPzInvAmb authPtr sendPtr nonceVal authBytes senderBytes i)

theorem teerPzCntBeqTaken :
    cpsTripleWithin 1 AfterLi20Pz AfterPriorJoin teerLinkedField0
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerPzCntBeqOff
    (0 : Word) (0 : Word) AfterLi20Pz
  rw [teerPzCntBeqOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLi20Pz teerProg 558
          (.BEQ .x29 .x0 teerPzCntBeqOff)
          (by simp only [AfterLi20Pz]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

theorem teerPzCntBeqNtaken (cnt : Word) (hne : cnt ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterLi20Pz AfterPzBeqNtaken teerLinkedField0
      ((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerPzCntBeqOff
    cnt (0 : Word) AfterLi20Pz
  change cpsBranchWithin _ _ _ _ _ _ (AfterLi20Pz + 4) _ at hbr
  have hnt := cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLi20Pz teerProg 558
          (.BEQ .x29 .x0 teerPzCntBeqOff)
          (by simp only [AfterLi20Pz]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)
  have hpc : (AfterLi20Pz + 4 : Word) = AfterPzBeqNtaken := by
    simp only [AfterLi20Pz, AfterPzBeqNtaken]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerPzBneNtaken (b : Word) :
    cpsTripleWithin 1 AfterPzLbuSend AfterPzBneNtaken teerLinkedField0
      ((.x30 ↦ᵣ b) ** (.x31 ↦ᵣ b))
      ((.x30 ↦ᵣ b) ** (.x31 ↦ᵣ b)) := by
  have hbr := bne_spec_gen_within .x30 .x31 teerPzBneOff b b AfterPzLbuSend
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPzLbuSend teerProg 561
        (.BNE .x30 .x31 teerPzBneOff)
        (by simp only [AfterPzLbuSend]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterPzLbuSend + 4 = AfterPzBneNtaken := by
    simp only [AfterPzLbuSend, AfterPzBneNtaken]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerPzBody6
    (authPtr sendPtr nonceVal baOld bsOld cnt : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat)
    (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hi : i < authBytes.length)
    (hoverA : authPtr.toNat + i < 2 ^ 64)
    (hoverS : sendPtr.toNat + i < 2 ^ 64)
    (hvalidA : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true)
    (hvalidS : isValidByteAccess (sendPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 6 AfterPzBeqNtaken AfterPzAddiCnt teerLinkedField0
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
  have lbuA := bytesRegion_lbu_within .x30 .x7 authPtr baOld AfterPzBeqNtaken
    authBytes i (by decide) halignA hi hoverA hvalidA
  have s1 : cpsTripleWithin 1 AfterPzBeqNtaken AfterPzLbuAuth teerLinkedField0
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
        (CodeReq.ofProg_mem_at E AfterPzBeqNtaken teerProg 559
          (.LBU .x30 .x7 (0 : BitVec 12))
          (by simp only [AfterPzBeqNtaken]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterPzBeqNtaken + 4 : Word) = AfterPzLbuAuth := by
      simp only [AfterPzBeqNtaken, AfterPzLbuAuth]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  -- LBU send x31
  have lbuS := bytesRegion_lbu_within .x31 .x28 sendPtr bsOld AfterPzLbuAuth
    senderBytes i (by decide) halignS hiS hoverS hvalidS
  have s2 : cpsTripleWithin 1 AfterPzLbuAuth AfterPzLbuSend teerLinkedField0
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
        (CodeReq.ofProg_mem_at E AfterPzLbuAuth teerProg 560
          (.LBU .x31 .x28 (0 : BitVec 12))
          (by simp only [AfterPzLbuAuth]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterPzLbuAuth + 4 : Word) = AfterPzLbuSend := by
      simp only [AfterPzLbuAuth, AfterPzLbuSend]; bv_omega
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
  have s3 : cpsTripleWithin 1 AfterPzLbuSend AfterPzBneNtaken teerLinkedField0
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
      (by pcf) (teerPzBneNtaken byteZ)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  -- ADDI x7 +1
  have addiA := addi_spec_gen_same_within .x7 (authPtr + BitVec.ofNat 64 i)
    1 AfterPzBneNtaken (by nofun)
  have hptrA : (authPtr + BitVec.ofNat 64 i) + (1 : Word) =
      authPtr + BitVec.ofNat 64 (i + 1) := by
    rw [teer_word_ofNat_add_one i]; bv_omega
  have s4 : cpsTripleWithin 1 AfterPzBneNtaken AfterPzAddiAuth teerLinkedField0
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
        (CodeReq.ofProg_mem_at E AfterPzBneNtaken teerProg 562
          (.ADDI .x7 .x7 (1 : BitVec 12))
          (by simp only [AfterPzBneNtaken]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterPzBneNtaken + 4 : Word) = AfterPzAddiAuth := by
      simp only [AfterPzBneNtaken, AfterPzAddiAuth]; bv_omega
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
    1 AfterPzAddiAuth (by nofun)
  have hptrS : (sendPtr + BitVec.ofNat 64 i) + (1 : Word) =
      sendPtr + BitVec.ofNat 64 (i + 1) := by
    rw [teer_word_ofNat_add_one i]; bv_omega
  have s5 : cpsTripleWithin 1 AfterPzAddiAuth AfterPzAddiSend teerLinkedField0
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
        (CodeReq.ofProg_mem_at E AfterPzAddiAuth teerProg 563
          (.ADDI .x28 .x28 (1 : BitVec 12))
          (by simp only [AfterPzAddiAuth]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterPzAddiAuth + 4 : Word) = AfterPzAddiSend := by
      simp only [AfterPzAddiAuth, AfterPzAddiSend]; bv_omega
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
  have addiC := addi_spec_gen_same_within .x29 cnt (-1) AfterPzAddiSend (by nofun)
  have s6 : cpsTripleWithin 1 AfterPzAddiSend AfterPzAddiCnt teerLinkedField0
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
        (CodeReq.ofProg_mem_at E AfterPzAddiSend teerProg 564
          (.ADDI .x29 .x29 (-1 : BitVec 12))
          (by simp only [AfterPzAddiSend]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterPzAddiSend + 4 : Word) = AfterPzAddiCnt := by
      simp only [AfterPzAddiSend, AfterPzAddiCnt]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 s2
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 s3
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 s4
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 s5
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c45 s6

/-- Body6 with x30/x31 owned via of_forall2 (P ** r1 ** r2). -/
theorem teerPzBody6_own
    (authPtr sendPtr nonceVal cnt : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat)
    (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hi : i < authBytes.length)
    (hoverA : authPtr.toNat + i < 2 ^ 64)
    (hoverS : sendPtr.toNat + i < 2 ^ 64)
    (hvalidA : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true)
    (hvalidS : isValidByteAccess (sendPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 6 AfterPzBeqNtaken AfterPzAddiCnt teerLinkedField0
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
        (teerPzBody6 authPtr sendPtr nonceVal baOld bsOld cnt
          authBytes senderBytes i heq halignA halignS hi hoverA hoverS
          hvalidA hvalidS))

/-- JAL x0 -28: AfterPzAddiCnt → AfterLi20Pz. -/
theorem teerPzJalBackTrip (P : Assertion) (hpc : P.pcFree) :
    cpsTripleWithin 1 AfterPzAddiCnt AfterLi20Pz teerLinkedField0 P P := by
  have h0 := jal_x0_spec_gen_within teerPzJalBack AfterPzAddiCnt
  rw [teerPzJalBack_eq] at h0
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPzAddiCnt teerProg 565
        (.JAL .x0 teerPzJalBack)
        (by simp only [AfterPzAddiCnt]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 := cpsTripleWithin_frameR P hpc h1
  exact cpsTripleWithin_weaken
    (fun s hp => (sepConj_emp_left _).2 hp)
    (fun s hq => (sepConj_emp_left _).1 hq) h2

/-- One full iteration: BEQ ntaken + body6 + JAL → inv i → inv (i+1). -/
theorem teerPzBodyIter
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8)) (i : Nat)
    (hlen : authBytes.length = 20) (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hi : i < authBytes.length)
    (hoverA : authPtr.toNat + i < 2 ^ 64)
    (hoverS : sendPtr.toNat + i < 2 ^ 64)
    (hvalidA : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true)
    (hvalidS : isValidByteAccess (sendPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 8 AfterLi20Pz AfterLi20Pz teerLinkedField0
      (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes i)
      (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes (i + 1)) := by
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
  have hbneF : cpsTripleWithin 1 AfterLi20Pz AfterPzBeqNtaken teerLinkedField0
      (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes i)
      (((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) **
        teerPzInvAmb authPtr sendPtr nonceVal authBytes senderBytes i) := by
    have h0 := cpsTripleWithin_frameR
      (teerPzInvAmb authPtr sendPtr nonceVal authBytes senderBytes i)
      (by simp only [teerPzInvAmb]; pcf)
      (teerPzCntBeqNtaken cnt hne)
    exact cpsTripleWithin_weaken
      (fun s hp => by
        dsimp only [teerPzInv, cnt] at hp
        exact hp)
      (fun _ hq => hq) h0
  have hbodyF : cpsTripleWithin 6 AfterPzBeqNtaken AfterPzAddiCnt teerLinkedField0
      (((.x29 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) **
        teerPzInvAmb authPtr sendPtr nonceVal authBytes senderBytes i)
      (((.x29 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x6 ↦ᵣ nonceVal) **
          (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
          (.x28 ↦ᵣ (sendPtr + BitVec.ofNat 64 (i + 1))) **
          (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
          (.x31 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
          bytesRegion authPtr authBytes **
          bytesRegion sendPtr senderBytes)) := by
    have hraw := teerPzBody6_own authPtr sendPtr nonceVal cnt
      authBytes senderBytes i heq halignA halignS hi hoverA hoverS hvalidA hvalidS
    have h0 := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hraw
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [teerPzInvAmb] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  have hjal := teerPzJalBackTrip
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
        teerPzInv authPtr sendPtr nonceVal authBytes senderBytes (i + 1) s := by
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
    simpa only [teerPzInv, teerPzInvAmb] using hq2
  exact cpsTripleWithin_weaken (fun _ hp => hp) hpost c2

/-- Loop with remaining fuel `k` starting at index `20-k`. -/
theorem teerPzLoop_fuel
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
    cpsTripleWithin (8 * k + 1) AfterLi20Pz AfterPriorJoin teerLinkedField0
      (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes (20 - k))
      (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes 20) := by
  induction k with
  | zero =>
      have h0 := cpsTripleWithin_frameR
        (teerPzInvAmb authPtr sendPtr nonceVal authBytes senderBytes 20)
        (by simp only [teerPzInvAmb]; pcf)
        teerPzCntBeqTaken
      exact cpsTripleWithin_weaken
        (fun s hp => by
          change (((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            teerPzInvAmb authPtr sendPtr nonceVal authBytes senderBytes 20) s
          dsimp only [teerPzInv] at hp
          simpa only [Nat.sub_zero, hlen, Nat.sub_self, teer_ofNat_zero_eq] using hp)
        (fun s hq => by
          dsimp only [teerPzInv]
          simpa only [hlen, Nat.sub_self, teer_ofNat_zero_eq] using hq)
        (by simpa only [Nat.mul_zero, Nat.zero_add] using h0)
  | succ m ih =>
      have hm : m ≤ 20 := by omega
      have hi : 20 - (m + 1) < authBytes.length := by omega
      have hoverAi : authPtr.toNat + (20 - (m + 1)) < 2 ^ 64 := by omega
      have hoverSi : sendPtr.toNat + (20 - (m + 1)) < 2 ^ 64 := by omega
      have hva := hvalidA (20 - (m + 1)) (by omega)
      have hvs := hvalidS (20 - (m + 1)) (by omega)
      have hstep := teerPzBodyIter authPtr sendPtr nonceVal authBytes senderBytes
        (20 - (m + 1)) hlen heq halignA halignS hi hoverAi hoverSi hva hvs
      have hidx : (20 - (m + 1)) + 1 = 20 - m := by omega
      have hstep' : cpsTripleWithin 8 AfterLi20Pz AfterLi20Pz teerLinkedField0
          (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes (20 - (m + 1)))
          (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes (20 - m)) := by
        simpa only [hidx] using hstep
      have hrest := ih hm
      have hseq := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hstep' hrest
      have hn : 8 + (8 * m + 1) = 8 * (m + 1) + 1 := by omega
      simpa only [hn] using hseq

/-- Full 20-iter memcmp under inv: AfterLi20Pz → AfterPriorJoin. -/

theorem teerPzLoop20
    (authPtr sendPtr nonceVal : Word)
    (authBytes senderBytes : List (BitVec 8))
    (hlen : authBytes.length = 20) (heq : authBytes = senderBytes)
    (halignA : authPtr.toNat % 8 = 0) (halignS : sendPtr.toNat % 8 = 0)
    (hvalidA : ∀ j, j < 20 →
      isValidByteAccess (authPtr + BitVec.ofNat 64 j) = true)
    (hvalidS : ∀ j, j < 20 →
      isValidByteAccess (sendPtr + BitVec.ofNat 64 j) = true)
    (hoverA : authPtr.toNat + 20 ≤ 2 ^ 64)
    (hoverS : sendPtr.toNat + 20 ≤ 2 ^ 64) :
    cpsTripleWithin 161 AfterLi20Pz AfterPriorJoin teerLinkedField0
      (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes 0)
      (teerPzInv authPtr sendPtr nonceVal authBytes senderBytes 20) := by
  have h := teerPzLoop_fuel authPtr sendPtr nonceVal authBytes senderBytes 20
    hlen heq halignA halignS (by omega) hvalidA hvalidS hoverA hoverS
  simpa only [Nat.sub_self, show 8 * 20 + 1 = 161 from by decide] using h

#print axioms teerPzLoop20

end EvmAsm.Codegen.TxEip7702TeerSpec
