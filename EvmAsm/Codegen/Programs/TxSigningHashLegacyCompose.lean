/-
  K146 bounded body composition.

  This file starts the dispatcher proof at a genuine internal boundary: the
  eight-instruction chain-id byte loop.  The loop theorem is already proved in
  `TxSigningHashLegacyLoopSpec`; the only new fact here is that the local loop
  program is the linked K146 slice at `H+172`, so the theorem is lifted to the
  deployed K146 code requirement without adding a callee assumption.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyLoopSpec
import EvmAsm.Codegen.Programs.TxSigningHashLegacyCopySpec

namespace EvmAsm.Codegen.TxSigningHashLegacyCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
open EvmAsm.Codegen.TxSigningHashLegacyCopySpec

abbrev legacyLoopBase : Word := legacyH + (172 : Word)

theorem legacyLoop_slice :
    (txSigningHashLegacyEip155_prog.drop 43).take loopProg.length = loopProg := by
  decide

theorem legacyLoop_mono : ∀ a i,
    CodeReq.ofProg legacyLoopBase loopProg a = some i →
      legacyFullCode a = some i := by
  intro a i h
  apply legacyCode_mono a i
  exact CodeReq.ofProg_mono_sub legacyH legacyLoopBase
    txSigningHashLegacyEip155_prog loopProg 43
    (by unfold legacyLoopBase legacyH; decide)
    (by exact legacyLoop_slice)
    (by decide)
    (by decide)
    a i h

theorem legacyLoop_callWithin
    (dst chainId : Word) (F : Assertion)
    (hF : F.pcFree)
    (halign : dst.toNat % 8 = 0) (hover : dst.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess (dst + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 65 legacyLoopBase (legacyLoopBase + 32) legacyFullCode
      (loopInv dst chainId F 0) (loopInv dst chainId F 8) := by
  have hloop := loopCps_owned legacyLoopBase dst chainId F hF halign hover hvalid hbound
  simpa only [legacyLoopBase] using
    (cpsTripleWithin_extend_code legacyLoop_mono hloop)

abbrev legacyCopyBase : Word := legacyH + (296 : Word)

theorem legacyCopy_slice :
    (txSigningHashLegacyEip155_prog.drop 74).take copyLoopProg.length = copyLoopProg := by
  decide

theorem legacyCopy_mono : ∀ a i,
    CodeReq.ofProg legacyCopyBase copyLoopProg a = some i →
      legacyFullCode a = some i := by
  intro a i h
  apply legacyCode_mono a i
  exact CodeReq.ofProg_mono_sub legacyH legacyCopyBase
    txSigningHashLegacyEip155_prog copyLoopProg 74
    (by unfold legacyCopyBase legacyH; decide)
    (by exact legacyCopy_slice)
    (by decide)
    (by decide)
    a i h

theorem legacyCopy_callWithin
    (srcBase dstBase : Word) (N : Nat)
    (srcBytes dstBytes : List (BitVec 8))
    (hlen : dstBytes.length = N)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hNsrc : N ≤ srcBytes.length)
    (hsover : srcBase.toNat + N < 2 ^ 64)
    (hdover : dstBase.toNat + N < 2 ^ 64)
    (hsvalid : ∀ i, i < N →
      isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hdvalid : ∀ i, i < N →
      isValidByteAccess (dstBase + BitVec.ofNat 64 i) = true)
    (hNbound : N < 18446744073709551616) :
    cpsTripleWithin (N * (6 + 1) + 1) legacyCopyBase (legacyCopyBase + 28)
      legacyFullCode
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 N) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInvCore srcBase dstBase N srcBytes dstBytes N)
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 0) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInvCore srcBase dstBase N srcBytes dstBytes 0) := by
  have hcopy := copyLoop legacyCopyBase srcBase dstBase N srcBytes dstBytes
    hlen hsalign hdalign hNsrc hsover hdover hsvalid hdvalid hNbound
  exact cpsTripleWithin_extend_code legacyCopy_mono hcopy

private theorem legacy_mem_at (pc : Word) (idx : Nat) (ins : Instr)
    (hk : idx < 120)
    (hpc : pc = legacyH + BitVec.ofNat 64 (4 * idx))
    (hins : ∀ h : idx < txSigningHashLegacyEip155_prog.length,
      txSigningHashLegacyEip155_prog[idx]'h = ins) :
    ∀ a i, CodeReq.singleton pc ins a = some i → legacyFullCode a = some i := by
  intro a i hi
  apply legacyCode_mono a i
  exact CodeReq.ofProg_mem_at legacyH pc
    (txSigningHashLegacyEip155_prog : List Instr) idx ins hpc
    (by rw [legacy_prog_length]; exact hk) (hins _) (by
      rw [legacy_prog_length]
      norm_num) a i hi

/-! ## K146 dispatcher entry and empty-length branch

    The legacy EIP-155 body has four ABI moves (the chain id is kept in
    `x18`), then tests the saved input length at `H+52`.  The empty-length
    arm jumps to the common failure `li a0, 1` at `H+436`. -/

theorem legacySetupMoves_spec
    (a0 a1 a2 a3 v8 v9 v18 v19 : Word) :
    cpsTripleWithin 4 (legacyH + 36) (legacyH + 52) legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) := by
  have h0 := mv_spec_gen_within .x8 .x10 a0 v8 (legacyH + 36) (by decide)
  rw [show (legacyH + 36 : Word) + 4 = legacyH + 40 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 36) 9 (.MV .x8 .x10) (by decide) (by decide)
      (by intro h; rfl))
    h0
  have c0 : cpsTripleWithin 1 (legacyH + 36) (legacyH + 40) legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19)) := by
    have hF := cpsTripleWithin_frameR
      ((.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19)) (by pcf) l0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1 := mv_spec_gen_within .x9 .x11 a1 v9 (legacyH + 40) (by decide)
  rw [show (legacyH + 40 : Word) + 4 = legacyH + 44 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 40) 10 (.MV .x9 .x11) (by decide) (by decide)
      (by intro h; rfl))
    h1
  have c1 : cpsTripleWithin 1 (legacyH + 40) (legacyH + 44) legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19)) := by
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19)) (by pcf) l1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c0 c1
  have h2 := mv_spec_gen_within .x18 .x12 a2 v18 (legacyH + 44) (by decide)
  rw [show (legacyH + 44 : Word) + 4 = legacyH + 48 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 44) 11 (.MV .x18 .x12) (by decide) (by decide)
      (by intro h; rfl))
    h2
  have c2 : cpsTripleWithin 1 (legacyH + 44) (legacyH + 48) legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ v19)) := by
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x19 ↦ᵣ v19)) (by pcf) l2
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 c2
  have h3 := mv_spec_gen_within .x19 .x13 a3 v19 (legacyH + 48) (by decide)
  rw [show (legacyH + 48 : Word) + 4 = legacyH + 52 from by decide] at h3
  have l3 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 48) 12 (.MV .x19 .x13) (by decide) (by decide)
      (by intro h; rfl))
    h3
  have c3 : cpsTripleWithin 1 (legacyH + 48) (legacyH + 52) legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ v19))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) := by
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2)) (by pcf) l3
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c012 c3

abbrev legacyEmptyLenBeqOff : BitVec 13 := (384 : BitVec 13)
abbrev legacyFailLiPC : Word := legacyH + 436

theorem legacyEmptyLenBeq_taken_pc :
    (legacyH + 52) + signExtend13 legacyEmptyLenBeqOff = legacyFailLiPC := by
  unfold legacyEmptyLenBeqOff legacyFailLiPC legacyH
  decide

theorem legacyEmptyLenBeq_taken (lenW : Word) (hlen : lenW = 0) :
    cpsTripleWithin 1 (legacyH + 52) legacyFailLiPC legacyFullCode
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x9 .x0 legacyEmptyLenBeqOff lenW 0
    (legacyH + 52)
  rw [legacyEmptyLenBeq_taken_pc] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 52) 13
        (.BEQ .x9 .x0
          (brOff (GuestAddrs.tx_signing_hash_legacy_eip155 + 436)
            (GuestAddrs.tx_signing_hash_legacy_eip155 + 52))) (by decide)
        (by decide) (by intro h; rfl)) hbeq)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hlen)

theorem legacyEmptyLenBeq_ntaken (lenW : Word) (hlen : lenW ≠ 0) :
    cpsTripleWithin 1 (legacyH + 52) (legacyH + 56) legacyFullCode
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x9 .x0 legacyEmptyLenBeqOff lenW 0
    (legacyH + 52)
  rw [show (legacyH + 52 : Word) + 4 = legacyH + 56 from by decide] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 52) 13
        (.BEQ .x9 .x0
          (brOff (GuestAddrs.tx_signing_hash_legacy_eip155 + 436)
            (GuestAddrs.tx_signing_hash_legacy_eip155 + 52))) (by decide)
        (by decide) (by intro h; rfl)) hbeq)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hlen ((sepConj_pure_right _).1 hBP).2)

theorem legacyFailLi_spec (v10 : Word) :
    cpsTripleWithin 1 legacyFailLiPC (legacyH + 440) legacyFullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x10 v10 (1 : Word) legacyFailLiPC (by decide)
  rw [show legacyFailLiPC + 4 = legacyH + 440 from by
    unfold legacyFailLiPC
    decide] at h0
  exact cpsTripleWithin_extend_code
    (legacy_mem_at legacyFailLiPC 109 (.LI .x10 (1 : Word)) (by decide)
      (by decide) (by intro h; rfl)) h0

theorem legacySetupThenEmptyFail_spec
    (a0 a1 a2 a3 v8 v9 v18 v19 : Word) (hlen : a1 = 0) :
    cpsTripleWithin (4 + 1 + 1) (legacyH + 36) (legacyH + 440)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hsetup := legacySetupMoves_spec a0 a1 a2 a3 v8 v9 v18 v19
  have hsetupF := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hsetup
  have hsetupW : cpsTripleWithin 4 (legacyH + 36) (legacyH + 52)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x0 ↦ᵣ (0 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsetupF
  have hbranch := legacyEmptyLenBeq_taken a1 hlen
  have hbranchF := cpsTripleWithin_frameR (.x10 ↦ᵣ a0) (by pcf) hbranch
  have hbranchW : cpsTripleWithin 1 (legacyH + 52) legacyFailLiPC
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x0 ↦ᵣ (0 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hbranchF
  have hbranchW' : cpsTripleWithin 1 (legacyH + 52) legacyFailLiPC
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
          (.x8 ↦ᵣ a0) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) (by pcf) hbranchW)
  have hfail := legacyFailLi_spec a0
  have hfailF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
      (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
      (.x19 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) hfail
  have hfailW : cpsTripleWithin 1 legacyFailLiPC (legacyH + 440)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hfailF
  have hseq := cpsTripleWithin_seq_same_cr hsetupW hbranchW'
  have hseq' := cpsTripleWithin_seq_same_cr hseq hfailW
  exact hseq'

/-! ## K146 list-header dispatcher

    This is the first non-empty dispatcher slice.  The input header byte is
    loaded at `H+56`; `< 0xc0` jumps to the common failure, while list headers
    split at `0xf8` into the short (`x20 := 1`) and long (`x20 := hdr - 246`)
    arms. -/

def legacyHdrByte (input : List (BitVec 8)) (h0 : 0 < input.length) : Word :=
  (input[0]'h0).zeroExtend 64

theorem legacyHdrLbu_spec (inPtr v5 : Word) (input : List (BitVec 8))
    (h0 : 0 < input.length)
    (halign : inPtr.toNat % 8 = 0)
    (hover : inPtr.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess inPtr = true) :
    cpsTripleWithin 1 (legacyH + 56) (legacyH + 60) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        bytesRegion inPtr input) := by
  have hptr : inPtr + BitVec.ofNat 64 0 = inPtr := by bv_omega
  have hlbu := bytesRegion_lbu_within .x5 .x8 inPtr v5 (legacyH + 56)
    input 0 (by decide) halign h0 (by omega) (by rwa [hptr])
  rw [hptr, show (legacyH + 56 : Word) + 4 = legacyH + 60 from by decide] at hlbu
  change cpsTripleWithin 1 (legacyH + 56) (legacyH + 60)
      (CodeReq.singleton (legacyH + 56) (.LBU .x5 .x8 0))
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        bytesRegion inPtr input) at hlbu
  exact cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 56) 14 (.LBU .x5 .x8 (0 : BitVec 12))
      (by decide) (by decide) (by intro h; rfl)) hlbu

theorem legacyHdrLi192_spec (v6 : Word) :
    cpsTripleWithin 1 (legacyH + 60) (legacyH + 64) legacyFullCode
      (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (192 : Word)) := by
  have h0 := li_spec_gen_within .x6 v6 (192 : Word) (legacyH + 60) (by decide)
  rw [show (legacyH + 60 : Word) + 4 = legacyH + 64 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 60) 15 (.LI .x6 (192 : Word))
      (by decide) (by decide) (by intro h; rfl)) h0

abbrev legacyHdrNotListOff : BitVec 13 := (372 : BitVec 13)
abbrev legacyHdrNotListFailPC : Word := legacyH + 436

theorem legacyHdrNotList_taken_pc :
    (legacyH + 64) + signExtend13 legacyHdrNotListOff = legacyHdrNotListFailPC := by
  unfold legacyHdrNotListOff legacyHdrNotListFailPC legacyH
  decide

theorem legacyHdrNotList_taken (hdr : Word)
    (hult : BitVec.ult hdr (192 : Word)) :
    cpsTripleWithin 1 (legacyH + 64) legacyHdrNotListFailPC legacyFullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word))) := by
  have hbr := bltu_spec_gen_within .x5 .x6 legacyHdrNotListOff hdr (192 : Word)
    (legacyH + 64)
  rw [legacyHdrNotList_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 64) 16
        (.BLTU .x5 .x6
          (brOff (GuestAddrs.tx_signing_hash_legacy_eip155 + 436)
            (GuestAddrs.tx_signing_hash_legacy_eip155 + 64))) (by decide)
        (by decide) (by intro h; rfl)) hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hult)

theorem legacyHdrNotList_ntaken (hdr : Word)
    (hge : ¬BitVec.ult hdr (192 : Word)) :
    cpsTripleWithin 1 (legacyH + 64) (legacyH + 68) legacyFullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word))) := by
  have hbr := bltu_spec_gen_within .x5 .x6 legacyHdrNotListOff hdr (192 : Word)
    (legacyH + 64)
  rw [show (legacyH + 64 : Word) + 4 = legacyH + 68 from by decide] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 64) 16
        (.BLTU .x5 .x6
          (brOff (GuestAddrs.tx_signing_hash_legacy_eip155 + 436)
            (GuestAddrs.tx_signing_hash_legacy_eip155 + 64))) (by decide)
        (by decide) (by intro h; rfl)) hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hge ((sepConj_pure_right _).1 hBP).2)

theorem legacyHdrLi248_spec (v6 : Word) :
    cpsTripleWithin 1 (legacyH + 68) (legacyH + 72) legacyFullCode
      (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (248 : Word)) := by
  have h0 := li_spec_gen_within .x6 v6 (248 : Word) (legacyH + 68) (by decide)
  rw [show (legacyH + 68 : Word) + 4 = legacyH + 72 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 68) 17 (.LI .x6 (248 : Word))
      (by decide) (by decide) (by intro h; rfl)) h0

abbrev legacyHdrShortListOff : BitVec 13 := (16 : BitVec 13)
abbrev legacyHdrShortLiPC : Word := legacyH + 88

theorem legacyHdrShortList_taken_pc :
    (legacyH + 72) + signExtend13 legacyHdrShortListOff = legacyHdrShortLiPC := by
  unfold legacyHdrShortListOff legacyHdrShortLiPC legacyH
  decide

theorem legacyHdrShortList_taken (hdr : Word)
    (hult : BitVec.ult hdr (248 : Word)) :
    cpsTripleWithin 1 (legacyH + 72) legacyHdrShortLiPC legacyFullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word))) := by
  have hbr := bltu_spec_gen_within .x5 .x6 legacyHdrShortListOff hdr (248 : Word)
    (legacyH + 72)
  rw [legacyHdrShortList_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 72) 18
        (.BLTU .x5 .x6 legacyHdrShortListOff) (by decide) (by decide)
        (by intro h; rfl)) hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hult)

theorem legacyHdrShortList_ntaken (hdr : Word)
    (hge : ¬BitVec.ult hdr (248 : Word)) :
    cpsTripleWithin 1 (legacyH + 72) (legacyH + 76) legacyFullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word))) := by
  have hbr := bltu_spec_gen_within .x5 .x6 legacyHdrShortListOff hdr (248 : Word)
    (legacyH + 72)
  rw [show (legacyH + 72 : Word) + 4 = legacyH + 76 from by decide] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 72) 18
        (.BLTU .x5 .x6 legacyHdrShortListOff) (by decide) (by decide)
        (by intro h; rfl)) hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hge ((sepConj_pure_right _).1 hBP).2)

theorem legacyHdrShortLi_spec (v20 : Word) :
    cpsTripleWithin 1 legacyHdrShortLiPC (legacyH + 92) legacyFullCode
      (.x20 ↦ᵣ v20) (.x20 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x20 v20 (1 : Word) legacyHdrShortLiPC (by decide)
  rw [show legacyHdrShortLiPC + 4 = legacyH + 92 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (legacy_mem_at legacyHdrShortLiPC 22 (.LI .x20 (1 : Word))
      (by decide) (by decide) (by intro h; rfl)) h0

theorem legacyHdrShortList_ntaken_long (hdr : Word)
    (hge : ¬BitVec.ult hdr (248 : Word)) :
    cpsTripleWithin 1 (legacyH + 72) (legacyH + 76) legacyFullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word))) :=
  legacyHdrShortList_ntaken hdr hge

theorem legacyHdrLongLenLen_spec (hdr v20 : Word) :
    cpsTripleWithin 1 (legacyH + 76) (legacyH + 80) legacyFullCode
      ((.x5 ↦ᵣ hdr) ** (.x20 ↦ᵣ v20))
      ((.x5 ↦ᵣ hdr) **
        (.x20 ↦ᵣ (hdr + signExtend12 (-247 : BitVec 12)))) := by
  have h0 := addi_spec_gen_within .x20 .x5 v20 hdr (-247 : BitVec 12)
    (legacyH + 76) (by decide)
  rw [show (legacyH + 76 : Word) + 4 = legacyH + 80 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 76) 19
      (.ADDI .x20 .x5 (-247 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) h0

theorem legacyHdrLongPlusOne_spec (v20 : Word) :
    cpsTripleWithin 1 (legacyH + 80) (legacyH + 84) legacyFullCode
      (.x20 ↦ᵣ v20)
      (.x20 ↦ᵣ (v20 + signExtend12 (1 : BitVec 12))) := by
  have h0 := addi_spec_gen_same_within .x20 v20 (1 : BitVec 12)
    (legacyH + 80) (by decide)
  rw [show (legacyH + 80 : Word) + 4 = legacyH + 84 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 80) 20
      (.ADDI .x20 .x20 (1 : BitVec 12)) (by decide) (by decide)
      (by intro h; rfl)) h0

theorem legacyHdrLongSkip_spec (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 1 (legacyH + 84) (legacyH + 92) legacyFullCode P P := by
  have h0 := jal_x0_spec_gen_within (8 : BitVec 21) (legacyH + 84)
  rw [show (legacyH + 84 : Word) + signExtend21 (8 : BitVec 21) =
      legacyH + 92 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 84) 21 (.JAL .x0 (8 : BitVec 21))
      (by decide) (by decide) (by intro h; rfl)) h0
  have hF := cpsTripleWithin_frameL P hP l0
  exact (sepConj_emp_right' P) ▸ hF

theorem legacyHdrLongLen_eq (hdr : Word) :
    hdr + signExtend12 (-247 : BitVec 12) + signExtend12 (1 : BitVec 12) =
      hdr - (246 : Word) := by
  rw [show signExtend12 (-247 : BitVec 12) = (-247 : Word) from by decide,
    show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

def legacyHdrLenOf (hdr : Word) : Word :=
  if BitVec.ult hdr (248 : Word) then (1 : Word) else hdr - (246 : Word)

abbrev legacyHdrLen (input : List (BitVec 8)) (h0 : 0 < input.length) : Word :=
  legacyHdrLenOf (legacyHdrByte input h0)

theorem legacyHdrLenOf_short (hdr : Word) (h : BitVec.ult hdr (248 : Word)) :
    legacyHdrLenOf hdr = (1 : Word) := by
  simp only [legacyHdrLenOf, h, if_true]

theorem legacyHdrLenOf_long (hdr : Word)
    (h : ¬BitVec.ult hdr (248 : Word)) :
    legacyHdrLenOf hdr = hdr - (246 : Word) := by
  simp only [legacyHdrLenOf]
  rw [if_neg h]

theorem legacyHdrParseLong_spec (inPtr v5 v6 v20 : Word)
    (input : List (BitVec 8))
    (h0 : 0 < input.length)
    (halign : inPtr.toNat % 8 = 0)
    (hover : inPtr.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess inPtr = true)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word))
    (hlong : ¬BitVec.ult (legacyHdrByte input h0) (248 : Word)) :
    cpsTripleWithin 8 (legacyH + 56) (legacyH + 92) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        (.x6 ↦ᵣ (248 : Word)) **
        (.x20 ↦ᵣ (legacyHdrByte input h0 - (246 : Word))) **
        bytesRegion inPtr input) := by
  have hlbu := legacyHdrLbu_spec inPtr v5 input h0 halign hover hvalid
  have hlbuF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20)) (by pcf) hlbu
  have hli192 := legacyHdrLi192_spec v6
  have hli192F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
      (.x20 ↦ᵣ v20) ** bytesRegion inPtr input) (by pcf) hli192
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlbuF hli192F
  have hnt := legacyHdrNotList_ntaken (legacyHdrByte input h0) hge
  have hntF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x20 ↦ᵣ v20) ** bytesRegion inPtr input)
    (by pcf) hnt
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hntF
  have hli248 := legacyHdrLi248_spec (192 : Word)
  have hli248F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
      (.x20 ↦ᵣ v20) ** bytesRegion inPtr input) (by pcf) hli248
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c012 hli248F
  have hnt2 := legacyHdrShortList_ntaken_long
    (legacyHdrByte input h0) hlong
  have hnt2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x20 ↦ᵣ v20) ** bytesRegion inPtr input)
    (by pcf) hnt2
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c0123 hnt2F
  have hll := legacyHdrLongLenLen_spec
    (legacyHdrByte input h0) v20
  have hllF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x6 ↦ᵣ (248 : Word)) **
      bytesRegion inPtr input) (by pcf) hll
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c4 hllF
  have hp1 := legacyHdrLongPlusOne_spec
    (legacyHdrByte input h0 + signExtend12 (-247 : BitVec 12))
  have hp1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
      (.x6 ↦ᵣ (248 : Word)) ** bytesRegion inPtr input)
    (by pcf) hp1
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c5 hp1F
  have hjal := legacyHdrLongSkip_spec
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
      (.x6 ↦ᵣ (248 : Word)) **
      (.x20 ↦ᵣ (legacyHdrByte input h0 + signExtend12 (-247 : BitVec 12) +
        signExtend12 (1 : BitVec 12))) ** bytesRegion inPtr input) (by pcf)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c6 hjal
  rw [← legacyHdrLongLen_eq (legacyHdrByte input h0)]
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

theorem legacyHdrParseShort_spec (inPtr v5 v6 v20 : Word)
    (input : List (BitVec 8))
    (h0 : 0 < input.length)
    (halign : inPtr.toNat % 8 = 0)
    (hover : inPtr.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess inPtr = true)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word))
    (hshort : BitVec.ult (legacyHdrByte input h0) (248 : Word)) :
    cpsTripleWithin 7 (legacyH + 56) (legacyH + 92) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x20 ↦ᵣ (1 : Word)) **
        bytesRegion inPtr input) := by
  have hlbu := legacyHdrLbu_spec inPtr v5 input h0 halign hover hvalid
  have hlbuF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20)) (by pcf) hlbu
  have hli192 := legacyHdrLi192_spec v6
  have hli192F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
      (.x20 ↦ᵣ v20) ** bytesRegion inPtr input) (by pcf) hli192
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlbuF hli192F
  have hnt := legacyHdrNotList_ntaken (legacyHdrByte input h0) hge
  have hntF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x20 ↦ᵣ v20) ** bytesRegion inPtr input)
    (by pcf) hnt
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hntF
  have hli248 := legacyHdrLi248_spec (192 : Word)
  have hli248F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
      (.x20 ↦ᵣ v20) ** bytesRegion inPtr input) (by pcf) hli248
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c012 hli248F
  have htk := legacyHdrShortList_taken (legacyHdrByte input h0) hshort
  have htkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x20 ↦ᵣ v20) ** bytesRegion inPtr input)
    (by pcf) htk
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c0123 htkF
  have hli1 := legacyHdrShortLi_spec v20
  have hli1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
      (.x6 ↦ᵣ (248 : Word)) ** bytesRegion inPtr input)
    (by pcf) hli1
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01234 hli1F
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

theorem legacyHdrParseAny_spec (inPtr v5 v6 v20 : Word)
    (input : List (BitVec 8))
    (h0 : 0 < input.length)
    (halign : inPtr.toNat % 8 = 0)
    (hover : inPtr.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess inPtr = true)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word)) :
    cpsTripleWithin 8 (legacyH + 56) (legacyH + 92) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x20 ↦ᵣ legacyHdrLen input h0) **
        bytesRegion inPtr input) := by
  by_cases hshort : BitVec.ult (legacyHdrByte input h0) (248 : Word)
  · rw [show legacyHdrLen input h0 = (1 : Word) from
      legacyHdrLenOf_short _ hshort]
    exact cpsTripleWithin_mono_nSteps (by omega)
      (legacyHdrParseShort_spec inPtr v5 v6 v20 input h0 halign hover hvalid
        hge hshort)
  · rw [show legacyHdrLen input h0 =
      legacyHdrByte input h0 - (246 : Word) from
      legacyHdrLenOf_long _ hshort]
    exact legacyHdrParseLong_spec inPtr v5 v6 v20 input h0 halign hover hvalid
      hge hshort

theorem legacySetupThenHdrParseAny_spec
    (a0 a1 a2 a3 v5 v6 v20 : Word) (input : List (BitVec 8))
    (hlen : a1 ≠ 0)
    (h0 : 0 < input.length)
    (halign : a0.toNat % 8 = 0)
    (hover : a0.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (legacyHdrByte input h0) (192 : Word)) :
    cpsTripleWithin (4 + 1 + 8) (legacyH + 36) (legacyH + 92)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
        (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        (.x6 ↦ᵣ (248 : Word)) **
        (.x20 ↦ᵣ legacyHdrLen input h0) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion a0 input ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) := by
  have hsetup := legacySetupMoves_spec a0 a1 a2 a3
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
  have hsetupF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x20 ↦ᵣ v20) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input) (by pcf) hsetup
  have hsetupW : cpsTripleWithin 4 (legacyH + 36) (legacyH + 52)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
        (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsetupF
  have hbranch := legacyEmptyLenBeq_ntaken a1 hlen
  have hbranchF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
      (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
      (.x20 ↦ᵣ v20) ** bytesRegion a0 input ** (.x8 ↦ᵣ a0) **
      (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) (by pcf) hbranch
  have hbranchW : cpsTripleWithin 1 (legacyH + 52) (legacyH + 56)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hbranchF
  have hhdr := legacyHdrParseAny_spec a0 v5 v6 v20 input h0 halign hover
    hvalid hge
  have hhdrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
      (.x13 ↦ᵣ a3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ a1) **
      (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) (by pcf) hhdr
  have hhdrW : cpsTripleWithin 8 (legacyH + 56) (legacyH + 92)
      legacyFullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) **
        (.x13 ↦ᵣ a3) ** (.x5 ↦ᵣ legacyHdrByte input h0) **
        (.x6 ↦ᵣ (248 : Word)) ** (.x20 ↦ᵣ legacyHdrLen input h0) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input ** (.x8 ↦ᵣ a0) **
        (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hhdrF
  have hseq := cpsTripleWithin_seq_same_cr hsetupW hbranchW
  have hseq' := cpsTripleWithin_seq_same_cr hseq hhdrW
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hseq')

theorem legacyNthArgMoves_spec
    (inPtr lenW v10 v11 v12 : Word) :
    cpsTripleWithin 3 (legacyH + 92) (legacyH + 104) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word))) := by
  have h0 := mv_spec_gen_within .x10 .x8 inPtr v10 (legacyH + 92)
    (by decide)
  rw [show (legacyH + 92 : Word) + 4 = legacyH + 96 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 92) 23 (.MV .x10 .x8) (by decide)
      (by decide) (by intro h; rfl)) h0
  have c0 : cpsTripleWithin 1 (legacyH + 92) (legacyH + 96)
      legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) := by
    have hF := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ lenW) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) (by pcf) l0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1 := mv_spec_gen_within .x11 .x9 lenW v11 (legacyH + 96)
    (by decide)
  rw [show (legacyH + 96 : Word) + 4 = legacyH + 100 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 96) 24 (.MV .x11 .x9) (by decide)
      (by decide) (by intro h; rfl)) h1
  have c1 : cpsTripleWithin 1 (legacyH + 96) (legacyH + 100)
      legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ v12)) := by
    have hF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) ** (.x10 ↦ᵣ inPtr) ** (.x12 ↦ᵣ v12)) (by pcf) l1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c0 c1
  have h2 := li_spec_gen_within .x12 v12 (5 : Word) (legacyH + 100)
    (by decide)
  rw [show (legacyH + 100 : Word) + 4 = legacyH + 104 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 100) 25 (.LI .x12 (5 : Word)) (by decide)
      (by decide) (by intro h; rfl)) h2
  have c2 : cpsTripleWithin 1 (legacyH + 100) (legacyH + 104)
      legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word))) := by
    have hF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW)) (by pcf) l2
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

abbrev legacyLinkedNthOffPtr : Word :=
  BitVec.ofNat 64 GuestAddrs.t155_offset_hi

abbrev legacyLinkedNthLenPtr : Word :=
  BitVec.ofNat 64 GuestAddrs.t155_length_hi

theorem legacyNthPointerAliases_derived :
    legacyNthOffPtr = legacyLinkedNthOffPtr ∧
      legacyNthLenPtr = legacyLinkedNthLenPtr := by
  constructor <;> rfl

abbrev legacyLinkedChainPtr : Word :=
  BitVec.ofNat 64 GuestAddrs.t155_chain_be

abbrev legacyLinkedChainEncPtr : Word :=
  BitVec.ofNat 64 GuestAddrs.t155_chain_enc

theorem legacy_la_chain_hi :
    Codegen.laHi GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 204) =
      Rv64.laHi (legacyH + 204) legacyLinkedChainPtr := by
  decide

theorem legacy_la_chain_lo :
    Codegen.laLo GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 204) =
      Rv64.laLo (legacyH + 204) legacyLinkedChainPtr := by
  decide

theorem legacy_la_chain_range :
    laInRange (legacyH + 204) legacyLinkedChainPtr := by
  decide

theorem legacy_la_chain_enc_hi :
    Codegen.laHi GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 216) =
      Rv64.laHi (legacyH + 216) legacyLinkedChainEncPtr := by
  decide

theorem legacy_la_chain_enc_lo :
    Codegen.laLo GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 216) =
      Rv64.laLo (legacyH + 216) legacyLinkedChainEncPtr := by
  decide

theorem legacy_la_chain_enc_range :
    laInRange (legacyH + 216) legacyLinkedChainEncPtr := by
  decide

theorem legacy_la_nth_off_hi :
    Codegen.laHi GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 104) =
      Rv64.laHi (legacyH + 104) legacyLinkedNthOffPtr := by
  decide

theorem legacy_la_nth_off_lo :
    Codegen.laLo GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 104) =
      Rv64.laLo (legacyH + 104) legacyLinkedNthOffPtr := by
  decide

theorem legacy_la_nth_off_range :
    laInRange (legacyH + 104) legacyLinkedNthOffPtr := by
  decide

theorem legacy_la_nth_len_hi :
    Codegen.laHi GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 112) =
      Rv64.laHi (legacyH + 112) legacyLinkedNthLenPtr := by
  decide

theorem legacy_la_nth_len_lo :
    Codegen.laLo GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 112) =
      Rv64.laLo (legacyH + 112) legacyLinkedNthLenPtr := by
  decide

theorem legacy_la_nth_len_range :
    laInRange (legacyH + 112) legacyLinkedNthLenPtr := by
  decide

theorem legacyNthOffPtr_spec (v13 : Word) :
    cpsTripleWithin 2 (legacyH + 104) (legacyH + 112) legacyFullCode
      (.x13 ↦ᵣ v13) (.x13 ↦ᵣ legacyLinkedNthOffPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 104)
        (.AUIPC .x13 (Rv64.laHi (legacyH + 104) legacyLinkedNthOffPtr)) a = some i →
        legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 104) 26
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 104))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_nth_off_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 104) + 4)
        (.ADDI .x13 .x13 (Rv64.laLo (legacyH + 104) legacyLinkedNthOffPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 108) 27
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.t155_offset_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 104))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 104 : Word) + 4 = legacyH + 108 := by decide
    rw [hpc, ← legacy_la_nth_off_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x13 v13 (legacyH + 104)
    legacyLinkedNthOffPtr (by decide) legacy_la_nth_off_range hau had
  rw [show (legacyH + 104 : Word) + 8 = legacyH + 112 from by decide] at hla
  exact hla

theorem legacyNthLenPtr_spec (v14 : Word) :
    cpsTripleWithin 2 (legacyH + 112) (legacyH + 120) legacyFullCode
      (.x14 ↦ᵣ v14) (.x14 ↦ᵣ legacyLinkedNthLenPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 112)
        (.AUIPC .x14 (Rv64.laHi (legacyH + 112) legacyLinkedNthLenPtr)) a = some i →
        legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 112) 28
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 112))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_nth_len_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 112) + 4)
        (.ADDI .x14 .x14 (Rv64.laLo (legacyH + 112) legacyLinkedNthLenPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 116) 29
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.t155_length_hi
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 112))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 112 : Word) + 4 = legacyH + 116 := by decide
    rw [hpc, ← legacy_la_nth_len_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x14 v14 (legacyH + 112)
    legacyLinkedNthLenPtr (by decide) legacy_la_nth_len_range hau had
  rw [show (legacyH + 112 : Word) + 8 = legacyH + 120 from by decide] at hla
  exact hla

theorem legacyNthLenPtr_own_spec :
    cpsTripleWithin 2 (legacyH + 112) (legacyH + 120) legacyFullCode
      (regOwn .x14) (.x14 ↦ᵣ legacyLinkedNthLenPtr) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn_single (r := .x14)
  intro v14
  exact legacyNthLenPtr_spec v14

theorem legacyNthPtrs_spec (v13 v14 : Word) :
    cpsTripleWithin (2 + 2) (legacyH + 104) (legacyH + 120) legacyFullCode
      ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))
      ((.x13 ↦ᵣ legacyLinkedNthOffPtr) **
        (.x14 ↦ᵣ legacyLinkedNthLenPtr)) := by
  have h1 := legacyNthOffPtr_spec v13
  have h1F := cpsTripleWithin_frameR (.x14 ↦ᵣ v14) (by pcf) h1
  have h1W : cpsTripleWithin 2 (legacyH + 104) (legacyH + 112)
      legacyFullCode
      ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))
      ((.x14 ↦ᵣ v14) ** (.x13 ↦ᵣ legacyLinkedNthOffPtr)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have h2 := legacyNthLenPtr_spec v14
  have h2F := cpsTripleWithin_frameR
    (.x13 ↦ᵣ legacyLinkedNthOffPtr) (by pcf) h2
  have h2W : cpsTripleWithin 2 (legacyH + 112) (legacyH + 120)
      legacyFullCode
      ((.x14 ↦ᵣ v14) ** (.x13 ↦ᵣ legacyLinkedNthOffPtr))
      ((.x13 ↦ᵣ legacyLinkedNthOffPtr) **
        (.x14 ↦ᵣ legacyLinkedNthLenPtr)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_same_cr h1W h2W

theorem legacyNthSetup_spec
    (inPtr lenW v10 v11 v12 outPtr : Word) :
    cpsTripleWithin 7 (legacyH + 92) (legacyH + 120) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ outPtr) ** regOwn .x14)
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) **
        (.x13 ↦ᵣ legacyLinkedNthOffPtr) **
        (.x14 ↦ᵣ legacyLinkedNthLenPtr)) := by
  have hargs := legacyNthArgMoves_spec inPtr lenW v10 v11 v12
  have hargsF := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ outPtr) ** regOwn .x14) (by pcf) hargs
  have hargsW : cpsTripleWithin 3 (legacyH + 92) (legacyH + 104) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ outPtr) ** regOwn .x14)
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) ** (.x13 ↦ᵣ outPtr) **
        regOwn .x14) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hargsF
  have hoff := legacyNthOffPtr_spec outPtr
  have hoffF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
      (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) ** regOwn .x14) (by pcf) hoff
  have hoffW : cpsTripleWithin 2 (legacyH + 104) (legacyH + 112) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) ** (.x13 ↦ᵣ outPtr) **
        regOwn .x14)
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) **
        (.x13 ↦ᵣ legacyLinkedNthOffPtr) ** regOwn .x14) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hoffF
  have hlen := legacyNthLenPtr_own_spec
  have hlenF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
      (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) **
      (.x13 ↦ᵣ legacyLinkedNthOffPtr)) (by pcf) hlen
  have hlenW : cpsTripleWithin 2 (legacyH + 112) (legacyH + 120) legacyFullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) **
        (.x13 ↦ᵣ legacyLinkedNthOffPtr) ** regOwn .x14)
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) **
        (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ (5 : Word)) **
        (.x13 ↦ᵣ legacyLinkedNthOffPtr) **
        (.x14 ↦ᵣ legacyLinkedNthLenPtr)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlenF
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hargsW hoffW
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq hlenW

theorem legacySetupThenNthCall_spec
    (a0 a1 a2 a3 vOld sp0 hdrLen v21 : Word)
    (oldOff oldLen : Word) (input : List (BitVec 8)) (listLen : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (halign : a0.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalid : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (7 + (1 + ((12 + ((85 + 93 * (5 + 2)) + 6)) + 9)))
      (legacyH + 92) (legacyH + 124) legacyFullCode
      (((.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x10 ↦ᵣ a0) **
        (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** regOwn .x14) **
       ((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ hdrLen) **
        (.x21 ↦ᵣ v21) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) ** F))
      (((.x1 ↦ᵣ (legacyNthJalPC + 4)) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 a0 (5 : Word)
          legacyNthOffPtr legacyNthLenPtr oldOff oldLen
          { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2,
            s3 := a3, s4 := hdrLen, s5 := v21 }
          input listLen 5) ** F) := by
  have hsetup := legacyNthSetup_spec a0 a1 a0 a1 a2 a3
  have hAmb :
      ((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ hdrLen) **
        (.x21 ↦ᵣ v21) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
        (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) ** F).pcFree := by
    pcf
    exact hF
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
      (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ hdrLen) **
      (.x21 ↦ᵣ v21) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion a0 input **
      (legacyNthOffPtr ↦ₘ oldOff) ** (legacyNthLenPtr ↦ₘ oldLen) ** F)
    hAmb hsetup
  have hcall := legacyNth_callWithin vOld sp0 a0 a1 oldOff oldLen
    { ra := legacyNthJalPC + 4, s0 := a0, s1 := a1, s2 := a2,
      s3 := a3, s4 := hdrLen, s5 := v21 }
    input listLen F hF hlistLenW halign hslack hover hvalid
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold EvmAsm.Codegen.RlpListNthItemSAsm.callEntryRest
        EvmAsm.Codegen.RlpListNthItemSAsm.entryRest
        EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail
      xperm_hyp hp)
    hsetupF hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

/-! ## K146 post-Nth status branch

    The linked body branches immediately after `rlp_list_nth_item` returns:
    nonzero status goes to the common `li a0, 1` tail, while zero falls
    through to the payload-length path.  These are kept as separate linked
    branch lemmas so the later `Result` peel cannot hide the actual status
    test. -/

abbrev legacyNthFailBeqOff : BitVec 13 :=
  brOff (GuestAddrs.tx_signing_hash_legacy_eip155 + 436)
    (GuestAddrs.tx_signing_hash_legacy_eip155 + 124)

theorem legacyNthFailBeq_taken_pc :
    (legacyH + 124) + signExtend13 legacyNthFailBeqOff = legacyFailLiPC := by
  unfold legacyNthFailBeqOff legacyFailLiPC legacyH
  decide

theorem legacyNthFail_taken (st : Word) (hnz : st ≠ 0) :
    cpsTripleWithin 1 (legacyH + 124) legacyFailLiPC legacyFullCode
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 legacyNthFailBeqOff st 0
    (legacyH + 124)
  rw [legacyNthFailBeq_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 124) 31
        (.BNE .x10 .x0 legacyNthFailBeqOff) (by decide) (by decide)
        (by intro h; rfl)) hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hnz ((sepConj_pure_right _).1 hBP).2)

theorem legacyNthFail_ntaken (st : Word) (hz : st = 0) :
    cpsTripleWithin 1 (legacyH + 124) (legacyH + 128) legacyFullCode
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 legacyNthFailBeqOff st 0
    (legacyH + 124)
  rw [show (legacyH + 124 : Word) + 4 = legacyH + 128 from by decide] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (legacy_mem_at (legacyH + 124) 31
        (.BNE .x10 .x0 legacyNthFailBeqOff) (by decide) (by decide)
        (by intro h; rfl)) hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 hz)

theorem legacyNthFailThroughBodyExit_spec
    (st : Word) (F : Assertion) (hF : F.pcFree) (hnz : st ≠ 0) :
    cpsTripleWithin 2 (legacyH + 124) (legacyH + 440) legacyFullCode
      (((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word))) ** F)
      (((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F) := by
  have hbranch := legacyNthFail_taken st hnz
  have hbranchF := cpsTripleWithin_frameR F hF hbranch
  have hfail := legacyFailLi_spec st
  have hfailF := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hfail
  have hfailW : cpsTripleWithin 1 legacyFailLiPC (legacyH + 440)
      legacyFullCode
      (((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word))) ** F)
      (((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hfailF
  exact cpsTripleWithin_seq_same_cr hbranchF hfailW

/-- Peel the existential `callReturnResult` into the concrete `Result` case
    needed by the post-Nth branch. -/
theorem legacy_cpsTripleWithin_callReturn_pre
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h : ∀ status offset len v11 v12,
        EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
          oldOffset oldLen status offset len →
        cpsTripleWithin N (legacyH + 124) ret legacyFullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
              EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail csaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q) :
    cpsTripleWithin N (legacyH + 124) ret legacyFullCode
      (((.x1 ↦ᵣ X) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 listBase indexW
          offsetPtr lenPtr oldOffset oldLen csaved bytes listLen index) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult at hcRR
  obtain ⟨status, offset, len, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status offset len v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

private structure LoopMemAtom where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive LoopWitnessAtom where
  | reg (r : Reg) (v : Word)
  | ownReg (r : Reg)
  | mem (m : LoopMemAtom)

private def loopWitnessAssertion : LoopWitnessAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .ownReg r => regOwn r
  | .mem m => m.a ↦ₘ m.v

private def loopWitnessHeap : LoopWitnessAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .ownReg r => PartialState.singletonReg r 0
  | .mem m => PartialState.singletonMem m.a m.v

private inductive LoopWitnessResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def loopWitnessResource : LoopWitnessAtom → LoopWitnessResource
  | .reg r _ => .reg r
  | .ownReg r => .reg r
  | .mem m => .mem m.a

private theorem loop_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r
    right
    simp [PartialState.singletonReg, hne]
  · left
    simp [PartialState.singletonReg, h]

private theorem loop_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

private theorem loop_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem loop_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  loop_reg_mem_disjoint.symm

private theorem loopWitnessHeap_disjoint_of_resource_ne
    {x y : LoopWitnessAtom}
    (h : loopWitnessResource x ≠ loopWitnessResource y) :
    (loopWitnessHeap x).Disjoint (loopWitnessHeap y) := by
  cases x <;> cases y
  · apply loop_reg_reg_disjoint
    simpa [loopWitnessResource] using h
  · apply loop_reg_reg_disjoint
    simpa [loopWitnessResource] using h
  · exact loop_reg_mem_disjoint
  · apply loop_reg_reg_disjoint
    simpa [loopWitnessResource] using h
  · apply loop_reg_reg_disjoint
    simpa [loopWitnessResource] using h
  · exact loop_reg_mem_disjoint
  · exact loop_mem_reg_disjoint
  · exact loop_mem_reg_disjoint
  · apply loop_mem_mem_disjoint
    simpa [loopWitnessResource] using h

private def loopWitnessAtoms : List LoopWitnessAtom :=
  [ .reg .x5 (0x1000 : Word)
  , .reg .x6 (7 : Word)
  , .reg .x18 (1 : Word)
  , .reg .x0 (0 : Word)
  , .ownReg .x7
  , .ownReg .x28
  , .mem ⟨0x1000, 0, by decide⟩
  ]

private theorem loopWitnessAtoms_resource_pairwise :
    loopWitnessAtoms.Pairwise
      (fun x y => loopWitnessResource x ≠ loopWitnessResource y) := by
  unfold loopWitnessAtoms loopWitnessResource
  decide

private def loopWitnessHeapFold : PartialState :=
  loopWitnessAtoms.foldr
    (fun x acc => (loopWitnessHeap x).union acc) PartialState.empty

private theorem loopWitness_hsat :
    (loopWitnessAtoms.foldr
      (fun x acc => loopWitnessAssertion x ** acc) empAssertion)
      loopWitnessHeapFold := by
  apply sepConj_foldr_satisfiable
    loopWitnessAssertion loopWitnessHeap loopWitnessAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | ownReg r => exact ⟨0, rfl⟩
    | mem m => exact ⟨rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => loopWitnessHeap_disjoint_of_resource_ne h)
      loopWitnessAtoms_resource_pairwise

theorem loopInv_zero_inhabited :
    ∃ h : PartialState,
      loopInv (0x1000 : Word) (1 : Word) empAssertion 0 h := by
  have hpack :
      packBytes (List.replicate 8 (0 : BitVec 8)) = (0 : Word) := by
    decide
  have hpack' :
      packBytes ([0, 0, 0, 0, 0, 0, 0, 0] : List (BitVec 8)) =
        (0 : Word) := by
    decide
  refine ⟨loopWitnessHeapFold, ?_⟩
  simpa [loopInv, chainWin_zero, loopWitnessHeapFold,
    loopWitnessAtoms, loopWitnessAssertion, loopWitnessHeap,
    bytesRegion, bytesRegionAux, counterVal, hpack, hpack',
    packBytes, getByteAt, packDword, sepConj_emp_right'] using loopWitness_hsat

private def loopWitnessAtoms_mid : List LoopWitnessAtom :=
  [ .reg .x5 (0x1003 : Word)
  , .reg .x6 (4 : Word)
  , .reg .x18 (0x0102030405060708 : Word)
  , .reg .x0 (0 : Word)
  , .ownReg .x7
  , .ownReg .x28
  , .mem ⟨0x1000,
      packBytes ([1, 2, 3, 0, 0, 0, 0, 0] : List (BitVec 8)), by decide⟩
  ]

private theorem loopWitnessAtoms_mid_resource_pairwise :
    loopWitnessAtoms_mid.Pairwise
      (fun x y => loopWitnessResource x ≠ loopWitnessResource y) := by
  unfold loopWitnessAtoms_mid loopWitnessResource
  decide

private def loopWitnessHeapFold_mid : PartialState :=
  loopWitnessAtoms_mid.foldr
    (fun x acc => (loopWitnessHeap x).union acc) PartialState.empty

private theorem loopWitness_hsat_mid :
    (loopWitnessAtoms_mid.foldr
      (fun x acc => loopWitnessAssertion x ** acc) empAssertion)
      loopWitnessHeapFold_mid := by
  apply sepConj_foldr_satisfiable
    loopWitnessAssertion loopWitnessHeap loopWitnessAtoms_mid
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | ownReg r => exact ⟨0, rfl⟩
    | mem m => exact ⟨rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => loopWitnessHeap_disjoint_of_resource_ne h)
      loopWitnessAtoms_mid_resource_pairwise

theorem loopInv_three_inhabited :
    ∃ h : PartialState,
      loopInv (0x1000 : Word) (0x0102030405060708 : Word)
        empAssertion 3 h := by
  have hchain :
      chainWin (0x0102030405060708 : Word) 3 =
        ([1, 2, 3, 0, 0, 0, 0, 0] : List (BitVec 8)) := by
    decide
  have hpack :
      packBytes ([1, 2, 3, 0, 0, 0, 0, 0] : List (BitVec 8)) =
        packBytes (chainWin (0x0102030405060708 : Word) 3) := by
    rw [hchain]
  have hlen :
      (chainWin (0x0102030405060708 : Word) 3).length = 8 := by
    rw [hchain]
    decide
  refine ⟨loopWitnessHeapFold_mid, ?_⟩
  unfold loopInv
  rw [hchain]
  simpa [loopInv, loopWitnessHeapFold_mid,
    loopWitnessAtoms_mid, loopWitnessAssertion, loopWitnessHeap,
    bytesRegion, bytesRegionAux, counterVal, hchain, hlen, hpack,
    packBytes, getByteAt, packDword, sepConj_emp_right'] using loopWitness_hsat_mid

end EvmAsm.Codegen.TxSigningHashLegacyCompose
