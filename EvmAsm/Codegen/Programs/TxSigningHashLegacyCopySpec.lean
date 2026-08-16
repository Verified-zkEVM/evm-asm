/-
  K146 chain-encoding to destination copy loop.

  This direct CPS proof covers the five-instruction byte-copy body and its
  countdown back-edge inside tx_signing_hash_legacy_eip155.  It is kept
  separate from the reverse chain-id loop so each loop contract is readable.
-/
import EvmAsm.Codegen.Programs.TxSigningHashLegacyLoopSpec
import EvmAsm.Codegen.Programs.SgMemcpySAsm
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen.TxSigningHashLegacyCopySpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.SgMemcpySAsm

def copyBodyBlock : List Instr :=
  [.LBU .x31 .x6 0,
   .SB .x5 .x31 0,
   .ADDI .x5 .x5 1,
   .ADDI .x6 .x6 1,
   .ADDI .x28 .x28 (-1 : BitVec 12)]

def copyLoopProg : List Instr :=
  [.BEQ .x28 .x0 (28 : BitVec 13)] ++ copyBodyBlock ++
  [.JAL .x0 (-24 : BitVec 21)]

def copyInv (srcBase dstBase : Word) (N : Nat)
    (srcBytes dstBytes : List (BitVec 8)) : Nat → Assertion :=
  fun n =>
    let core : Assertion :=
      ((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (N - n))) **
      ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (N - n))) **
      ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes **
      bytesRegion dstBase (copyWin srcBytes dstBytes (N - n))
    core ** regOwn .x31

def copyInvCore (srcBase dstBase : Word) (N : Nat)
    (srcBytes dstBytes : List (BitVec 8)) : Nat → Assertion :=
  fun n =>
    ((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (N - n))) **
    ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (N - n))) **
    bytesRegion srcBase srcBytes **
    bytesRegion dstBase (copyWin srcBytes dstBytes (N - n)) **
    regOwn .x31

theorem copyBody (hdr : Word)
    (srcBase dstBase : Word) (N n : Nat)
    (srcBytes dstBytes : List (BitVec 8))
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hNdst : N ≤ dstBytes.length)
    (hsi : N - (n + 1) < srcBytes.length)
    (hsover : srcBase.toNat + (N - (n + 1)) < 2 ^ 64)
    (hdover : dstBase.toNat + (N - (n + 1)) < 2 ^ 64)
    (hsvalid : isValidByteAccess
      (srcBase + BitVec.ofNat 64 (N - (n + 1))) = true)
    (hdvalid : isValidByteAccess
      (dstBase + BitVec.ofNat 64 (N - (n + 1))) = true)
    (hn : n < N) :
    cpsTripleWithin 6 (hdr + 4) hdr (CodeReq.ofProg hdr copyLoopProg)
      (copyInv srcBase dstBase N srcBytes dstBytes (n + 1))
      (copyInv srcBase dstBase N srcBytes dstBytes n) := by
  let i := N - (n + 1)
  let CR := CodeReq.ofProg hdr copyLoopProg
  have hiN : i < N := by dsimp [i]; omega
  have hdi' : i < (copyWin srcBytes dstBytes i).length := by
    have hlen := length_copyWin srcBytes dstBytes i rfl (by omega)
    rw [hlen]
    dsimp [i]
    omega
  have hconcrete (v : Word) :
    cpsTripleWithin 6 (hdr + 4) hdr CR
        (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 i)) **
         ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) **
         ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
         bytesRegion dstBase (copyWin srcBytes dstBytes i) **
         ((.x31 : Reg) ↦ᵣ v))
        (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (i + 1))) **
         ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
         ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
         bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1)) **
         ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64)) := by
    have hbound : 4 * copyLoopProg.length < 2 ^ 64 := by decide +kernel
    have hidx : i < srcBytes.length := by exact hsi
    have hdstidx : i < (copyWin srcBytes dstBytes i).length := hdi'
    have hL := liftCode (cr' := CR)
      (bytesRegion_lbu_within .x31 .x6 srcBase v (hdr + 4)
        srcBytes i (by decide) hsalign hidx hsover hsvalid)
      (CodeReq.ofProg_mem_at hdr (hdr + 4) copyLoopProg 1
        (.LBU .x31 .x6 (0 : BitVec 12)) rfl (by decide +kernel)
        (by decide +kernel) hbound)
    have hLF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 i)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion dstBase (copyWin srcBytes dstBytes i))
      (by pcFree) hL
    have hS := liftCode (cr' := CR)
      (bytesRegion_sb_within .x5 .x31 dstBase
        ((srcBytes[i]'(by omega)).zeroExtend 64) (hdr + 8)
        (copyWin srcBytes dstBytes i) i hdalign hdstidx hdover hdvalid)
      (CodeReq.ofProg_mem_at hdr (hdr + 8) copyLoopProg 2
        (.SB .x5 .x31 (0 : BitVec 12)) rfl (by decide +kernel)
        (by decide +kernel) hbound)
    have hSF := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      (by pcFree) hS
    have h5 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x5
        (dstBase + BitVec.ofNat 64 i) (1 : BitVec 12) (hdr + 12) (by decide))
      (CodeReq.ofProg_mem_at hdr (hdr + 12) copyLoopProg 3
        (.ADDI .x5 .x5 (1 : BitVec 12)) rfl (by decide +kernel)
        (by decide +kernel) hbound)
    have h5F := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1)) **
       ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64))
      (by pcFree) h5
    have h6 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x6
        (srcBase + BitVec.ofNat 64 i) (1 : BitVec 12) (hdr + 16) (by decide))
      (CodeReq.ofProg_mem_at hdr (hdr + 16) copyLoopProg 4
        (.ADDI .x6 .x6 (1 : BitVec 12)) rfl (by decide +kernel)
        (by decide +kernel) hbound)
    have h6F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (i + 1))) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1)) **
       ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64))
      (by pcFree) h6
    have h28 := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x28
        (BitVec.ofNat 64 (n + 1)) (-1 : BitVec 12) (hdr + 20) (by decide))
      (CodeReq.ofProg_mem_at hdr (hdr + 20) copyLoopProg 5
        (.ADDI .x28 .x28 (-1 : BitVec 12)) rfl (by decide +kernel)
        (by decide +kernel) hbound)
    have h28F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (i + 1))) **
       ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1)) **
       ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64))
      (by pcFree) h28
    have hJ := liftCode (cr' := CR)
      (jal_x0_spec_gen_within (-24 : BitVec 21) (hdr + 24))
      (CodeReq.ofProg_mem_at hdr (hdr + 24) copyLoopProg 6
        (.JAL .x0 (-24 : BitVec 21)) rfl (by decide +kernel)
        (by decide +kernel) hbound)
    have hJF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (i + 1))) **
       ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1)) **
       ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64))
      (by pcFree) hJ
    rw [show hdr + 4 + 4 = hdr + 8 from by bv_omega] at hLF
    rw [show hdr + 8 + 4 = hdr + 12 from by bv_omega] at hSF
    rw [show hdr + 12 + 4 = hdr + 16 from by bv_omega] at h5F
    rw [show hdr + 16 + 4 = hdr + 20 from by bv_omega] at h6F
    rw [show hdr + 20 + 4 = hdr + 24 from by bv_omega] at h28F
    have hbyte : BitVec.truncate 8
        (BitVec.zeroExtend 64 srcBytes[i]) = srcBytes[i] := by simp
    have hwin : (copyWin srcBytes dstBytes i).set i (srcBytes[i]'(by omega)) =
        copyWin srcBytes dstBytes (i + 1) := by
      have hcopy : copyByte srcBytes i = srcBytes[i]'(by omega) := by
        simp [copyByte, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show i < srcBytes.length by omega)]
      rw [← setBytes_singleton]
      simpa [hcopy] using copyWin_step srcBytes dstBytes i rfl (by omega)
    rw [hbyte, hwin] at hSF
    have hdststep : dstBase + BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) =
        dstBase + BitVec.ofNat 64 (i + 1) := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
      bv_omega
    have hsrcstep : srcBase + BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) =
        srcBase + BitVec.ofNat 64 (i + 1) := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
      bv_omega
    have hcountstep : BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) =
        BitVec.ofNat 64 n := by
      rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) by decide]
      bv_omega
    rw [hdststep] at h5F
    rw [hsrcstep] at h6F
    rw [hcountstep] at h28F
    have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) hLF hSF
    have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) h1 h5F
    have h3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) h2 h6F
    have h4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) h3 h28F
    have hjump : hdr + 24 + signExtend21 (-24 : BitVec 21) = hdr := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) by decide]
      bv_omega
    rw [hjump] at hJF
    have hJF' := cpsTripleWithin_weaken (fun _ hp => by simpa only [sepConj_emp_left'] using hp)
      (fun _ hq => by simpa only [sepConj_emp_left'] using hq) hJF
    have h5' := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) h4 hJF'
    exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun _ hp => by xcancel_struct hp) h5'
  let Ppre : Assertion :=
    ((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 i)) **
    ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) **
    ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
    bytesRegion dstBase (copyWin srcBytes dstBytes i)
  let Ppost : Assertion :=
    ((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (i + 1))) **
    ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
    ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
    bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1)) **
    ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64)
  have hconcrete' : ∀ v, cpsTripleWithin 6 (hdr + 4) hdr CR
      (Ppre ** ((.x31 : Reg) ↦ᵣ v)) Ppost := by
    intro v
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) (hconcrete v)
  have hbody := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x31)
    (P := ((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 i)) **
      ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 i)) **
      ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
      bytesRegion dstBase (copyWin srcBytes dstBytes i))
    (Q := (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (i + 1))) **
      ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
      ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
      bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1)) **
      ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64)))
    hconcrete'
  have hbody' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      let Q0 : Assertion :=
        (((.x5 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (i + 1))) **
         ((.x6 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (i + 1))) **
         ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes **
         bytesRegion dstBase (copyWin srcBytes dstBytes (i + 1))) **
        ((.x31 : Reg) ↦ᵣ (srcBytes[i]'(by omega)).zeroExtend 64)
      have hq0 : Q0 h := by
        dsimp [Q0]
        xcancel_struct hq
      have hq1 := sepConj_mono_right (regIs_implies_regOwn .x31) h hq0
      rw [show i + 1 = N - n by dsimp [i]; omega] at hq1
      exact hq1) hbody
  simpa [copyInv, i, CR] using hbody'


theorem copyLoop
    (hdr srcBase dstBase : Word) (N : Nat)
    (srcBytes dstBytes : List (BitVec 8))
    (hlen : dstBytes.length = N)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hNsrc : N ≤ srcBytes.length)
    (hsover : srcBase.toNat + N < 2 ^ 64)
    (hdover : dstBase.toNat + N < 2 ^ 64)
    (hsvalid : ∀ i, i < N → isValidByteAccess (srcBase + BitVec.ofNat 64 i) = true)
    (hdvalid : ∀ i, i < N → isValidByteAccess (dstBase + BitVec.ofNat 64 i) = true)
    (hNbound : N < 18446744073709551616) :
    cpsTripleWithin (N * (6 + 1) + 1) hdr (hdr + 28)
      (CodeReq.ofProg hdr copyLoopProg)
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 N) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInvCore srcBase dstBase N srcBytes dstBytes N)
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 0) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        copyInvCore srcBase dstBase N srcBytes dstBytes 0) := by
  let CR : CodeReq := CodeReq.ofProg hdr copyLoopProg
  have hbound : 4 * copyLoopProg.length < 2 ^ 64 := by decide +kernel
  have hguard : ∀ a i,
      CodeReq.singleton hdr (.BEQ .x28 .x0 (28 : BitVec 13)) a = some i →
        CR a = some i := by
    intro a i h
    have hm := CodeReq.ofProg_lookup_addr hdr copyLoopProg 0 hdr
      (by decide) hbound (by simp)
    rw [show copyLoopProg.get ⟨0, by decide⟩ =
      (.BEQ .x28 .x0 (28 : BitVec 13)) by rfl] at hm
    exact CodeReq.singleton_mono hm a i h
  have hpc : ∀ n, (copyInvCore srcBase dstBase N srcBytes dstBytes n).pcFree := by
    intro n
    dsimp [copyInvCore]
    pcFree
  have hbody : ∀ n, n < N →
      cpsTripleWithin 6 (hdr + 4) hdr CR
        (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          copyInvCore srcBase dstBase N srcBytes dstBytes (n + 1))
        (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          copyInvCore srcBase dstBase N srcBytes dstBytes n) := by
    intro n hn
    have hi : N - (n + 1) < N := by omega
    have hsi : N - (n + 1) < srcBytes.length := by omega
    have hdi : N - (n + 1) <
        (copyWin srcBytes dstBytes (N - (n + 1))).length := by
      rw [length_copyWin srcBytes dstBytes _ hlen (by omega)]
      omega
    have hso : srcBase.toNat + (N - (n + 1)) < 2 ^ 64 := by omega
    have hdo : dstBase.toNat + (N - (n + 1)) < 2 ^ 64 := by omega
    have hsv : isValidByteAccess
        (srcBase + BitVec.ofNat 64 (N - (n + 1))) = true := by
      exact hsvalid _ hi
    have hdv : isValidByteAccess
        (dstBase + BitVec.ofNat 64 (N - (n + 1))) = true := by
      exact hdvalid _ hi
    have hb := copyBody hdr srcBase dstBase N n srcBytes dstBytes hsalign hdalign
      (by omega) hsi hso hdo hsv hdv hn
    dsimp [copyInvCore, copyInv] at hb ⊢
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) hb
  exact countdownLoop_spec CR hdr (hdr + 28) .x28 (28 : BitVec 13)
    6 N (copyInvCore srcBase dstBase N srcBytes dstBytes)
    (by decide) hNbound
    (by rw [show signExtend13 (28 : BitVec 13) = (28 : Word) by decide])
    hpc hguard hbody

end EvmAsm.Codegen.TxSigningHashLegacyCopySpec
