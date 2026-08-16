/-
  K146 chain-id reverse loop.

  This is the direct CPS lift for the eight-byte big-endian chain-id loop in
  `tx_signing_hash_legacy_eip155`.  Keeping it separate from the caller
  contract makes the loop's signed countdown and owned scratch explicit.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacySpecCore
import EvmAsm.Codegen.Programs.RlpEncodeBytesSAsm
import EvmAsm.Codegen.Programs.Blake2fStoreLe64SAsm
import EvmAsm.Rv64.SAsm.RetFromLoop
import EvmAsm.Rv64.SAsm.AccumLoop
import EvmAsm.Rv64.Tactics.XCancelStruct

namespace EvmAsm.Codegen.TxSigningHashLegacyLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Blake2fStoreLe64SAsm

def chainBytes (chainId : Word) : List (BitVec 8) :=
  [((chainId >>> 56) &&& (255 : Word)).truncate 8,
   ((chainId >>> 48) &&& (255 : Word)).truncate 8,
   ((chainId >>> 40) &&& (255 : Word)).truncate 8,
   ((chainId >>> 32) &&& (255 : Word)).truncate 8,
   ((chainId >>> 24) &&& (255 : Word)).truncate 8,
   ((chainId >>> 16) &&& (255 : Word)).truncate 8,
   ((chainId >>> 8) &&& (255 : Word)).truncate 8,
   ((chainId >>> 0) &&& (255 : Word)).truncate 8]

def chainWin (chainId : Word) (i : Nat) : List (BitVec 8) :=
  (chainBytes chainId).take i ++ List.replicate (8 - i) 0

theorem chainWin_zero (chainId : Word) :
    chainWin chainId 0 = List.replicate 8 0 := by
  simp [chainWin]

theorem chainWin_full (chainId : Word) :
    chainWin chainId 8 = chainBytes chainId := by
  simp [chainWin, chainBytes]

theorem chainWin_step (chainId : Word) (i : Nat) (hi : i < 8) :
    setBytes (chainWin chainId i) i
      [((chainId >>> (8 * (7 - i))) &&& (255 : Word)).truncate 8] =
      chainWin chainId (i + 1) := by
  interval_cases i <;> simp [chainWin, chainBytes, setBytes]

theorem chainWin_set_step (chainId : Word) (i : Nat) (hi : i < 8) :
    (chainWin chainId i).set i
      (((chainId >>> (8 * (7 - i))) &&& (255 : Word)).truncate 8) =
      chainWin chainId (i + 1) := by
  interval_cases i <;> simp [chainWin, chainBytes]

theorem chainBytes_length (chainId : Word) : (chainBytes chainId).length = 8 := by
  simp [chainBytes]

theorem chainWin_length (chainId : Word) (i : Nat) (hi : i ≤ 8) :
    (chainWin chainId i).length = 8 := by
  simp [chainWin, chainBytes_length]
  omega

theorem chainByte_eq_shift (chainId : Word) (i : Nat) (hi : i < 8) :
    ((chainId >>> (8 * (7 - i))) &&& (255 : Word)).truncate 8 =
      (chainBytes chainId).getD i 0 := by
  interval_cases i <;> simp [chainBytes]

private theorem slt_small_false (i : Nat) (h : i < 8) :
    BitVec.slt (BitVec.ofNat 64 i) (0 : Word) = false := by
  interval_cases i <;> decide

private theorem slt_neg_one : BitVec.slt (-1 : Word) (0 : Word) = true := by
  decide

theorem slt_counter_small (i : Nat) (hi : i < 8) :
    BitVec.slt (BitVec.ofNat 64 (7 - i)) (0 : Word) = false := by
  have hi' : 7 - i < 8 := by omega
  exact slt_small_false _ hi'

theorem slt_counter_exit :
    BitVec.slt (-1 : Word) (0 : Word) = true := slt_neg_one

theorem chain_ptr_step (p : Word) (i : Nat) :
    p + BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) =
      p + BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
  bv_omega

def counterVal (i : Nat) : Word :=
  if i < 8 then BitVec.ofNat 64 (7 - i) else -1

theorem shift_count_eq (i : Nat) (hi : i < 8) :
    (counterVal i <<< 3).toNat % 64 = 8 * (7 - i) := by
  interval_cases i <;> decide

theorem chain_counter_step (i : Nat) (hi : i < 8) :
    counterVal i + signExtend12 (-1 : BitVec 12) = counterVal (i + 1) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) by decide]
  interval_cases i <;> simp [counterVal]

def loopProg : List Instr :=
  [.BLT .x6 .x0 (32 : BitVec 13),
   .SLLI .x7 .x6 (3 : BitVec 6),
   .SRL .x28 .x18 .x7,
   .ANDI .x28 .x28 (255 : BitVec 12),
   .SB .x5 .x28 (0 : BitVec 12),
   .ADDI .x5 .x5 (1 : BitVec 12),
   .ADDI .x6 .x6 (-1 : BitVec 12),
   .JAL .x0 (-28 : BitVec 21)]

def loopInv (dst chainId : Word) (F : Assertion) (i : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
  ((.x6 : Reg) ↦ᵣ counterVal i) **
  ((.x18 : Reg) ↦ᵣ chainId) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x7 ** regOwn .x28 **
  bytesRegion dst (chainWin chainId i) ** F

set_option maxRecDepth 8000 in
theorem loopBody_pinned (base dst chainId : Word) (F : Assertion)
    (i : Nat) (hi : i < 8) (v7 v28 : Word) (hF : F.pcFree)
    (halign : dst.toNat % 8 = 0) (hover : dst.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 →
      isValidByteAccess (dst + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 7 (base + 4) base (CodeReq.ofProg base loopProg)
      (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
       ((.x6 : Reg) ↦ᵣ counterVal i) ** ((.x18 : Reg) ↦ᵣ chainId) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion dst (chainWin chainId i) ** F)
      (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
       ((.x6 : Reg) ↦ᵣ counterVal (i + 1)) ** ((.x18 : Reg) ↦ᵣ chainId) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x7 : Reg) ↦ᵣ (counterVal i <<< 3)) **
       ((.x28 : Reg) ↦ᵣ ((chainId >>> (8 * (7 - i))) &&& (255 : Word))) **
       bytesRegion dst (chainWin chainId (i + 1)) ** F) := by
  set CR := CodeReq.ofProg base loopProg with hCR
  have hlen : (chainWin chainId i).length = 8 :=
    chainWin_length _ _ (by omega)
  have hidx : i < (chainWin chainId i).length := by rw [hlen]; omega
  have hbyte := chainByte_eq_shift chainId i hi
  have h255 : signExtend12 (255 : BitVec 12) = (255 : Word) := by decide
  have hSlli := liftCode (cr' := CR)
    (slli_spec_gen_within .x7 .x6 v7 (counterVal i) (3 : BitVec 6)
      (base + 4) (by decide))
    (CodeReq.ofProg_mem_at base (base + 4) loopProg 1
      (.SLLI .x7 .x6 (3 : BitVec 6)) rfl (by decide +kernel)
      (by decide +kernel) hbound)
  have hSlliF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion dst (chainWin chainId i) ** F)
    (by pcf; exact hF) hSlli
  have hSrl := liftCode (cr' := CR)
    (srl_spec_gen_within .x28 .x18 .x7 v28 chainId (counterVal i <<< 3)
      (base + 8) (by decide))
    (CodeReq.ofProg_mem_at base (base + 8) loopProg 2
      (.SRL .x28 .x18 .x7) rfl (by decide +kernel)
      (by decide +kernel) hbound)
  have hSrlF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
      ((.x6 : Reg) ↦ᵣ counterVal i) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion dst (chainWin chainId i) ** F)
    (by pcf; exact hF) hSrl
  have hAnd := liftCode (cr' := CR)
    (andi_spec_gen_same_within .x28
      (chainId >>> ((counterVal i <<< 3).toNat % 64))
      (255 : BitVec 12) (base + 12) (by decide))
    (CodeReq.ofProg_mem_at base (base + 12) loopProg 3
      (.ANDI .x28 .x28 (255 : BitVec 12)) rfl (by decide +kernel)
      (by decide +kernel) hbound)
  have hAndF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
      ((.x6 : Reg) ↦ᵣ counterVal i) ** ((.x18 : Reg) ↦ᵣ chainId) **
      ((.x7 : Reg) ↦ᵣ (counterVal i <<< 3)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion dst (chainWin chainId i) ** F)
    (by pcf; exact hF) hAnd
  have hstep : dst.toNat + i < dst.toNat + 8 := by omega
  have hi_over : dst.toNat + i < 2 ^ 64 := lt_of_lt_of_le hstep hover
  have hSb := liftCode (cr' := CR)
    (bytesRegion_sb_within .x5 .x28 dst
      ((chainId >>> ((counterVal i <<< 3).toNat % 64)) &&&
        signExtend12 (255 : BitVec 12))
      (base + 16) (chainWin chainId i) i halign hidx hi_over (hvalid i hi))
    (CodeReq.ofProg_mem_at base (base + 16) loopProg 4
      (.SB .x5 .x28 (0 : BitVec 12)) rfl (by decide +kernel)
      (by decide +kernel) hbound)
  have hSbF := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ counterVal i) **
      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x7 : Reg) ↦ᵣ (counterVal i <<< 3)) ** F)
    (by pcf; exact hF) hSb
  have hAddi5 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x5 (dst + BitVec.ofNat 64 i)
      (1 : BitVec 12) (base + 20) (by decide))
    (CodeReq.ofProg_mem_at base (base + 20) loopProg 5
      (.ADDI .x5 .x5 (1 : BitVec 12)) rfl (by decide +kernel)
      (by decide +kernel) hbound)
  have hAddi5F := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x6 : Reg) ↦ᵣ counterVal i) **
      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x7 : Reg) ↦ᵣ (counterVal i <<< 3)) **
      ((.x28 : Reg) ↦ᵣ ((chainId >>> ((counterVal i <<< 3).toNat % 64)) &&&
        signExtend12 (255 : BitVec 12))) **
      bytesRegion dst ((chainWin chainId i).set i
        (((chainId >>> ((counterVal i <<< 3).toNat % 64)) &&&
          signExtend12 (255 : BitVec 12)).truncate 8)) ** F)
    (by pcf; exact hF) hAddi5
  have hAddi6 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x6 (counterVal i)
      (-1 : BitVec 12) (base + 24) (by decide))
    (CodeReq.ofProg_mem_at base (base + 24) loopProg 6
      (.ADDI .x6 .x6 (-1 : BitVec 12)) rfl (by decide +kernel)
      (by decide +kernel) hbound)
  have hAddi6F := cpsTripleWithin_frameR
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
      ((.x18 : Reg) ↦ᵣ chainId) ** ((.x7 : Reg) ↦ᵣ (counterVal i <<< 3)) **
      ((.x28 : Reg) ↦ᵣ ((chainId >>> ((counterVal i <<< 3).toNat % 64)) &&&
        signExtend12 (255 : BitVec 12))) **
      bytesRegion dst ((chainWin chainId i).set i
        (((chainId >>> ((counterVal i <<< 3).toNat % 64)) &&&
          signExtend12 (255 : BitVec 12)).truncate 8)) ** F)
    (by pcf; exact hF) hAddi6
  have hJal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-28 : BitVec 21) (base + 28))
    (CodeReq.ofProg_mem_at base (base + 28) loopProg 7
      (.JAL .x0 (-28 : BitVec 21)) rfl (by decide +kernel)
      (by decide +kernel) hbound)
  have hJalF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
      ((.x6 : Reg) ↦ᵣ counterVal (i + 1)) ** ((.x18 : Reg) ↦ᵣ chainId) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x7 : Reg) ↦ᵣ (counterVal i <<< 3)) **
      ((.x28 : Reg) ↦ᵣ ((chainId >>> ((counterVal i <<< 3).toNat % 64)) &&&
        signExtend12 (255 : BitVec 12))) **
      bytesRegion dst ((chainWin chainId i).set i
        (((chainId >>> ((counterVal i <<< 3).toNat % 64)) &&&
          signExtend12 (255 : BitVec 12)).truncate 8)) ** F)
    (by pcf; exact hF) hJal
  rw [shift_count_eq i hi] at hSrlF hAndF hSbF hAddi5F hAddi6F hJalF
  simp only [h255] at hAndF hSbF hAddi5F hAddi6F hJalF
  have hthree : BitVec.toNat (3 : BitVec 6) = 3 := by decide
  rw [hthree] at hSlliF
  rw [chainWin_set_step chainId i hi] at hSbF hAddi5F hAddi6F hJalF
  rw [chain_ptr_step] at hAddi5F
  rw [chain_counter_step i hi] at hAddi6F
  have hpc08 : base + 4 + 4 = base + 8 := by simp [BitVec.add_assoc]
  have hpc12 : base + 8 + 4 = base + 12 := by simp [BitVec.add_assoc]
  have hpc16 : base + 12 + 4 = base + 16 := by simp [BitVec.add_assoc]
  have hpc20 : base + 16 + 4 = base + 20 := by simp [BitVec.add_assoc]
  have hpc24 : base + 20 + 4 = base + 24 := by simp [BitVec.add_assoc]
  have hpc28 : base + 24 + 4 = base + 28 := by simp [BitVec.add_assoc]
  rw [hpc08] at hSlliF
  rw [hpc12] at hSrlF
  rw [hpc16] at hAndF
  rw [hpc20] at hSbF
  rw [hpc24] at hAddi5F
  rw [hpc28] at hAddi6F
  have h1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) hSlliF hSrlF
  have h2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) h1 hAndF
  have h3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) h2 hSbF
  have h4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) h3 hAddi5F
  have h5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) h4 hAddi6F
  have hJalF' := cpsTripleWithin_weaken
    (fun _ hp => by rw [sepConj_emp_left']; exact hp)
    (fun _ hq => by rw [sepConj_emp_left'] at hq; exact hq) hJalF
  have hjal_target : base + 28 + signExtend21 (-28 : BitVec 21) = base := by
    rw [show signExtend21 (-28 : BitVec 21) = (-28 : Word) by decide]
    bv_omega
  rw [hjal_target] at hJalF'
  have h6 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) h5 hJalF'
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) h6

set_option maxRecDepth 8000 in
theorem loopBody_owned (base dst chainId : Word) (F : Assertion)
    (i : Nat) (hi : i < 8) (hF : F.pcFree)
    (halign : dst.toNat % 8 = 0) (hover : dst.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 → isValidByteAccess (dst + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 7 (base + 4) base (CodeReq.ofProg base loopProg)
      ((((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
       ((.x6 : Reg) ↦ᵣ counterVal i) ** ((.x18 : Reg) ↦ᵣ chainId) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion dst (chainWin chainId i) ** F) **
       regOwn .x7 ** regOwn .x28)
      (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
       ((.x6 : Reg) ↦ᵣ counterVal (i + 1)) ** ((.x18 : Reg) ↦ᵣ chainId) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x28 **
       bytesRegion dst (chainWin chainId (i + 1)) ** F) := by
  apply cpsTripleWithin_of_forall_regIs_to_regOwn2
    (P := (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
      ((.x6 : Reg) ↦ᵣ counterVal i) ** ((.x18 : Reg) ↦ᵣ chainId) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion dst (chainWin chainId i) ** F))
    (r1 := .x7) (r2 := .x28)
  intro v7 v28
  have h := loopBody_pinned base dst chainId F i hi v7 v28 hF halign hover hvalid hbound
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      have htrans : ∀ h,
          (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
           ((.x6 : Reg) ↦ᵣ counterVal (i + 1)) ** ((.x18 : Reg) ↦ᵣ chainId) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((.x7 : Reg) ↦ᵣ (counterVal i <<< 3)) **
           ((.x28 : Reg) ↦ᵣ ((chainId >>> (8 * (7 - i))) &&& (255 : Word))) **
           bytesRegion dst (chainWin chainId (i + 1)) ** F) h →
          (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
           ((.x6 : Reg) ↦ᵣ counterVal (i + 1)) ** ((.x18 : Reg) ↦ᵣ chainId) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x7 ** regOwn .x28 **
           bytesRegion dst (chainWin chainId (i + 1)) ** F) h := by
        intro hstate hh
        exact (sepConj_mono (fun _ hp => hp)
          (sepConj_mono (fun _ hp => hp)
            (sepConj_mono (fun _ hp => hp)
              (sepConj_mono (fun _ hp => hp)
                (sepConj_mono (regIs_to_regOwn .x7 (counterVal i <<< 3))
                  (sepConj_mono
                    (regIs_to_regOwn .x28
                      ((chainId >>> (8 * (7 - i))) &&& (255 : Word)))
                    (sepConj_mono (fun _ hp => hp) (fun _ hp => hp)))))))
          hstate hh)
      exact htrans _ hq) h

set_option maxRecDepth 8000 in
theorem loopHeader_owned (base dst chainId : Word) (F : Assertion)
    (i : Nat) (hi : i < 8) (hF : F.pcFree)
    (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base loopProg)
      (loopInv dst chainId F i) (loopInv dst chainId F i) := by
  set CR := CodeReq.ofProg base loopProg with hCR
  have hmono : ∀ a ins,
      CodeReq.singleton base (.BLT .x6 .x0 (32 : BitVec 13)) a = some ins →
        CR a = some ins := by
    rw [hCR]
    exact CodeReq.ofProg_mem_at base base loopProg 0
      (.BLT .x6 .x0 (32 : BitVec 13)) (by simp) (by decide) (by rfl) hbound
  have hblt := blt_spec_gen_within .x6 .x0 (32 : BitVec 13)
      (counterVal i) (0 : Word) base
  have hbr := cpsBranchWithin_extend_code (cr' := CR) hmono hblt
  let rest : Assertion :=
    ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
    ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x7 ** regOwn .x28 **
    bytesRegion dst (chainWin chainId i) ** F
  have hrestFree : rest.pcFree := by
    dsimp [rest]
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regOwn
          (pcFree_sepConj pcFree_regOwn
            (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))
  have hbrF := cpsBranchWithin_frameR rest hrestFree hbr
  have hbrWhole : cpsBranchWithin 1 base CR (loopInv dst chainId F i)
      (base + signExtend13 32) (loopInv dst chainId F i **
        ⌜(counterVal i).slt 0 = true⌝)
      (base + 4) (loopInv dst chainId F i **
        ⌜¬(counterVal i).slt 0 = true⌝) := cpsBranchWithin_weaken
    (fun _ hp => by simp only [loopInv, rest] at *; xperm_hyp hp)
    (fun _ hq => by simp only [loopInv, rest] at *; xperm_hyp hq)
    (fun _ hq => by simp only [loopInv, rest] at *; xperm_hyp hq) hbrF
  have hguard0 := cpsBranchWithin_ntakenPath hbrWhole
    (fun hp hQt => by
      have hq := (sepConj_pure_right _).1 hQt
      have hfalse : (counterVal i).slt 0 = false := by
        simpa [counterVal, hi] using slt_counter_small i hi
      rw [hfalse] at hq
      simp at hq)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp) (fun _ hq => (sepConj_pure_right _).1 hq |>.1) hguard0

set_option maxRecDepth 8000 in
theorem loopIter_owned (base dst chainId : Word) (F : Assertion)
    (i : Nat) (hi : i < 8) (hF : F.pcFree)
    (halign : dst.toNat % 8 = 0) (hover : dst.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 → isValidByteAccess (dst + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 8 base base (CodeReq.ofProg base loopProg)
      (loopInv dst chainId F i) (loopInv dst chainId F (i + 1)) := by
  have hguard := loopHeader_owned base dst chainId F i hi hF hbound
  have hbody := loopBody_owned base dst chainId F i hi hF halign hover hvalid hbound
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [loopInv] at *; xperm_hyp hp) hguard hbody

set_option maxRecDepth 8000 in
theorem loopExit_owned (base dst chainId : Word) (F : Assertion)
    (hF : F.pcFree) (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 1 base (base + 32) (CodeReq.ofProg base loopProg)
      (loopInv dst chainId F 8) (loopInv dst chainId F 8) := by
  set CR := CodeReq.ofProg base loopProg with hCR
  have hmono : ∀ a ins,
      CodeReq.singleton base (.BLT .x6 .x0 (32 : BitVec 13)) a = some ins →
        CR a = some ins := by
    rw [hCR]
    exact CodeReq.ofProg_mem_at base base loopProg 0
      (.BLT .x6 .x0 (32 : BitVec 13)) (by simp) (by decide) (by rfl) hbound
  have hblt := blt_spec_gen_within .x6 .x0 (32 : BitVec 13)
      (counterVal 8) (0 : Word) base
  have hbr := cpsBranchWithin_extend_code (cr' := CR) hmono hblt
  let rest : Assertion :=
    ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 8)) **
    ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x7 ** regOwn .x28 **
    bytesRegion dst (chainWin chainId 8) ** F
  have hrestFree : rest.pcFree := by
    dsimp [rest]
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regOwn
          (pcFree_sepConj pcFree_regOwn
            (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))
  have hbrF := cpsBranchWithin_frameR rest hrestFree hbr
  have hbrWhole : cpsBranchWithin 1 base CR (loopInv dst chainId F 8)
      (base + 32) (loopInv dst chainId F 8 **
        ⌜(counterVal 8).slt 0 = true⌝)
      (base + 4) (loopInv dst chainId F 8 **
        ⌜¬(counterVal 8).slt 0 = true⌝) := by
    have htmp : cpsBranchWithin 1 base CR (loopInv dst chainId F 8)
        (base + signExtend13 (32 : BitVec 13)) (loopInv dst chainId F 8 **
          ⌜(counterVal 8).slt 0 = true⌝)
        (base + 4) (loopInv dst chainId F 8 **
          ⌜¬(counterVal 8).slt 0 = true⌝) := cpsBranchWithin_weaken
      (fun _ hp => by simp only [loopInv, rest] at *; xperm_hyp hp)
      (fun _ hq => by simp only [loopInv, rest] at *; xperm_hyp hq)
      (fun _ hq => by simp only [loopInv, rest] at *; xperm_hyp hq) hbrF
    have haddr : base + signExtend13 (32 : BitVec 13) = base + (32 : Word) := by
      rw [show signExtend13 (32 : BitVec 13) = (32 : Word) by decide]
    rw [haddr] at htmp
    exact htmp
  have hguard0 := cpsBranchWithin_takenPath hbrWhole
    (fun hp hQf => by
      have hq := (sepConj_pure_right _).1 hQf
      have htrue : (counterVal 8).slt 0 = true := by simp [counterVal]
      rw [htrue] at hq
      simp at hq)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp) (fun _ hq => (sepConj_pure_right _).1 hq |>.1) hguard0

theorem loopCps_owned (base dst chainId : Word) (F : Assertion)
    (hF : F.pcFree)
    (halign : dst.toNat % 8 = 0) (hover : dst.toNat + 8 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 8 → isValidByteAccess (dst + BitVec.ofNat 64 k) = true)
    (hbound : 4 * loopProg.length < 2 ^ 64) :
    cpsTripleWithin 65 base (base + 32) (CodeReq.ofProg base loopProg)
      (loopInv dst chainId F 0) (loopInv dst chainId F 8) := by
  have hiter : ∀ i, i < 8 →
      cpsTripleWithin 8 base base (CodeReq.ofProg base loopProg)
        (loopInv dst chainId F i) (loopInv dst chainId F (i + 1)) := by
    intro i hi
    exact loopIter_owned base dst chainId F i hi hF halign hover hvalid hbound
  have hexh := loopExit_owned base dst chainId F hF hbound
  simpa using (retLoop_spec 8 8 1 (loopInv dst chainId F) hiter hexh)

end EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
