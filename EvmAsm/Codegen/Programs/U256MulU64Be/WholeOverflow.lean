import EvmAsm.Codegen.Programs.U256MulU64Be.WholeCopy

namespace EvmAsm.Codegen.U256MulU64Be

open EvmAsm Rv64 Rv64.SAsm Rv64.SAsm.Stmt

theorem overflowInit_spec (F : Assertion) (hF : F.pcFree)
    (old6 old10 : Word) :
    cpsTripleWithin 2 (mulBase + 280) (mulBase + 288) mulCR
      (((.x6 : Reg) ↦ᵣ old6) ** ((.x10 : Reg) ↦ᵣ old10) ** F)
      (((.x6 : Reg) ↦ᵣ (8 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** F) := by
  have h6 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x6 old6 (8 : Word) (mulBase + 280) (by decide))
  rw [show mulBase + 280 + 4 = mulBase + 284 from by decide] at h6
  have h6F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ old10) ** F)
    (pcFree_sepConj pcFree_regIs hF) h6
  have h10 := cpsTripleWithin_extend_code (cr' := mulCR) (hmono := by code_mem)
    (li_spec_gen_within .x10 old10 (0 : Word) (mulBase + 284) (by decide))
  rw [show mulBase + 284 + 4 = mulBase + 288 from by decide] at h10
  have h10F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ (8 : Word)) ** F)
    (pcFree_sepConj pcFree_regIs hF) h10
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h6F h10F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

/-! ## Hand-managed overflow seam

The final eight-byte scan is intentionally not represented by a `Stmt`: its
machine shape is `BEQ; LBU; BEQ-to-step; LI/JAL-over-step; step; backedge`.
The following invariant is the exact CPS-level seam for the all-zero path.
The full result-producing scan will refine the same shape with the first
nonzero-byte exit; keeping this control proof separate prevents the raw block
from being mistaken for an unproved structured remainder.
-/

def overflowZeroCore (accBytes : List (BitVec 8)) (k : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
    bytesRegion accBase accBytes

def overflowZeroInv (F : Assertion) (accBytes : List (BitVec 8)) (k : Nat) : Assertion :=
  F ** overflowZeroCore accBytes k

def overflowNonzeroCore (accBytes : List (BitVec 8)) (k : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
    regOwn .x28 ** bytesRegion accBase accBytes

def overflowNonzeroInv (F : Assertion) (accBytes : List (BitVec 8)) (k : Nat) : Assertion :=
  F ** overflowNonzeroCore accBytes k

def overflowNonzeroPost (F : Assertion) (accBytes : List (BitVec 8)) : Assertion :=
  fun s => ∃ k, overflowNonzeroInv F accBytes k s

theorem overflow_scan_ctr_dec (k : Nat) (hk : k < 8) :
    BitVec.ofNat 64 (8 - k) + Rv64.signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (8 - (k + 1)) := by
  rw [show Rv64.signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  bv_omega

theorem overflow_scan_ctr_ne (k : Nat) (hk : k < 8) :
    BitVec.ofNat 64 (8 - k) ≠ 0 := by
  intro hzero
  have hnat := congrArg BitVec.toNat hzero
  simp [BitVec.toNat_ofNat] at hnat
  omega

theorem overflow_scan_ptr_succ (k : Nat) (_hk : k < 8) :
    accBase + BitVec.ofNat 64 (32 + k) + Rv64.signExtend12 (1 : BitVec 12) =
      accBase + BitVec.ofNat 64 (32 + (k + 1)) := by
  rw [show Rv64.signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  bv_omega

theorem overflow_scan_byte_valid (k : Nat) (hk : k < 8) :
    isValidByteAccess (accBase + BitVec.ofNat 64 (32 + k)) = true := by
  apply accBase_valid_byte
  omega

theorem overflow_scan_byte_no_overflow (k : Nat) (hk : k < 8) :
    accBase.toNat + (32 + k) < 2 ^ 64 := by
  apply accBase_no_overflow
  omega

theorem overflowLbu_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (hlen : accBytes.length = 40)
    (k : Nat) (hk : k < 8) :
    cpsTripleWithin 1 (mulBase + 292) (mulBase + 296) mulCR
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x28 ** bytesRegion accBase accBytes)
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ (accBytes[32 + k]'(by omega)).zeroExtend 64) **
        bytesRegion accBase accBytes) := by
  let P : Assertion := F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
    ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion accBase accBytes
  have hown : cpsTripleWithin 1 (mulBase + 292) (mulBase + 296) mulCR
      (P ** regOwn .x28)
      (P ** ((.x28 : Reg) ↦ᵣ (accBytes[32 + k]'(by omega)).zeroExtend 64)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28) ?_
    intro old28
    have hlbu := bytesRegion_lbu_within .x28 .x5 accBase old28
      (mulBase + 292) accBytes (32 + k) (by decide) accBase_align
      (by omega) (overflow_scan_byte_no_overflow k hk)
      (overflow_scan_byte_valid k hk)
    have hlbu' := cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := by code_mem) hlbu
    have hfr := cpsTripleWithin_frameR
      (F ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)))
      (by
        apply pcFree_sepConj
        · exact hF
        · pcf) hlbu'
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hfr
  unfold P at hown
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hown

theorem overflowZeroStep_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (_hlen : accBytes.length = 40)
    (k : Nat) (hk : k < 8) :
    cpsTripleWithin 3 (mulBase + 308) (mulBase + 288) mulCR
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes)
      (overflowZeroInv F accBytes (k + 1)) := by
  have h1 := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := addi_spec_gen_same_within .x5
      (accBase + BitVec.ofNat 64 (32 + k)) (1 : BitVec 12)
      (mulBase + 308) (by decide))
  rw [show mulBase + 308 + 4 = mulBase + 312 from by decide,
    overflow_scan_ptr_succ k hk] at h1
  have h1f := cpsTripleWithin_frameR
    (F ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes)
    (by
      apply pcFree_sepConj
      · exact hF
      · pcf) h1
  have h2 := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := addi_spec_gen_same_within .x6
      (BitVec.ofNat 64 (8 - k)) (-1 : BitVec 12)
      (mulBase + 312) (by decide))
  rw [show mulBase + 312 + 4 = mulBase + 316 from by decide,
    overflow_scan_ctr_dec k hk] at h2
  have h2f := cpsTripleWithin_frameR
    (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + (k + 1)))) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes)
    (by
      apply pcFree_sepConj
      · exact hF
      · pcf) h2
  have h3 := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := jal_x0_spec_gen_within (-28 : BitVec 21) (mulBase + 316))
  rw [show mulBase + 316 + Rv64.signExtend21 (-28 : BitVec 21) = mulBase + 288 from by decide] at h3
  have h3f := cpsTripleWithin_frameR
    (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + (k + 1)))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - (k + 1))) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes)
    (by
      apply pcFree_sepConj
      · exact hF
      · pcf) h3
  have h3f' : cpsTripleWithin 1 (mulBase + 316) (mulBase + 288) mulCR
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + (k + 1)))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - (k + 1))) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes)
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + (k + 1)))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - (k + 1))) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h3f
    · simpa only [sepConj_emp_left'] using hp
    · simpa only [sepConj_emp_left'] using hq
  have hs := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1f h2f
  have hs' := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs h3f'
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hs'
  intro h hq
  unfold overflowZeroInv overflowZeroCore
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
              (sepConj_mono (regIs_to_regOwn .x28 _)
                (fun _ h => h)))))) h hq

theorem overflowZeroContinue_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (hlen : accBytes.length = 40)
    (k : Nat) (hk : k < 8)
    (hzero : accBytes[32 + k]'(by omega) = 0) :
    cpsTripleWithin 5 (mulBase + 292) (mulBase + 288) mulCR
      (overflowZeroInv F accBytes k)
      (overflowZeroInv F accBytes (k + 1)) := by
  let frame : Assertion :=
    F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes
  let scanPre : Assertion :=
    F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes
  have hframe_pc : frame.pcFree := by
    dsimp only [frame]
    apply pcFree_sepConj
    · exact hF
    · pcf
  have hlbu := overflowLbu_spec F hF accBytes hlen k hk
  have hlbu' : cpsTripleWithin 1 (mulBase + 292) (mulBase + 296) mulCR
      (overflowZeroInv F accBytes k) scanPre := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun s hq => ?_) hlbu
    · simp only [overflowZeroInv, overflowZeroCore] at hp ⊢
      xperm_hyp hp
    · simp only [scanPre] at ⊢
      simp [hzero] at hq
      change (F ** ((.x5 : Reg) ↦ᵣ
          (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes) s at hq
      xperm_hyp hq
  have hbeq := cpsBranchWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := beq_spec_gen_within .x28 .x0 (12 : BitVec 13)
      (0 : Word) (0 : Word) (mulBase + 296))
  rw [show mulBase + 296 + Rv64.signExtend13 (12 : BitVec 13) = mulBase + 308 from by decide,
    show mulBase + 296 + 4 = mulBase + 300 from by decide] at hbeq
  have hbeqF := cpsBranchWithin_frameR
    frame hframe_pc hbeq
  have hbeq' : cpsBranchWithin 1 (mulBase + 296) mulCR
      ((((.x28 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** frame)
      (mulBase + 308) (⌜(0 : Word) = 0⌝ ** scanPre)
      (mulBase + 300) (⌜(0 : Word) ≠ 0⌝ ** scanPre) := by
    refine cpsBranchWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        simp only [frame, scanPre] at hq ⊢
        xperm_hyp hq)
      (fun _ hq => by
        simp only [frame, scanPre] at hq ⊢
        xperm_hyp hq) hbeqF
  have hstep : cpsTripleWithin 3 (mulBase + 308) (mulBase + 288) mulCR
      scanPre (overflowZeroInv F accBytes (k + 1)) := by
    simpa only [scanPre] using overflowZeroStep_spec F hF accBytes hlen k hk
  have htaken : cpsTripleWithin 3 (mulBase + 308) (mulBase + 288) mulCR
      (⌜(0 : Word) = 0⌝ ** scanPre)
      (overflowZeroInv F accBytes (k + 1)) := by
    exact cpsTripleWithin_pure_pre (fun _ => hstep)
  have hfall : cpsTripleWithin 3 (mulBase + 300) (mulBase + 288) mulCR
      (⌜(0 : Word) ≠ 0⌝ ** scanPre)
      (overflowZeroInv F accBytes (k + 1)) := by
    refine cpsTripleWithin_pure_pre ?_
    intro hneq
    exact False.elim (hneq rfl)
  have hinner := cpsBranchWithin_merge_same_cr (nSteps2 := 3)
    hbeq' htaken hfall
  have hinner' : cpsTripleWithin 4 (mulBase + 296) (mulBase + 288) mulCR
      scanPre (overflowZeroInv F accBytes (k + 1)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hinner
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbu' hinner'

theorem overflowZeroIter_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (hlen : accBytes.length = 40)
    (k : Nat) (hk : k < 8)
    (hzero : accBytes[32 + k]'(by omega) = 0) :
    cpsTripleWithin 6 (mulBase + 288) (mulBase + 288) mulCR
      (overflowZeroInv F accBytes k)
      (overflowZeroInv F accBytes (k + 1)) := by
  let frame : Assertion :=
    F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** bytesRegion accBase accBytes
  have hframe_pc : frame.pcFree := by
    dsimp only [frame]
    apply pcFree_sepConj
    · exact hF
    · pcf
  have hbeq := cpsBranchWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := beq_spec_gen_within .x6 .x0 (32 : BitVec 13)
      (BitVec.ofNat 64 (8 - k)) (0 : Word) (mulBase + 288))
  rw [show mulBase + 288 + Rv64.signExtend13 (32 : BitVec 13) = mulBase + 320 from by decide,
    show mulBase + 288 + 4 = mulBase + 292 from by decide] at hbeq
  have hbeqF := cpsBranchWithin_frameR frame hframe_pc hbeq
  have hbeq' : cpsBranchWithin 1 (mulBase + 288) mulCR
      (overflowZeroInv F accBytes k)
      (mulBase + 320) (⌜BitVec.ofNat 64 (8 - k) = 0⌝ ** overflowZeroInv F accBytes k)
      (mulBase + 292) (⌜BitVec.ofNat 64 (8 - k) ≠ 0⌝ ** overflowZeroInv F accBytes k) := by
    refine cpsBranchWithin_weaken
      (fun _ hp => by
        simp only [overflowZeroInv, overflowZeroCore, frame] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [overflowZeroInv, overflowZeroCore, frame] at hq ⊢
        xperm_hyp hq)
      (fun _ hq => by
        simp only [overflowZeroInv, overflowZeroCore, frame] at hq ⊢
        xperm_hyp hq) hbeqF
  have htaken : cpsTripleWithin 5 (mulBase + 320) (mulBase + 288) mulCR
      (⌜BitVec.ofNat 64 (8 - k) = 0⌝ ** overflowZeroInv F accBytes k)
      (overflowZeroInv F accBytes (k + 1)) := by
    refine cpsTripleWithin_pure_pre ?_
    intro hzero'
    exact False.elim (overflow_scan_ctr_ne k hk (by simpa using hzero'))
  have hcont := overflowZeroContinue_spec F hF accBytes hlen k hk hzero
  have hfall : cpsTripleWithin 5 (mulBase + 292) (mulBase + 288) mulCR
      (⌜BitVec.ofNat 64 (8 - k) ≠ 0⌝ ** overflowZeroInv F accBytes k)
      (overflowZeroInv F accBytes (k + 1)) := by
    exact cpsTripleWithin_pure_pre (fun _ => hcont)
  exact cpsBranchWithin_merge_same_cr (nSteps2 := 5) hbeq' htaken hfall

theorem overflowZeroExh_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) :
    cpsTripleWithin 1 (mulBase + 288) (mulBase + 320) mulCR
      (overflowZeroInv F accBytes 8)
      (overflowZeroInv F accBytes 8) := by
  let frame : Assertion :=
    F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 40)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 ** bytesRegion accBase accBytes
  have hframe_pc : frame.pcFree := by
    dsimp only [frame]
    apply pcFree_sepConj
    · exact hF
    · pcf
  have hbeq := cpsBranchWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := beq_spec_gen_within .x6 .x0 (32 : BitVec 13)
      (0 : Word) (0 : Word) (mulBase + 288))
  rw [show mulBase + 288 + Rv64.signExtend13 (32 : BitVec 13) = mulBase + 320 from by decide,
    show mulBase + 288 + 4 = mulBase + 292 from by decide] at hbeq
  have hbeqF := cpsBranchWithin_frameR frame hframe_pc hbeq
  have hbeq' : cpsBranchWithin 1 (mulBase + 288) mulCR
      (overflowZeroInv F accBytes 8)
      (mulBase + 320) (⌜(0 : Word) = 0⌝ ** overflowZeroInv F accBytes 8)
      (mulBase + 292) (⌜(0 : Word) ≠ 0⌝ ** overflowZeroInv F accBytes 8) := by
    refine cpsBranchWithin_weaken
      (fun _ hp => by
        simp only [overflowZeroInv, overflowZeroCore, frame] at hp ⊢
        rw [show BitVec.ofNat 64 (8 - 8) = (0 : Word) from by decide,
          show BitVec.ofNat 64 (32 + 8) = BitVec.ofNat 64 40 from by decide] at hp
        xperm_hyp hp)
      (fun _ hq => by
        simp only [overflowZeroInv, overflowZeroCore, frame] at hq ⊢
        rw [show BitVec.ofNat 64 (8 - 8) = (0 : Word) from by decide,
          show BitVec.ofNat 64 (32 + 8) = BitVec.ofNat 64 40 from by decide] at ⊢
        xperm_hyp hq)
      (fun _ hq => by
        simp only [overflowZeroInv, overflowZeroCore, frame] at hq ⊢
        rw [show BitVec.ofNat 64 (8 - 8) = (0 : Word) from by decide,
          show BitVec.ofNat 64 (32 + 8) = BitVec.ofNat 64 40 from by decide] at ⊢
        xperm_hyp hq) hbeqF
  have htaken : cpsTripleWithin 0 (mulBase + 320) (mulBase + 320) mulCR
      (⌜(0 : Word) = 0⌝ ** overflowZeroInv F accBytes 8)
      (overflowZeroInv F accBytes 8) := by
    refine cpsTripleWithin_pure_pre ?_
    intro _heq
    exact cpsTripleWithin_extend_code (cr' := mulCR)
      (hmono := fun a i h => by simp [CodeReq.empty] at h)
      (cpsTripleWithin_refl (fun _ hp => hp))
  have hfall : cpsTripleWithin 0 (mulBase + 292) (mulBase + 320) mulCR
      (⌜(0 : Word) ≠ 0⌝ ** overflowZeroInv F accBytes 8)
      (overflowZeroInv F accBytes 8) := by
    refine cpsTripleWithin_pure_pre ?_
    intro hneq
    exact False.elim (hneq rfl)
  exact cpsBranchWithin_merge_same_cr (nSteps2 := 0) hbeq' htaken hfall

theorem overflowZeroLoop_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (hlen : accBytes.length = 40)
    (hzero : ∀ i : Fin 8,
      accBytes[32 + i.1]'(by rw [hlen]; omega) = 0) :
    cpsTripleWithin 49 (mulBase + 288) (mulBase + 320) mulCR
      (overflowZeroInv F accBytes 0)
      (overflowZeroInv F accBytes 8) := by
  exact retLoop_spec 8 6 1 (overflowZeroInv F accBytes)
    (fun k hk => overflowZeroIter_spec F hF accBytes hlen k hk
      (hzero ⟨k, hk⟩))
    (overflowZeroExh_spec F hF accBytes)

theorem overflowNonzeroTail_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (_hlen : accBytes.length = 40)
    (k : Nat) (_hk : k < 8) (old28 : Word) (_hne : old28 ≠ (0 : Word)) :
    cpsTripleWithin 2 (mulBase + 300) (mulBase + 320) mulCR
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ old28) ** bytesRegion accBase accBytes)
      (overflowNonzeroInv F accBytes k) := by
  have h1 := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := li_spec_gen_within .x10 (0 : Word) (1 : Word)
      (mulBase + 300) (by decide))
  rw [show mulBase + 300 + 4 = mulBase + 304 from by decide] at h1
  have h1f := cpsTripleWithin_frameR
    (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ old28) **
      bytesRegion accBase accBytes)
    (by
      apply pcFree_sepConj
      · exact hF
      · pcf) h1
  have h2 := cpsTripleWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := jal_x0_spec_gen_within (16 : BitVec 21) (mulBase + 304))
  rw [show mulBase + 304 + Rv64.signExtend21 (16 : BitVec 21) =
      mulBase + 320 from by decide] at h2
  have h2f := cpsTripleWithin_frameR
    (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
      ((.x28 : Reg) ↦ᵣ old28) ** bytesRegion accBase accBytes)
    (by
      apply pcFree_sepConj
      · exact hF
      · pcf) h2
  have h2f' : cpsTripleWithin 1 (mulBase + 304) (mulBase + 320) mulCR
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
        ((.x28 : Reg) ↦ᵣ old28) ** bytesRegion accBase accBytes)
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
        ((.x28 : Reg) ↦ᵣ old28) ** bytesRegion accBase accBytes) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by simpa only [sepConj_emp_left'] using hp)
      (fun _ hq => by simpa only [sepConj_emp_left'] using hq) h2f
  have hs := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h1f h2f'
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hs
  intro h hq
  unfold overflowNonzeroInv
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (regIs_to_regOwn .x28 _)
              (fun _ hh => hh)))))) h hq

theorem overflowNonzeroInner_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (_hlen : accBytes.length = 40)
    (k : Nat) (hk : k < 8)
    (hbyte : accBytes[32 + k]'(by omega) ≠ 0) :
    cpsBranchWithin 4 (mulBase + 296) mulCR
      (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x28 : Reg) ↦ᵣ (accBytes[32 + k]'(by omega)).zeroExtend 64) **
        bytesRegion accBase accBytes)
      (mulBase + 320) (overflowNonzeroInv F accBytes k)
      (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
  let byteW : Word := (accBytes[32 + k]'(by omega)).zeroExtend 64
  have hbyteW : byteW ≠ (0 : Word) := by
    dsimp [byteW]
    intro h
    apply hbyte
    have hmod := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth] at hmod
    have hlt : (accBytes[32 + k]'(by omega)).toNat < 256 :=
      (accBytes[32 + k]'(by omega)).isLt
    have hmod' : (accBytes[32 + k]'(by omega)).toNat % 2 ^ 64 = 0 := by
      simpa using hmod
    rw [Nat.mod_eq_of_lt (by omega)] at hmod'
    apply BitVec.eq_of_toNat_eq
    simpa using hmod'
  let pre : Assertion :=
    F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ byteW) ** bytesRegion accBase accBytes
  let frame : Assertion :=
    F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion accBase accBytes
  have hframe_pc : frame.pcFree := by
    dsimp only [frame]
    apply pcFree_sepConj
    · exact hF
    · pcf
  have hbr := cpsBranchWithin_extend_code (cr' := mulCR)
    (hmono := by code_mem)
    (h := beq_spec_gen_within .x28 .x0 (12 : BitVec 13)
      byteW (0 : Word) (mulBase + 296))
  rw [show mulBase + 296 + Rv64.signExtend13 (12 : BitVec 13) =
      mulBase + 308 from by decide,
    show mulBase + 296 + 4 = mulBase + 300 from by decide] at hbr
  have hbrF := cpsBranchWithin_frameR frame hframe_pc hbr
  have hbr' : cpsBranchWithin 1 (mulBase + 296) mulCR
      pre
      (mulBase + 308) (⌜byteW = 0⌝ ** pre)
      (mulBase + 300) (⌜byteW ≠ 0⌝ ** pre) := by
    refine cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (fun _ hq => by xperm_hyp hq) hbrF
  have hzero : cpsBranchWithin 3 (mulBase + 308) mulCR
      (⌜byteW = 0⌝ ** pre)
      (mulBase + 320) (overflowNonzeroInv F accBytes k)
      (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
    refine cpsBranchWithin_pure_pre ?_
    intro hz
    exact False.elim (hbyteW hz)
  have hnonzero : cpsBranchWithin 3 (mulBase + 300) mulCR
      (⌜byteW ≠ 0⌝ ** pre)
      (mulBase + 320) (overflowNonzeroInv F accBytes k)
      (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
    refine cpsBranchWithin_pure_pre ?_
    intro hn
    have ht := overflowNonzeroTail_spec F hF accBytes _hlen k hk byteW hn
    exact cpsTripleWithin_as_cpsBranchWithin_left
      (mulBase + 288) (overflowZeroInv F accBytes (k + 1))
      (cpsTripleWithin_mono_nSteps (by omega) ht)
  have hinner := cpsBranchWithin_merge_branch_same_cr
    (m := 3) hbr' hzero hnonzero
  simpa only [pre, byteW] using hinner

theorem overflowScanIter_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (hlen : accBytes.length = 40)
    (k : Nat) (hk : k < 8) :
    cpsBranchWithin 6 (mulBase + 288) mulCR
      (overflowZeroInv F accBytes k)
      (mulBase + 320) (overflowNonzeroPost F accBytes)
      (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
  by_cases hzero : accBytes[32 + k]'(by omega) = 0
  · have hz := overflowZeroIter_spec F hF accBytes hlen k hk hzero
    exact cpsTripleWithin_as_cpsBranchWithin_right
      (mulBase + 320) (overflowNonzeroPost F accBytes) hz
  · let frame : Assertion :=
      F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
        bytesRegion accBase accBytes
    have hframe_pc : frame.pcFree := by
      dsimp only [frame]
      apply pcFree_sepConj
      · exact hF
      · pcf
    have hbeq := cpsBranchWithin_extend_code (cr' := mulCR)
      (hmono := by code_mem)
      (h := beq_spec_gen_within .x6 .x0 (32 : BitVec 13)
        (BitVec.ofNat 64 (8 - k)) (0 : Word) (mulBase + 288))
    rw [show mulBase + 288 + Rv64.signExtend13 (32 : BitVec 13) =
        mulBase + 320 from by decide,
      show mulBase + 288 + 4 = mulBase + 292 from by decide] at hbeq
    have hbeqF := cpsBranchWithin_frameR frame hframe_pc hbeq
    have hbeq' : cpsBranchWithin 1 (mulBase + 288) mulCR
        (overflowZeroInv F accBytes k)
        (mulBase + 320) (⌜BitVec.ofNat 64 (8 - k) = 0⌝ **
          overflowZeroInv F accBytes k)
        (mulBase + 292) (⌜BitVec.ofNat 64 (8 - k) ≠ 0⌝ **
          overflowZeroInv F accBytes k) := by
      refine cpsBranchWithin_weaken
        (fun _ hp => by
          simp only [overflowZeroInv, overflowZeroCore, frame] at hp ⊢
          xperm_hyp hp)
        (fun _ hq => by
          simp only [overflowZeroInv, overflowZeroCore, frame] at hq ⊢
          xperm_hyp hq)
        (fun _ hq => by
          simp only [overflowZeroInv, overflowZeroCore, frame] at hq ⊢
          xperm_hyp hq) hbeqF
    have htaken : cpsBranchWithin 5 (mulBase + 320) mulCR
        (⌜BitVec.ofNat 64 (8 - k) = 0⌝ ** overflowZeroInv F accBytes k)
        (mulBase + 320) (overflowNonzeroPost F accBytes)
        (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
      refine cpsBranchWithin_pure_pre ?_
      intro hzeroCtr
      exact False.elim (overflow_scan_ctr_ne k hk (by simpa using hzeroCtr))
    have hlbu := overflowLbu_spec F hF accBytes hlen k hk
    let byteW : Word := (accBytes[32 + k]'(by omega)).zeroExtend 64
    have hinner := overflowNonzeroInner_spec F hF accBytes hlen k hk hzero
    have hinner' : cpsBranchWithin 4 (mulBase + 296) mulCR
        (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
          ((.x28 : Reg) ↦ᵣ byteW) ** bytesRegion accBase accBytes)
        (mulBase + 320) (overflowNonzeroInv F accBytes k)
        (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
      simpa only [byteW] using hinner
    have hinner'' : cpsBranchWithin 4 (mulBase + 296) mulCR
        (F ** ((.x5 : Reg) ↦ᵣ (accBase + BitVec.ofNat 64 (32 + k))) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (8 - k)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
          ((.x28 : Reg) ↦ᵣ byteW) ** bytesRegion accBase accBytes)
        (mulBase + 320) (overflowNonzeroPost F accBytes)
        (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
      refine cpsBranchWithin_weaken (fun _ hp => hp)
        (fun _ hq => ⟨k, hq⟩) (fun _ hq => hq) hinner'
    have hcont := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hlbu hinner''
    have hfall : cpsBranchWithin 5 (mulBase + 292) mulCR
        (⌜BitVec.ofNat 64 (8 - k) ≠ 0⌝ ** overflowZeroInv F accBytes k)
        (mulBase + 320) (overflowNonzeroPost F accBytes)
        (mulBase + 288) (overflowZeroInv F accBytes (k + 1)) := by
      exact cpsBranchWithin_pure_pre (fun _ => hcont)
    exact cpsBranchWithin_merge_branch_same_cr
      (m := 5) hbeq' htaken hfall

theorem overflowScanLoop_spec (F : Assertion) (hF : F.pcFree)
    (accBytes : List (BitVec 8)) (hlen : accBytes.length = 40) :
    cpsBranchWithin 49 (mulBase + 288) mulCR
      (overflowZeroInv F accBytes 0)
      (mulBase + 320) (overflowNonzeroPost F accBytes)
      (mulBase + 320) (overflowZeroInv F accBytes 8) := by
  exact twoExitRetLoop_spec (hdr := mulBase + 288)
    (exitA := mulBase + 320) (exitB := mulBase + 320) (cr := mulCR)
    8 6 1 (overflowZeroInv F accBytes)
    (fun k hk => overflowScanIter_spec F hF accBytes hlen k hk)
    (overflowZeroExh_spec F hF accBytes)

/-! ## Overflow tail to the saved-register epilogue

The scan has two semantic exits but one machine PC.  Keep the scratch cells
in the post while composing the epilogue: they are caller-owned resources, not
facts that may be silently discarded merely because the return path does not
read them. -/

def mulEpiloguePre (spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 : Word) : Assertion :=
  ((.x2 : Reg) ↦ᵣ spNew) ** ((.x1 : Reg) ↦ᵣ j1) **
    ((.x8 : Reg) ↦ᵣ j8) ** ((.x9 : Reg) ↦ᵣ j9) **
    ((.x18 : Reg) ↦ᵣ j18) ** ((.x19 : Reg) ↦ᵣ j19) ** ((.x20 : Reg) ↦ᵣ j20) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

def mulEpiloguePost (spNew vRa v8 v9 v18 v19 v20 : Word) : Assertion :=
  ((.x2 : Reg) ↦ᵣ (spNew + Rv64.signExtend12 (48 : BitVec 12))) **
    ((.x1 : Reg) ↦ᵣ vRa) ** ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
    ((.x18 : Reg) ↦ᵣ v18) ** ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
    frameSlots spNew vRa v8 v9 v18 v19 v20

def overflowTailPost
    (spNew vRa v8 v9 v18 v19 v20 outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) : Assertion :=
  fun s =>
    (∃ k, (mulEpiloguePost spNew vRa v8 v9 v18 v19 v20 **
      bytesRegion outPtr outBytes ** overflowNonzeroCore accBytes k) s) ∨
    (mulEpiloguePost spNew vRa v8 v9 v18 v19 v20 **
      bytesRegion outPtr outBytes ** overflowZeroCore accBytes 8) s

theorem overflowNonzero_epilogue_spec
    (spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 8 (mulBase + 320) vRa mulCR
      (overflowNonzeroPost (mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
        bytesRegion outPtr outBytes) accBytes)
      (fun s => ∃ k, (mulEpiloguePost spNew vRa v8 v9 v18 v19 v20 **
        bytesRegion outPtr outBytes ** overflowNonzeroCore accBytes k) s) := by
  intro R hR s hcr hpre hpc
  obtain ⟨hs, hcompat, hsplit⟩ := hpre
  obtain ⟨hOuter1, hOuter2, hdOuter, huOuter, hq, hR0⟩ := hsplit
  obtain ⟨k, hk⟩ := hq
  have hframe : (bytesRegion outPtr outBytes ** overflowNonzeroCore accBytes k).pcFree := by
    pcf
  have hepi := epilogue_spec spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 hret
  have hepiF := cpsTripleWithin_frameR
    (bytesRegion outPtr outBytes ** overflowNonzeroCore accBytes k) hframe hepi
  have hpre' : ((mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
      (bytesRegion outPtr outBytes ** overflowNonzeroCore accBytes k)) ** R).holdsFor s := by
    obtain ⟨hFst, hCoreSt, hFdis, hFuni, hFprop, hCoreProp⟩ := hk
    obtain ⟨hPst, hOutSt, hPdis, hPuni, hPprop, hOutProp⟩ := hFprop
    have hFNested : ((mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
        bytesRegion outPtr outBytes) ** overflowNonzeroCore accBytes k) hOuter1 := by
      exact ⟨hFst, hCoreSt, hFdis, hFuni,
        ⟨hPst, hOutSt, hPdis, hPuni, hPprop, hOutProp⟩, hCoreProp⟩
    have hNested := (sepConj_assoc _).mp hFNested
    refine ⟨hs, hcompat, ?_⟩
    exact ⟨hOuter1, hOuter2, hdOuter, huOuter, hNested, hR0⟩
  obtain ⟨n, hn, s', hstep, hpc', hpost⟩ := hepiF (R := R) hR s hcr hpre' hpc
  refine ⟨n, hn, s', hstep, hpc', ?_⟩
  obtain ⟨hs', hcompat', hpost'⟩ := hpost
  obtain ⟨ha, hb, hdab, huab, hpa, hpb⟩ := hpost'
  exact ⟨hs', hcompat', ⟨ha, hb, hdab, huab,
    ⟨k, hpa⟩, hpb⟩⟩

theorem overflowZero_epilogue_spec
    (spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 8 (mulBase + 320) vRa mulCR
      (overflowZeroInv
        (mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
          bytesRegion outPtr outBytes) accBytes 8)
      (fun s => (mulEpiloguePost spNew vRa v8 v9 v18 v19 v20 **
        bytesRegion outPtr outBytes ** overflowZeroCore accBytes 8) s) := by
  have hepi := epilogue_spec spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 hret
  have hframe : (bytesRegion outPtr outBytes ** overflowZeroCore accBytes 8).pcFree := by
    pcf
  have hepiF := cpsTripleWithin_frameR
    (bytesRegion outPtr outBytes ** overflowZeroCore accBytes 8) hframe hepi
  have hpre : ∀ h, overflowZeroInv
      (mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
        bytesRegion outPtr outBytes) accBytes 8 h →
      ((mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
        (bytesRegion outPtr outBytes ** overflowZeroCore accBytes 8)) h) := by
    intro h hp
    unfold overflowZeroInv at hp
    exact (sepConj_assoc _).mp hp
  exact cpsTripleWithin_weaken hpre (fun _ hq => hq) hepiF

theorem overflowTail_epilogue_spec
    (spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 outPtr : Word)
    (accBytes outBytes : List (BitVec 8)) (hlen : accBytes.length = 40)
    (hret : (vRa &&& ~~~(1 : Word)) = vRa) :
    cpsTripleWithin 57 (mulBase + 288) vRa mulCR
      (overflowZeroInv
        (mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
          bytesRegion outPtr outBytes) accBytes 0)
      (overflowTailPost spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes) := by
  let F0 := mulEpiloguePre spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 **
    bytesRegion outPtr outBytes
  have hF0 : F0.pcFree := by
    dsimp only [F0]
    pcf
  have hscan := overflowScanLoop_spec F0 hF0 accBytes hlen
  have hnon := overflowNonzero_epilogue_spec
    spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 outPtr
    accBytes outBytes hret
  have hnon' : cpsTripleWithin 8 (mulBase + 320) vRa mulCR
      (overflowNonzeroPost F0 accBytes)
      (overflowTailPost spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp) (fun _ hp => Or.inl hp) hnon
  have hzero := overflowZero_epilogue_spec
    spNew vRa v8 v9 v18 v19 v20 j1 j8 j9 j18 j19 j20 outPtr
    accBytes outBytes hret
  have hzero' : cpsTripleWithin 8 (mulBase + 320) vRa mulCR
      (overflowZeroInv F0 accBytes 8)
      (overflowTailPost spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp) (fun _ hp => Or.inr hp) hzero
  exact cpsBranchWithin_merge_same_cr hscan hnon' hzero'

def mulTailExtra
    (aPtr b outPtr : Word) (aBytes : List (BitVec 8)) : Assertion :=
  bytesRegion aPtr aBytes ** ((.x7 : Reg) ↦ᵣ (0 : Word)) **
    ((.x11 : Reg) ↦ᵣ b) ** ((.x12 : Reg) ↦ᵣ outPtr) **
    regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

def mulWholeBodyPost
    (spNew vRa v8 v9 v18 v19 v20 aPtr b outPtr : Word)
    (aBytes : List (BitVec 8)) (accBytes outBytes : List (BitVec 8)) : Assertion :=
  mulTailExtra aPtr b outPtr aBytes **
    overflowTailPost spNew vRa v8 v9 v18 v19 v20 outPtr accBytes outBytes


end EvmAsm.Codegen.U256MulU64Be
